import Langlands.HarmonicAnalysis.GroupAction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.AdmissibleCoefficientSpace
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.L2
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceFamilyScalar
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.Smooth.Contragredient.ExactProof

/-! # Waldspurger, Lemma I.6.1 for left translation

Waldspurger I.6 (printed p. 249), Lemma I.6.1: for `f ∈ A_λ`, `V_{ρ×λ}(f) = A(λ̌_f)`, and
`A_λ = A(G)`. The module `AdmissibleCoefficientSpace` proves the statements for `ρ`; this module
deduces those for `λ` (the Library's `GroupAction.leftFunctions`) through
`f ↦ f̌ = (g ↦ f(g⁻¹))`, which intertwines `λ` with `ρ` (`checkIntertwiningMap`) and identifies
`λ_f` with `ρ_{f̌}` (`leftRightCheck`):

* `isLeftAdmissible_iff_check`: `f ∈ A_λ` iff `f̌ ∈ A_ρ`;
* `check_mem_coefficientFunctionSpace`: `A(π)ˇ ⊂ A(π̌)`, so `A(G)ˇ = A(G)` for the admissible
  coefficient spaces (`exists_admissible_coefficient_check`);
* `isLeftAdmissible_iff` (Lemma I.6.1 (2) for `λ`, `A_λ = A(G)`);
* `twoSidedTranslateSpan_eq_coefficientFunctionSpace_left` (Lemma I.6.1 (1) for `λ`). -/

noncomputable section

namespace Langlands.HarishChandraSchwartz

open Langlands.HarmonicAnalysis.GroupAction (leftFunctions leftFunctions_apply)

universe u

section LeftTranslates

variable {G : Type u} [Group G]

/-- Waldspurger's `V_λ(f)`. -/
abbrev leftTranslateSpan (f : G → ℂ) : Subrepresentation (leftFunctions (G := G)) :=
  FiniteVectors.orbitSubrepresentation leftFunctions f

/-- `f ↦ f̌` intertwines left translation with right translation. -/
def checkIntertwiningMap :
    (leftFunctions (G := G)).IntertwiningMap (Whittaker.rightTranslation ℂ G) where
  toLinearMap :=
    { toFun := check
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    funext x
    change check (leftFunctions g f) x = check f (x * g)
    rw [check_apply, check_apply, leftFunctions_apply, mul_inv_rev]

theorem checkIntertwiningMap_apply (f : G → ℂ) : checkIntertwiningMap f = check f :=
  rfl

theorem checkIntertwiningMap_injective :
    Function.Injective (checkIntertwiningMap (G := G)) := by
  intro _ _ h
  have h' := congrArg check h
  simpa [checkIntertwiningMap_apply, check_check] using h'

/-- The isomorphism `λ_f ≅ ρ_{f̌}` given by `f' ↦ f̌'`. -/
abbrev leftRightCheck (f : G → ℂ) :
    (leftTranslateSpan f).toRepresentation.IntertwiningMap
      (rightTranslateSpan (check f)).toRepresentation :=
  orbitSpanMap checkIntertwiningMap f

theorem leftRightCheck_apply (f : G → ℂ) (v : (leftTranslateSpan f).toSubmodule) :
    ((leftRightCheck f v : (rightTranslateSpan (check f)).toSubmodule) : G → ℂ) =
      check (v : G → ℂ) :=
  rfl

theorem leftRightCheck_injective (f : G → ℂ) : Function.Injective (leftRightCheck f) :=
  fun _ _ h => Subtype.ext (checkIntertwiningMap_injective (congrArg Subtype.val h))

theorem leftRightCheck_surjective (f : G → ℂ) : Function.Surjective (leftRightCheck f) :=
  orbitSpanMap_surjective _ f

/-- The functions `g ↦ v(g y)`, `v ∈ V_λ(f)`, are two-sided translates of `f`. -/
theorem translate_mem_twoSidedTranslateSpan_left {f : G → ℂ} (y : G) {v : G → ℂ}
    (hv : v ∈ (leftTranslateSpan f).toSubmodule) :
    (fun g => v (g * y)) ∈ twoSidedTranslateSpan f := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨h, rfl⟩ := hw
    refine Submodule.subset_span ⟨(y, h), ?_⟩
    funext g
    simp only [translate_apply, leftFunctions_apply, mul_assoc]
  | zero => exact (twoSidedTranslateSpan f).zero_mem
  | add a b _ _ ha hb => exact (twoSidedTranslateSpan f).add_mem ha hb
  | smul c a _ ha => exact (twoSidedTranslateSpan f).smul_mem c ha

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Waldspurger's `A_λ`: `f` is bi-invariant under a compact open subgroup and left translation
on `V_λ(f)` is admissible. -/
def IsLeftAdmissible (f : G → ℂ) : Prop :=
  (∃ H : CompactOpenSubgroup G, IsBiInvariant H.toSubgroup f) ∧
    IsAdmissible (leftTranslateSpan f).toRepresentation

variable [Nonempty (CompactOpenSubgroup G)]

/-- `f ∈ A_λ` if and only if `f̌ ∈ A_ρ`. -/
theorem isLeftAdmissible_iff_check (f : G → ℂ) :
    IsLeftAdmissible f ↔ IsRightAdmissible (check f) := by
  constructor
  · rintro ⟨⟨H, hH⟩, hW⟩
    exact ⟨⟨H, hH.check⟩, Langlands.Unramified.SphericalExistence.isAdmissible_of_surjective
      CompactOpenSubgroup.cofinal (leftRightCheck f) (leftRightCheck_surjective f) hW⟩
  · rintro ⟨⟨H, hH⟩, hW⟩
    refine ⟨⟨H, by simpa [check_check] using hH.check⟩, ?_⟩
    exact isAdmissible_of_injective (leftRightCheck f) (leftRightCheck_injective f) hW

omit [Nonempty (CompactOpenSubgroup G)] in
/-- `A(π)ˇ ⊂ A(π̌)`: `g ↦ ℓ(π(g⁻¹) x)` is the coefficient of `π̌` at `ℓ` and the evaluation at
`x`. -/
theorem check_mem_coefficientFunctionSpace {A : SmoothRep.{0, u, u} ℂ G}
    {f : G → ℂ} (hf : f ∈ coefficientFunctionSpace A) :
    check f ∈ coefficientFunctionSpace (contragredientRep A.representation) := by
  refine Submodule.iSup_induction _
    (motive := fun φ => check φ ∈ coefficientFunctionSpace (contragredientRep
      A.representation)) hf (fun ℓ y hy => ?_) ?_ (fun a b ha hb => ?_)
  · obtain ⟨x, rfl⟩ := hy
    have h := matrixCoefficient_mem_coefficientFunctionSpace
      (contragredientRep A.representation) (smoothBidual A.isSmooth x) ℓ
    convert h using 1
    funext g
    rfl
  · exact Submodule.zero_mem _
  · exact Submodule.add_mem _ ha hb

/-- `A(G)ˇ ⊂ A(G)`. -/
theorem exists_admissible_coefficient_check {f : G → ℂ}
    (h : ∃ A : SmoothRep.{0, u, u} ℂ G, IsAdmissible A.representation ∧
      f ∈ coefficientFunctionSpace A) :
    ∃ A : SmoothRep.{0, u, u} ℂ G, IsAdmissible A.representation ∧
      check f ∈ coefficientFunctionSpace A := by
  obtain ⟨A, hA, hf⟩ := h
  exact ⟨contragredientRep A.representation,
    isAdmissible_smoothContragredient_of_compact_cofinal CompactOpenSubgroup.cofinal _ hA,
    check_mem_coefficientFunctionSpace hf⟩

/-- **Waldspurger, Lemma I.6.1 (2)** for `λ`: `A_λ = A(G)`. -/
theorem isLeftAdmissible_iff (f : G → ℂ) :
    IsLeftAdmissible f ↔
      ∃ A : SmoothRep.{0, u, u} ℂ G, IsAdmissible A.representation ∧
        f ∈ coefficientFunctionSpace A := by
  rw [isLeftAdmissible_iff_check, isRightAdmissible_iff]
  constructor
  · intro h
    simpa [check_check] using exists_admissible_coefficient_check h
  · exact exists_admissible_coefficient_check

/-- **Waldspurger, Lemma I.6.1 (1)** for `λ`: for `f ∈ A_λ`, `V_{ρ×λ}(f) = A(λ̌_f)`. -/
theorem twoSidedTranslateSpan_eq_coefficientFunctionSpace_left {f : G → ℂ}
    (hf : IsLeftAdmissible f) :
    twoSidedTranslateSpan f =
      coefficientFunctionSpace (contragredientRep (leftTranslateSpan f).toRepresentation) := by
  have hfc : IsRightAdmissible (check f) := (isLeftAdmissible_iff_check f).1 hf
  have hLs : IsSmooth (leftTranslateSpan f).toRepresentation := hf.2.1
  have hρs : IsSmooth (rightTranslateSpan (check f)).toRepresentation := hfc.2.1
  obtain ⟨⟨H, hH⟩, -⟩ := id hfc
  have hfL : ∀ h ∈ H.toSubgroup, ∀ z, check f (h * z) = check f z := fun h hh z => by
    simpa using hH h hh 1 H.toSubgroup.one_mem z
  let evR : G → SmoothDual (rightTranslateSpan (check f)).toRepresentation := fun y =>
    ⟨evalFunctional (check f) y, isSmoothVector_evalFunctional H hfL y⟩
  let evL : G → SmoothDual (leftTranslateSpan f).toRepresentation := fun y =>
    contragredientMap (leftRightCheck f) (evR y⁻¹)
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g₁, g₂⟩, rfl⟩
    have h := matrixCoefficient_mem_coefficientFunctionSpace
      (contragredientRep (leftTranslateSpan f).toRepresentation)
      (smoothBidual hLs ⟨leftFunctions g₂ f, FiniteVectors.action_mem_orbitSpan _ g₂ f⟩)
      (evL g₁)
    have e : translate g₁ g₂ f = matrixCoefficient
        (contragredientRep (leftTranslateSpan f).toRepresentation).representation
        (smoothBidual hLs ⟨leftFunctions g₂ f, FiniteVectors.action_mem_orbitSpan _ g₂ f⟩).val
        (evL g₁) := by
      funext g
      change f (g₂⁻¹ * g * g₁) = f (g₂⁻¹ * ((g⁻¹)⁻¹ * (g₁⁻¹)⁻¹))
      simp only [inv_inv, mul_assoc]
    change translate g₁ g₂ f ∈ (coefficientFunctionSpace
      (contragredientRep (leftTranslateSpan f).toRepresentation) : Set (G → ℂ))
    rw [e]
    exact h
  · refine iSup_le fun Λ => ?_
    rintro _ ⟨ℓ, rfl⟩
    obtain ⟨x, rfl⟩ := smoothBidual_surjective_of_compact_cofinal CompactOpenSubgroup.cofinal _
      hf.2 Λ
    obtain ⟨ℓ', rfl⟩ := contragredientMap_surjective_of_injective_of_compact_cofinal
      CompactOpenSubgroup.cofinal hLs hρs (leftRightCheck f) (leftRightCheck_injective f) ℓ
    have key : ∀ ψ ∈ Submodule.span ℂ (Set.range (evalFunctional (check f))),
        (fun g => ψ (leftRightCheck f ((leftTranslateSpan f).toRepresentation g⁻¹ x))) ∈
          twoSidedTranslateSpan f := by
      intro ψ hψ
      induction hψ using Submodule.span_induction with
      | mem φ hφ =>
        obtain ⟨y, rfl⟩ := hφ
        have h := translate_mem_twoSidedTranslateSpan_left y⁻¹ x.2
        convert h using 1
        funext g
        change (x : G → ℂ) ((g⁻¹)⁻¹ * y⁻¹) = (x : G → ℂ) (g * y⁻¹)
        rw [inv_inv]
      | zero => exact (twoSidedTranslateSpan f).zero_mem
      | add a b _ _ ha hb => exact (twoSidedTranslateSpan f).add_mem ha hb
      | smul c a _ ha => exact (twoSidedTranslateSpan f).smul_mem c ha
    exact key ℓ'.val (mem_span_evalFunctional hfc ℓ')

end LeftTranslates

end Langlands.HarishChandraSchwartz
