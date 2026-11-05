import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SquareIntegrableSemisimplicity
import Langlands.Representation.Plancherel.CoefficientTensors
import Langlands.Representation.Unitary.CentralCharacterProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof

/-! # Coefficients of unitary admissible representations (Waldspurger, Theorem VIII.4.2)

Waldspurger, proof of Theorem VIII.4.2 (printed pp. 330–331), inclusion
`p_χ(°C(G)) ⊂ A₂(G)_χ`: the representation `(ρ, V)` of `G` on `V = p_χ(°C(H \ G))` by right
translations is unitary and admissible, hence semisimple; its coefficient space `A(ρ)` is spanned
by the functions `g ↦ (f₁, ρ(g) f₂)`, which are square integrable on `A_G \ G`, so every
irreducible subrepresentation is square integrable with central character `χ` on `A_G`, and
`A(ρ) ⊂ A₂(G)_χ`; finally every `f ∈ V` is the coefficient `g ↦ mes(H)⁻¹ (p_χ °e, ρ(g) f)`, so
`V ⊂ A(ρ)`.

This module proves the representation-theoretic part for an abstract representation `ρ` with an
invariant positive form `b`: the coefficients `g ↦ ℓ(ρ(g) v)` of a smooth semisimple
representation lie in the span of the coefficient spaces of its irreducible subrepresentations;
for admissible unitary `ρ` whose coefficients `g ↦ b(e, ρ(g) f)` are square integrable on
`G ⧸ A` and on which `A` acts by a character `χ`, these subrepresentations are square integrable
modulo `A` with central character `χ` on `A`; and a reproducing identity
`ev f = (g ↦ b(e, ρ(g) f))` puts `ev f` in that span.
-/

noncomputable section

open MeasureTheory

namespace Langlands.HarishChandraSchwartz

open Langlands.Plancherel

universe u v

section Coefficients

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- A subrepresentation of a smooth representation, bundled as a smooth representation. -/
abbrev subrepresentationSmoothRep (hs : IsSmooth ρ) (S : Subrepresentation ρ) :
    SmoothRep.{0, u, v} ℂ G :=
  SmoothRep.of S.toRepresentation
    (isSmooth_of_injective (ScalarSubReduction.inclusion ρ S)
      (ScalarSubReduction.inclusion_injective ρ S) hs)

/-- The span `Σ_S A(S)` of the coefficient spaces of the subrepresentations `S` of `ρ`
satisfying `p`. With `p = irreducible, square integrable modulo A, with central character χ on
A`, this is the part of Waldspurger's `A₂(G)_χ = ⊕_{ω ∈ E₂(G)_χ} A(ω)` coming from
subrepresentations of `ρ`. -/
def subrepresentationCoefficientSpace (hs : IsSmooth ρ) (p : Subrepresentation ρ → Prop) :
    Submodule ℂ (LocallyConstant G ℂ) :=
  ⨆ (S : Subrepresentation ρ) (_ : p S),
    LinearMap.range (coefficientTensorMap (subrepresentationSmoothRep hs S))

theorem subrepresentationCoefficientSpace_mono (hs : IsSmooth ρ)
    {p q : Subrepresentation ρ → Prop} (hpq : ∀ S, p S → q S) :
    subrepresentationCoefficientSpace hs p ≤ subrepresentationCoefficientSpace hs q :=
  iSup_mono fun S => iSup_le fun hS =>
    le_iSup_of_le (hpq S hS) le_rfl

/-- The coefficient `g ↦ ℓ(ρ(g) x)` of a vector `x` of a subrepresentation `S` with `p S` lies in
`Σ_S A(S)`: it is the coefficient of `x` and of the restriction of `ℓ` to `S`. -/
theorem smoothCoefficient_mem_of_mem (hs : IsSmooth ρ) {p : Subrepresentation ρ → Prop}
    (S : Subrepresentation ρ) (hS : p S) {x : V} (hx : x ∈ S.toSubmodule)
    (ℓ : SmoothDual ρ) :
    smoothCoefficientBilinear (SmoothRep.of ρ hs) x ℓ ∈
      subrepresentationCoefficientSpace hs p := by
  refine Submodule.mem_iSup_of_mem S (Submodule.mem_iSup_of_mem hS ?_)
  refine ⟨(⟨x, hx⟩ : S.toSubmodule) ⊗ₜ[ℂ]
    contragredientMap (ScalarSubReduction.inclusion ρ S) ℓ, ?_⟩
  ext g
  rfl

/-- **Coefficients of a semisimple representation**: for a smooth representation `ρ` whose
`ℂ[G]`-module is semisimple, every coefficient `g ↦ ℓ(ρ(g) v)` lies in the span of the
coefficient spaces of the irreducible subrepresentations of `ρ`. -/
theorem smoothCoefficient_mem_irreducible (hs : IsSmooth ρ)
    (hss : IsSemisimpleModule (MonoidAlgebra ℂ G) ρ.asModule) (v : V) (ℓ : SmoothDual ρ) :
    smoothCoefficientBilinear (SmoothRep.of ρ hs) v ℓ ∈
      subrepresentationCoefficientSpace hs (fun S => S.toRepresentation.IsIrreducible) := by
  have hv : ρ.asModuleEquiv.symm v ∈ ⨆ N : {N : Submodule (MonoidAlgebra ℂ G) ρ.asModule //
      IsSimpleModule (MonoidAlgebra ℂ G) N}, N.1 := by
    have htop : (⨆ N : {N : Submodule (MonoidAlgebra ℂ G) ρ.asModule //
        IsSimpleModule (MonoidAlgebra ℂ G) N}, N.1) = ⊤ := by
      rw [← IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra ℂ G) ρ.asModule, sSup_eq_iSup']
      rfl
    rw [htop]
    exact Submodule.mem_top
  rw [← ρ.asModuleEquiv.apply_symm_apply v]
  refine Submodule.iSup_induction _ (motive := fun y : ρ.asModule =>
    smoothCoefficientBilinear (SmoothRep.of ρ hs) (ρ.asModuleEquiv y) ℓ ∈
      subrepresentationCoefficientSpace hs (fun S => S.toRepresentation.IsIrreducible))
    hv ?_ ?_ ?_
  · rintro ⟨N, hN⟩ y hy
    have hi : (Subrepresentation.ofSubmodule' N).toRepresentation.IsIrreducible := by
      rw [Representation.irreducible_iff_isSimpleModule_asModule]
      exact (subrepresentationAsModuleEquiv
        (Subrepresentation.ofSubmodule' N)).isSimpleModule_iff.mpr hN
    exact smoothCoefficient_mem_of_mem hs (Subrepresentation.ofSubmodule' N) hi
      (x := ρ.asModuleEquiv y) hy ℓ
  · change smoothCoefficientBilinear (SmoothRep.of ρ hs) (ρ.asModuleEquiv 0) ℓ ∈ _
    rw [map_zero, map_zero, LinearMap.zero_apply]
    exact zero_mem _
  · intro y z hy hz
    rw [map_add, map_add, LinearMap.add_apply]
    exact add_mem hy hz

end Coefficients

section Unitary

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- The coefficient `g ↦ b(e, ρ(g) f)` of a smooth representation with an invariant positive
form, as a locally constant function: it is the coefficient of `f` and the smooth functional
`b(e, -)`. -/
theorem formCoefficient_apply (b : InvariantPositiveForm ρ) (hs : IsSmooth ρ) (e f : V)
    (g : G) :
    smoothCoefficientBilinear (SmoothRep.of ρ hs) f (b.toSmoothDual hs e) g =
      b.inner e (ρ g f) :=
  rfl

/-- **Semisimplicity step** (proof of Theorem VIII.4.2): for an admissible representation with
an invariant positive form, every coefficient `g ↦ b(e, ρ(g) f)` lies in the span of the
coefficient spaces of the irreducible subrepresentations. -/
theorem formCoefficient_mem_irreducible
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (b : InvariantPositiveForm ρ) (ha : IsAdmissible ρ) (e f : V) :
    smoothCoefficientBilinear (SmoothRep.of ρ ha.1) f (b.toSmoothDual ha.1 e) ∈
      subrepresentationCoefficientSpace ha.1 (fun S => S.toRepresentation.IsIrreducible) := by
  have hss : IsSemisimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp
      (admissibleUnitarySemisimplicity G hcof V ρ ha ⟨b⟩)
  exact smoothCoefficient_mem_irreducible ha.1 hss f (b.toSmoothDual ha.1 e)

variable (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure]

/-- **Irreducible subrepresentations are square integrable** (proof of Theorem VIII.4.2): if
`ρ` is admissible with an invariant positive form `b` and every coefficient
`g ↦ b(e, ρ(g) f)` has square-integrable absolute value on `G ⧸ A` (hypothesis `hL2`), then every
irreducible subrepresentation of `ρ` is square integrable modulo `A`. -/
theorem isSquareIntegrable_of_irreducible_subrepresentation
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (b : InvariantPositiveForm ρ) (ha : IsAdmissible ρ)
    (hL2 : ∀ e f : V, ∃ F : G ⧸ A → ℝ, MemLp F 2 μ ∧
      ∀ g : G, F (QuotientGroup.mk g) = ‖b.inner e (ρ g f)‖)
    (S : Subrepresentation ρ) (hi : S.toRepresentation.IsIrreducible) :
    IsSquareIntegrableModCentralSubgroup A hA S.toRepresentation μ := by
  have hinj := ScalarSubReduction.inclusion_injective ρ S
  have hSa : IsAdmissible S.toRepresentation :=
    isAdmissible_of_injective (ScalarSubReduction.inclusion ρ S) hinj ha
  let bS := b.comap (ScalarSubReduction.inclusion ρ S) hinj
  obtain ⟨c⟩ := unitarizableCentralCharacter S.toRepresentation hSa hi ⟨bS⟩
  refine ⟨hSa, c, fun ℓ w => ?_⟩
  obtain ⟨e, rfl⟩ := (bS.smoothDualEquiv hcof hSa).surjective ℓ
  obtain ⟨F, hF, hFg⟩ := hL2 (e : V) (w : V)
  have heq : centralSubgroupCoefficientNorm A hA c
      (bS.smoothDualEquiv hcof hSa e).val w = F := by
    funext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [centralSubgroupCoefficientNorm_mk, hFg]
    rfl
  rw [heq]
  exact hF

/-- **Theorem VIII.4.2, inclusion `A(ρ) ⊂ A₂(G)_χ`, abstract form**: for an admissible
representation `ρ` with an invariant positive form `b`, on which `A` acts by the character `χ`
(`hχ`) and whose coefficients `g ↦ b(e, ρ(g) f)` are square integrable on `G ⧸ A` (`hL2`), every
coefficient `g ↦ b(e, ρ(g) f)` lies in the span of the coefficient spaces of the irreducible
subrepresentations of `ρ` that are square integrable modulo `A` and on which `A` acts by `χ`. -/
theorem formCoefficient_mem_squareIntegrable
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (b : InvariantPositiveForm ρ) (ha : IsAdmissible ρ) (χ : A →* ℂˣ)
    (hχ : ∀ (a : A) (x : V), ρ a x = (χ a : ℂ) • x)
    (hL2 : ∀ e f : V, ∃ F : G ⧸ A → ℝ, MemLp F 2 μ ∧
      ∀ g : G, F (QuotientGroup.mk g) = ‖b.inner e (ρ g f)‖) (e f : V) :
    smoothCoefficientBilinear (SmoothRep.of ρ ha.1) f (b.toSmoothDual ha.1 e) ∈
      subrepresentationCoefficientSpace ha.1 (fun S => S.toRepresentation.IsIrreducible ∧
        IsSquareIntegrableModCentralSubgroup A hA S.toRepresentation μ ∧
        ∀ (a : A) (y : S.toSubmodule), S.toRepresentation a y = (χ a : ℂ) • y) := by
  refine subrepresentationCoefficientSpace_mono ha.1 (fun S hi => ⟨hi,
    isSquareIntegrable_of_irreducible_subrepresentation A hA μ hcof b ha hL2 S hi,
    fun a y => Subtype.ext (hχ a y)⟩) (formCoefficient_mem_irreducible hcof b ha e f)

/-- **Theorem VIII.4.2, inclusion `V ⊂ A₂(G)_χ`, abstract form**: if moreover every `f ∈ V`
is realized by a function `ev f` on `G` that is a coefficient `g ↦ b(e, ρ(g) f)` for some
`e ∈ V` (`hrep`; in the source `ev f = f`, `e = mes(H)⁻¹ p_χ °e`), then `ev f` lies in the span
of the coefficient spaces of the irreducible subrepresentations of `ρ` that are square integrable
modulo `A` with central character `χ` on `A`. -/
theorem exists_mem_squareIntegrable_of_reproducing
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (b : InvariantPositiveForm ρ) (ha : IsAdmissible ρ) (χ : A →* ℂˣ)
    (hχ : ∀ (a : A) (x : V), ρ a x = (χ a : ℂ) • x)
    (hL2 : ∀ e f : V, ∃ F : G ⧸ A → ℝ, MemLp F 2 μ ∧
      ∀ g : G, F (QuotientGroup.mk g) = ‖b.inner e (ρ g f)‖)
    (ev : V → G → ℂ) (hrep : ∀ f : V, ∃ e : V, ∀ g : G, ev f g = b.inner e (ρ g f))
    (f : V) :
    ∃ φ ∈ subrepresentationCoefficientSpace ha.1 (fun S => S.toRepresentation.IsIrreducible ∧
        IsSquareIntegrableModCentralSubgroup A hA S.toRepresentation μ ∧
        ∀ (a : A) (y : S.toSubmodule), S.toRepresentation a y = (χ a : ℂ) • y),
      ⇑φ = ev f := by
  obtain ⟨e, he⟩ := hrep f
  exact ⟨_, formCoefficient_mem_squareIntegrable A hA μ hcof b ha χ hχ hL2 e f,
    funext fun g => (he g).symm⟩

end Unitary

end Langlands.HarishChandraSchwartz
