import Langlands.Representation.Whittaker.ModelGenericSocleStatement
import Langlands.Representation.Whittaker.FunctionalExactness
import Langlands.Representation.RankinSelberg.UnequalRankSpecializationInputs
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.Representation.Classification.FiniteLengthProof
import Langlands.Representation.Classification.StrongIndecomposabilitySocleProof
import Langlands.Representation.Category.FiniteIndexRestriction
import Langlands.Group.GL.UpperUnipotentCompactContainmentProof
import Langlands.Group.GL.Padic
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Mathlib.RingTheory.FiniteLength

/-!
# The actual irreducible generic socle of a Whittaker coefficient model

The coefficient model of a representation of Whittaker type is a quotient of
it, hence admissible of finite length. Evaluation at the identity is nonzero
on every nonzero invariant subspace of this function model, and the model's
functional space is at most one-dimensional. Exactness of the functional
functor then forbids two nonzero invariant subspaces with zero intersection,
so the unique atom is the least nonzero subrepresentation.
-/

noncomputable section

namespace Langlands.Whittaker

open HarmonicAnalysis

universe uF uG uV uW

section Algebraic

variable {G : Type uG} [Group G] {N : Subgroup G} {θ : N →* ℂˣ}
variable {X : Type uV} [AddCommGroup X] [Module ℂ X]

/-- On a representation embedded in the equivariant function space, evaluation
at the identity is nonzero as soon as the representation has a nonzero vector:
a right translate moves a nonzero value to the identity. -/
theorem evaluationFunctional_ne_zero (ρ : Representation ℂ G X)
    (j : ρ.IntertwiningMap (functionRepresentation N θ)) (hj : Function.Injective j)
    {x : X} (hx : x ≠ 0) : (evaluationFunctional ρ j).val ≠ 0 := by
  intro h
  apply hx
  apply hj
  rw [map_zero]
  apply Subtype.ext
  funext g
  have hg : (evaluationFunctional ρ j).val (ρ g x) = 0 := by
    rw [h]
    rfl
  change (j (ρ g x)).val 1 = 0 at hg
  rw [j.isIntertwining] at hg
  change (j x).val (1 * g) = 0 at hg
  rw [one_mul] at hg
  exact hg

/-- A linear injection into a line makes its source at most one-dimensional:
every vector is a multiple of any fixed nonzero vector. -/
theorem exists_eq_smul_of_injective_line {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (φ : A →ₗ[ℂ] B) (hφ : Function.Injective φ)
    (e : B ≃ₗ[ℂ] ℂ) (a b : A) (hb : b ≠ 0) : ∃ c : ℂ, a = c • b := by
  have hb' : e (φ b) ≠ 0 := by
    intro h
    apply hb
    apply hφ
    rw [map_zero]
    apply e.injective
    rw [h, map_zero]
  refine ⟨e (φ a) / e (φ b), ?_⟩
  apply hφ
  apply e.injective
  rw [map_smul, map_smul, smul_eq_mul, div_mul_cancel₀ _ hb']

/-- A module in which every vector is a multiple of one nonzero vector is a line. -/
theorem nonempty_linearEquiv_of_forall_eq_smul {A : Type*} [AddCommGroup A] [Module ℂ A]
    (a : A) (ha : a ≠ 0) (h : ∀ x : A, ∃ c : ℂ, x = c • a) : Nonempty (A ≃ₗ[ℂ] ℂ) := by
  refine ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℂ A a)
    ⟨smul_left_injective ℂ ha, fun x => ?_⟩).symm⟩
  obtain ⟨c, rfl⟩ := h x
  exact ⟨c, rfl⟩

/-- A nonzero subrepresentation has a nonzero vector. -/
theorem exists_ne_zero_of_subrepresentation_ne_bot {ρ : Representation ℂ G X}
    (R : Subrepresentation ρ) (hR : R ≠ ⊥) : ∃ x : R.toSubmodule, x ≠ 0 := by
  have hR' : R.toSubmodule ≠ ⊥ := fun h => hR (Subrepresentation.toSubmodule_injective h)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR'
  exact ⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩

end Algebraic

section Smooth

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {X : Type uV} [AddCommGroup X] [Module ℂ X]

/-- A smooth representation embedded in an equivariant function space whose
functional space is at most one-dimensional has no two nonzero invariant
subspaces with zero intersection. If `S ⊓ T = ⊥`, the identity evaluation on
`S` extends through the injection `S → ρ/T`; its pullback vanishes on `T`, but
it must be a multiple of the evaluation functional, which does not. -/
theorem isStronglyIndecomposable_of_functionModel
    (U : Subgroup G) (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U)
    (θ : U →* ℂˣ) (hθ : IsLocallyConstant (fun u : U => (θ u : ℂ)))
    (ρ : Representation ℂ G X) (hρ : IsSmooth ρ)
    (j : ρ.IntertwiningMap (functionRepresentation U θ)) (hj : Function.Injective j)
    (hone : ∀ a b : functionals U θ ρ, b ≠ 0 → ∃ c : ℂ, a = c • b) :
    Classification.IsStronglyIndecomposable ρ := by
  intro S T hS hT hST
  let Q := ρ.quotient T.toSubmodule (fun g _ hv => T.apply_mem_toSubmodule g hv)
  let q : ρ.IntertwiningMap Q :=
    { toLinearMap := T.toSubmodule.mkQ
      isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hQ : IsSmooth Q := isSmooth_of_surjective q hq hρ
  let k : S.toRepresentation.IntertwiningMap Q :=
    { toLinearMap := T.toSubmodule.mkQ ∘ₗ S.toSubmodule.subtype
      isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }
  have hk : Function.Injective k := by
    intro x y hxy
    have hT' : (x : X) - y ∈ T.toSubmodule := (Submodule.Quotient.eq _).mp hxy
    have hmem : (x : X) - y ∈ (S ⊓ T).toSubmodule := ⟨Submodule.sub_mem _ x.2 y.2, hT'⟩
    rw [hST] at hmem
    change (x : X) - y ∈ (⊥ : Submodule ℂ X) at hmem
    exact Subtype.ext (sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp hmem))
  let jS : S.toRepresentation.IntertwiningMap (functionRepresentation U θ) :=
    { toLinearMap := j.toLinearMap ∘ₗ S.toSubmodule.subtype
      isIntertwining' := fun g => LinearMap.ext fun x =>
        LinearMap.congr_fun (j.isIntertwining' g) x.val }
  let jT : T.toRepresentation.IntertwiningMap (functionRepresentation U θ) :=
    { toLinearMap := j.toLinearMap ∘ₗ T.toSubmodule.subtype
      isIntertwining' := fun g => LinearMap.ext fun x =>
        LinearMap.congr_fun (j.isIntertwining' g) x.val }
  obtain ⟨x, hx⟩ := exists_ne_zero_of_subrepresentation_ne_bot S hS
  obtain ⟨t, ht⟩ := exists_ne_zero_of_subrepresentation_ne_bot T hT
  have hevS := evaluationFunctional_ne_zero S.toRepresentation jS
    (fun a b h => Subtype.ext (hj h)) hx
  have hevT := evaluationFunctional_ne_zero T.toRepresentation jT
    (fun a b h => Subtype.ext (hj h)) ht
  let ev := evaluationFunctional ρ j
  have hev : ev ≠ 0 := fun h =>
    evaluationFunctional_ne_zero ρ j hj (x := (x : X))
      (fun h0 => hx (Subtype.ext h0)) (congrArg Subtype.val h)
  obtain ⟨μ, hμ⟩ := functionalsComap_surjective_of_smooth U hU θ hθ k hk hQ
    (evaluationFunctional S.toRepresentation jS)
  let lam := functionalsComap (N := U) (θ := θ) q μ
  obtain ⟨c, hc⟩ := hone lam ev hev
  obtain ⟨t', ht'⟩ : ∃ t' : T.toSubmodule,
      (evaluationFunctional T.toRepresentation jT).val t' ≠ 0 := by
    by_contra! h
    exact hevT (LinearMap.ext h)
  have h1 : lam.val t' = 0 := by
    change μ.val (q t'.val) = 0
    have hqt : q t'.val = 0 := (Submodule.Quotient.mk_eq_zero _).mpr t'.2
    rw [hqt, map_zero]
  have h2 : lam.val t' = c * ev.val t' := by
    rw [hc]
    rfl
  have hc0 : c = 0 := by
    have hct : c * ev.val t' = 0 := h2 ▸ h1
    exact (mul_eq_zero.mp hct).resolve_right ht'
  apply hevS
  apply LinearMap.ext
  intro s
  have hs := congrArg (fun φ : functionals U θ S.toRepresentation => φ.val s) hμ
  change (functionalsComap (N := U) (θ := θ) k μ).val s =
    (evaluationFunctional S.toRepresentation jS).val s at hs
  rw [← hs]
  change lam.val s.val = 0
  rw [hc, hc0, zero_smul]
  rfl


/-- A quotient of an admissible finite-length representation whose functional
space is a line, embedded in an equivariant function space, has a least nonzero
subrepresentation. That subrepresentation is the unique atom: it is irreducible,
admissible, finitely generated, and its functional space is a line. -/
theorem exists_least_subrepresentation_of_functionModel {Y : Type uW} [AddCommGroup Y]
    [Module ℂ Y] [Nontrivial X]
    (hcof : ∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ H)
    (U : Subgroup G) (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U)
    (θ : U →* ℂˣ) (hθ : IsLocallyConstant (fun u : U => (θ u : ℂ)))
    {π : Representation ℂ G Y} (hπ : IsAdmissible π)
    (hπfl : IsFiniteLength (MonoidAlgebra ℂ G) π.asModule)
    (hπfun : Nonempty (functionals U θ π ≃ₗ[ℂ] ℂ))
    (ρ : Representation ℂ G X) (f : π.IntertwiningMap ρ) (hf : Function.Surjective f)
    (j : ρ.IntertwiningMap (functionRepresentation U θ)) (hj : Function.Injective j) :
    ∃ S : Subrepresentation ρ, S ≠ ⊥ ∧ S.toRepresentation.IsIrreducible ∧
      (∀ T : Subrepresentation ρ, T ≠ ⊥ → S ≤ T) ∧ IsAdmissible S.toRepresentation ∧
      Module.Finite (MonoidAlgebra ℂ G) S.toRepresentation.asModule ∧
      Nonempty (functionals U θ S.toRepresentation ≃ₗ[ℂ] ℂ) := by
  have hρ : IsAdmissible ρ := Unramified.SphericalExistence.isAdmissible_of_surjective hcof f hf hπ
  have hρfl : IsFiniteLength (MonoidAlgebra ℂ G) ρ.asModule :=
    FiniteLengthAssembly.finiteLength_of_surjective f hf hπfl
  have hone : ∀ a b : functionals U θ ρ, b ≠ 0 → ∃ c : ℂ, a = c • b :=
    exists_eq_smul_of_injective_line (functionalsComap (N := U) (θ := θ) f)
      (functionalsComap_injective U θ f hf) (Classical.choice hπfun)
  have hSI : Classification.IsStronglyIndecomposable ρ :=
    isStronglyIndecomposable_of_functionModel U hU θ hθ ρ hρ.1 j hj hone
  have hArt := (isFiniteLength_iff_isNoetherian_isArtinian.mp hρfl).2
  obtain ⟨S, hS, -⟩ := Classification.unique_atom_of_stronglyIndecomposable hArt hSI
  let ι : S.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  have hSfl := FiniteLengthAssembly.finiteLength_of_injective ι hι hρfl
  have hSnoeth := (isFiniteLength_iff_isNoetherian_isArtinian.mp hSfl).1
  refine ⟨S, hS.ne_bot, FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom S hS,
    ?_, isAdmissible_of_injective ι hι hρ, inferInstance, ?_⟩
  · intro R hR
    exact inf_eq_left.mp ((hS.ne_bot_iff_eq inf_le_left).mp (hSI S R hS.ne_bot hR))
  let jS : S.toRepresentation.IntertwiningMap (functionRepresentation U θ) :=
    { toLinearMap := j.toLinearMap ∘ₗ S.toSubmodule.subtype
      isIntertwining' := fun g => LinearMap.ext fun x =>
        LinearMap.congr_fun (j.isIntertwining' g) x.val }
  obtain ⟨x, hx⟩ := exists_ne_zero_of_subrepresentation_ne_bot S hS.ne_bot
  have hevS := evaluationFunctional_ne_zero S.toRepresentation jS
    (fun a b h => Subtype.ext (hj h)) hx
  let ev := evaluationFunctional ρ j
  have hev : ev ≠ 0 := fun h =>
    evaluationFunctional_ne_zero ρ j hj (x := (x : X))
      (fun h0 => hx (Subtype.ext h0)) (congrArg Subtype.val h)
  have hsurj := functionalsComap_surjective_of_smooth U hU θ hθ ι hι hρ.1
  refine nonempty_linearEquiv_of_forall_eq_smul
    (evaluationFunctional S.toRepresentation jS) (fun h => hevS (congrArg Subtype.val h)) ?_
  intro φ
  obtain ⟨Φ, rfl⟩ := hsurj φ
  obtain ⟨c, rfl⟩ := hone Φ ev hev
  refine ⟨c, ?_⟩
  rw [map_smul]
  rfl

end Smooth

/-- The coefficient model of a representation of Whittaker type has a least
nonzero subrepresentation; it is irreducible and of full Whittaker type. -/
theorem modelGenericSocle : ModelGenericSocleStatement.{uF,uV} := by
  intro p hp F
  let T := F.canonicalTopologicalData
  let := T.topology
  intro ψ n V _ _ σ hσ ℓ hℓ
  let := T.generalLinearTopologicalGroup (n + 1)
  intro M
  let U := GeneralLinear.upperUnipotent (n + 1) F.Carrier
  let θ := standardCharacter ψ n
  let W := (glCoefficientModel ψ n σ ℓ).toSubmodule
  let j : M.IntertwiningMap (functionRepresentation U θ) :=
    { toLinearMap := W.subtype
      isIntertwining' := fun _ => rfl }
  obtain ⟨v, hv⟩ : ∃ v : V, ℓ.val v ≠ 0 := by
    by_contra! h
    exact hℓ (LinearMap.ext h)
  have hmv : modelMap σ ℓ v ≠ 0 := by
    intro h
    apply hv
    have h1 : ((modelMap σ ℓ v).val).val 1 = 0 := by
      rw [h]
      rfl
    change ℓ.val (σ 1 v) = 0 at h1
    rwa [map_one, Module.End.one_apply] at h1
  have : Nontrivial W := ⟨⟨modelMap σ ℓ v, 0, hmv⟩⟩
  exact exists_least_subrepresentation_of_functionModel (X := W)
    (RankinSelberg.UnequalRankAssembly.generalLinear_compactOpen_cofinal F T n) U
    (GeneralLinear.upperUnipotent_isLimitOfCompactSubgroups F T (n + 1)) θ
    (RankinSelberg.UnequalRankAssembly.character_locallyConstant_of_whittakerType F T n θ σ hσ)
    hσ.1 (RankinSelberg.UnequalRankAssembly.finiteLength_of_whittakerType F T n θ σ hσ) hσ.2.2
    M (modelMap σ ℓ) (modelMap_surjective σ ℓ) j Subtype.val_injective

end Langlands.Whittaker
