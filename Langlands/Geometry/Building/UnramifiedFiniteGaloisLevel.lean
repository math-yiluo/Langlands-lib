import Langlands.Galois.Local.SeparableInertiaDefinitions
import Langlands.GroupScheme.LocalUnramifiedTwistDescent

/-! # A finite Galois level inside the maximal unramified extension

For a finite subextension `E₀` of `K = F^ur` (the fixed field of inertia in
`SeparableClosure F`), some finite Galois subextension `E` of `K / F` contains `E₀`, and the
restriction `Aut(K/F) → Gal(E/F)` is surjective, compatible with the inclusion `E ⊆ K`, has
fixed field exactly `E`, and has kernel inside the fixing subgroup of `E₀`. The structure
`GaloisLevel F E₀` bundles these data; `exists_galoisLevel` and `nonempty_galoisLevel` say
that they exist.
-/

noncomputable section

universe u

open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.MaximalUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- A finite subextension of `F^ur / F` lies in a finite Galois subextension `E`, whose
restriction map from `Aut(F^ur/F)` is surjective, compatible with `E ⊆ F^ur`, has fixed field
`E`, and has kernel fixing the given subextension. -/
theorem exists_galoisLevel (E₀ : IntermediateField F (inertiaFixedField F))
    [FiniteDimensional F E₀] :
    ∃ (E : IntermediateField F (SeparableClosure F)) (_ : FiniteDimensional F E)
      (_ : IsGalois F E) (_ : E ≤ inertiaFixedField F)
      (res : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →* (E ≃ₐ[F] E)),
      Function.Surjective res ∧
      (∀ σ (x : inertiaFixedField F) (hx : (x : SeparableClosure F) ∈ E),
        ((res σ ⟨x, hx⟩ : E) : SeparableClosure F) =
          ((σ x : inertiaFixedField F) : SeparableClosure F)) ∧
      (∀ x : inertiaFixedField F, (∀ σ, res σ = 1 → σ x = x) →
        (x : SeparableClosure F) ∈ E) ∧
      (∀ σ, res σ = 1 → σ ∈ E₀.fixingSubgroup) := by
  classical
  let K := inertiaFixedField F
  let E₁ : IntermediateField F (SeparableClosure F) := E₀.map K.val
  have : FiniteDimensional F E₁ :=
    (IntermediateField.equivMap E₀ K.val).toLinearEquiv.finiteDimensional
  have hE₁ : E₁ ≤ K := by
    rintro _ ⟨y, -, rfl⟩
    exact y.property
  obtain ⟨E, hfin, hgal, hE₁E, hEK⟩ :=
    Langlands.GroupScheme.GaloisCocycle.exists_finiteDimensional_isGalois_between K E₁ hE₁
  let : Algebra E K := (IntermediateField.inclusion hEK).toAlgebra
  have : IsScalarTower F E K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let res : (K ≃ₐ[F] K) →* (E ≃ₐ[F] E) := AlgEquiv.restrictNormalHom E
  have hcomm : ∀ (σ : K ≃ₐ[F] K) (y : E),
      ((res σ y : E) : SeparableClosure F) =
        ((σ (IntermediateField.inclusion hEK y) : K) : SeparableClosure F) := fun σ y =>
    congrArg Subtype.val (AlgEquiv.restrictNormal_commutes σ E y)
  refine ⟨E, hfin, hgal, hEK, res, AlgEquiv.restrictNormalHom_surjective K, ?_, ?_, ?_⟩
  · intro σ x hx
    exact hcomm σ ⟨x, hx⟩
  · intro x hx
    have hker : ∀ σ : K ≃ₐ[F] K,
        σ ∈ (IntermediateField.restrict hEK).fixingSubgroup → res σ = 1 := by
      intro σ hσ
      refine AlgEquiv.ext fun y => Subtype.ext ?_
      rw [hcomm σ y, AlgEquiv.one_apply]
      have hy : IntermediateField.inclusion hEK y ∈ IntermediateField.restrict hEK :=
        (IntermediateField.mem_restrict hEK _).2 y.property
      have h := (IntermediateField.mem_fixingSubgroup_iff _ σ).1 hσ _ hy
      have h' : ((σ (IntermediateField.inclusion hEK y) : K) : SeparableClosure F) =
          ((IntermediateField.inclusion hEK y : K) : SeparableClosure F) :=
        congrArg Subtype.val h
      exact h'
    have hmem : x ∈ IntermediateField.fixedField
        (IntermediateField.restrict hEK).fixingSubgroup := fun σ => hx σ (hker σ σ.property)
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
    exact (IntermediateField.mem_restrict hEK x).1 hmem
  · intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hyE : (y : SeparableClosure F) ∈ E := hE₁E ⟨y, hy, rfl⟩
    have h := hcomm σ ⟨y, hyE⟩
    rw [hσ, AlgEquiv.one_apply] at h
    exact Subtype.ext h.symm

/-- A finite Galois level of `F^ur / F` over a subextension `E₀`: a finite Galois intermediate
field `E ≤ F^ur` of `SeparableClosure F / F` together with a surjective restriction map
`Aut(F^ur/F) →* Gal(E/F)` that agrees with the automorphisms on `E`, whose kernel has fixed
field `E` and fixes `E₀`. -/
structure GaloisLevel (E₀ : IntermediateField F (inertiaFixedField F)) where
  /-- The finite Galois intermediate field. -/
  E : IntermediateField F (SeparableClosure F)
  finiteDimensional : FiniteDimensional F E
  isGalois : IsGalois F E
  le_inertiaFixedField : E ≤ inertiaFixedField F
  /-- Restriction from `Aut(F^ur/F)` to `Gal(E/F)`. -/
  res : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →* (E ≃ₐ[F] E)
  res_surjective : Function.Surjective res
  res_apply : ∀ σ (x : inertiaFixedField F) (hx : (x : SeparableClosure F) ∈ E),
    ((res σ ⟨x, hx⟩ : E) : SeparableClosure F) =
      ((σ x : inertiaFixedField F) : SeparableClosure F)
  mem_of_forall_fixed : ∀ x : inertiaFixedField F, (∀ σ, res σ = 1 → σ x = x) →
    (x : SeparableClosure F) ∈ E
  ker_le_fixingSubgroup : ∀ σ, res σ = 1 → σ ∈ E₀.fixingSubgroup

attribute [instance] GaloisLevel.finiteDimensional GaloisLevel.isGalois

/-- Every finite subextension of `F^ur / F` has a finite Galois level. -/
theorem nonempty_galoisLevel (E₀ : IntermediateField F (inertiaFixedField F))
    [FiniteDimensional F E₀] : Nonempty (GaloisLevel F E₀) := by
  obtain ⟨E, hfin, hgal, hE, res, h₁, h₂, h₃, h₄⟩ := exists_galoisLevel F E₀
  exact ⟨⟨E, hfin, hgal, hE, res, h₁, h₂, h₃, h₄⟩⟩

end Langlands.Geometry.Building.MaximalUnramified
