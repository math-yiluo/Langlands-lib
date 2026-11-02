import Langlands.AlgebraicGeometry.Picard.GroupObjectTangentAddition
import Langlands.AlgebraicGeometry.AlgebraicSpace.ExtensionProduct
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorPoints
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Spectra of field extensions over a field

For a field `k` and a `k`-algebra `L`, `specOver k L` is `Spec L` as a scheme over
`Spec k`, and `k`-algebra maps give morphisms over `Spec k`. Two field points of a normal
extension differ by a Galois automorphism; consequently an open subfunctor of `F × Spec L`
that is stable under `Aut(L/k)` is invariant along the projection to `F`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard.DualNumberDouble (specOverMap specOverMap_left)

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable (k : Type u) [Field k]

/-- `Spec L` as a scheme over `Spec k`. -/
abbrev specOver (L : Type u) [CommRing L] [Algebra k L] : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)))

variable {k}

instance (L : Type u) [CommRing L] [Algebra k L] : IsAffine (specOver k L).left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of L)))

instance {L L' : Type u} [CommRing L] [CommRing L'] [Algebra k L] [Algebra k L']
    (σ : L →ₐ[k] L') : IsAffineHom (specOverMap σ).left :=
  isAffineHom_of_isAffine _

instance {L L' : Type u} [Field L] [Field L'] [Algebra k L] [Algebra k L']
    [FiniteDimensional k L'] (σ : L →ₐ[k] L') :
    _root_.AlgebraicGeometry.IsFinite (specOverMap σ).left := by
  rw [specOverMap_left, IsFinite.SpecMap_iff]
  let := σ.toRingHom.toAlgebra
  have : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq fun x ↦ (σ.commutes x).symm
  have : Module.Finite L L' := Module.Finite.of_restrictScalars_finite k L L'
  exact RingHom.finite_algebraMap.mpr this

lemma specMap_comp {L L' L'' : Type u} [CommRing L] [CommRing L'] [CommRing L'']
    [Algebra k L] [Algebra k L'] [Algebra k L''] (τ : L →ₐ[k] L') (σ : L' →ₐ[k] L'') :
    specOverMap (σ.comp τ) = specOverMap σ ≫ specOverMap τ := by
  apply Over.OverMorphism.ext
  simp only [specOverMap_left, Over.comp_left, ← Spec.map_comp]
  rfl

lemma specMap_id {L : Type u} [CommRing L] [Algebra k L] :
    specOverMap (AlgHom.id k L) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp only [specOverMap_left, Over.id_left]
  exact Spec.map_id _

section Instances

variable (L : Type u) [Field L] [Algebra k L]

instance [Module.Finite k L] :
    _root_.AlgebraicGeometry.IsFinite (specOver k L).hom := by
  show _root_.AlgebraicGeometry.IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k L)))
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

instance : Flat (specOver k L).hom := by
  show Flat (Spec.map (CommRingCat.ofHom (algebraMap k L)))
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

instance [Module.Finite k L] : LocallyOfFinitePresentation (specOver k L).hom := by
  show LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap k L)))
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  have : Algebra.FiniteType k L := inferInstance
  have : Algebra.FinitePresentation k L := Algebra.FinitePresentation.of_finiteType.mp this
  exact RingHom.finitePresentation_algebraMap.mpr this

instance : IsSeparated (specOver k L).hom := by
  show IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap k L)))
  infer_instance

instance : Surjective (specOver k L).hom := by
  constructor
  intro x
  obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
  refine ⟨y, Subsingleton.elim _ _⟩

end Instances

/-- Two `k`-embeddings of a normal extension differ by a `k`-automorphism of the source. -/
theorem exists_algEquiv_comp {L K : Type*} [Field L] [Field K] [Algebra k L] [Algebra k K]
    [Normal k L] (ψ₁ ψ₂ : L →ₐ[k] K) : ∃ σ : L ≃ₐ[k] L, ∀ x, ψ₂ x = ψ₁ (σ x) := by
  let : Algebra L K := ψ₁.toRingHom.toAlgebra
  have : IsScalarTower k L K := IsScalarTower.of_algebraMap_eq fun x ↦ (ψ₁.commutes x).symm
  refine ⟨Normal.algHomEquivAut k K L ψ₂, fun x ↦ ?_⟩
  have h := congrArg (fun f : L →ₐ[k] K ↦ f x) ((Normal.algHomEquivAut k K L).left_inv ψ₂)
  exact h.symm

/-- Restriction of an automorphism of `L'` to a normal subextension `L` embedded by `j`. -/
theorem exists_restrict {L L' : Type*} [Field L] [Field L'] [Algebra k L] [Algebra k L']
    [Normal k L] (j : L →ₐ[k] L') (σ : L' ≃ₐ[k] L') : ∃ τ : L ≃ₐ[k] L, ∀ x, σ (j (τ x)) = j x := by
  let : Algebra L L' := j.toRingHom.toAlgebra
  have : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq fun x ↦ (j.commutes x).symm
  refine ⟨σ.symm.restrictNormal L, fun x ↦ ?_⟩
  have h := AlgEquiv.restrictNormal_commutes σ.symm L x
  change j _ = σ.symm (j x) at h
  rw [h, AlgEquiv.apply_symm_apply]

/-- A finite extension embeds into a finite normal extension in the same universe. -/
theorem exists_finite_normal_extension (K : Type u) [Field K] [Algebra k K]
    [FiniteDimensional k K] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L), FiniteDimensional k L ∧ Normal k L ∧
      Nonempty (K →ₐ[k] L) := by
  let Ω := AlgebraicClosure K
  have : Algebra.IsAlgebraic k Ω := Algebra.IsAlgebraic.trans k K Ω
  have : IsAlgClosure k Ω := (isAlgClosure_iff k Ω).mpr ⟨inferInstance, inferInstance⟩
  exact ⟨IntermediateField.normalClosure k K Ω, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨IsScalarTower.toAlgHom k K (IntermediateField.normalClosure k K Ω)⟩⟩

/-- A morphism from a field point to `specOver k L` comes from a `k`-algebra map, for the
`k`-algebra structure on the field given by the point. -/
theorem exists_algHom_of_hom {L K : Type u} [CommRing L] [Algebra k L] [Field K]
    (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) (f : Over.mk s ⟶ specOver k L) :
    letI := (Spec.preimage s).hom.toAlgebra
    ∃ ψ : L →ₐ[k] K, f.left = Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
  let := (Spec.preimage s).hom.toAlgebra
  have hw : CommRingCat.ofHom (algebraMap k L) ≫ Spec.preimage f.left = Spec.preimage s := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    exact Over.w f
  refine ⟨{ toRingHom := (Spec.preimage f.left).hom, commutes' := fun x ↦ ?_ }, ?_⟩
  · exact congrArg (fun g : CommRingCat.of k ⟶ CommRingCat.of K ↦ g.hom x) hw
  · exact (Spec.map_preimage f.left).symm

/-- Two field points of a normal extension over `Spec k` differ by a Galois automorphism. -/
theorem exists_galois_of_hom {L K : Type u} [Field L] [Algebra k L] [Normal k L] [Field K]
    (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) (f₁ f₂ : Over.mk s ⟶ specOver k L) :
    ∃ σ : L ≃ₐ[k] L, f₂ = f₁ ≫ specOverMap σ.toAlgHom := by
  let := (Spec.preimage s).hom.toAlgebra
  obtain ⟨ψ₁, h₁⟩ := exists_algHom_of_hom s f₁
  obtain ⟨ψ₂, h₂⟩ := exists_algHom_of_hom s f₂
  obtain ⟨σ, hσ⟩ := exists_algEquiv_comp ψ₁ ψ₂
  refine ⟨σ, Over.OverMorphism.ext ?_⟩
  rw [Over.comp_left, h₁, h₂, specOverMap_left, ← Spec.map_comp]
  congr 1
  ext x
  exact hσ x

/-- Every morphism between spectra of `k`-algebras over `Spec k` is induced by a
`k`-algebra map. -/
theorem exists_algHom_of_specOver_hom {L L' : Type u} [CommRing L] [CommRing L']
    [Algebra k L] [Algebra k L'] (f : specOver k L' ⟶ specOver k L) :
    ∃ j : L →ₐ[k] L', f = specOverMap j := by
  have hw : CommRingCat.ofHom (algebraMap k L) ≫ Spec.preimage f.left =
      CommRingCat.ofHom (algebraMap k L') := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact Over.w f
  refine ⟨{ toRingHom := (Spec.preimage f.left).hom, commutes' := fun x ↦ ?_ }, ?_⟩
  · exact congrArg (fun g : CommRingCat.of k ⟶ CommRingCat.of L' ↦ g.hom x) hw
  · apply Over.OverMorphism.ext
    exact (Spec.map_preimage f.left).symm

/-- A Galois automorphism as an automorphism of `specOver k L`. -/
def specIso {L : Type u} [CommRing L] [Algebra k L] (σ : L ≃ₐ[k] L) :
    specOver k L ≅ specOver k L where
  hom := specOverMap σ.toAlgHom
  inv := specOverMap σ.symm.toAlgHom
  hom_inv_id := by
    rw [← specMap_comp]
    convert specMap_id (k := k) (L := L)
    ext x
    simp
  inv_hom_id := by
    rw [← specMap_comp]
    convert specMap_id (k := k) (L := L)
    ext x
    simp

/-- Any morphism over `Spec k` from the spectrum of a nonzero ring to the spectrum of a
field is surjective. -/
theorem surjective_specOver_hom {L K : Type u} [CommRing L] [Nontrivial L] [Field K]
    [Algebra k L] [Algebra k K] (f : specOver k L ⟶ specOver k K) : Surjective f.left := by
  constructor
  intro x
  obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstance
  exact ⟨y, Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _⟩

/-- An open subfunctor of `F × Spec L`, for `L` normal over `k`, that is stable under the
Galois action on the second factor is invariant along the projection to `F`. -/
theorem fst_invariant_of_galois_stable {F : Presheaf (Spec (CommRingCat.of k))}
    {L : Type u} [Field L] [Algebra k L] [Normal k L]
    {W : Subfunctor (extProd F (specOver k L))} (hW : IsOpenImmersion W.ι)
    (hstab : ∀ (σ : L ≃ₐ[k] L) (T : (Over (Spec (CommRingCat.of k)))ᵒᵖ)
      (z : (extProd F (specOver k L)).obj T), z ∈ W.obj T →
        (extProd.mapRight (specOverMap σ.toAlgHom)).app T z ∈ W.obj T) :
    ∀ (T : (Over (Spec (CommRingCat.of k)))ᵒᵖ) (x y : (extProd F (specOver k L)).obj T),
      extProd.fst.app T x = extProd.fst.app T y → (x ∈ W.obj T ↔ y ∈ W.obj T) := by
  have key : ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
      (x y : (extProd F (specOver k L)).obj (op (Over.mk s))), x.1 = y.1 →
        x ∈ W.obj (op (Over.mk s)) → y ∈ W.obj (op (Over.mk s)) := by
    intro K _ s x y hxy hx
    obtain ⟨σ, hσ⟩ := exists_galois_of_hom s x.2.down y.2.down
    have hy : y = (extProd.mapRight (specOverMap σ.toAlgHom)).app _ x := by
      refine Prod.ext hxy.symm ?_
      exact ULift.ext _ _ hσ
    rw [hy]
    exact hstab σ _ x hx
  apply OpenSubfunctorPoints.invariant_of_field_tests hW extProd.fst
  intro K _ s x y hxy
  exact ⟨key K s x y hxy, key K s y x hxy.symm⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
