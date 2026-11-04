import Langlands.AlgebraicGeometry.SchemePureDimensionAffine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Actual affine scheme scalar extension in global sections -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The actual structure map on global sections, with the canonical
identification of the global sections of `Spec R` with `R`. -/
noncomputable def affineStructureMap (f : X ⟶ Spec (CommRingCat.of R)) :
    CommRingCat.of R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop

/-- Local finite type of an affine scheme over `Spec R` gives finite type
for the actual global-section algebra structure. -/
theorem affineStructureMap_finiteType [IsAffine X]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    (affineStructureMap f).hom.FiniteType := by
  exact (HasRingHomProperty.appTop (P := @LocallyOfFiniteType)
    f inferInstance).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2)

/-- The canonical affine isomorphism is compatible with the original structure map. -/
@[reassoc (attr := simp)]
theorem isoSpec_hom_affineStructureMap [IsAffine X]
    (f : X ⟶ Spec (CommRingCat.of R)) :
    X.isoSpec.hom ≫ Spec.map (affineStructureMap f) = f := by
  rw [affineStructureMap, Spec.map_comp, Scheme.isoSpec_hom_naturality_assoc,
    ← Scheme.isoSpec_Spec_inv]
  simp

/-- An affine scheme's scalar extension is the spectrum of the tensor product
of its actual global sections, with the algebra structure induced by its map. -/
noncomputable def affinePullbackTensorIso (B : Type u) [CommRing B] [Algebra R B]
    [IsAffine X] (f : X ⟶ Spec (CommRingCat.of R)) :
    letI : Algebra R Γ(X, ⊤) := (affineStructureMap f).hom.toAlgebra
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap R B))) ≅
      Spec (CommRingCat.of (Γ(X, ⊤) ⊗[R] B)) := by
  letI : Algebra R Γ(X, ⊤) := (affineStructureMap f).hom.toAlgebra
  let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
  exact (asIso (pullback.map f g (Spec.map (affineStructureMap f)) g
    X.isoSpec.hom (𝟙 _) (𝟙 _)
    (by simp) (by simp))) ≪≫
      pullbackSpecIso R Γ(X, ⊤) B

/-- The spectrum comparison retains the original projection to the affine scheme. -/
@[reassoc (attr := simp)]
theorem affinePullbackTensorIso_hom_fst (B : Type u) [CommRing B] [Algebra R B]
    [IsAffine X] (f : X ⟶ Spec (CommRingCat.of R)) :
    letI : Algebra R Γ(X, ⊤) := (affineStructureMap f).hom.toAlgebra
    (affinePullbackTensorIso B f).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Γ(X, ⊤) ⊗[R] B))) =
      pullback.fst _ _ ≫ X.isoSpec.hom := by
  let : Algebra R Γ(X, ⊤) := (affineStructureMap f).hom.toAlgebra
  dsimp only [affinePullbackTensorIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, pullbackSpecIso_hom_fst']
  change pullback.map _ _ _ _ _ _ _ _ _ ≫
    pullback.fst (Spec.map (affineStructureMap f)) _ = _
  exact pullback.lift_fst _ _ _

/-- The spectrum comparison also retains the original projection to `Spec B`. -/
@[reassoc (attr := simp)]
theorem affinePullbackTensorIso_hom_snd (B : Type u) [CommRing B] [Algebra R B]
    [IsAffine X] (f : X ⟶ Spec (CommRingCat.of R)) :
    letI : Algebra R Γ(X, ⊤) := (affineStructureMap f).hom.toAlgebra
    (affinePullbackTensorIso B f).hom ≫
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) =
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  let : Algebra R Γ(X, ⊤) := (affineStructureMap f).hom.toAlgebra
  dsimp only [affinePullbackTensorIso, Iso.trans_hom, asIso_hom]
  rw [AlgHom.toRingHom_eq_coe, Category.assoc, pullbackSpecIso_hom_snd]
  change pullback.map _ _ _ _ _ _ _ _ _ ≫
    pullback.snd (Spec.map (affineStructureMap f)) _ = _
  simp only [pullback.map, pullback.lift_snd, Category.comp_id]

/-- The componentwise dimension condition on the actual scalar extension is
computed on the actual global-section tensor algebra. -/
theorem hasPureDimension_affinePullback_iff (B : Type u) [CommRing B] [Algebra R B]
    [IsAffine X] (f : X ⟶ Spec (CommRingCat.of R)) (d : ℕ) :
    letI : Algebra R Γ(X, ⊤) := (affineStructureMap f).hom.toAlgebra
    HasPureDimension (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R B)))) d ↔
      HasPureRingDimension (Γ(X, ⊤) ⊗[R] B) d := by
  let : Algebra R Γ(X, ⊤) := (affineStructureMap f).hom.toAlgebra
  exact (hasPureDimension_iff_of_iso (affinePullbackTensorIso B f)).trans
    hasPureDimension_spec_iff

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
