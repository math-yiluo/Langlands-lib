import Langlands.AlgebraicGeometry.SchemePureDimensionAffine
import Langlands.AlgebraicGeometry.SchemePureDimensionFibers

/-! # Actual scheme fibre base change and affine tensor comparisons -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

variable {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
  {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The actual map from a base-changed fibre to the original residue-field fibre. -/
noncomputable def fiberBaseChangeMap (h : IsPullback a b f g) (y : Y) :
    b.fiber y ⟶ f.fiber (g y) :=
  pullback.map _ _ _ _ a (Spec.map (g.residueFieldMap y)) g h.w.symm (by simp)

/-- The fibre square is cartesian over the actual residue-field extension. -/
theorem fiberBaseChangeSquare (h : IsPullback a b f g) (y : Y) :
    IsPullback (fiberBaseChangeMap h y) (b.fiberToSpecResidueField y)
      (f.fiberToSpecResidueField (g y)) (Spec.map (g.residueFieldMap y)) :=
  isPullback_fiberToSpecResidueField_of_isPullback h y

/-- A fibre of an arbitrary cartesian square is scalar extension of the original fibre. -/
noncomputable def fiberBaseChangeIso (h : IsPullback a b f g) (y : Y) :
    b.fiber y ≅ pullback (f.fiberToSpecResidueField (g y))
      (Spec.map (g.residueFieldMap y)) :=
  (fiberBaseChangeSquare h y).isoPullback

@[reassoc (attr := simp)]
theorem fiberBaseChangeIso_hom_fst (h : IsPullback a b f g) (y : Y) :
    (fiberBaseChangeIso h y).hom ≫ pullback.fst _ _ = fiberBaseChangeMap h y :=
  (fiberBaseChangeSquare h y).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem fiberBaseChangeIso_hom_snd (h : IsPullback a b f g) (y : Y) :
    (fiberBaseChangeIso h y).hom ≫ pullback.snd _ _ = b.fiberToSpecResidueField y :=
  (fiberBaseChangeSquare h y).isoPullback_hom_snd

/-- The componentwise condition is computed on this actual field-extension pullback. -/
theorem hasPureDimension_fiberBaseChange_iff (h : IsPullback a b f g) (y : Y) (d : ℕ) :
    HasPureDimension (b.fiber y) d ↔
      HasPureDimension (pullback (f.fiberToSpecResidueField (g y))
        (Spec.map (g.residueFieldMap y))) d :=
  hasPureDimension_iff_of_iso (fiberBaseChangeIso h y)

/-- Pure-dimensional fibres can be tested after the explicit cartesian fibre comparison. -/
theorem hasPureDimensionFibers_baseChange_iff (h : IsPullback a b f g) (d : ℕ) :
    HasPureDimensionFibers d b ↔
      ∀ y : Y, HasPureDimension (pullback (f.fiberToSpecResidueField (g y))
        (Spec.map (g.residueFieldMap y))) d :=
  forall_congr' fun y => hasPureDimension_fiberBaseChange_iff h y d

/-- The actual affine residue-field fibre is the spectrum of its tensor algebra. -/
noncomputable def specFiberTensorIso (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (p : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber p ≅
      Spec (CommRingCat.of (p.asIdeal.Fiber A)) :=
  Arrow.leftFunc.mapIso (Spec.fiberToSpecResidueFieldIso R A p)

/-- For every commutative algebra, the actual affine fibre condition is componentwise
Krull dimension of its residue-field tensor algebra. -/
theorem hasPureDimension_specFiber_iff (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (p : PrimeSpectrum R) (d : ℕ) :
    HasPureDimension ((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber p) d ↔
      HasPureRingDimension (p.asIdeal.Fiber A) d :=
  (hasPureDimension_iff_of_iso (specFiberTensorIso R A p)).trans hasPureDimension_spec_iff

/-- The pure-dimension comparison for an actual affine base change is exactly
that for the corresponding tensor algebra, without finiteness hypotheses. -/
theorem hasPureDimension_pullback_spec_iff (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (d : ℕ) :
    HasPureDimension (pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))) d ↔
      HasPureRingDimension (A ⊗[R] B) d :=
  (hasPureDimension_iff_of_iso (pullbackSpecIso R A B)).trans hasPureDimension_spec_iff

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
