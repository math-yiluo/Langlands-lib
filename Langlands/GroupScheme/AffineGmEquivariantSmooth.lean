import Langlands.GroupScheme.AffineGmEquivariantMap
import Langlands.CommutativeAlgebra.RelativeGradedFormallySmooth

/-! # Smooth equivariant morphisms on actual fixed and attracting schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace AffineSchemeCoordinates

variable {R : CommRingCat.{u}} {B C : CommAlgCat.{u} R}

/-- A map from a finite-type algebra to a finitely presented algebra is finitely presented. -/
theorem finitePresentation_hom [Algebra.FiniteType R B] [Algebra.FinitePresentation R C]
    (f : B ⟶ C) : f.hom.toRingHom.FinitePresentation := by
  apply RingHom.FinitePresentation.of_comp_finiteType (algebraMap R B)
  · have he : f.hom.toRingHom.comp (algebraMap R B) = algebraMap R C :=
      RingHom.ext f.hom.commutes
    rw [he]
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  · exact RingHom.finiteType_algebraMap.mpr inferInstance

end AffineSchemeCoordinates

namespace GmCoordinateAction

open Langlands.CommutativeAlgebra.GradedFormallySmooth
open Langlands.CommutativeAlgebra.RelativeGradedFormallySmooth

variable {R : CommRingCat.{u}} {B C : CommAlgCat.{u} R}
  (a : Action B) (b : Action C) (f : B ⟶ C)
  (heq : f ≫ coaction b = coaction a ≫ coefficientMap f)

include heq

/-- Equivariance at each algebra element, in the ring-homomorphism notation. -/
theorem coaction_map_apply (d : B) :
    (coaction b).hom (f.hom d) =
      AddMonoidAlgebra.mapRingHom ℤ f.hom.toRingHom ((coaction a).hom d) := by
  have h := congrArg (fun g : B ⟶ laurentAlgebra C => g.hom d) heq
  change (coaction b).hom (f.hom d) = (coefficientMap f).hom ((coaction a).hom d) at h
  rw [← coefficientMap_eq]
  exact h

/-- The algebra map induced on actual attracting coordinate quotients. -/
def attractingAlgebraMap : attractingAlgebra a ⟶ attractingAlgebra b := by
  let : Algebra B C := f.hom.toRingHom.toAlgebra
  let q := negQuotientMap (coaction a).hom.toRingHom (coaction b).hom.toRingHom
    (coaction_map_apply a b f heq)
  exact CommAlgCat.ofHom
    { q with
      commutes' := fun r => by
        change q (Ideal.Quotient.mk (attractingIdeal a) (algebraMap R B r)) =
          Ideal.Quotient.mk (attractingIdeal b) (algebraMap R C r)
        exact congrArg (Ideal.Quotient.mk (attractingIdeal b)) (f.hom.commutes r) }

/-- The induced attracting coordinate map sends a class to the class of its image. -/
theorem attractingAlgebraMap_mk (d : B) :
    (attractingAlgebraMap a b f heq).hom (Ideal.Quotient.mk (attractingIdeal a) d) =
      Ideal.Quotient.mk (attractingIdeal b) (f.hom d) := rfl

omit heq in
/-- The coefficient sum is the identity for an actual unit action. -/
theorem coaction_coeff_sum (d : B) :
    (((coaction a).hom d).coeff.sum fun _ e => e) = d := by
  have h := congrArg (fun g : B ⟶ B => g.hom d) (coaction_counit a)
  change LaurentPolynomial.eval₂ (RingHom.id B) 1 ((coaction a).hom d) = d at h
  exact (AffineLine.eval₂_id_one (A := CommRingCat.of B) ((coaction a).hom d)).symm.trans h

/-- Relative formal smoothness passes to the actual attracting algebra map. -/
theorem formallySmooth_attractingAlgebraMap (hf : f.hom.toRingHom.FormallySmooth) :
    (attractingAlgebraMap a b f heq).hom.toRingHom.FormallySmooth := by
  let : Algebra B C := f.hom.toRingHom.toAlgebra
  have : Algebra.FormallySmooth B C := hf
  exact formallySmooth_negQuotientMap (coaction a).hom.toRingHom
    (coaction b).hom.toRingHom (coaction_coeff_sum a)
    (coaction_coefficient_homogeneous a) (coaction_coeff_sum b)
    (coaction_coefficient_homogeneous b) (coaction_map_apply a b f heq)

/-- Smooth base algebras and a smooth equivariant map give a smooth attracting algebra map. -/
theorem smooth_attractingAlgebraMap [Algebra.Smooth R B] [Algebra.Smooth R C]
    (hf : f.hom.toRingHom.Smooth) :
    (attractingAlgebraMap a b f heq).hom.toRingHom.Smooth := by
  have := smooth_attractingAlgebra a
  have := smooth_attractingAlgebra b
  rw [RingHom.smooth_def]
  exact ⟨formallySmooth_attractingAlgebraMap a b f heq hf.formallySmooth,
    AffineSchemeCoordinates.finitePresentation_hom _⟩

/-- The fixed algebra of a natural action. -/
abbrev fixedAlgebra : CommAlgCat.{u} R :=
  CommAlgCat.of R (B ⧸ Langlands.CommutativeAlgebra.GradedFixedQuotient.fixedIdeal
    (coaction a).hom.toRingHom)

/-- The actual map induced on fixed coordinate quotients. -/
def fixedAlgebraMap : fixedAlgebra a ⟶ fixedAlgebra b := by
  let : Algebra B C := f.hom.toRingHom.toAlgebra
  let q := offQuotientMap (coaction a).hom.toRingHom (coaction b).hom.toRingHom
    (coaction_map_apply a b f heq)
  exact CommAlgCat.ofHom
    { q with
      commutes' := fun r => by
        change q (Ideal.Quotient.mk (offIdeal (coaction a).hom.toRingHom)
            (algebraMap R B r)) =
          Ideal.Quotient.mk (offIdeal (coaction b).hom.toRingHom) (algebraMap R C r)
        exact congrArg (Ideal.Quotient.mk (offIdeal (coaction b).hom.toRingHom))
          (f.hom.commutes r) }

/-- The induced fixed coordinate map sends a class to the class of its image. -/
theorem fixedAlgebraMap_mk (d : B) :
    (fixedAlgebraMap a b f heq).hom (Ideal.Quotient.mk
        (Langlands.CommutativeAlgebra.GradedFixedQuotient.fixedIdeal
          (coaction a).hom.toRingHom) d) =
      Ideal.Quotient.mk (Langlands.CommutativeAlgebra.GradedFixedQuotient.fixedIdeal
        (coaction b).hom.toRingHom) (f.hom d) := rfl

/-- Relative formal smoothness passes to the actual fixed algebra map. -/
theorem formallySmooth_fixedAlgebraMap (hf : f.hom.toRingHom.FormallySmooth) :
    (fixedAlgebraMap a b f heq).hom.toRingHom.FormallySmooth := by
  let : Algebra B C := f.hom.toRingHom.toAlgebra
  have : Algebra.FormallySmooth B C := hf
  exact formallySmooth_offQuotientMap (coaction a).hom.toRingHom
    (coaction b).hom.toRingHom (coaction_coefficient_homogeneous b)
    (coaction_map_apply a b f heq)

/-- Smooth base algebras and a smooth equivariant map give a smooth fixed algebra map. -/
theorem smooth_fixedAlgebraMap [Algebra.Smooth R B] [Algebra.Smooth R C]
    (hf : f.hom.toRingHom.Smooth) :
    (fixedAlgebraMap a b f heq).hom.toRingHom.Smooth := by
  have := Langlands.CommutativeAlgebra.GradedFixedQuotient.smooth_fixedQuotient
    (coaction a).hom (coaction_coefficient_homogeneous a)
  have := Langlands.CommutativeAlgebra.GradedFixedQuotient.smooth_fixedQuotient
    (coaction b).hom (coaction_coefficient_homogeneous b)
  rw [RingHom.smooth_def]
  exact ⟨formallySmooth_fixedAlgebraMap a b f heq hf.formallySmooth,
    AffineSchemeCoordinates.finitePresentation_hom _⟩

end GmCoordinateAction

namespace GmCoordinateAction

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}
  [IsAffine X.left] [IsAffine Y.left]
  (s : PointwiseSchemeAction (Gm (Spec R)).toGrp X)
  (t : PointwiseSchemeAction (Gm (Spec R)).toGrp Y)
  {f : X ⟶ Y} (hf : s.IsEquivariant t f)

include hf

/-- The quotient coordinate map gives the actual map of attracting schemes. -/
theorem algSpec_attractingAlgebraMap :
    (algSpec R).map (attractingAlgebraMap
      (ofPointwiseSchemeAction t) (ofPointwiseSchemeAction s)
      (AffineSchemeCoordinates.map f) (coordinateMap_coaction s t hf)).op =
        schemeActionAttractingMap s t hf := by
  apply (cancel_mono (schemeActionAttractingHom t)).mp
  rw [schemeActionAttractingMap_comp]
  change (algSpec R).map _ ≫
      AffineSchemeCoordinates.pointEquiv Y _
        (AffineSchemeCoordinates.quotientMap Y (schemeActionAttractingIdeal t)) =
    AffineSchemeCoordinates.pointEquiv X _
        (AffineSchemeCoordinates.quotientMap X (schemeActionAttractingIdeal s)) ≫ f
  rw [← AffineSchemeCoordinates.pointEquiv_comp,
    ← AffineSchemeCoordinates.pointEquiv_map_comp]
  apply congrArg (AffineSchemeCoordinates.pointEquiv Y _)
  ext d
  rfl

/-- The quotient coordinate map gives the actual map of fixed schemes. -/
theorem algSpec_fixedAlgebraMap :
    (algSpec R).map (fixedAlgebraMap
      (ofPointwiseSchemeAction t) (ofPointwiseSchemeAction s)
      (AffineSchemeCoordinates.map f) (coordinateMap_coaction s t hf)).op =
        schemeActionFixedMap s t hf := by
  apply (cancel_mono (schemeActionFixedHom t)).mp
  rw [schemeActionFixedMap_comp]
  change (algSpec R).map _ ≫
      AffineSchemeCoordinates.pointEquiv Y _
        (AffineSchemeCoordinates.quotientMap Y (schemeActionFixedIdeal t)) =
    AffineSchemeCoordinates.pointEquiv X _
        (AffineSchemeCoordinates.quotientMap X (schemeActionFixedIdeal s)) ≫ f
  rw [← AffineSchemeCoordinates.pointEquiv_comp,
    ← AffineSchemeCoordinates.pointEquiv_map_comp]
  apply congrArg (AffineSchemeCoordinates.pointEquiv Y _)
  ext d
  rfl

/-- Smooth equivariant maps between smooth affine schemes induce smooth attracting maps. -/
theorem smooth_schemeActionAttractingMap
    (hX : Smooth X.hom) (hY : Smooth Y.hom) (hsm : Smooth f.left) :
    Smooth (schemeActionAttractingMap s t hf).left := by
  let := AffineSchemeCoordinates.smooth_algebra X hX
  let := AffineSchemeCoordinates.smooth_algebra Y hY
  have h := smooth_attractingAlgebraMap
    (ofPointwiseSchemeAction t) (ofPointwiseSchemeAction s)
    (AffineSchemeCoordinates.map f) (coordinateMap_coaction s t hf)
    (AffineSchemeCoordinates.smooth_map f hsm)
  rw [← algSpec_attractingAlgebraMap s t hf]
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr h

/-- Smooth equivariant maps between smooth affine schemes induce smooth fixed maps. -/
theorem smooth_schemeActionFixedMap
    (hX : Smooth X.hom) (hY : Smooth Y.hom) (hsm : Smooth f.left) :
    Smooth (schemeActionFixedMap s t hf).left := by
  let := AffineSchemeCoordinates.smooth_algebra X hX
  let := AffineSchemeCoordinates.smooth_algebra Y hY
  have h := smooth_fixedAlgebraMap
    (ofPointwiseSchemeAction t) (ofPointwiseSchemeAction s)
    (AffineSchemeCoordinates.map f) (coordinateMap_coaction s t hf)
    (AffineSchemeCoordinates.smooth_map f hsm)
  rw [← algSpec_fixedAlgebraMap s t hf]
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr h

end GmCoordinateAction

end Langlands.GroupScheme
