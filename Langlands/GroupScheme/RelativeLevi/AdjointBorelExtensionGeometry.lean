import Langlands.GroupScheme.RelativeLevi.AdjointBorelExtension
import Langlands.GroupScheme.Torus.RelativeQuotient
import Langlands.GroupScheme.Rational.FppfQuotientSmooth

/-! # Geometry of the actual adjoint Borel extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeLevi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {S : Scheme.{u}} {G B A : GroupScheme S}
    {i : B ⟶ G} {q : G ⟶ A} {a : AutomorphicAction A G}
    {T : CommGroupScheme S} {t : T.toGrp ⟶ B}

namespace AdjointBorelExtensionData

variable (d : AdjointBorelExtensionData i q a T t)

/-- The actual torus quotient with its descended commutative group law. -/
def torusCommGroup : CommGroupScheme S := by
  let : Flat d.torus.projection.hom.hom.left := d.torus.flat
  let : Surjective d.torus.projection.hom.hom.left := d.torus.surjective
  let : LocallyOfFinitePresentation d.torus.projection.hom.hom.left :=
    d.torus.locallyOfFinitePresentation
  exact commGroupSchemeTargetOfFppfHom d.torus.projection

@[simp]
theorem torusCommGroup_toGrp : d.torusCommGroup.toGrp = d.torus.group := rfl

/-- The actual Borel quotient is affine when the ambient quotient is affine. -/
theorem borel_isAffineHom [IsAffineHom A.X.hom] :
    IsAffineHom d.borel.group.X.hom := by
  let : IsClosedImmersion d.borel.inclusion.hom.hom.left := d.borel.closed
  rw [← Over.w d.borel.inclusion.hom.hom]
  infer_instance

/-- The actual torus quotient is affine when the ambient quotient is affine. -/
theorem torus_isAffineHom [IsAffineHom A.X.hom] :
    IsAffineHom d.torus.group.X.hom := by
  let : IsAffineHom d.borel.group.X.hom := d.borel_isAffineHom
  let : IsClosedImmersion d.torus.inclusion.hom.hom.left := d.torus.closed
  rw [← Over.w d.torus.inclusion.hom.hom]
  infer_instance

/-- The actual adjoint torus quotient is a relative torus. -/
theorem torus_isTorus [IsAffineHom A.X.hom]
    (hT : RelativeTorus.IsTorus T.toGrp) :
    RelativeTorus.IsTorus d.torus.group := by
  let : IsAffineHom d.torus.group.X.hom := d.torus_isAffineHom
  let : Flat d.torus.projection.hom.hom.left := d.torus.flat
  let : Surjective d.torus.projection.hom.hom.left := d.torus.surjective
  let : LocallyOfFinitePresentation d.torus.projection.hom.hom.left :=
    d.torus.locallyOfFinitePresentation
  exact hT.of_fppfHom d.torus.projection

/-- Affineness of the ambient quotient supplies the separatedness needed for
the original radical to be a closed subgroup of the actual Borel quotient. -/
theorem radical_isClosedSubgroup_of_affine [IsAffineHom A.X.hom] :
    IsClosedSubgroup (d.retraction.radicalInclusion ≫ d.borel.projection) := by
  let : IsAffineHom d.torus.group.X.hom := d.torus_isAffineHom
  exact d.radical_isClosedSubgroup

/-- The sectioned quotient projection is smooth, with the original smooth
relative unipotent radical as its represented full kernel. -/
theorem projection_smooth [IsAffineHom A.X.hom] :
    Smooth d.projection.hom.hom.left := by
  let : IsAffineHom d.borel.group.X.hom := d.borel_isAffineHom
  let : IsAffineHom d.torus.group.X.hom := d.torus_isAffineHom
  have hcomp : QuasiCompact (d.projection.hom.hom.left ≫ d.torus.group.X.hom) := by
    rw [Over.w d.projection.hom.hom]
    infer_instance
  let : QuasiCompact (d.projection.hom.hom.left ≫ d.torus.group.X.hom) := hcomp
  let : QuasiCompact d.projection.hom.hom.left :=
    QuasiCompact.of_comp d.projection.hom.hom.left d.torus.group.X.hom
  exact d.isFppfQuotient.smooth_of_smooth_kernel
    ⟨d.radical_mono, rfl⟩ d.retraction.isRelativeUnipotentRadical.smooth

/-- Smoothness of the actual Borel quotient follows from its smooth projection
onto the actual relative torus. -/
theorem borel_smooth [IsAffineHom A.X.hom]
    (hT : RelativeTorus.IsTorus T.toGrp) :
    Smooth d.borel.group.X.hom := by
  let : Smooth d.projection.hom.hom.left := d.projection_smooth
  let : Smooth d.torus.group.X.hom := (d.torus_isTorus hT).smooth
  rw [← Over.w d.projection.hom.hom]
  infer_instance

end AdjointBorelExtensionData
end Langlands.GroupScheme.RelativeLevi
