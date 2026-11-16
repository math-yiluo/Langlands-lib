import Langlands.GroupScheme.Dynamic.MonomorphismImmersion
import Langlands.GroupScheme.Dynamic.BaseRepresentabilityProof
import Langlands.GroupScheme.Reductive.RegularCocharacterCentralizer
import Langlands.GroupScheme.RelativeParabolicNormalizerReduction
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Immersions from a closed regular torus image -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace Dynamic

variable {S : Scheme.{u}} {H G K : GroupScheme S}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ : (Gm S).toGrp ⟶ H) (f : H ⟶ G) [Mono f.hom.hom]
    {i : K ⟶ H} (hi : (centralizer χ).IsRepresentedBy i)

include χ hi in
/-- A monomorphism is an immersion when a representative of one dynamic
centralizer has closed composite with it. Dynamic representatives are chosen
from general-base representability. -/
theorem isImmersion_of_isClosedSubgroup_centralizer_comp
    (hc : IsClosedSubgroup (i ≫ f)) : IsImmersion f.hom.hom.left := by
  obtain ⟨MH, iM, _, _, hM⟩ := (dynamicBaseRepresentability S H
    (CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ χ)).2.1
  obtain ⟨UH, iU, _, _, hU⟩ := (dynamicBaseRepresentability S H χ).2.1
  obtain ⟨MG, jM, _, _, hMG⟩ := (dynamicBaseRepresentability S G
    (CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ (χ ≫ f))).2.1
  obtain ⟨ZG, jZ, hjZ, _, hZG⟩ := (dynamicBaseRepresentability S G (χ ≫ f)).2.2
  obtain ⟨UG, jU, _, _, hUG⟩ := (dynamicBaseRepresentability S G (χ ≫ f)).2.1
  have hcomp : IsClosedSubgroup
      (hi.restrictionHom hZG f (centralizer_le_comap χ f) ≫ jZ) := by
    rw [hi.restrictionHom_comp]
    exact hc
  exact isImmersion_of_isClosedSubgroup_centralizer χ f hM hi hU hMG hZG hUG
    (IsClosedSubgroup.of_comp hjZ hcomp)

end Dynamic

namespace AffineRegularBorel

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I]
    {H G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom H.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ H)
    (P : RootDatum J (I → ℤ) (I → ℤ))

/-- The actual cocharacter chosen from a finite common coordinate root datum. -/
def regularCocharacter [Finite J] : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ H :=
  cocharacter i (CoordinateRootDatum.regularExponent P)

variable [Mono i.hom.hom]
    (hP : IsFibrewiseRootDatumOf I H i P) (hH : IsReductive H)
    (hmax : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (f : H ⟶ G) [Mono f.hom.hom]

include hP hH hmax in
/-- For a reductive source with a supplied split maximal torus and common
fibrewise root datum, a monomorphism into a smooth affine group is an immersion
if the composite of that torus inclusion with the monomorphism is closed. -/
theorem isImmersion_of_isClosedSubgroup_torus_comp
    (hc : IsClosedSubgroup (i ≫ f)) : IsImmersion f.hom.hom.left := by
  let : Finite J := hP.finite
  let : Smooth H.X.hom := hH.smooth
  let : GeometricallyConnected H.X.hom := hH.geometricallyConnected
  have hi : (Dynamic.centralizer (regularCocharacter i P)).IsRepresentedBy i :=
    ⟨inferInstance, (centralizer_eq_range_of_mono i (CoordinateRootDatum.regularExponent P) P
      hP (CoordinateRootDatum.regularExponent_spec P) hH hmax).symm⟩
  exact Dynamic.isImmersion_of_isClosedSubgroup_centralizer_comp
    (regularCocharacter i P) f hi hc

end AffineRegularBorel

end Langlands.GroupScheme
