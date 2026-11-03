import Langlands.GroupScheme.Rational.GeometricUnipotentRadicalComparison
import Langlands.GroupScheme.Rational.LeviMultiplication
import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # Geometric unipotent radicals and rational Levis in affine groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {U P L : GroupScheme (Spec (CommRingCat.of k))}
  {r : U ⟶ P} {l : L ⟶ P}

/-- In an affine ambient group, geometric radical greatestness also gives
radical greatestness over the ground field. -/
theorem IsGeometricUnipotentRadical.isUnipotentRadical [IsAffineHom P.X.hom]
    (hr : IsGeometricUnipotentRadical r) : IsUnipotentRadical r := by
  apply hr.isUnipotentRadical_of_unipotentFieldExtension
  intro k K _ _ _ H hAffine _ hUnipotent
  let : IsAffineHom H.X.hom := hAffine
  exact hUnipotent.baseChange

/-- The two geometric unipotent radical predicates agree for affine ambient
groups, using the proved preservation of unipotence under field extension. -/
theorem IsGeometricUnipotentRadical.leviSubgroup [IsAffineHom P.X.hom]
    (hr : IsGeometricUnipotentRadical r) :
    LeviSubgroup.IsGeometricUnipotentRadical r := by
  apply hr.leviSubgroup_of_unipotentFieldExtension
  intro k K _ _ _ H hAffine _ hUnipotent
  let : IsAffineHom H.X.hom := hAffine
  exact hUnipotent.baseChange

/-- The geometric radical interfaces are equivalent in an affine ambient group. -/
theorem leviSubgroup_isGeometricUnipotentRadical_iff_of_affine
    [IsAffineHom P.X.hom] :
    LeviSubgroup.IsGeometricUnipotentRadical r ↔ IsGeometricUnipotentRadical r :=
  ⟨fun hr => hr.isGeometricUnipotentRadical, fun hr => hr.leviSubgroup⟩

/-- Canonical equivalence of the two geometric unipotent radical witness types
in an affine ambient group. -/
def LeviSubgroup.geometricUnipotentRadicalEquivOfAffine [IsAffineHom P.X.hom] :
    LeviSubgroup.IsGeometricUnipotentRadical r ≃
      Langlands.GroupScheme.IsGeometricUnipotentRadical r :=
  Equiv.ofIff leviSubgroup_isGeometricUnipotentRadical_iff_of_affine

/-- The semistandard geometric radical predicate and an actual multiplication
isomorphism suffice for the radical clause of a rational Levi. -/
theorem IsRationalLeviSubgroup.of_geometricUnipotentRadical [IsAffineHom P.X.hom]
    (hl : IsClosedSubgroup l) (hL : IsConnectedReductive L)
    (hr : IsGeometricUnipotentRadical r) (hmul : IsIso (subgroupMultiplication l r)) :
    IsRationalLeviSubgroup l :=
  ⟨inferInstance, hl, hL, U, r, hr.leviSubgroup, hmul⟩

namespace Dynamic

variable {G Z : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsSeparated G.X.hom]
  {χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G}
  {iP : P ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}

/-- Compatible representatives of a dynamic centralizer and geometric unipotent
radical give a rational Levi once the centralizer is connected reductive. -/
theorem isRationalLeviSubgroup_of_geometricUnipotentRadical
    (hP : (parabolic χ).IsRepresentedBy iP)
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy iU)
    (l : Z ⟶ P) (r : U ⟶ P) (hl : l ≫ iP = iZ) (hr : r ≫ iP = iU)
    (hZred : IsConnectedReductive Z) (hrad : IsGeometricUnipotentRadical r) :
    IsRationalLeviSubgroup l := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hPc : IsClosedSubgroup iP := Affine.isClosedSubgroup_of_isRepresentedBy_parabolic χ hP
  have hZc : IsClosedSubgroup iZ := Affine.isClosedSubgroup_of_isRepresentedBy_centralizer χ hZ
  let : IsClosedImmersion iP.hom.hom.left := hPc
  let : IsAffineHom P.X.hom := by
    rw [← Over.w iP.hom.hom]
    infer_instance
  have hlc : IsClosedSubgroup l :=
    IsClosedSubgroup.of_comp hPc (by rw [hl]; exact hZc)
  exact IsRationalLeviSubgroup.of_geometricUnipotentRadical hlc hZred hrad
    (isIso_subgroupMultiplication hP hZ hU l r hl hr)

end Dynamic

end Langlands.GroupScheme
