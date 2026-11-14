import Langlands.Geometry.Building.RootFieldCoordinatesOfTorus
import Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinates

/-! # Opposite R1 coordinates on the same root stabilizer field -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G

/-- Opposite absolute roots have the same stabilizer field, as actual
intermediate fields of the supplied extension. -/
theorem rootOrbitField_eq_of_neg
    {beta gamma : roots (T := T_L) (G := G_L) j_L}
    (hgamma : gamma.val = -beta.val) :
    rootOrbitField k L j gamma = rootOrbitField k L j beta := by
  ext x
  simp only [mem_rootOrbitField_iff, hgamma, map_neg, neg_inj]

end Langlands.GroupScheme

namespace Langlands.Geometry.Building

open Langlands.GroupScheme

section Packaging

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : Z ⟶ G} {s : S.toGrp ⟶ Z}
  {a : characterLattice S}

/-- View existing field coordinates on their own extension, retaining the
character and full-centralizer action. -/
def RootFieldCoordinates.toOn (R : RootFieldCoordinates i j s a) :
    RootFieldCoordinatesOn i j s a R.extension where
  equiv := R.equiv
  character := R.character
  restriction := R.restriction
  conjugation := R.conjugation

end Packaging

section Opposite

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
  [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
  (f : S ⟶ T) (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G

attribute [local instance] rootsGaloisAction

/-- A root and its negative have full-centralizer field coordinates on the
same finite separable stabilizer field. This asserts no rank-one homomorphism
or coroot morphism. -/
def oppositeRootFieldCoordinatesOfTorus
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hjc : IsClosedSubgroup j)
    (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j))
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hT : IsSplitTorus (T_L).toGrp)
    {J : Type u} [Finite J]
    {P : RootDatum J (characterLattice T_L) (cocharacterLattice T_L)}
    (hP : IsRootDatumOf j_L P)
    {a : characterLattice S}
    (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hna : -a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) a)
    (hnhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) (-a))
    (beta : roots (T := T_L) (G := G_L) j_L)
    (hbeta : beta ∈ rootRestrictionFiber k L j f a) :
    RootFieldCoordinatesOn (CommGroupScheme.groupHom f ≫ j) j
        (CommGroupScheme.groupHom f) a (rootOrbitField k L j beta) ×
      RootFieldCoordinatesOn (CommGroupScheme.groupHom f ≫ j) j
        (CommGroupScheme.groupHom f) (-a) (rootOrbitField k L j beta) := by
  letI : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  letI : IsAffineHom S.toGrp.X.hom := hf.1.1.isAffineHom
  letI : IsAffine S.toGrp.X.left := isAffine_of_isAffineHom S.toGrp.X.hom
  let gamma : roots (T := T_L) (G := G_L) j_L :=
    ⟨-beta.val, hP.neg_mem_roots beta.property⟩
  have hgamma : gamma ∈ rootRestrictionFiber k L j f (-a) := by
    change (CommGroupScheme.baseChange b).map f ≫ (-beta.val) =
      characterLattice.baseChange b S (-a)
    change (CommGroupScheme.baseChange b).map f ≫ beta.val =
      characterLattice.baseChange b S a at hbeta
    rw [Preadditive.comp_neg, hbeta, map_neg]
  let R := rootFieldCoordinatesOfOrbit k L f j hG hj hf.1.1 hcent hT ha hhigh beta hbeta
    (rootOrbit_eq_restrictionFiber_of_torusCentralizer k L f j hf hjc hcent hT hP a hbeta)
  let N := rootFieldCoordinatesOfOrbit k L f j hG hj hf.1.1 hcent hT hna hnhigh gamma hgamma
    (rootOrbit_eq_restrictionFiber_of_torusCentralizer k L f j hf hjc hcent hT hP (-a) hgamma)
  have hfield : rootOrbitField k L j gamma = rootOrbitField k L j beta :=
    rootOrbitField_eq_of_neg k L j rfl
  refine ⟨R.toOn, ?_⟩
  rw [← hfield]
  exact N.toOn

end Opposite

end Langlands.Geometry.Building
