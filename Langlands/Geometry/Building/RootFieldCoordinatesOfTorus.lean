import Langlands.GroupScheme.Lie.RootOrbitCharacterDescent
import Langlands.GroupScheme.Rational.RootFiberTransitivity
import Langlands.GroupScheme.Rational.RootPointLieAutomorphisms
import Langlands.Geometry.Building.QuasiSplitR1RootFieldCoordinatesStatement

/-! # Actual root field coordinates when a maximal torus is the centralizer -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

open Langlands.GroupScheme

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (f : S ⟶ T) (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j

omit [IsAffineHom G.X.hom] in
/-- Conjugation by points of a representative of the torus centralizer fixes the torus. -/
theorem conjugation_act_of_torusCentralizer
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (X : Over (Spec (CommRingCat.of k))) (h : X ⟶ T.toGrp.X) (s : X ⟶ S.X) :
    (AutomorphicAction.conjugation j).act h (s ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom) =
      s ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom := by
  have hmem : h ≫ j.hom.hom ∈
      (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).carrier X := by
    rw [← hcent.2]
    exact ⟨h, rfl⟩
  have hc := (mem_torusCentralizer _).1 hmem X (𝟙 X) s
  rw [Category.id_comp] at hc
  rw [AutomorphicAction.conjugation_act, hc.eq, mul_inv_cancel_right]

attribute [local instance] rootsGaloisAction

variable [FiniteDimensional k L] [IsGalois k L] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]

/-- Conjugation by a rational torus point acts on the root points with field
coordinate `x` by multiplying the coordinate with the root value. -/
theorem conjugation_rootPointLieEquiv_symm
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hT : IsSplitTorus (T_L).toGrp)
    {a : characterLattice S} (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) a)
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (z : rationalPoints T.toGrp) (x : rootOrbitField k L j β) :
    rationalPoints.map j z *
        ((RelativeRoot.rootPointLieEquiv hS (CommGroupScheme.groupHom f ≫ j) ha.1 hhigh).symm
          (rootOrbitFieldWeightSpaceLinearEquiv k L j f a hG hj hS hT ha.1 β horbit x)).toMul.val *
      (rationalPoints.map j z)⁻¹ =
    ((RelativeRoot.rootPointLieEquiv hS (CommGroupScheme.groupHom f ≫ j) ha.1 hhigh).symm
      (rootOrbitFieldWeightSpaceLinearEquiv k L j f a hG hj hS hT ha.1 β horbit
        (rootOrbitCharacterValue k L j β
          (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z) * x))).toMul.val := by
  set R := RelativeRoot.rootPointLieEquiv hS (CommGroupScheme.groupHom f ≫ j) ha.1 hhigh
  set W := rootOrbitFieldWeightSpaceLinearEquiv k L j f a hG hj hS hT ha.1 β horbit
  have hfix := conjugation_act_of_torusCentralizer k f j hcent
  have key := RelativeRoot.rootPointLieEquiv_act hS (CommGroupScheme.groupHom f ≫ j) ha.1 hhigh
    (AutomorphicAction.conjugation j) hfix z (R.symm (W x))
  rw [AddEquiv.apply_symm_apply] at key
  have hW := conjugation_differential_rootOrbitFieldWeightSpaceEquiv k L j f a hG hj hS hT
    ha.1 β horbit z x
  have key2 : R (Additive.ofMul (RelativeRoot.rootPointsActionOfFixesTorus _ a
      (AutomorphicAction.conjugation j) hfix _ z (R.symm (W x)).toMul)) =
      W (rootOrbitCharacterValue k L j β
        (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z) * x) :=
    Subtype.ext (key.trans hW)
  have key3 := congrArg (fun v => (R.symm v).toMul.val) key2
  simp only [AddEquiv.symm_apply_apply, toMul_ofMul] at key3
  rw [← key3]
  change _ = (AutomorphicAction.conjugation j).act z (R.symm (W x)).toMul.val
  rw [AutomorphicAction.conjugation_act]
  rfl

/-- Root field coordinates for a type R1 root, when a maximal torus represents the
centralizer and the restriction fiber is one Galois orbit. -/
def rootFieldCoordinatesOfOrbit [IsAffine T.toGrp.X.left] [IsAffine S.toGrp.X.left]
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hT : IsSplitTorus (T_L).toGrp)
    {a : characterLattice S} (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) a)
    (β : roots (T := T_L) (G := G_L) j_L) (hβ : β ∈ rootRestrictionFiber k L j f a)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a) :
    RootFieldCoordinates (CommGroupScheme.groupHom f ≫ j) j (CommGroupScheme.groupHom f) a where
  extension := rootOrbitField k L j β
  separable := Algebra.isSeparable_tower_bot_of_isSeparable k (rootOrbitField k L j β) L
  equiv := AddEquiv.toMultiplicativeLeft
    ((rootOrbitFieldWeightSpaceLinearEquiv k L j f a hG hj hS hT ha.1 β horbit).toAddEquiv.trans
      (RelativeRoot.rootPointLieEquiv hS (CommGroupScheme.groupHom f ≫ j) ha.1 hhigh).symm)
  character := rootOrbitCharacter k L j β
  restriction := characterRestrict_rootOrbitCharacter k L j f a hβ
  conjugation z x := by
    rw [rationalCharacterEval_rootOrbitCharacter]
    exact conjugation_rootPointLieEquiv_symm k L f j hG hj hS hcent hT ha hhigh β horbit z x

/-- Root field coordinates for a type R1 root when a maximal torus split by a finite
Galois extension represents the centralizer of the maximal split torus, given an
absolute root datum of the split torus. -/
def rootFieldCoordinatesOfTorus [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hjc : IsClosedSubgroup j)
    (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j))
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hT : IsSplitTorus (T_L).toGrp)
    {J : Type*} [Finite J] {P : RootDatum J (characterLattice T_L) (cocharacterLattice T_L)}
    (hP : IsRootDatumOf (T := T_L) j_L P)
    {a : characterLattice S} (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) a) :
    RootFieldCoordinates (CommGroupScheme.groupHom f ≫ j) j (CommGroupScheme.groupHom f) a :=
  let : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  let : IsAffineHom S.toGrp.X.hom := hf.1.1.isAffineHom
  let : IsAffine S.toGrp.X.left := isAffine_of_isAffineHom S.toGrp.X.hom
  let hne : (rootRestrictionFiber k L j f a).Nonempty :=
    rootRestrictionFiber_nonempty k L j f hf.1.1 hT ⟨a, ha⟩
  rootFieldCoordinatesOfOrbit k L f j hG hj hf.1.1 hcent hT ha hhigh hne.some hne.some_mem
    (rootOrbit_eq_restrictionFiber_of_torusCentralizer k L f j hf hjc hcent hT hP a
      hne.some_mem)

end Langlands.Geometry.Building
