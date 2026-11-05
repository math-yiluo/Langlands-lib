import Langlands.GroupScheme.Torus.RelativeAdjointWeightBaseChange
import Langlands.GroupScheme.Torus.RelativeAdjointWeightRanks
import Langlands.GroupScheme.Reductive.Basic

/-! # Locally constant adjoint weight dimensions of actual geometric fibres -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.splitTorus

variable {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [IsAffineHom G.X.hom]
  [Smooth G.X.hom] (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)

local instance affine_pullback {S : Scheme.{u}} (b : S ⟶ Spec (CommRingCat.of r)) :
    IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

instance finite_exponentWeightSpaceOf (m : I → ℤ) :
    Module.Finite r (exponentWeightSpace I G i m) :=
  finite_exponentWeightSpace I G i m

instance projective_exponentWeightSpaceOf (m : I → ℤ) :
    Module.Projective r (exponentWeightSpace I G i m) :=
  projective_exponentWeightSpace I G i m

/-- Over every specified field-valued point, the dimension of the actual
weight summand equals the relative weight rank at its image. -/
theorem finrank_exponentWeightSpace_fieldBaseChange {k : Type u} [Field k]
    [Algebra r k] (m : I → ℤ) :
    Module.finrank k
        (exponentWeightSpace I ((baseChange (algebraBaseMap r k)).obj G)
          (baseChangeHom (K := k) G I i) m) =
      exponentWeightRank I G i m
        ((algebraBaseMap r k) (IsLocalRing.closedPoint k)) := by
  have h := Module.rankAtStalk_baseChange
    (R := r) (M := exponentWeightSpace I G i m) (IsLocalRing.closedPoint k)
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  exact (exponentWeightBaseChangeEquiv (K := k) G I i m).finrank_eq.symm.trans h

local instance smooth_geometricFiber (s : Spec (CommRingCat.of r)) :
    Smooth (geometricFiber G s).X.hom :=
  inferInstanceAs (Smooth (pullback.snd G.X.hom (geometricPoint _ s)))

local instance affine_geometricFiber (s : Spec (CommRingCat.of r)) :
    IsAffineHom (geometricFiber G s).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (geometricPoint _ s)))

/-- The actual split-torus homomorphism in the actual chosen geometric fibre. -/
def geometricFiberHom (s : Spec (CommRingCat.of r)) :
    splitTorus
        (Spec (CommRingCat.of
          (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) I ⟶
      geometricFiber G s :=
  (baseChangeIso (geometricPoint _ s) I).inv ≫
    (baseChange (geometricPoint _ s)).map i

/-- The full profile of dimensions of actual character weight spaces on the
actual geometric fibre, indexed by integral exponents. -/
def geometricExponentWeightRankProfile
    (s : Spec (CommRingCat.of r)) (m : I → ℤ) : ℕ :=
  Module.finrank (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))
    (weightSpace (geometricFiberHom I G i s)
      ((characterLatticeEquiv
        (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)) I).symm m))

set_option maxHeartbeats 4000000 in
/-- Actual geometric-fibre character weight dimensions are the ranks of
the actual relative exponent weight summands. -/
theorem geometricExponentWeightRankProfile_apply
    (s : Spec (CommRingCat.of r)) (m : I → ℤ) :
    geometricExponentWeightRankProfile I G i s m = exponentWeightRank I G i m s := by
  let S := Spec (CommRingCat.of r)
  let k := AlgebraicClosure (S.residueField s)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (geometricPoint S s)
  let : Algebra r k := φ.hom.toAlgebra
  have hb : algebraBaseMap r k = geometricPoint S s := hφ
  have himage : (algebraBaseMap r k) (IsLocalRing.closedPoint k) = s := by
    rw [hb]
    change S.fromSpecResidueField s _ = s
    exact Scheme.fromSpecResidueField_apply _ _
  have h := finrank_exponentWeightSpace_fieldBaseChange I G i (k := k) m
  rw [himage] at h
  let F (f : Spec (CommRingCat.of k) ⟶ S) : ℕ :=
    Module.finrank k (exponentWeightSpace I ((baseChange f).obj G)
      ((baseChangeIso f I).inv ≫ (baseChange f).map i) m)
  have he : F (algebraBaseMap r k) = F (geometricPoint S s) := congrArg F hb
  have hgeom : F (geometricPoint S s) = exponentWeightRank I G i m s := he.symm.trans h
  change Module.finrank k
      (weightSpace (geometricFiberHom I G i s)
        ((characterLatticeEquiv k I).symm m)) = _
  rw [← exponentWeightSpace_eq_weightSpace k I (geometricFiber G s)
    (geometricFiberHom I G i s) m]
  dsimp only [F, geometricFiberHom, geometricFiber, S, k] at hgeom ⊢
  exact hgeom

/-- The geometric-fibre character weight profile equals the relative
actual weight-rank profile. -/
theorem geometricExponentWeightRankProfile_eq :
    geometricExponentWeightRankProfile I G i = exponentWeightRankProfile I G i := by
  funext s m
  exact geometricExponentWeightRankProfile_apply I G i s m

/-- All actual geometric-fibre character weight dimensions are locally
constant simultaneously over the arbitrary affine base. -/
theorem isLocallyConstant_geometricExponentWeightRankProfile :
    IsLocallyConstant (geometricExponentWeightRankProfile I G i) := by
  rw [geometricExponentWeightRankProfile_eq]
  exact isLocallyConstant_exponentWeightRankProfile I G i

end Langlands.GroupScheme.splitTorus
