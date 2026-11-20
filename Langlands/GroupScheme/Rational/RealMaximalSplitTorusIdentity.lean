import Langlands.GroupScheme.Rational.RealSplitTorusCorootReduction
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.SeparablyClosedSplitting
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.SimplyConnected.SplitNecessity

/-! # Structural specialization of the split-torus identity-component reduction -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.CocharacterUniformizer (cocharacterPoints)

namespace Langlands.GroupScheme.RealPointTopology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

local notation "b" => algebraBaseMap ℝ ℂ
local notation "complexTorus" T =>
  CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "complexHom" i =>
  CategoryTheory.Functor.map (GroupScheme.baseChange b) i

variable (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left]
  [IsAffineHom G.X.hom]

local instance (H : GroupScheme (Spec (CommRingCat.of ℝ))) :
    Group (RingPoint ℝ H.X ℝ) := H.ringPointGroup (CommAlgCat.of ℝ ℝ)

local instance : IsAffineHom (baseChanged ℝ ℂ G).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom b)
  infer_instance

/-- The remaining root condition for the real identity-component argument. -/
def FixedSimpleCorootSignsInIdentity : Prop :=
  ∀ (T : CommGroupScheme (Spec (CommRingCat.of ℝ))) (i : T.toGrp ⟶ G),
    IsMaximalTorus i → IsSplitTorus (complexTorus T).toGrp →
    ∀ (J : Type) [Finite J]
      (P : RootDatum J (characterLattice (complexTorus T)) (cocharacterLattice (complexTorus T)))
      [P.IsReduced] (hP : IsRootDatumOf (T := complexTorus T) (complexHom i) P)
      (B : P.Base) (j : J), j ∈ B.support →
      IsRootDatumOf.galoisRootIndexEquiv ℝ ℂ i hP Complex.conjAe j = j →
      rationalPoints.map (complexHom i)
          (cocharacterPoints ℂ (complexTorus T) (P.coroot j) (-1)) ∈
        (identityComponentPreimage G).map (rationalExtend ℝ ℂ G)

private theorem conj_inv : Complex.conjAe⁻¹ = Complex.conjAe := by
  apply inv_eq_of_mul_eq_one_left
  ext z
  simp

set_option linter.defProp false in
/-- A maximal real split torus maps into the real identity component under
the fixed absolute simple coroot condition. -/
def maximalSplitTorus_mem_connectedComponent_of_fixedSimpleCorootSigns
    (hG : IsSimplyConnected G) (hfix : FixedSimpleCorootSignsInIdentity G)
    {S : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (s : RingPoint ℝ S.X ℝ) :
    s ≫ i.hom.hom ∈ connectedComponent (1 : RingPoint ℝ G.X ℝ) := by
  let hred := hG.isSemisimple.isConnectedReductive
  let : Smooth G.X.hom := hred.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  obtain ⟨T, j, hj, a, ha⟩ := exists_maximalTorus_extension_of_finiteType G i
    hi.isSplitSubtorus.1.isTorus hi.isSplitSubtorus.2
  let : IsClosedImmersion j.hom.hom.left := hj.2.1
  let : IsAffine T.X.left := isAffine_of_isAffineHom j.hom.hom.left
  let : Smooth T.X.hom := hj.1.smooth
  let : LocallyOfFiniteType T.X.hom := inferInstance
  let G_C := baseChanged ℝ ℂ G
  let T_C := complexTorus T
  let j_C := complexHom j
  have hscC : IsSimplyConnected G_C := isSimplyConnectedFieldExtension ℝ ℂ G hG
  have hredC := hscC.isSemisimple.isConnectedReductive
  have hmaxC : IsMaximalTorus (T := T_C) j_C :=
    (maximalTorusBaseChange ℝ ℂ G T j hj.1 hj.2.1).mp hj
  have hsplitC : IsSplitTorus T_C.toGrp :=
    toriAreSplit_of_isSepClosed ℂ T_C.toGrp hmaxC.1
  obtain ⟨J, hJ, P, hP, hPred⟩ := rootDatumExistence ℂ G_C hredC T_C hsplitC j_C hmaxC
  let : Finite J := hJ
  let : Fintype J := Fintype.ofFinite J
  let : P.IsReduced := hPred
  have hspan : P.corootSpan ℤ = ⊤ :=
    splitSimplyConnectedCorootSpan ℂ G_C hscC T_C hsplitC j_C hmaxC J P hP hPred
  let σ := IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus ℝ ℂ j hsplitC hmaxC.2.1 hP
    Complex.conjAe
  have hσ (x : cocharacterLattice T_C) :
      σ.coweightEquiv x = cocharacterLattice.galoisRepresentation ℝ ℂ T Complex.conjAe x := by
    have hmap : σ.coweightMap =
        cocharacterLattice.galoisRepresentation ℝ ℂ T Complex.conjAe⁻¹ :=
      IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus_coweightMap
        ℝ ℂ j hsplitC hmaxC.2.1 hP Complex.conjAe
    rw [conj_inv] at hmap
    exact DFunLike.congr_fun hmap x
  have hindex : σ.indexEquiv = IsRootDatumOf.galoisRootIndexEquiv ℝ ℂ j hP Complex.conjAe :=
    IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus_indexEquiv
      ℝ ℂ j hsplitC hmaxC.2.1 hP Complex.conjAe
  let x := (rationalRingPointMulEquiv S.toGrp).symm s
  have hs := splitSubtorus_maps_identityComponent_of_fixedCoroots j hsplitC P hspan σ hσ
    (fun B k hk hfixk => hfix T j hj hsplitC J P hP B k hk
      ((congrArg (fun e : Equiv.Perm J => e k) hindex).symm.trans hfixk))
    hi.isSplitSubtorus.1 (Additive.ofMul a) x
  change rationalPoints.map (a ≫ j) x ∈ identityComponentPreimage G at hs
  rw [ha] at hs
  change rationalPointEquiv ℝ G.X (x ≫ i.hom.hom) ∈
    connectedComponent (1 : RingPoint ℝ G.X ℝ) at hs
  rw [rationalPointEquiv_natural] at hs
  have hx : rationalPointEquiv ℝ S.X x = s :=
    (rationalRingPointMulEquiv S.toGrp).apply_symm_apply s
  rwa [hx] at hs

end Langlands.GroupScheme.RealPointTopology
