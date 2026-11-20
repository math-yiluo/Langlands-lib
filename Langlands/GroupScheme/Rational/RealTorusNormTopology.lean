import Langlands.GroupScheme.Torus.GaloisNormRational
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.GroupScheme.Torus.SplitPointTopology
import Langlands.GroupScheme.AffinePointTopologicalGroup
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Continuity of torus norms and their real identity-component image -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisNorm

set_option backward.isDefEq.respectTransparency false

open GaloisPointComparison (baseChanged baseMap rationalCoeffEquiv rationalNorm)

local instance coefficientTopology {K : Type u} [Field K] [TopologicalSpace K]
    (G : GroupScheme (Spec (CommRingCat.of K))) :
    TopologicalSpace (G.affinePoints (CommAlgCat.of K K)) :=
  G.affinePointsTopologicalSpace _

section FiniteGalois

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  [TopologicalSpace k] [IsTopologicalRing k] [TopologicalSpace L] [IsTopologicalRing L]
  [IsModuleTopology k L]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]
  [LocallyOfFiniteType T.X.hom]

local notation "T_L" => baseChanged k L T.toGrp

local instance : IsAffine (T_L).X.left := by
  change IsAffine (Limits.pullback T.X.hom (baseMap k L))
  infer_instance

local instance : LocallyOfFiniteType (T_L).X.hom := by
  change LocallyOfFiniteType (Limits.pullback.snd T.X.hom (baseMap k L))
  infer_instance

/-- The existing rational norm is continuous for the evaluation topologies. -/
def rationalNormContinuousHom :
    letI : TopologicalSpace (rationalPoints T_L) := rationalPointTopology L (T_L).X
    letI : TopologicalSpace (rationalPoints T.toGrp) := rationalPointTopology k T.X
    rationalPoints T_L →ₜ* rationalPoints T.toGrp := by
  letI : TopologicalSpace (rationalPoints T_L) := rationalPointTopology L (T_L).X
  letI : TopologicalSpace (rationalPoints T.toGrp) := rationalPointTopology k T.X
  refine { toMonoidHom := rationalNorm k L T, continuous_toFun := ?_ }
  let W := AffineWeil.groupScheme k L T_L
  let eL := rationalPointsAffineHomeomorph (R := L) T_L
  let ek := rationalPointsAffineHomeomorph (R := k) T.toGrp
  let eW := AffineWeil.basePointsContinuousEquiv k L T_L
  have hc := ek.symm.continuous.comp
    ((W.continuous_affinePointsTarget (CommAlgCat.of k k) (norm k L T)).comp
      (eW.symm.continuous.comp eL.continuous))
  have hmap (x : rationalPoints T_L) :
      rationalNorm k L T x =
        ek.symm (W.affinePointsTarget (norm k L T) (CommAlgCat.of k k)
          (eW.symm (eL x))) := by
    apply (rationalCoeffEquiv k T.toGrp).injective
    rw [← norm_rationalPoints k L T x, GaloisPointComparison.rationalCoeffEquiv_map,
      rationalPointsEquiv_coeff]
    have hk (z : rationalPoints T.toGrp) : rationalCoeffEquiv k T.toGrp z = ek z :=
      GaloisPointComparison.rationalCoeffEquiv_eq k T.toGrp z
    have hL : rationalCoeffEquiv L T_L x = eL x :=
      GaloisPointComparison.rationalCoeffEquiv_eq L T_L x
    rw [hk, Homeomorph.apply_symm_apply, hL]
    rfl
  change Continuous (fun x : rationalPoints T_L => rationalNorm k L T x)
  exact hc.congr (fun x => (hmap x).symm)

@[simp] theorem rationalNormContinuousHom_apply (x : rationalPoints T_L) :
    rationalNormContinuousHom k L T x = rationalNorm k L T x := rfl

end FiniteGalois

section Real

variable (T : CommGroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine T.X.left]
  [LocallyOfFiniteType T.X.hom]

local notation "T_C" => baseChanged ℝ ℂ T.toGrp

local instance : IsAffine (T_C).X.left := by
  change IsAffine (Limits.pullback T.X.hom (baseMap ℝ ℂ))
  infer_instance

local instance : IsModuleTopology ℝ ℂ := isModuleTopologyOfFiniteDimensional

local instance : IsAlgClosure ℝ ℂ :=
  ⟨inferInstance, Algebra.IsAlgebraic.of_finite ℝ ℂ⟩

omit [LocallyOfFiniteType T.X.hom] in
/-- Complex points of a split torus are connected in the evaluation topology. -/
theorem connectedSpace_complexPoints (hT : IsSplitTorus T_C) :
    letI : TopologicalSpace (rationalPoints T_C) := rationalPointTopology ℂ (T_C).X
    ConnectedSpace (rationalPoints T_C) := by
  let : TopologicalSpace (rationalPoints T_C) := rationalPointTopology ℂ (T_C).X
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let A := CommAlgCat.of ℂ ℂ
  let h := (rationalPointsAffineHomeomorph (R := ℂ) T_C).trans
    ((affinePointsIsoHomeomorph e A).trans
      (splitTorus.affinePointsHomeomorph I (CommRingCat.of ℂ) A).toHomeomorph)
  exact h.connectedSpace_iff.mpr (inferInstanceAs (ConnectedSpace (I → ℂˣ)))

/-- Every complex norm of the torus lies in the identity component of its real points. -/
theorem rationalNorm_mem_connectedComponent_one (hT : IsSplitTorus T_C)
    (x : rationalPoints T_C) :
    letI : TopologicalSpace (rationalPoints T.toGrp) := rationalPointTopology ℝ T.X
    rationalNorm ℝ ℂ T x ∈ connectedComponent (1 : rationalPoints T.toGrp) := by
  let : TopologicalSpace (rationalPoints T_C) := rationalPointTopology ℂ (T_C).X
  let : TopologicalSpace (rationalPoints T.toGrp) := rationalPointTopology ℝ T.X
  let : ConnectedSpace (rationalPoints T_C) := connectedSpace_complexPoints T hT
  let f := rationalNormContinuousHom ℝ ℂ T
  have h := (isPreconnected_range f.continuous).subset_connectedComponent
    (show 1 ∈ Set.range f from ⟨1, map_one f⟩)
  exact h ⟨x, rfl⟩

end Real

end Langlands.GroupScheme.GaloisNorm
