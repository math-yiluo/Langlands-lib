import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityStatement
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.Global.LocalModularCharacter.AdjointBound
import Langlands.GroupScheme.Lie.AdjointDeterminantReductiveStatement
import Langlands.GroupScheme.Reductive.CentralDerivedProductProof
import Langlands.GroupScheme.Rational.ScalarExtensionTopology
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof
import Langlands.GroupScheme.Reductive.CentralDerivedProductReduction
import Langlands.GroupScheme.Reductive.CentralTorusSurjectivityProof
import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.Representation.Aubert.General.RationalPointSecondCountable

/-!
# Unimodularity of the rational points of connected reductive groups

For a connected reductive group `G` over a nonarchimedean local field `k`, Mathlib's modular
character of `G(k)`, with the published point topology, is identically `1`. The proof bounds the
modular character by the Haar scaling of `det Ad(g)` (the published ultrametric adjoint bound),
and `det Ad(g) = 1` because the rational adjoint determinant character of a connected reductive
group vanishes. No Bruhat–Tits or Cartan decomposition input is used.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal
open ValuativeRel

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

section NormedField

variable (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

/-- The nontrivially normed field structure of a nonarchimedean local field defined by a
rank-one representative of its valuation; its underlying field is the given one. -/
@[instance_reducible]
def localFieldNormedField : NontriviallyNormedField k :=
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k) (Γ₀ := ValueGroupWithZero k)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := k).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  Valued.toNontriviallyNormedField (L := k) (Γ₀ := ValueGroupWithZero k)

/-- The underlying field of `localFieldNormedField k` is the given field structure. -/
theorem localFieldNormedField_toField : (localFieldNormedField k).toField = ‹Field k› := rfl

/-- The metric topology of `localFieldNormedField k` is the given topology of `k`, already at
reducible-and-instances transparency. -/
theorem localFieldNormedField_topology : @UniformSpace.toTopologicalSpace k
    (@PseudoMetricSpace.toUniformSpace k (localFieldNormedField k).toPseudoMetricSpace) =
      ‹TopologicalSpace k› := by
  with_reducible_and_instances rfl

/-- A nonarchimedean local field is complete for `localFieldNormedField k`. -/
theorem localFieldNormedField_completeSpace :
    @CompleteSpace k (@PseudoMetricSpace.toUniformSpace k
      (localFieldNormedField k).toPseudoMetricSpace) := by
  let := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  exact (inferInstance : CompleteSpace k)

/-- A nonarchimedean local field is proper for `localFieldNormedField k`. -/
theorem localFieldNormedField_properSpace :
    @ProperSpace k (localFieldNormedField k).toPseudoMetricSpace := by
  let := localFieldNormedField k
  exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k

/-- The distance of `localFieldNormedField k` is ultrametric. -/
theorem localFieldNormedField_isUltrametricDist :
    @IsUltrametricDist k (localFieldNormedField k).toPseudoMetricSpace.toDist := by
  let := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let : (Valued.v (R := k) (Γ₀ := ValueGroupWithZero k)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := k).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in exact (inferInstance : IsUltrametricDist k)

end NormedField

section AffinePoints

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- If the rational adjoint determinant character vanishes, then the adjoint action of every
point has determinant one. -/
theorem det_adjoint_eq_one_of_adjointDeterminantCharacter_eq_zero
    (hdet : Lie.adjointDeterminantCharacter G = 0)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (g : G.affinePoints A) :
    LinearMap.det (adjoint G A g) = 1 := by
  rw [← Lie.adjointDeterminantCharacter_val G A g]
  have h := congrArg Additive.toMul
    (GroupScheme.evalHom G (GroupScheme.Gm (Spec (CommRingCat.of k))).toGrp
      ((algSpec (CommRingCat.of k)).obj (Opposite.op A)) g).map_zero
  change g ≫ (0 : GroupScheme.rationalCharacters G).toMul.hom.hom = 1 at h
  rw [hdet]
  erw [h, map_one, Units.val_one]
  rfl

variable (k) [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- The evaluation topology on the `k`-points of `G`. -/
local instance unimodularityPointsTopology :
    TopologicalSpace (G.affinePoints (CommAlgCat.of k k)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of k k)

/-- The `k`-points of `G` form a topological group. -/
local instance unimodularityPointsTopologicalGroup :
    IsTopologicalGroup (G.affinePoints (CommAlgCat.of k k)) :=
  G.affinePointsIsTopologicalGroup (CommAlgCat.of k k)

/-- Over a nonarchimedean local field, the modular character of the `k`-points of a smooth
affine group whose adjoint determinant character vanishes is at most one. -/
theorem affinePoints_modularCharacter_le_one [IsAffineHom G.X.hom] (hG : Smooth G.X.hom)
    (hdet : Lie.adjointDeterminantCharacter G = 0)
    [LocallyCompactSpace (G.affinePoints (CommAlgCat.of k k))]
    [T2Space (G.affinePoints (CommAlgCat.of k k))]
    (g : G.affinePoints (CommAlgCat.of k k)) :
    Measure.modularCharacter g ≤ 1 := by
  let N : NontriviallyNormedField k := localFieldNormedField k
  have := localFieldNormedField_completeSpace k
  have := localFieldNormedField_properSpace k
  have := localFieldNormedField_isUltrametricDist k
  have : SecondCountableTopology (CommAlgCat.of k k) :=
    HarmonicAnalysis.GeneralLocalField.secondCountableTopology k
  have : SecondCountableTopology (G.affinePoints (CommAlgCat.of k k)) :=
    G.affinePointsSecondCountableTopology (CommAlgCat.of k k)
  borelize (G.affinePoints (CommAlgCat.of k k))
  refine Langlands.Global.LocalModularCharacter.modularCharacter_le_of_adjoint_ultrametric
    G hG g 1 ?_
  intro d _ _ A hA
  have hA' : LinearMap.det (A : (Fin d → k) →ₗ[k] (Fin d → k)) = 1 :=
    hA.trans (det_adjoint_eq_one_of_adjointDeterminantCharacter_eq_zero G hdet
      (CommAlgCat.of k k) g)
  borelize k
  have hχ : ∀ a : kˣ, (Measure.addHaar : Measure k).map (fun x => (a : k) * x) =
      (distribHaarChar k a)⁻¹ • (Measure.addHaar : Measure k) := by
    intro a
    have :=
      HarmonicAnalysis.GeneralLocalField.haarMeasure_regular k (Measure.addHaar : Measure k)
    ext s hs
    change ((Measure.addHaar : Measure k).map (fun x => a • x)) s = _
    rw [Measure.map_apply (measurable_const_smul a) hs, Set.preimage_smul,
      ← distribHaarChar_mul (Measure.addHaar : Measure k), map_inv, Measure.smul_apply]
    rfl
  rw [Global.addEquivAddHaarChar_linearPi_eq (Field.toIsField k) Measure.addHaar
    (distribHaarChar k) hχ A]
  have hA1 : LinearEquiv.det A = 1 := Units.ext (by rw [LinearEquiv.coe_det, hA']; rfl)
  rw [hA1, map_one]

/-- Over a nonarchimedean local field, the `k`-points of a smooth affine group whose adjoint
determinant character vanishes form a unimodular group. -/
theorem affinePoints_modularCharacter_eq_one [IsAffineHom G.X.hom] (hG : Smooth G.X.hom)
    (hdet : Lie.adjointDeterminantCharacter G = 0)
    [LocallyCompactSpace (G.affinePoints (CommAlgCat.of k k))]
    [T2Space (G.affinePoints (CommAlgCat.of k k))]
    (g : G.affinePoints (CommAlgCat.of k k)) :
    Measure.modularCharacter g = 1 := by
  have h1 := affinePoints_modularCharacter_le_one k G hG hdet g
  have h2 := affinePoints_modularCharacter_le_one k G hG hdet g⁻¹
  rw [map_inv] at h2
  by_contra hne
  have hlt : Measure.modularCharacter g < 1 := lt_of_le_of_ne h1 hne
  have hpos : 0 < Measure.modularCharacter g := pos_of_ne_zero
    ((Group.isUnit g).map
      (Measure.modularCharacter (G := G.affinePoints (CommAlgCat.of k k)))).ne_zero
  exact absurd hlt (not_lt.mpr ((inv_le_one₀ hpos).mp h2))

/-- The identity-test rational points of `G`, with the published point topology, are
the `k`-points of `G` with their evaluation topology, as topological groups. -/
def rationalPointContinuousMulEquiv :
    letI : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
    RationalPoint k G.X ≃ₜ* G.affinePoints (CommAlgCat.of k k) := by
  letI : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
  have he : (GaloisPointComparison.rationalCoeffEquiv k G :
      RationalPoint k G.X → G.affinePoints (CommAlgCat.of k k)) =
      rationalPointsAffineHomeomorph G := by
    funext p
    exact GaloisPointComparison.rationalCoeffEquiv_eq k G p
  have hh : IsHomeomorph (GaloisPointComparison.rationalCoeffEquiv k G) := by
    rw [he]
    exact (rationalPointsAffineHomeomorph G).isHomeomorph
  exact
    { toMulEquiv := GaloisPointComparison.rationalCoeffEquiv k G
      continuous_toFun := hh.continuous
      continuous_invFun :=
        ((GaloisPointComparison.rationalCoeffEquiv k G).toEquiv.isHomeomorph_iff.mp hh).2 }

end AffinePoints

/-- **Unimodularity of `G(k)`.** For every connected reductive group `G` over a
nonarchimedean local field `k`, Mathlib's modular character of `G(k)`, with the published
point topology, is identically `1`. -/
theorem rationalReductiveUnimodularity : RationalReductiveUnimodularityStatement.{u} := by
  intro k _ _ _ _ G hG _ _ _ _ g
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let _ : TopologicalSpace (G.affinePoints (CommAlgCat.of k k)) :=
    G.affinePointsTopologicalSpace (CommAlgCat.of k k)
  let e : RationalPoint k G.X ≃ₜ* G.affinePoints (CommAlgCat.of k k) :=
    rationalPointContinuousMulEquiv k G
  have : IsTopologicalGroup (G.affinePoints (CommAlgCat.of k k)) :=
    G.affinePointsIsTopologicalGroup (CommAlgCat.of k k)
  have : LocallyCompactSpace (G.affinePoints (CommAlgCat.of k k)) :=
    e.symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have : T2Space (G.affinePoints (CommAlgCat.of k k)) := e.symm.toHomeomorph.isEmbedding.t2Space
  have hdet : Lie.adjointDeterminantCharacter G = 0 :=
    Lie.connectedReductiveAdjointDeterminant_of_centralDerivedProduct
      reductiveCentralDerivedProduct k G hG
  rw [← modularCharacter_continuousMulEquiv e g]
  exact affinePoints_modularCharacter_eq_one k G hG.smooth hdet (e g)

/-! ## Additional normed-field interfaces -/

set_option backward.isDefEq.respectTransparency false

open Langlands.Global Langlands.Global.LocalModularCharacter
open scoped Pointwise

section Normed

variable {K : Type u} [NontriviallyNormedField K] [ProperSpace K]

/-- A linear automorphism of `K^d` of determinant one preserves additive Haar measure. -/
theorem addEquivAddHaarChar_linearPi_eq_one_of_det {d : ℕ}
    [MeasurableSpace (Fin d → K)] [BorelSpace (Fin d → K)]
    (A : (Fin d → K) ≃ₗ[K] (Fin d → K))
    (hA : LinearMap.det (A : (Fin d → K) →ₗ[K] (Fin d → K)) = 1) :
    addEquivAddHaarChar (linearPiContinuousAddEquiv A) = 1 := by
  borelize K
  have hχ : ∀ a : Kˣ, (Measure.addHaar : Measure K).map (fun x => (a : K) * x) =
      (distribHaarChar K a)⁻¹ • (Measure.addHaar : Measure K) := by
    intro a
    ext s hs
    rw [Measure.map_apply (measurable_const_mul (a : K)) hs]
    have hpre : (fun x => (a : K) * x) ⁻¹' s = a⁻¹ • s := Set.preimage_smul a s
    rw [hpre, ← distribHaarChar_mul (Measure.addHaar : Measure K) a⁻¹ s, map_inv]
    rfl
  rw [addEquivAddHaarChar_linearPi_eq (Field.toIsField K) Measure.addHaar (distribHaarChar K) hχ A]
  have hdet : LinearEquiv.det A = 1 := by
    apply Units.ext
    rw [LinearEquiv.coe_det, hA, Units.val_one]
  rw [hdet, map_one]

end Normed

section Chart

attribute [local instance] identityChartTopology identityChartTopologicalRing
  identityChartPointsTopology identityChartPointsTopologicalGroup

variable {K : Type u} [NontriviallyNormedField K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]

variable [CompleteSpace K] [ProperSpace K] [IsUltrametricDist K]
  [LocallyCompactSpace (G.affinePoints (CommAlgCat.of K K))]
  [T2Space (G.affinePoints (CommAlgCat.of K K))]
  [SecondCountableTopology (G.affinePoints (CommAlgCat.of K K))]
  [MeasurableSpace (G.affinePoints (CommAlgCat.of K K))]
  [BorelSpace (G.affinePoints (CommAlgCat.of K K))]

/-- Over a complete ultrametric field, a trivial adjoint determinant character bounds the
modular character of `G(K)` by one. -/
theorem modularCharacter_affinePoints_le_one (hG : Smooth G.X.hom)
    (hdet : Lie.adjointDeterminantCharacter G = 0) (g : G.affinePoints (CommAlgCat.of K K)) :
    Measure.modularCharacter g ≤ 1 := by
  apply modularCharacter_le_of_adjoint_ultrametric G hG g 1
  intro d _ _ A hA
  apply addEquivAddHaarChar_linearPi_eq_one_of_det A
  rw [hA]
  exact det_adjoint_eq_one_of_adjointDeterminantCharacter_eq_zero G hdet (CommAlgCat.of K K) g

/-- Over a complete ultrametric field, a trivial adjoint determinant character makes `G(K)`
unimodular. -/
theorem modularCharacter_affinePoints_eq_one (hG : Smooth G.X.hom)
    (hdet : Lie.adjointDeterminantCharacter G = 0) (g : G.affinePoints (CommAlgCat.of K K)) :
    Measure.modularCharacter g = 1 := by
  apply le_antisymm (modularCharacter_affinePoints_le_one G hG hdet g)
  have h := modularCharacter_affinePoints_le_one G hG hdet g⁻¹
  calc (1 : ℝ≥0) = Measure.modularCharacter (g * g⁻¹) := by rw [mul_inv_cancel, map_one]
    _ = Measure.modularCharacter g * Measure.modularCharacter g⁻¹ := map_mul _ _ _
    _ ≤ Measure.modularCharacter g * 1 := mul_le_mul_right h _
    _ = Measure.modularCharacter g := mul_one _

end Chart

section Comparison

variable (k : Type u) [Field k] [TopologicalSpace k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- The rational points of `G`, with the published rational-point topology, and the points
of `G` with values in `k`, with the evaluation topology, are isomorphic topological groups. -/
def rationalPointsAffineContinuousMulEquiv :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X
    letI : TopologicalSpace (G.affinePoints (CommAlgCat.of k k)) :=
      G.affinePointsTopologicalSpace (CommAlgCat.of k k)
    rationalPoints G ≃ₜ* G.affinePoints (CommAlgCat.of k k) := by
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X
  letI : TopologicalSpace (G.affinePoints (CommAlgCat.of k k)) :=
    G.affinePointsTopologicalSpace (CommAlgCat.of k k)
  let h := rationalPointsAffineHomeomorph G
  have he : (GaloisPointComparison.rationalCoeffEquiv k G :
      rationalPoints G → G.affinePoints (CommAlgCat.of k k)) = h := by
    funext p
    exact GaloisPointComparison.rationalCoeffEquiv_eq k G p
  exact
    { toMulEquiv := GaloisPointComparison.rationalCoeffEquiv k G
      continuous_toFun := by
        change Continuous (GaloisPointComparison.rationalCoeffEquiv k G :
          rationalPoints G → G.affinePoints (CommAlgCat.of k k))
        rw [he]
        exact h.continuous
      continuous_invFun := by
        change Continuous (GaloisPointComparison.rationalCoeffEquiv k G).symm
        have hinv : ((GaloisPointComparison.rationalCoeffEquiv k G).symm :
            G.affinePoints (CommAlgCat.of k k) → rationalPoints G) = h.symm := by
          funext q
          apply (GaloisPointComparison.rationalCoeffEquiv k G).injective
          rw [MulEquiv.apply_symm_apply]
          exact (congrFun he (h.symm q)).trans (h.apply_symm_apply q) |>.symm
        rw [hinv]
        exact h.symm.continuous }

end Comparison

end Langlands.Aubert.General.RationalPointFamily
