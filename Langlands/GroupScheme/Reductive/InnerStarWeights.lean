import Langlands.GroupScheme.Reductive.AbsoluteStarAction
import Langlands.GroupScheme.Torus.FundamentalWeightGaloisRootSpan
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof

/-! # Integral weights of inner simply connected groups are star fixed -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme
namespace GaloisPinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : GaloisPinningData k K G)

/-- The vertex formulation of innerness for the supplied Galois pinning. -/
def IsInnerStarAction : Prop :=
  ∀ (σ : K ≃ₐ[k] K) (v : d.toSplitPinning.base.support),
    (d.starAction σ).val.indexEquiv v = v

/-- Fixedness of an actual integral character under the supplied star action. -/
def IsStarFixedWeight (lam : characterLattice d.toSplitPinning.torus) : Prop :=
  ∀ σ : K ≃ₐ[k] K, (d.starAction σ).val.weightEquiv lam = lam

omit [LocallyOfFiniteType G.X.hom] in
/-- Simple connectedness of the actual group gives the integral coroot-span
condition for the actual split pinning after field extension. -/
theorem corootSpan_eq_top_of_simplyConnected (hG : IsSimplyConnected G) :
    d.toSplitPinning.rootDatum.corootSpan ℤ = ⊤ := by
  have hGK := isSimplyConnectedFieldExtension k K G hG
  exact splitSimplyConnectedCorootSpan K _ hGK d.toSplitPinning.torus
    d.toSplitPinning.isSplitTorus d.toSplitPinning.inclusion
    d.toSplitPinning.isMaximalTorus d.toSplitPinning.rootIndex
    d.toSplitPinning.rootDatum d.toSplitPinning.isRootDatum d.toSplitPinning.isReduced

/-- Vertex fixedness implies fixedness of each actual fundamental weight;
the required integral coroot generation is proved from simple connectedness. -/
theorem starAction_fundamentalWeight_of_inner (hG : IsSimplyConnected G)
    (hinner : d.IsInnerStarAction) (σ : K ≃ₐ[k] K)
    (v : d.toSplitPinning.base.support) :
    (d.starAction σ).val.weightEquiv
        (Langlands.RootDatum.fundamentalWeightBasis d.toSplitPinning.rootDatum
          d.toSplitPinning.base (d.corootSpan_eq_top_of_simplyConnected hG) v) =
      Langlands.RootDatum.fundamentalWeightBasis d.toSplitPinning.rootDatum
        d.toSplitPinning.base (d.corootSpan_eq_top_of_simplyConnected hG) v :=
  Langlands.RootDatum.fundamentalWeightBasis_fixed_of_based
    d.toSplitPinning.rootDatum d.toSplitPinning.base
    (d.corootSpan_eq_top_of_simplyConnected hG)
    (d.starAction σ).val (d.starAction σ).property v (hinner σ v)

/-- For a simply connected group, an inner star action fixes the whole
actual integral weight lattice, not only its simple-root vertices. -/
theorem starAction_weight_of_inner (hG : IsSimplyConnected G)
    (hinner : d.IsInnerStarAction) (σ : K ≃ₐ[k] K)
    (lam : characterLattice d.toSplitPinning.torus) :
    (d.starAction σ).val.weightEquiv lam = lam := by
  have hmap : (d.starAction σ).val.weightEquiv.toLinearMap = LinearMap.id := by
    apply (Langlands.RootDatum.fundamentalWeightBasis d.toSplitPinning.rootDatum
      d.toSplitPinning.base (d.corootSpan_eq_top_of_simplyConnected hG)).ext
    intro v
    exact d.starAction_fundamentalWeight_of_inner hG hinner σ v
  exact DFunLike.congr_fun hmap lam

/-- Every integral weight is star fixed under the vertex innerness hypothesis. -/
theorem isStarFixedWeight_of_inner (hG : IsSimplyConnected G)
    (hinner : d.IsInnerStarAction) (lam : characterLattice d.toSplitPinning.torus) :
    d.IsStarFixedWeight lam :=
  fun σ => d.starAction_weight_of_inner hG hinner σ lam

end GaloisPinningData

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Innerness expressed by the full absolute Galois action on every simple
vertex of the canonical separable-closure pinning. -/
def IsInnerAbsoluteStarAction (hG : IsConnectedReductive G) : Prop :=
  ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (v : (GaloisPinningData.ofSeparableClosure hG).toSplitPinning.base.support),
    (absoluteStarAction hG σ).val.indexEquiv v = v

/-- The canonical full absolute star action fixes every actual integral weight
of an inner simply connected group. -/
theorem absoluteStarAction_weight_of_inner (hG : IsSimplyConnected G)
    (hinner : IsInnerAbsoluteStarAction hG.isSemisimple.isConnectedReductive)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (lam : characterLattice
      (GaloisPinningData.ofSeparableClosure
        hG.isSemisimple.isConnectedReductive).toSplitPinning.torus) :
    (absoluteStarAction hG.isSemisimple.isConnectedReductive σ).val.weightEquiv lam =
      lam :=
  (GaloisPinningData.ofSeparableClosure hG.isSemisimple.isConnectedReductive
    ).starAction_weight_of_inner hG hinner σ lam

/-- Uniform actual integral-weight fixedness, for any supplied pinning over
the separable closure and the full absolute Galois vertex action. -/
def InnerSimplyConnectedStarFixedWeightsStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsSimplyConnected G →
      ∀ d : GaloisPinningData k (SeparableClosure k) G,
        d.IsInnerStarAction →
          ∀ lam : characterLattice d.toSplitPinning.torus, d.IsStarFixedWeight lam

/-- The vertex innerness condition suffices, without a weight-fixedness premise. -/
theorem innerSimplyConnectedStarFixedWeights :
    InnerSimplyConnectedStarFixedWeightsStatement.{u} := by
  intro k _ G _ _ hG d hinner lam
  exact d.isStarFixedWeight_of_inner hG hinner lam

end Langlands.GroupScheme
