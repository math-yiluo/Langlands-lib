import Langlands.GroupScheme.FiniteNormalSubgroupQuotient
import Langlands.GroupScheme.FiniteUniformExponent
import Langlands.GroupScheme.Reductive.CentralFiniteQuotientReductive
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.FlatMorphismCharts
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # Reductivity of finite flat normal quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- An isogeny locally of finite presentation from a connected reductive group
over a field to an affine group has connected reductive target. -/
theorem isConnectedReductive_of_isIsogeny {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))} (q : G ⟶ Q)
    (hG : IsConnectedReductive G) [IsAffineHom Q.X.hom]
    [LocallyOfFinitePresentation q.hom.hom.left] (hq : IsIsogeny q) :
    IsConnectedReductive Q := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : Flat q.hom.hom.left := hq.2.1
  have : Surjective q.hom.hom.left := hq.2.2
  let b := toAlgebraicClosure k
  have : IsAffineHom ((baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : Smooth ((baseChange b).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom ((baseChange b).obj Q).X.hom := by
    change IsAffineHom (pullback.snd Q.X.hom b)
    infer_instance
  let qb := (baseChange b).map q
  have hqb : IsIsogeny qb := hq.baseChange b
  have : Flat qb.hom.hom.left := hqb.2.1
  have : LocallyOfFinitePresentation qb.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation)
      b q.hom.hom inferInstance
  have hfin : IsFinite (kernel qb).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme qb) hqb.1
  obtain ⟨n, hn, hker⟩ :=
    finiteGroupSchemeUniformExponent (AlgebraicClosure k) (kernel qb) hfin
  exact
    { smooth := smooth_target_of_surjective_flat_hom q
      isAffineHom := inferInstance
      connectedSpace := hq.2.2.surj.connectedSpace q.hom.hom.left.continuous
      hasTrivialGeometricUnipotentRadical :=
        FiniteCentralQuotient.hasTrivialUnipotentRadical_of_kernel_pow_eq_one
          qb hG.hasTrivialGeometricUnipotentRadical hn hker }

/-- An isogeny locally of finite presentation from a reductive group scheme
to an affine group scheme has reductive target over any base scheme. -/
theorem isReductive_of_isIsogeny {S : Scheme.{u}} {G Q : GroupScheme S}
    (q : G ⟶ Q) (hG : IsReductive G) [IsAffineHom Q.X.hom]
    [LocallyOfFinitePresentation q.hom.hom.left] (hq : IsIsogeny q) :
    IsReductive Q := by
  have : Smooth G.X.hom := hG.smooth
  have : Flat q.hom.hom.left := hq.2.1
  have : Surjective q.hom.hom.left := hq.2.2
  have : Flat (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : Flat Q.X.hom :=
    Langlands.AlgebraicGeometry.AlgebraicSpace.flat_of_surjective_flat_comp
      q.hom.hom.left Q.X.hom
  have : LocallyOfFinitePresentation (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : LocallyOfFinitePresentation Q.X.hom :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_surjective_flat_comp
      q.hom.hom.left Q.X.hom
  have hf : ∀ {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S),
      IsConnectedReductive ((baseChange b).obj Q) := by
    intro k _ b
    have : IsAffineHom ((baseChange b).obj Q).X.hom := by
      change IsAffineHom (pullback.snd Q.X.hom b)
      infer_instance
    have : LocallyOfFinitePresentation ((baseChange b).map q).hom.hom.left :=
      MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation)
        b q.hom.hom inferInstance
    exact isConnectedReductive_of_isIsogeny ((baseChange b).map q)
      (hG.isConnectedReductive_baseChange b) (hq.baseChange b)
  refine ⟨?_, inferInstance, fun s => (hf (geometricPoint S s)).isPseudoReductive⟩
  apply Smooth.of_smooth_fiberToSpecResidueField
  intro s
  exact (hf (S.fromSpecResidueField s)).smooth

/-- A finite fppf normal quotient together with reductivity of its target. -/
structure ReductiveFiniteNormalSubgroupQuotient {S : Scheme.{u}}
    {G N : GroupScheme S} (i : N ⟶ G)
    extends FiniteNormalSubgroupQuotient i where
  reductive : IsReductive quotient

/-- Construct the reductive quotient of a reductive group over an affine base
by a finite flat locally finitely presented normal subgroup. -/
def reductiveFiniteNormalSubgroupQuotient
    {S : Scheme.{u}} [IsAffine S] {G N : GroupScheme S}
    (hG : IsReductive G) (i : N ⟶ G) [Mono i.hom.hom]
    [IsFinite N.X.hom] [Flat N.X.hom] [LocallyOfFinitePresentation N.X.hom]
    (hn : (SubgroupFunctor.range i).IsNormal) :
    ReductiveFiniteNormalSubgroupQuotient i := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  let q := finiteNormalSubgroupQuotient i hn
  have : IsAffineHom q.quotient.X.hom := q.affine
  have : LocallyOfFinitePresentation q.projection.hom.hom.left :=
    q.isFppfQuotient.2.2.1
  exact
    { toFiniteNormalSubgroupQuotient := q
      reductive := isReductive_of_isIsogeny q.projection hG
        ⟨q.finite, q.isFppfQuotient.1, q.isFppfQuotient.2.1⟩ }

end Langlands.GroupScheme
