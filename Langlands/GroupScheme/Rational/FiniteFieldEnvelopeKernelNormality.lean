import Langlands.GroupScheme.Rational.EnvelopeRationalProductFactorization
import Langlands.GroupScheme.Rational.EnvelopeProductNormality
import Langlands.GroupScheme.Rational.FiniteFieldSplitUnipotentProductStatement
import Langlands.GroupScheme.Rational.PerfectFieldSectionedSolvableQuotient

/-! # Finite-field normality from actual kernel and centralizer geometry -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Actual envelope-kernel and centralizer presentations with the geometry
needed by the finite-field product criterion. This data includes neither
product surjectivity nor envelope normality. -/
structure EnvelopeKernelCentralizerGeometry
    {k : Type u} [Field k]
    {G N : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (D : TorusGeneratedEnvelope G) (n : N ⟶ G)
    (q : G ⟶ T.toGrp) (s : T.toGrp ⟶ G) where
  kernel : GroupScheme (Spec (CommRingCat.of k))
  inclusion : kernel ⟶ D.group
  closed : IsClosedSubgroup inclusion
  toKernel : kernel ⟶ N
  toKernel_comp : toKernel ≫ n = inclusion ≫ D.inclusion
  smooth : Smooth kernel.X.hom
  connected : ConnectedSpace kernel.X.left
  unipotent : IsUnipotent kernel
  split : RelativeRoot.IsSplitUnipotent kernel
  quotient : RelativeRoot.IsFppfQuotient
    (SubgroupFunctor.range inclusion) (D.inclusion ≫ q)
  centralizer : GroupScheme (Spec (CommRingCat.of k))
  centralizerInclusion : centralizer ⟶ N
  centralizerClosed : IsClosedSubgroup centralizerInclusion
  representsCentralizer :
    ((torusCentralizer s).comap n).IsRepresentedBy centralizerInclusion
  centralizerSmooth : Smooth centralizer.X.hom
  centralizerConnected : ConnectedSpace centralizer.X.left
  centralizerSplit : RelativeRoot.IsSplitUnipotent centralizer
  intersectionSmooth :
    Smooth (subgroupIntersection toKernel centralizerInclusion).X.hom
  intersectionConnected :
    ConnectedSpace (subgroupIntersection toKernel centralizerInclusion).X.left
  intersectionSplit :
    RelativeRoot.IsSplitUnipotent (subgroupIntersection toKernel centralizerInclusion)

namespace TorusGeneratedEnvelope

variable {k : Type u} [Field k] [Finite k]
    {G N : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (D : TorusGeneratedEnvelope G)

/-- Rational torus-map correction, the finite-field product criterion, and
fpqc descent imply full normality from the specified geometric presentations.
Both remaining global proof inputs stay explicit. -/
theorem isNormal_of_finiteField_kernelCentralizer
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (hproduct : RelativeRoot.FiniteFieldSplitUnipotentProductStatement.{u})
    (n : N ⟶ G) (hn : IsClosedSubgroup n)
    [Smooth N.X.hom] [IsAffineHom N.X.hom] [ConnectedSpace N.X.left]
    (hN : IsUnipotent N) (hNsplit : RelativeRoot.IsSplitUnipotent N)
    (q : G ⟶ T.toGrp)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)
    (s : T.toGrp ⟶ G) (hs : s ≫ q = 𝟙 T.toGrp) (hT : IsTorus T.toGrp)
    (d : EnvelopeKernelCentralizerGeometry D n q s) :
    (SubgroupFunctor.range D.inclusion).IsNormal := by
  let : IsClosedImmersion n.hom.hom.left := hn
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom D.group.X.hom := D.isAffineHom
  let : IsClosedImmersion d.inclusion.hom.hom.left := d.closed
  let : Mono d.inclusion.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom d.kernel.X.hom := by
    rw [← Over.w d.inclusion.hom.hom]
    infer_instance
  let : Smooth d.kernel.X.hom := d.smooth
  let : ConnectedSpace d.kernel.X.left := d.connected
  let : IsClosedImmersion d.centralizerInclusion.hom.hom.left := d.centralizerClosed
  let : IsAffineHom d.centralizer.X.hom := by
    rw [← Over.w d.centralizerInclusion.hom.hom]
    infer_instance
  let : Smooth d.centralizer.X.hom := d.centralizerSmooth
  let : ConnectedSpace d.centralizer.X.left := d.centralizerConnected
  have hj : IsClosedSubgroup d.toKernel :=
    IsClosedSubgroup.of_comp hn (by
      rw [d.toKernel_comp]
      exact d.closed.comp D.closed)
  have hsc : IsClosedSubgroup s := IsClosedSubgroup.of_comp_eq_id s q hs
  let sH := D.torusFactor s hT hsc
  have hsH : sH ≫ D.inclusion = s := D.torusFactor_comp s hT hsc
  have hnq : n ≫ q = 0 := by
    apply (Grp.forget _).map_injective
    change n.hom.hom ≫ q.hom.hom = 1
    apply (mem_range_kernelι_iff q n.hom.hom).mp
    rw [hq.2.2.2]
    exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  have hrational :
      ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ N.X,
        ∃ v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ d.kernel.X,
        ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ d.centralizer.X,
          (v ≫ d.toKernel.hom.hom) * (z ≫ d.centralizerInclusion.hom.hom) = x :=
    D.rationalPoints_mul_surjective hstable d.inclusion d.unipotent d.split
      n q hnq d.quotient sH hT d.toKernel d.toKernel_comp
      d.centralizerInclusion (by simpa only [hsH] using d.representsCentralizer)
  obtain ⟨hsm, hsurj⟩ := hproduct k N d.kernel d.centralizer
    d.toKernel d.centralizerInclusion hj d.centralizerClosed
    hNsplit d.split d.centralizerSplit d.intersectionSmooth
    d.intersectionConnected d.intersectionSplit hrational
  let : Smooth (subgroupMultiplication d.toKernel d.centralizerInclusion).left := hsm
  let : Surjective (subgroupMultiplication d.toKernel d.centralizerInclusion).left := hsurj
  let : IsAffineHom (d.kernel.X ⊗ d.centralizer.X).hom := by
    change IsAffineHom (pullback.fst d.kernel.X.hom d.centralizer.X.hom ≫
      d.kernel.X.hom)
    let : IsAffineHom (pullback.fst d.kernel.X.hom d.centralizer.X.hom) :=
      MorphismProperty.pullback_fst _ _ inferInstance
    infer_instance
  let : IsAffine (d.kernel.X ⊗ d.centralizer.X).left :=
    isAffine_of_isAffineHom (d.kernel.X ⊗ d.centralizer.X).hom
  let : IsAffine N.X.left := isAffine_of_isAffineHom N.X.hom
  let : QuasiCompact (subgroupMultiplication d.toKernel d.centralizerInclusion).left :=
    inferInstance
  apply D.isNormal_of_fpqc_envelopeKernelProduct hstable n hn hN hNsplit
    q hq s hs hT d.toKernel d.centralizerInclusion
  · rw [d.toKernel_comp]
    intro R x hx
    obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨v ≫ d.inclusion.hom.hom, by
      rw [Grp.comp_hom_hom, Category.assoc]⟩
  · intro R x hx
    obtain ⟨c, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hc : c ≫ d.centralizerInclusion.hom.hom ∈
        ((torusCentralizer s).comap n).carrier R := by
      rw [← d.representsCentralizer.2]
      exact SubgroupFunctor.mem_range.mpr ⟨c, rfl⟩
    simpa only [SubgroupFunctor.mem_comap, Grp.comp_hom_hom, Category.assoc] using hc

/-- Apply the finite-field criterion to the actual perfect-field radical and
sectioned quotient without imposing any extra radical-existence premise. -/
theorem isNormal_of_finiteField_sectionedQuotient
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (hproduct : RelativeRoot.FiniteFieldSplitUnipotentProductStatement.{u})
    (a : SplitGeometricRadicalSectionedTorusQuotient G)
    (d : EnvelopeKernelCentralizerGeometry (T := a.torus) D a.inclusion
      a.quotientData.projection a.quotientData.sectionHom) :
    (closedTorusEnvelope G).IsNormal := by
  let : Smooth a.source.X.hom := a.isGeometricUnipotentRadical.1.smooth
  let : ConnectedSpace a.source.X.left :=
    a.isGeometricUnipotentRadical.1.connectedSpace
  let : IsClosedImmersion a.inclusion.hom.hom.left :=
    a.isGeometricUnipotentRadical.1.isClosedSubgroup
  let : IsAffineHom a.source.X.hom := by
    rw [← Over.w a.inclusion.hom.hom]
    infer_instance
  rw [← D.represents.2]
  exact D.isNormal_of_finiteField_kernelCentralizer hstable hproduct
    a.inclusion a.isGeometricUnipotentRadical.1.isClosedSubgroup
    a.isGeometricUnipotentRadical.1.isUnipotent a.isSplitUnipotent
    a.quotientData.projection a.quotientData.isFppfQuotient
    a.quotientData.sectionHom a.quotientData.sectionHom_comp a.torus_isTorus d

end TorusGeneratedEnvelope

end Langlands.GroupScheme
