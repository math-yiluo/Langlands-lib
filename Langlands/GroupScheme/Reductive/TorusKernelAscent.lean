import Langlands.GroupScheme.Reductive.TorusKernelAscentStatement
import Langlands.GroupScheme.Torus.UnipotentHomNonsplit
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.SubgroupFunctor.QuotientNormality
import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.KernelRepresentativeTransport
import Langlands.GroupScheme.ConnectedKernelGeometry

/-! # Reductivity ascent along an affine quotient with torus kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {E G T : GroupScheme (Spec (CommRingCat.of k))}

set_option backward.isDefEq.respectTransparency false

/-- An affine fppf extension by a torus inherits triviality of the
ground-field unipotent radical from its quotient. -/
theorem HasTrivialUnipotentRadical.of_torusKernel
    [IsAffineHom E.X.hom] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : T ⟶ E) (hi : IsClosedSubgroup i) (hT : IsTorus T)
    {p : E ⟶ G} (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p)
    (hG : HasTrivialUnipotentRadical G) :
    HasTrivialUnipotentRadical E := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Flat p.hom.hom.left := hp.1
  have : Surjective p.hom.hom.left := hp.2.1
  intro U j hj hs hc hu hn
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom U.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : Smooth U.X.hom := hs
  have : ConnectedSpace U.X.left := hc
  obtain ⟨I, inc, fac, hinc, hfac, hflat, hsurj, hqc, _, hIs, hIc, _⟩ :=
    HomImage.exists_image (j ≫ p)
  have : IsClosedImmersion inc.hom.hom.left := hinc
  have : Mono inc.hom.hom := Over.mono_of_mono_left _
  have : Flat fac.hom.hom.left := hflat
  have : Surjective fac.hom.hom.left := hsurj
  have : QuasiCompact fac.hom.hom.left := hqc
  have hIn : (SubgroupFunctor.range inc).IsNormal :=
    SubgroupFunctor.isNormal_range_of_fpqc_square j p fac inc hfac.symm hn
  have hbot := hG I inc hinc hIs hIc (hu.of_flat_surjective fac) hIn
  apply hu.range_eq_bot_of_range_le_isTorus hT j i
  intro S x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [← hp.2.2.2, mem_range_kernelι_iff]
  have hmem : (y ≫ j.hom.hom) ≫ p.hom.hom ∈
      (SubgroupFunctor.range inc).carrier S := by
    refine SubgroupFunctor.mem_range.mpr ⟨y ≫ fac.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hfac, Grp.comp_hom_hom,
      ← Category.assoc]
  simpa only [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] using hmem

/-- An affine source of an actual fppf quotient with full torus kernel is
connected reductive whenever the target is connected reductive. -/
theorem IsConnectedReductive.of_torusKernel
    [IsAffineHom E.X.hom]
    (i : T ⟶ E) (hi : IsClosedSubgroup i) (hT : IsTorus T)
    {p : E ⟶ G} (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p)
    (hG : IsConnectedReductive G) :
    IsConnectedReductive E := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom T.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : Smooth T.X.hom := hT.smooth
  have : ConnectedSpace T.X.left := hT.connectedSpace
  have : Smooth p.hom.hom.left :=
    hp.smooth_of_smooth_kernel ⟨inferInstance, rfl⟩ inferInstance
  have : Smooth E.X.hom := by
    rw [← Over.w p.hom.hom]
    infer_instance
  have : Surjective p.hom.hom.left := hp.2.1
  have : GeometricallyConnected T.X.hom := T.geometricallyConnected_of_connected
  have : GeometricallyConnected (kernel p).X.hom :=
    KernelRepresentative.geometricallyConnected p i hp.2.2.2
  have : GeometricallyConnected p.hom.hom.left :=
    geometricallyConnected_of_geometricallyConnected_kernel p
  refine ⟨inferInstance, inferInstance,
    GeometricallyConnected.connectedSpace (f := p.hom.hom.left)
      p.hom.hom.left.isOpenMap, ?_⟩
  let b := toAlgebraicClosure k
  let B := GroupScheme.baseChange b
  have : IsAffineHom (B.obj E).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd E.X.hom b)
    infer_instance
  have : IsAffineHom (B.obj G).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have : Smooth (B.obj G).X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have hbi : IsClosedSubgroup (B.map i) :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) b i.hom.hom hi
  have hbp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (B.map i))
      (B.map p) := by
    change RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((GroupScheme.baseChange b).map i))
      ((GroupScheme.baseChange b).map p)
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hp.baseChange b
  exact HasTrivialUnipotentRadical.of_torusKernel (B.map i) hbi
    (hT.baseChange (K := AlgebraicClosure k)) hbp hG.hasTrivialGeometricUnipotentRadical

/-- The exact affine-source torus-kernel ascent proposition. -/
theorem torusKernelReductiveAscent : TorusKernelReductiveAscentStatement.{u} := by
  intro k _ E G T _ i hi hT p hp hG
  exact hG.of_torusKernel i hi hT hp

end Langlands.GroupScheme
