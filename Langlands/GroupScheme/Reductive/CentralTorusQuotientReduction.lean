import Langlands.GroupScheme.Reductive.CentralTorusQuotientStatement
import Langlands.GroupScheme.Rational.SplitTorusKernelCentralityStatement
import Langlands.GroupScheme.Reductive.CentralQuotientReductiveStatement
import Langlands.GroupScheme.Rational.SplitTorusIsogenyOfLatticeMapsStatement
import Langlands.GroupScheme.CentralIsogeny.MaximalTorusImageStatement
import Langlands.GroupScheme.CentralIsogeny.FiniteKernelQuotient
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.AffineQuotientReduction
import Langlands.GroupScheme.MatrixRepresentation.UnipotentQuotient
import Langlands.GroupScheme.Torus.UnipotentQuotientClosed

/-! # The central torus quotient from its prerequisites -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A subgroup functor contained in the centre is normal. -/
theorem SubgroupFunctor.isNormal_of_le_center {S : Scheme.{u}} {G : GroupScheme S}
    {N : SubgroupFunctor G} (hN : N ≤ center G) : N.IsNormal := by
  intro T g x _ hx
  have he : g * x * g⁻¹ = x := by
    rw [(commute_of_mem_center (hN T hx) g).eq.symm, mul_assoc, mul_inv_cancel, mul_one]
  rw [he]
  exact hx

/-- The split central torus quotient, conditional on four prerequisite statements. -/
theorem splitCentralTorusQuotient_of_prerequisites
    (h1 : SplitTorusKernelCentralityStatement.{u})
    (h2 : CentralQuotientReductiveStatement.{u})
    (h3 : SplitTorusIsogenyOfLatticeMapsStatement.{u})
    (h5 : CentralIsogenyMaximalTorusImageStatement.{u}) :
    SplitCentralTorusQuotientStatement.{u} := by
  intro k _ G hG T T' hT hT' i hi t hX hY hroots
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  have : IsAffineHom T'.toGrp.X.hom := hT'.isAffineHom
  -- `t` is an isogeny of split tori.
  have ht : IsIsogeny (CommGroupScheme.groupHom t) := h3 k T T' t hT hT' hX hY
  have : IsFinite (CommGroupScheme.groupHom t).hom.hom.left := ht.1
  have : Flat (CommGroupScheme.groupHom t).hom.hom.left := ht.2.1
  have : Surjective (CommGroupScheme.groupHom t).hom.hom.left := ht.2.2
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have hmono : Mono i.hom.hom := Over.mono_of_mono_left _
  -- The kernel of `t`, mapped into `G`: a finite central closed subgroup.
  let ιN : (CommGroupScheme.kernel t).toGrp ⟶ G :=
    CommGroupScheme.groupHom (CommGroupScheme.kernelι t) ≫ i
  have hcent : IsCentral ιN := h1 k G T T' hT i t hroots
  have hle : SubgroupFunctor.range ιN ≤ center G :=
    (isCentral_iff_range_le_center ιN).mp hcent
  have hclosed : IsClosedSubgroup ιN := by
    have : IsClosedImmersion (kernelι (CommGroupScheme.groupHom t)).hom.hom.left :=
      inferInstance
    change IsClosedImmersion ((kernelι (CommGroupScheme.groupHom t)).hom.hom.left ≫
      i.hom.hom.left)
    infer_instance
  have hfin : IsFinite (CommGroupScheme.kernel t).toGrp.X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme (CommGroupScheme.groupHom t)) ht.1
  -- The central isogeny `q : G ⟶ Q` with kernel `ιN`.
  obtain ⟨Q, q, hQs, hQa, hcq, hker⟩ := exists_centralIsogeny_of_finite_central_subgroup k G _ ιN
    hclosed hfin hcent (SubgroupFunctor.isNormal_of_le_center hle)
  have := hQs
  have := hQa
  have hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range ιN) q :=
    ⟨hcq.flat, hcq.surjective, hcq.locallyOfFinitePresentation, hker⟩
  have hQ : IsConnectedReductive Q := h2 k G Q q _ hG hQa inferInstance hle hq
  -- Descend `i ≫ q` along `t`.
  have hk1 : SubgroupFunctor.range (kernelι (CommGroupScheme.groupHom t)) ≤
      SubgroupFunctor.range (kernelι (i ≫ q)) := by
    intro U x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply (mem_range_kernelι_iff (i ≫ q) _).mpr
    have hy : (y ≫ ιN.hom.hom) ≫ q.hom.hom = 1 := by
      apply (mem_range_kernelι_iff q _).mp
      rw [hker]
      exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
    simp only [ιN, Grp.comp_hom_hom, Category.assoc] at hy
    exact hy
  have hk2 : SubgroupFunctor.range (kernelι (i ≫ q)) ≤
      SubgroupFunctor.range (kernelι (CommGroupScheme.groupHom t)) := by
    intro U x hx
    have hx' : (x ≫ i.hom.hom) ≫ q.hom.hom = 1 := by
      simpa only [Grp.comp_hom_hom, Category.assoc] using (mem_range_kernelι_iff (i ≫ q) x).mp hx
    have hmem := (mem_range_kernelι_iff q _).mpr hx'
    rw [hker] at hmem
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hmem
    refine SubgroupFunctor.mem_range.mpr ⟨y, ?_⟩
    apply (cancel_mono i.hom.hom).mp
    simp only [ιN, Grp.comp_hom_hom] at hy
    exact hy
  have hk : kernelι (CommGroupScheme.groupHom t) ≫ (i ≫ q) = 0 :=
    AffineQuotient.kernelι_comp_eq_zero hk1
  let i'' : T'.toGrp ⟶ Q := FpqcHomDescent.hom (CommGroupScheme.groupHom t) (i ≫ q) hk
  have hfac : CommGroupScheme.groupHom t ≫ i'' = i ≫ q := FpqcHomDescent.fac _ _ hk
  have : Mono i''.hom.hom :=
    FpqcHomDescent.mono_of_kernel_range_le (CommGroupScheme.groupHom t) (i ≫ q) i'' hfac hk2
  have hclosed'' : IsClosedSubgroup i'' := hT'.isTorus.isClosedSubgroup_of_mono i''
  have hmax : IsMaximalTorus i'' :=
    h5 k G Q hG hQ q hcq T T' i i'' t hi hT'.isTorus hclosed'' ht.2.2 hfac.symm
  exact ⟨Q, hQ, q, i'', hmax, hcq, hfac.symm⟩

end Langlands.GroupScheme
