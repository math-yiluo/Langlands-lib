import Langlands.AlgebraicGeometry.StrictBirationalGroupLawHenselianSolutionStatement
import Langlands.AlgebraicGeometry.HenselianBirationalSolution.Restriction
import Langlands.AlgebraicGeometry.HenselianBirationalSolution.Assembly
import Langlands.AlgebraicGeometry.HenselianBirationalSolution.SectionDensity
import Langlands.AlgebraicGeometry.SmoothNormalDomainStalks

/-! # Existence of a solution over a strictly henselian discrete valuation ring -/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
  AlgebraicGeometry Topology NeronModelInfra GroupLawOverBase
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AlgebraicGeometry

open HenselianBirationalSolution

/-- The strictly henselian discrete valuation ring case of Bosch–Lütkebohmert–Raynaud,
*Néron Models*, §5.2 Theorem 3. The group scheme is obtained by gluing charts along extended
left translations of the restricted law. -/
theorem strictBirationalGroupLawHenselianSolution :
    StrictBirationalGroupLawHenselianSolutionStatement.{u} := by
  intro R _ _ _ _ _ X f hf hsep hft hqc hsurj m V hV hstrict
  let g := V.ι ≫ f
  have : IsNoetherian X := {
    toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
  have : IsNoetherian V.toScheme := {
    toIsLocallyNoetherian := inferInstance
    toCompactSpace := isCompact_iff_compactSpace.mp
      (TopologicalSpace.NoetherianSpace.isCompact (V : Set X)) }
  have : Smooth g := inferInstanceAs (Smooth (V.ι ≫ f))
  have : IsSeparated g := inferInstanceAs (IsSeparated (V.ι ≫ f))
  have : QuasiCompact g := quasiCompact_of_compactSpace g
  have : Surjective g := by
    constructor
    intro s
    obtain ⟨x, hx⟩ := f.surjective s
    obtain ⟨y, hy, hyx, -⟩ := hV x
    exact ⟨⟨y, hy⟩, hyx.trans hx⟩
  have : IsReduced V.toScheme := SmoothReducedBase.isReduced_of_smooth_of_isReduced g
  obtain ⟨n, hn, hfactor⟩ := exists_strictRestriction m V hstrict
  let H : GlueHyp n := ⟨hn, smoothNormalDomainStalks (CommRingCat.of R) g inferInstance⟩
  have hL : HasSectionLifts g := by
    intro P q Z hZo hZ p
    obtain ⟨c, hc, hmem⟩ := exists_section_lift_mem g q Z hZo hZ p
    exact ⟨⟨c, hc⟩, hmem⟩
  obtain ⟨c, hc, -⟩ := exists_section_closedPoint_mem g Set.univ isOpen_univ (by
    obtain ⟨y, hy⟩ := g.surjective (IsLocalRing.closedPoint R)
    exact ⟨y, trivial, hy⟩)
  have hs (s : Spec (CommRingCat.of R)) : s ⤳ IsLocalRing.closedPoint R := by
    rcases eq_genericPt_or_closedPoint s with rfl | rfl
    · exact genericPt_specializes _
    · exact specializes_rfl
  obtain ⟨e, he⟩ := exists_right_identity H hL ⟨c, hc⟩ (IsLocalRing.closedPoint R) hs
  let G := gluedGroup H (relativeGroupLaw H hL e he)
  have hSmooth : Smooth (toS H) := smooth_toS H
  have : CompactSpace (Gl H) := compactSpace_glued H hL
  refine ⟨{
    group := G
    smooth := hSmooth
    isSeparated := inferInstanceAs (IsSeparated (toS H))
    locallyOfFiniteType := inferInstanceAs (LocallyOfFiniteType (toS H))
    quasiCompact := quasiCompact_of_compactSpace (toS H)
    domain := V
    domain_dense := hV
    embedding := ch H none
    embedding_comp := ch_toS H none
    isOpenImmersion_embedding := inferInstanceAs (IsOpenImmersion (ch H none))
    embedding_dense := original_chart_dense H
    mul_eq := ?_ }, rfl⟩
  intro T a x y z hx hy hz
  obtain ⟨b, hbx, hby, hbz⟩ := hfactor a x y z hx hy hz
  have hxy : x ≫ g = y ≫ g := by
    change x ≫ (V.ι ≫ f) = y ≫ (V.ι ≫ f)
    rw [← hbx, ← hby]
    simp only [Category.assoc, pullback.condition]
  have hd : n.Defined x y hxy := by
    apply n.pairIn_domain_of_eq b
    apply pullback.hom_ext
    · simpa only [pullback.lift_fst, Category.assoc] using hbx.symm
    · simpa only [pullback.lift_snd, Category.assoc] using hby.symm
  have hmul : n.mulPt x y hxy hd = z := by
    rw [BirationalGroupLaw.mulPt, ← n.liftDom_eq x y hxy hd b hbx hby, hbz]
  let x₀ : SchemeHomOver (x ≫ g) g := ⟨x, rfl⟩
  let y₀ : SchemeHomOver (x ≫ g) g := ⟨y, hxy.symm⟩
  let xG : Over.mk (x ≫ g) ⟶ G.X := schemeHomOverToOverHom (chartPt H none x₀)
  let yG : Over.mk (x ≫ g) ⟶ G.X := schemeHomOverToOverHom (chartPt H none y₀)
  change z ≫ ch H none = (xG * yG).left
  have hprod := gluedGroup_mul H hL e he xG yG
  change (xG * yG).left = (mulPts H hL (chartPt H none x₀) (chartPt H none y₀)).1 at hprod
  rw [hprod, mulPts_in_chart H hL none x₀ y₀ hd]
  change z ≫ ch H none = n.mulPt x y hxy hd ≫ ch H none
  rw [hmul]

end Langlands.AlgebraicGeometry
