import Langlands.AlgebraicGeometry.HenselianBirationalSolution.MulBar
import Langlands.AnthropicFLT.OverBase.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

/-! # Associativity and chart formulas for the extended multiplication

The scheme of triples in the glued scheme contains a dense open on which both consecutive
pairs lie in the original domain. On that open, associativity is the identity for the extension
on `Y ×_S Y`. For a section chart, this gives `(a x)y = a(xy)` whenever `(x,y)` is in the
original domain.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology NeronModelInfra

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {m : BirationalGroupLaw g}
  [IsReduced Y] [Smooth g] [IsSeparated g] [IsNoetherian Y] [Surjective g]
  [QuasiCompact g] (H : GlueHyp m)

abbrev Gfst : GG H ⟶ Gl H := pullback.fst (toS H) (toS H)
abbrev Gsnd : GG H ⟶ Gl H := pullback.snd (toS H) (toS H)

namespace GluedTriples

abbrev G3 : Scheme.{u} := pullback (Gfst H) (Gsnd H)

/-- The open of triples for which the two consecutive pairs are in the original domain. -/
abbrev domainPair : m.domain.toScheme ⟶ GG H := m.domain.ι ≫ chartPair H none none

@[reassoc]
theorem domainPair_fst : domainPair H ≫ Gfst H = (m.domain.ι ≫ pullback.fst g g) ≫ ch H none := by
  simp [domainPair, chartPair]

@[reassoc]
theorem domainPair_snd : domainPair H ≫ Gsnd H = (m.domain.ι ≫ pullback.snd g g) ≫ ch H none := by
  simp [domainPair, chartPair]

abbrev j : Triples.T3 (m := m) ⟶ G3 H :=
  pullback.map (m.domain.ι ≫ pullback.fst g g) (m.domain.ι ≫ pullback.snd g g) (Gfst H) (Gsnd H)
    (domainPair H) (domainPair H) (ch H none) (domainPair_fst H).symm (domainPair_snd H).symm

theorem range_domainPair : Set.range (domainPair H) = mulOpen H := by
  rw [domainPair, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
  rfl

instance : IsDominant (j H) := by
  have : Smooth (toS H) := smooth_toS H
  have h : genericPoints (G3 H) ⊆ Set.range (j H) := by
    rw [j, Scheme.Pullback.range_map, range_domainPair]
    intro p hp
    exact ⟨genericPoints_mulOpen H (mapsTo_genericPoints _ (generalizingMap_of_flat _) hp),
      genericPoints_mulOpen H (mapsTo_genericPoints _ (generalizingMap_of_flat _) hp)⟩
  exact ⟨dense_of_genericPoints_subset h⟩

instance : IsReduced (G3 H) := by
  have : Smooth (toS H) := smooth_toS H
  exact SmoothReducedBase.isReduced_of_smooth_of_isReduced (pullback.snd (Gfst H) (Gsnd H))

variable [S.IsSeparated] (hL : HasSectionLifts g)

/-- The pairs `((x y), z)` and `(x, (y z))` formed using the extended multiplication. -/
abbrev L : G3 H ⟶ GG H :=
  pullback.lift (pullback.snd (Gfst H) (Gsnd H) ≫ mulBar H hL)
    (pullback.fst (Gfst H) (Gsnd H) ≫ Gsnd H) (by
      simp only [Category.assoc, mulBar_toS]
      have hc : Gfst H ≫ toS H = Gsnd H ≫ toS H := pullback.condition
      have hd : pullback.fst (Gfst H) (Gsnd H) ≫ Gfst H =
          pullback.snd (Gfst H) (Gsnd H) ≫ Gsnd H := pullback.condition
      change pullback.snd (Gfst H) (Gsnd H) ≫ Gfst H ≫ toS H = _
      rw [hc, ← reassoc_of% hd, hc])

abbrev R : G3 H ⟶ GG H :=
  pullback.lift (pullback.snd (Gfst H) (Gsnd H) ≫ Gfst H)
    (pullback.fst (Gfst H) (Gsnd H) ≫ mulBar H hL) (by
      simp only [Category.assoc, mulBar_toS]
      have hc : Gfst H ≫ toS H = Gsnd H ≫ toS H := pullback.condition
      have hd : pullback.fst (Gfst H) (Gsnd H) ≫ Gfst H =
          pullback.snd (Gfst H) (Gsnd H) ≫ Gsnd H := pullback.condition
      rw [hc, ← reassoc_of% hd, hc])

@[reassoc]
theorem j_L : j H ≫ L H hL = Triples.L (m := m) ≫ chartPair H none none := by
  apply pullback.hom_ext
  · simp only [L, Category.assoc, pullback.lift_fst, j, pullback.lift_snd_assoc, domainPair,
      domain_chartPair_mulBar, chartPair, Triples.L_fst_assoc]
  · simp only [L, Category.assoc, pullback.lift_snd, j, pullback.lift_fst_assoc,
      chartPair, Triples.L_snd_assoc]

@[reassoc]
theorem j_R : j H ≫ R H hL = Triples.R (m := m) ≫ chartPair H none none := by
  apply pullback.hom_ext
  · simp only [R, Category.assoc, pullback.lift_fst, j, pullback.lift_snd_assoc,
      chartPair, Triples.R_fst_assoc]
  · simp only [R, Category.assoc, pullback.lift_snd, j, pullback.lift_fst_assoc, domainPair,
      domain_chartPair_mulBar, chartPair, Triples.R_snd_assoc]

theorem assoc : L H hL ≫ mulBar H hL = R H hL ≫ mulBar H hL := by
  apply ext_of_isDominant (j H)
  rw [← Category.assoc, j_L, Category.assoc, chartPair_mulBar,
    ← Category.assoc, j_R, Category.assoc, chartPair_mulBar, mulG_assoc]

end GluedTriples

variable [S.IsSeparated] (hL : HasSectionLifts g)

/-- Multiplication of `T`-points of the glued scheme over the same map `t : T ⟶ S`. -/
def mulPts {T : Scheme.{u}} {t : T ⟶ S} (x y : SchemeHomOver t (toS H)) :
    SchemeHomOver t (toS H) :=
  ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ mulBar H hL, by
    rw [Category.assoc, mulBar_toS, pullback.lift_fst_assoc, x.2]⟩

/-- The `T`-point of the glued scheme induced by its chart of index `i`. -/
def chartPt {T : Scheme.{u}} {t : T ⟶ S} (i : Option (Sect g)) (x : SchemeHomOver t g) :
    SchemeHomOver t (toS H) := ⟨x.1 ≫ ch H i, by rw [Category.assoc, ch_toS, x.2]⟩

/-- Pointwise associativity follows by evaluating the equality on the scheme of triples. -/
theorem mulPts_assoc {T : Scheme.{u}} {t : T ⟶ S} (x y z : SchemeHomOver t (toS H)) :
    mulPts H hL (mulPts H hL x y) z = mulPts H hL x (mulPts H hL y z) := by
  let xy := pullback.lift x.1 y.1 (x.2.trans y.2.symm)
  let yz := pullback.lift y.1 z.1 (y.2.trans z.2.symm)
  let a : T ⟶ GluedTriples.G3 H := pullback.lift yz xy (by simp [xy, yz, Gfst, Gsnd])
  have hl : a ≫ GluedTriples.L H hL =
      pullback.lift (mulPts H hL x y).1 z.1 ((mulPts H hL x y).2.trans z.2.symm) := by
    apply pullback.hom_ext <;> simp [a, GluedTriples.L, xy, yz, mulPts, Gsnd]
  have hr : a ≫ GluedTriples.R H hL =
      pullback.lift x.1 (mulPts H hL y z).1 (x.2.trans (mulPts H hL y z).2.symm) := by
    apply pullback.hom_ext <;> simp [a, GluedTriples.R, xy, yz, mulPts, Gfst]
  apply Subtype.ext
  change _ ≫ mulBar H hL = _ ≫ mulBar H hL
  rw [← hl, ← hr, Category.assoc, Category.assoc, GluedTriples.assoc]

theorem mulPts_in_identity_chart {T : Scheme.{u}} {t : T ⟶ S} (x y : SchemeHomOver t g) :
    (mulPts H hL (chartPt H none x) (chartPt H none y)).1 =
      pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ mulG H hL := by
  change pullback.lift (x.1 ≫ ch H none) (y.1 ≫ ch H none) _ ≫ mulBar H hL = _
  rw [← lift_chartPair H none none x.1 y.1 (x.2.trans y.2.symm), Category.assoc, chartPair_mulBar]

theorem mulPts_section_chart {T : Scheme.{u}} {t : T ⟶ S} (c : Sect g) (x : SchemeHomOver t g) :
    mulPts H hL (chartPt H none ⟨t ≫ c.1, by simp [c.2]⟩) (chartPt H none x) =
      chartPt H (some c) x := by
  apply Subtype.ext
  rw [mulPts_in_identity_chart]
  change pullback.lift (t ≫ c.1) x.1 _ ≫ mulG H hL = x.1 ≫ ch H (some c)
  have he : pullback.lift (t ≫ c.1) x.1 (by simp [c.2, x.2]) = x.1 ≫ sectionPair c.1 c.2 := by
    rw [sectionPair_comp]
    apply lift_congr _ rfl
    rw [← Category.assoc, x.2]
  rw [he, Category.assoc, sectionPair_mulG]

/-- Left multiplication in the chart of a section is the original law on its domain. -/
theorem mulPts_in_chart {T : Scheme.{u}} {t : T ⟶ S} (i : Option (Sect g)) (x y : SchemeHomOver t g)
    (hd : m.Defined x.1 y.1 (x.2.trans y.2.symm)) :
    mulPts H hL (chartPt H i x) (chartPt H none y) =
      chartPt H i ⟨m.mulPt x.1 y.1 _ hd, by rw [m.mulPt_comp_g, x.2]⟩ := by
  let z : SchemeHomOver t g := ⟨m.mulPt x.1 y.1 _ hd, by rw [m.mulPt_comp_g, x.2]⟩
  have e : mulPts H hL (chartPt H none x) (chartPt H none y) = chartPt H none z := by
    apply Subtype.ext
    rw [mulPts_in_identity_chart, lift_mulG H hL _ _ _ hd]
    rfl
  cases i with
  | none => exact e
  | some c =>
    change mulPts H hL (chartPt H (some c) x) (chartPt H none y) = chartPt H (some c) z
    rw [← mulPts_section_chart H hL c x, mulPts_assoc, e, mulPts_section_chart]

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
