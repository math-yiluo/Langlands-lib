import Langlands.AlgebraicGeometry.HenselianBirationalSolution.MulAssoc

/-! # Choosing a section chart

For sections `d`, `b` and a point `y` with `δ = d⁻¹ b` defined and `(δ, y)` in the domain, the
chart of `d` at `δ y` is the chart of `b` at `y` (`chart_shift`; it follows from
`μ (d, δ y) = μ (d δ, y)`). For a chart index `j` and a `P`-point `y` of `Y`, `chartCover`
constructs a fibrewise dense open of `Y ×_S P` such that a section lifting into it over an
open of `P` puts the chart of `j` at `y` in the chart of that section over the same open.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {m : BirationalGroupLaw g}
  [IsReduced Y] [Smooth g] [IsSeparated g] [IsNoetherian Y] [Surjective g]
  [QuasiCompact g] (H : GlueHyp m) [S.IsSeparated] (hL : HasSectionLifts g)

include hL in
/-- **Chart shift.** If `d δ = b` then the chart of `d` at `δ y` is the chart of `b` at `y`. -/
theorem chart_shift (d b : Sect g) {T : Scheme.{u}} (δ y : T ⟶ Y) (hδy : δ ≫ g = y ≫ g)
    (h1 : m.Defined (δ ≫ g ≫ d.1) δ (section_comp_g d.1 d.2 δ))
    (h2 : m.mulPt (δ ≫ g ≫ d.1) δ (section_comp_g d.1 d.2 δ) h1 = δ ≫ g ≫ b.1)
    (h3 : m.Defined δ y hδy) :
    m.mulPt δ y hδy h3 ≫ ch H (some d) = y ≫ ch H (some b) := by
  rw [← sectionPair_mulG H hL d, ← sectionPair_mulG H hL b, ← Category.assoc, ← Category.assoc,
    sectionPair_comp, sectionPair_comp]
  have e1 : pullback.lift (m.mulPt δ y hδy h3 ≫ g ≫ d.1) (m.mulPt δ y hδy h3)
      (by rw [Category.assoc, Category.assoc, d.2, Category.comp_id]) =
      pullback.lift (δ ≫ g ≫ d.1) (m.mulPt δ y hδy h3)
        (by rw [m.mulPt_comp_g, section_comp_g d.1 d.2]) :=
    lift_congr (by rw [← Category.assoc, m.mulPt_comp_g, Category.assoc]) rfl
  rw [e1, ← mulG_assoc_pt H hL (δ ≫ g ≫ d.1) δ y (section_comp_g d.1 d.2 δ) hδy h1 h3]
  congr 1
  apply lift_congr _ rfl
  rw [h2, ← Category.assoc, hδy, Category.assoc]

omit [IsReduced Y] [Smooth g] [IsSeparated g] [AlgebraicGeometry.IsNoetherian Y]
  [Surjective g] [QuasiCompact g] [S.IsSeparated] in
/-- The image of the translation by `c` consists of the `y` with `(c, y)` in the image of the
universal left translation. -/
theorem range_secTrans_map (c : Sect g) :
    Set.range (secTrans H (some c)).map = sectionPair c.1 c.2 ⁻¹' Set.range (leftT m) := by
  have himg := Scheme.image_preimage_eq_of_isPullback
    (isPullback_sectionPair_restrict m c.1 c.2) Set.univ
  rw [Set.preimage_univ, Set.image_univ, Set.image_univ] at himg
  exact himg

omit [IsReduced Y] [Smooth g] [IsSeparated g] [AlgebraicGeometry.IsNoetherian Y]
  [Surjective g] [QuasiCompact g] [S.IsSeparated] in
theorem secLift_pairSnd {P : Scheme.{u}} (q : P ⟶ S) (y : P ⟶ Y) (hy : y ≫ g = q) (d : Sect g) :
    secLift q d ≫ pairSnd y hy = y ≫ sectionPair d.1 d.2 := by
  apply pullback.hom_ext
  · simp only [pullback.lift_fst, Category.assoc]
    rw [← Category.assoc, hy]
  · simp

include hL in
/-- **Chart cover.** For a chart index `j` and a family `y` of points of `Y` over `P`, there is
an open subscheme of `Y ×_S P`, dense in the fibres over `P`, such that whenever a section `d`
lifts into it over an open `O` of `P`, the chart of `j` at `y` lies in the chart of `d` over
`O`. -/
theorem chartCover (j : Option (Sect g)) {P : Scheme.{u}} (q : P ⟶ S) (y : P ⟶ Y)
    (hy : y ≫ g = q) :
    ∃ (Zs : Scheme.{u}) (jm : Zs ⟶ pullback g q) (_ : IsOpenImmersion jm),
      FibreGenerizationDense (pullback.snd g q) (Set.range jm) ∧
      ∀ (d : Sect g) (O : P.Opens) (ℓ : O.toScheme ⟶ Zs), ℓ ≫ jm = O.ι ≫ secLift q d →
        ∀ o : O.toScheme, ch H j (y (O.ι o)) ∈ Set.range (ch H (some d)) := by
  cases j with
  | none =>
    let Zs : (pullback g q).Opens := pairSnd y hy ⁻¹ᵁ (leftT m).opensRange
    refine ⟨Zs, Zs.ι, inferInstance, ?_, ?_⟩
    · rw [Scheme.Opens.range_ι]
      exact fibreGenerizationDense_pairSnd y hy (by simpa using H.strict.left_snd)
    · intro d O ℓ hℓ o
      have hmem : secLift q d (O.ι o) ∈ Zs := by
        rw [← Scheme.Hom.comp_apply, ← hℓ, Scheme.Hom.comp_apply]
        exact (ℓ o).2
      have h2 : y (O.ι o) ∈ Set.range (secTrans H (some d)).map := by
        rw [range_secTrans_map]
        change sectionPair d.1 d.2 (y (O.ι o)) ∈ Set.range (leftT m)
        rw [← Scheme.Hom.comp_apply, ← secLift_pairSnd q y hy d, Scheme.Hom.comp_apply]
        exact hmem
      obtain ⟨w, hw⟩ := h2
      refine ⟨(secTrans H (some d)).dom.ι w, ?_⟩
      have h3 := dom_chart H (some d) (𝟙 _)
      simp only [Category.id_comp] at h3
      rw [← Scheme.Hom.comp_apply, h3, Scheme.Hom.comp_apply, hw]
  | some b =>
    set xb := q ≫ b.1
    have hxb : xb ≫ g = q := by simp only [xb, Category.assoc, b.2, Category.comp_id]
    set s := sliceSnd m.mul xb hxb (leftT m) m.leftT_snd
    set t := sliceFst m.mul xb hxb (rightT m) m.rightT_fst
    let Z₂ : (pullback g q).Opens := pairSnd y hy ⁻¹ᵁ m.domain
    let Zs : (pullback m.mul xb).Opens := t ⁻¹ᵁ Z₂
    have hZ₂ : FibreGenerizationDense (pullback.snd g q) (Z₂ : Set _) :=
      fibreGenerizationDense_pairSnd _ hy H.strict.domain_snd
    refine ⟨Zs, Zs.ι ≫ s, inferInstance, ?_, ?_⟩
    · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
      exact fibreGenerizationDense_image s _
        (fibreGenerizationDense_range_sliceSnd _ _ hxb _ _ H.strict.left_snd)
        (FibreGenerizationDense.preimage_of_isOpenImmersion t
          (by rw [sliceFst_snd, sliceSnd_snd]) hZ₂)
    · intro d O ℓ hℓ o
      set a := ℓ ≫ Zs.ι
      set uu := a ≫ pullback.fst m.mul xb
      have ha : a ≫ s = O.ι ≫ secLift q d := by rw [Category.assoc]; exact hℓ
      have h1 : uu ≫ m.domain.ι ≫ pullback.fst g g = O.ι ≫ q ≫ d.1 := by
        have := congrArg (· ≫ pullback.fst g q) ha
        simp only [s, Category.assoc, sliceSnd_fst, pullback.lift_fst, m.leftT_fst] at this
        simpa only [uu, Category.assoc] using this
      have h2 : a ≫ pullback.snd m.mul xb = O.ι := by
        have := congrArg (· ≫ pullback.snd g q) ha
        simpa only [s, Category.assoc, sliceSnd_snd, pullback.lift_snd, Category.comp_id]
          using this
      have h3 : uu ≫ m.mul = O.ι ≫ q ≫ b.1 := by
        rw [Category.assoc, pullback.condition, ← Category.assoc, h2]
      set δ := uu ≫ m.domain.ι ≫ pullback.snd g g
      set yO := O.ι ≫ y
      have hδg : δ ≫ g = O.ι ≫ q := by
        calc δ ≫ g = (uu ≫ m.domain.ι ≫ pullback.fst g g) ≫ g := by
              simp only [δ, Category.assoc, pullback.condition]
          _ = O.ι ≫ q := by rw [h1]; simp only [Category.assoc, d.2, Category.comp_id]
      have hδy : δ ≫ g = yO ≫ g := by
        rw [hδg]
        simp only [yO, Category.assoc, hy]
      have h4 : m.Defined δ yO hδy := by
        have hat : a ≫ t ≫ pairSnd y hy = pullback.lift δ yO hδy := by
          apply pullback.hom_ext
          · simp only [t, Category.assoc, pullback.lift_fst]
            rw [sliceFst_fst, m.rightT_snd]
            simp only [δ, uu, Category.assoc]
          · simp only [t, Category.assoc, pullback.lift_snd, sliceFst_snd_assoc]
            rw [← Category.assoc, h2]
        rintro _ ⟨o', rfl⟩
        rw [← hat, Scheme.Hom.comp_apply]
        exact (ℓ o').2
      have hcδ : δ ≫ g ≫ d.1 = uu ≫ m.domain.ι ≫ pullback.fst g g := by
        rw [← Category.assoc, hδg, h1, Category.assoc]
      have hD1 : m.Defined (δ ≫ g ≫ d.1) δ (section_comp_g d.1 d.2 δ) := by
        refine m.pairIn_domain_of_eq uu ?_
        apply pullback.hom_ext
        · rw [pullback.lift_fst, hcδ]
          simp only [uu, Category.assoc]
        · rw [pullback.lift_snd]
          simp only [δ, uu, Category.assoc]
      have hD2 : m.mulPt (δ ≫ g ≫ d.1) δ (section_comp_g d.1 d.2 δ) hD1 = δ ≫ g ≫ b.1 := by
        rw [BirationalGroupLaw.mulPt, ← m.liftDom_eq _ _ _ hD1 uu hcδ.symm rfl, h3,
          ← Category.assoc δ, hδg, Category.assoc]
      have shift := chart_shift H hL d b δ yO hδy hD1 hD2 h4
      refine ⟨m.mulPt δ yO hδy h4 o, ?_⟩
      rw [← Scheme.Hom.comp_apply, shift]
      rfl

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
