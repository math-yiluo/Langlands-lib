import Langlands.AlgebraicGeometry.HenselianBirationalSolution.SectionCharts

/-! # The law extends to `Y ×_S Y ⟶ G`

Let `G` be the scheme glued from the translates of `Y` by all sections. The law
`m : U ⟶ Y ⟶ G` on the domain `U ⊆ Y ×_S Y` extends to a morphism `μ : Y ×_S Y ⟶ G`
(compare BLR §5.3, Lemma 6). Near a point `(x₀, y₀)` choose a section `c` such that `c⁻¹ x₀` is
defined and `(c⁻¹ x₀, y₀)` lies in `U`; on the pairs `(c w, y)` with `w` in the domain of `τ_c`
and `(w, y) ∈ U`, the local formula is `(c w, y) ↦ c · (w y)`, read in the chart of `c`. It
agrees with `m` wherever `w y` lies in the domain of `τ_c`, by associativity.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {m : BirationalGroupLaw g}

theorem flat_mul [Smooth g] : Flat m.mul := by
  rw [← m.leftT_snd]
  infer_instance

variable [IsReduced Y] [Smooth g] [IsSeparated g] [IsNoetherian Y] [Surjective g]
  [QuasiCompact g] (H : GlueHyp m)

instance : IsReduced (pullback g g) :=
  SmoothReducedBase.isReduced_of_smooth_of_isReduced (pullback.fst g g)

instance : IsSeparated (toS H) := Glue.isSeparated_toBase H _

instance [S.IsSeparated] : (Gl H).IsSeparated := isSeparated_of_isSeparated (toS H)


namespace MulPiece

variable (c : Sect g)

/-- `dom τ_c ×_S Y`. -/
abbrev D : Scheme.{u} := pullback ((secTrans H (some c)).dom.ι ≫ g) g

/-- The inclusion `dom τ_c ×_S Y ⟶ Y ×_S Y`. -/
abbrev ιD : D H c ⟶ pullback g g :=
  pullback.map _ _ _ _ (secTrans H (some c)).dom.ι (𝟙 Y) (𝟙 S) (by simp) (by simp)

/-- `τ_c × 1 : dom τ_c ×_S Y ⟶ Y ×_S Y`. -/
abbrev τD : D H c ⟶ pullback g g :=
  pullback.map _ _ _ _ (secTrans H (some c)).map (𝟙 Y) (𝟙 S)
    (by rw [Category.comp_id, (secTrans H (some c)).map_comp]) (by simp)

/-- The pairs `(w, y)` with `w ∈ dom τ_c` and `(w, y) ∈ U`. -/
abbrev Q : Scheme.{u} := pullback (ιD H c) m.domain.ι

/-- `(w, y) ↦ (c w, y)`. -/
abbrev e : Q H c ⟶ pullback g g := pullback.fst _ _ ≫ τD H c

/-- `(w, y) ↦ c · (w y)` in the chart of `c`. -/
abbrev φ : Q H c ⟶ Gl H := pullback.snd _ _ ≫ m.mul ≫ ch H (some c)

/-- The pairs with `w y ∈ dom τ_c`. -/
abbrev W : (Q H c).Opens := (pullback.snd (ιD H c) m.domain.ι ≫ m.mul) ⁻¹ᵁ
  (secTrans H (some c)).dom

omit [IsReduced Y] [IsSeparated g] [AlgebraicGeometry.IsNoetherian Y] [Surjective g]
  [QuasiCompact g] in
theorem genericPoints_subset : genericPoints (Q H c) ⊆ W H c := by
  have : Flat m.mul := flat_mul
  exact genericPoints_subset_preimage _ (generalizingMap_of_flat _)
    (FibreGenerizationDense.genericPoints_subset (secTrans H (some c)).dom_dense)

theorem agree {T : Scheme.{u}} (u : T ⟶ (W H c).toScheme) (v : T ⟶ m.domain.toScheme)
    (h : u ≫ (W H c).ι ≫ e H c = v ≫ m.domain.ι) :
    u ≫ (W H c).ι ≫ φ H c = v ≫ m.mul ≫ ch H none := by
  obtain ⟨r, hr⟩ : ∃ r, r = u ≫ (W H c).ι := ⟨_, rfl⟩
  rw [← Category.assoc, ← hr] at h ⊢
  set wD : T ⟶ (secTrans H (some c)).dom.toScheme :=
    r ≫ pullback.fst _ _ ≫ pullback.fst _ _
  set w := wD ≫ (secTrans H (some c)).dom.ι
  set y := r ≫ pullback.fst _ _ ≫ pullback.snd _ _
  have hwy : w ≫ g = y ≫ g := by
    simp only [w, wD, y, Category.assoc, pullback.condition]
  have hpr : r ≫ pullback.snd _ _ ≫ m.domain.ι = pullback.lift w y hwy := by
    rw [← pullback.condition]
    apply pullback.hom_ext <;> simp [w, wD, y]
  have hd : m.Defined w y hwy :=
    m.pairIn_domain_of_eq (r ≫ pullback.snd _ _) (by rw [Category.assoc, hpr])
  have hrd : r ≫ pullback.snd _ _ = m.liftDom w y hwy hd := by
    apply m.liftDom_eq
    · calc _ = (r ≫ pullback.snd _ _ ≫ m.domain.ι) ≫ pullback.fst g g := by
            simp only [Category.assoc]
        _ = w := by rw [hpr, pullback.lift_fst]
    · calc _ = (r ≫ pullback.snd _ _ ≫ m.domain.ι) ≫ pullback.snd g g := by
            simp only [Category.assoc]
        _ = y := by rw [hpr, pullback.lift_snd]
  have hz : r ≫ pullback.snd _ _ ≫ m.mul = m.mulPt w y hwy hd := by
    rw [← Category.assoc, hrd]
    rfl
  have hzr : Set.range (m.mulPt w y hwy hd) ⊆ Set.range (secTrans H (some c)).dom.ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι, ← hz, hr]
    exact (u t).2
  set z' := IsOpenImmersion.lift _ _ hzr
  have hz' : z' ≫ (secTrans H (some c)).dom.ι = m.mulPt w y hwy hd :=
    IsOpenImmersion.lift_fac _ _ _
  -- the product `x' y'` given by `v`
  have hv : v ≫ m.domain.ι = pullback.lift (wD ≫ (secTrans H (some c)).map) y
      (by rw [Category.assoc, (secTrans H (some c)).map_comp]; exact hwy) := by
    rw [← h]
    apply pullback.hom_ext <;> simp [wD, y]
  have hxg : (wD ≫ (secTrans H (some c)).map) ≫ g = y ≫ g := by
    rw [Category.assoc, (secTrans H (some c)).map_comp]; exact hwy
  have hdv : m.Defined (wD ≫ (secTrans H (some c)).map) y hxg := m.pairIn_domain_of_eq _ hv.symm
  have hvm : v ≫ m.mul = m.mulPt (wD ≫ (secTrans H (some c)).map) y hxg hdv := by
    rw [BirationalGroupLaw.mulPt]
    congr 1
    apply m.liftDom_eq
    · rw [← Category.assoc, hv, pullback.lift_fst]
    · rw [← Category.assoc, hv, pullback.lift_snd]
  -- associativity `c (w y) = (c w) y`
  have hcg : (w ≫ g ≫ c.1) ≫ g = w ≫ g := section_comp_g c.1 c.2 w
  have hcw : m.Defined (w ≫ g ≫ c.1) w hcg := secTrans_defined H c wD
  have hmap : wD ≫ (secTrans H (some c)).map = m.mulPt (w ≫ g ≫ c.1) w hcg hcw :=
    secTrans_map_eq H c wD
  have hzg : (z' ≫ (secTrans H (some c)).dom.ι) ≫ g ≫ c.1 = w ≫ g ≫ c.1 := by
    rw [hz', ← Category.assoc, m.mulPt_comp_g, Category.assoc]
  have dr : m.Defined (w ≫ g ≫ c.1) (m.mulPt w y hwy hd) (by simp [hcg]) :=
    (secTrans_defined H c z').of_eq hzg hz'
  have dl : m.Defined (m.mulPt (w ≫ g ≫ c.1) w hcg hcw) y (by simp [hcg, hwy]) :=
    hdv.of_eq hmap rfl
  have hassoc := m.mulPt_assoc (w ≫ g ≫ c.1) w y hcg hwy hcw hd dl dr
  have hchart := dom_chart_some H c z'
  calc r ≫ φ H c = m.mulPt w y hwy hd ≫ ch H (some c) := by
        rw [← hz]
        simp only [Category.assoc]
    _ = (z' ≫ (secTrans H (some c)).dom.ι) ≫ ch H (some c) := by rw [hz']
    _ = m.mulPt ((z' ≫ (secTrans H (some c)).dom.ι) ≫ g ≫ c.1)
          (z' ≫ (secTrans H (some c)).dom.ι) (section_comp_g c.1 c.2 _)
          (secTrans_defined H c z') ≫ ch H none := hchart
    _ = m.mulPt (w ≫ g ≫ c.1) (m.mulPt w y hwy hd) (by simp [hcg]) dr ≫ ch H none := by
        rw [m.mulPt_congr hzg hz']
    _ = m.mulPt (m.mulPt (w ≫ g ≫ c.1) w hcg hcw) y (by simp [hcg, hwy]) dl ≫ ch H none := by
        rw [hassoc]
    _ = v ≫ m.mul ≫ ch H none := by
        rw [← Category.assoc v, hvm]
        congr 1
        exact m.mulPt_congr hmap.symm rfl

omit [IsReduced Y] [Smooth g] [IsSeparated g] [AlgebraicGeometry.IsNoetherian Y]
  [Surjective g] [QuasiCompact g] in
/-- Every point of `Y ×_S Y` is `(c w, y)` with `w` in the domain of `τ_c` and `(w, y) ∈ U`, for
some section `c`. -/
theorem cover (hL : HasSectionLifts g) (p₀ : ↥(pullback g g)) :
    ∃ c : Sect g, p₀ ∈ Set.range (e H c) := by
  set q : pullback g g ⟶ S := pullback.fst g g ≫ g
  have hx : pullback.fst g g ≫ g = q := rfl
  have hy : pullback.snd g g ≫ g = q := pullback.condition.symm
  set s := sliceSnd m.mul (pullback.fst g g) hx (leftT m) m.leftT_snd
  set t := sliceFst m.mul (pullback.fst g g) hx (rightT m) m.rightT_fst
  let Z₂ : (pullback g q).Opens := pairSnd (pullback.snd g g) hy ⁻¹ᵁ m.domain
  let Zs : (pullback m.mul (pullback.fst g g)).Opens := t ⁻¹ᵁ Z₂
  have hZ₂ : FibreGenerizationDense (pullback.snd g q) (Z₂ : Set _) :=
    fibreGenerizationDense_pairSnd _ hy H.strict.domain_snd
  have hj : FibreGenerizationDense (pullback.snd g q) (Set.range (Zs.ι ≫ s)) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    exact fibreGenerizationDense_image s _
      (fibreGenerizationDense_range_sliceSnd _ _ hx _ _ H.strict.left_snd)
      (FibreGenerizationDense.preimage_of_isOpenImmersion t
        (by rw [sliceFst_snd, sliceSnd_snd]) hZ₂)
  obtain ⟨c, O, ℓ, hp₀, hℓ⟩ := hL.exists_lift q (Zs.ι ≫ s) hj p₀
  set a := ℓ ≫ Zs.ι
  set uu := a ≫ pullback.fst m.mul (pullback.fst g g)
  have ha : a ≫ s = O.ι ≫ secLift q c := by rw [Category.assoc]; exact hℓ
  have h1 : uu ≫ m.domain.ι ≫ pullback.fst g g = O.ι ≫ q ≫ c.1 := by
    have := congrArg (· ≫ pullback.fst g q) ha
    simp only [s, Category.assoc, sliceSnd_fst, pullback.lift_fst, m.leftT_fst] at this
    simpa only [uu, Category.assoc] using this
  have h2 : a ≫ pullback.snd m.mul (pullback.fst g g) = O.ι := by
    have := congrArg (· ≫ pullback.snd g q) ha
    simpa only [s, Category.assoc, sliceSnd_snd, pullback.lift_snd, Category.comp_id] using this
  have h3 : uu ≫ m.mul = O.ι ≫ pullback.fst g g := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, h2]
  set δ := uu ≫ m.domain.ι ≫ pullback.snd g g
  set y := O.ι ≫ pullback.snd g g
  have hδg : δ ≫ g = O.ι ≫ q := by
    calc δ ≫ g = (uu ≫ m.domain.ι ≫ pullback.fst g g) ≫ g := by
          simp only [δ, Category.assoc, pullback.condition]
      _ = O.ι ≫ q := by rw [h1]; simp only [Category.assoc, c.2, Category.comp_id]
  have hδy : δ ≫ g = y ≫ g := by
    rw [hδg]
    simp only [y, q, Category.assoc, pullback.condition]
  have h4 : m.Defined δ y hδy := by
    have hat : a ≫ t ≫ pairSnd (pullback.snd g g) hy = pullback.lift δ y hδy := by
      apply pullback.hom_ext
      · simp only [t, Category.assoc, pullback.lift_fst]
        rw [sliceFst_fst, m.rightT_snd]
        simp only [δ, uu, Category.assoc]
      · simp only [t, Category.assoc, pullback.lift_snd, sliceFst_snd_assoc]
        rw [← Category.assoc, h2]
    rintro _ ⟨o, rfl⟩
    rw [← hat, Scheme.Hom.comp_apply]
    exact (ℓ o).2
  have hcδ : δ ≫ g ≫ c.1 = uu ≫ m.domain.ι ≫ pullback.fst g g := by
    rw [← Category.assoc, hδg, h1, Category.assoc]
  have h5 : m.Defined (δ ≫ g ≫ c.1) δ (section_comp_g c.1 c.2 δ) := by
    refine m.pairIn_domain_of_eq uu ?_
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hcδ]
      simp only [uu, Category.assoc]
    · rw [pullback.lift_snd]
      simp only [δ, uu, Category.assoc]
  have hδr : Set.range δ ⊆ Set.range (secTrans H (some c)).dom.ι := by
    rw [Scheme.Opens.range_ι]
    exact range_subset_secTrans_dom H c δ h5
  set δD := IsOpenImmersion.lift _ δ hδr
  have hδD : δD ≫ (secTrans H (some c)).dom.ι = δ := IsOpenImmersion.lift_fac _ _ _
  set kD : O.toScheme ⟶ D H c := pullback.lift δD y (by rw [reassoc_of% hδD]; exact hδy)
  set kU := m.liftDom δ y hδy h4
  have hk : kD ≫ ιD H c = kU ≫ m.domain.ι := by
    apply pullback.hom_ext
    · simp [kD, kU, hδD]
    · simp [kD, kU]
  set k := pullback.lift kD kU hk
  have hmap : δD ≫ (secTrans H (some c)).map = O.ι ≫ pullback.fst g g := by
    rw [secTrans_map_eq H c δD, ← h3, BirationalGroupLaw.mulPt]
    congr 1
    symm
    apply m.liftDom_eq
    · rw [hδD, hcδ]
    · rw [hδD]
  have hke : k ≫ e H c = O.ι := by
    apply pullback.hom_ext
    · simp only [k, kD, e, τD, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact hmap
    · simp only [k, kD, e, τD, Category.assoc, pullback.lift_snd, pullback.lift_fst_assoc,
        Category.comp_id]
      rfl
  refine ⟨c, k (show O.toScheme from ⟨p₀, hp₀⟩), ?_⟩
  rw [← Scheme.Hom.comp_apply, hke]
  rfl

end MulPiece

variable [S.IsSeparated] (hL : HasSectionLifts g)

include hL in
theorem exists_mulG : ∃ μ : pullback g g ⟶ Gl H, m.domain.ι ≫ μ = m.mul ≫ ch H none :=
  exists_extension_of_pieces m.domain (FibreGenerizationDense.dense H.strict.domain_fst)
    (m.mul ≫ ch H none) fun p₀ => by
      obtain ⟨c, hc⟩ := MulPiece.cover H hL p₀
      exact ⟨MulPiece.Q H c, MulPiece.e H c, inferInstance, MulPiece.φ H c, MulPiece.W H c, hc,
        MulPiece.genericPoints_subset H c, fun T u v h => MulPiece.agree H c u v h⟩

/-- The extension `μ : Y ×_S Y ⟶ G` of the law. -/
def mulG : pullback g g ⟶ Gl H := (exists_mulG H hL).choose

@[reassoc]
theorem domain_mulG : m.domain.ι ≫ mulG H hL = m.mul ≫ ch H none :=
  (exists_mulG H hL).choose_spec

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
