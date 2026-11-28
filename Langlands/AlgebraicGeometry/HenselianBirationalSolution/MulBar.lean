import Langlands.AlgebraicGeometry.HenselianBirationalSolution.ChartCover
import Langlands.AlgebraicGeometry.HenselianBirationalSolution.RightSection

/-! # Multiplication on the glued scheme

On a pair of section charts, one can rewrite `(a x)(d y)` as `(a (x d)) y` where
right translation by `d` followed by the translation of chart `a` is defined.
The chart cover and section lifting allow `d` to be chosen locally. The expression
uses the already extended multiplication `Y ×_S Y ⟶ G`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {m : BirationalGroupLaw g}
  [IsReduced Y] [Smooth g] [IsSeparated g] [IsNoetherian Y] [Surjective g]
  [QuasiCompact g] (H : GlueHyp m)

instance : IsReduced (Gl H) := by
  let cover := (Glue.core H (secTrans H)).glueData.openCover
  let : ∀ i : cover.I₀, IsReduced (cover.X i) := fun _ => by
    change IsReduced Y
    infer_instance
  exact IsReduced.of_openCover _ cover

theorem smooth_toS : Smooth (toS H) := Glue.instSmoothToBase H (secTrans H)

abbrev GG : Scheme.{u} := pullback (toS H) (toS H)

instance : IsReduced (GG H) := by
  have : Smooth (toS H) := smooth_toS H
  exact SmoothReducedBase.isReduced_of_smooth_of_isReduced (pullback.fst (toS H) (toS H))

abbrev chartPair (i j : Option (Sect g)) : pullback g g ⟶ GG H :=
  pullback.map g g (toS H) (toS H) (ch H i) (ch H j) (𝟙 S)
    (by rw [ch_toS, Category.comp_id]) (by rw [ch_toS, Category.comp_id])

instance (i j : Option (Sect g)) : IsOpenImmersion (chartPair H i j) := by
  unfold chartPair
  infer_instance

theorem lift_chartPair {T : Scheme.{u}} (i j : Option (Sect g)) (x y : T ⟶ Y)
    (h : x ≫ g = y ≫ g) :
    pullback.lift x y h ≫ chartPair H i j =
      pullback.lift (x ≫ ch H i) (y ≫ ch H j) (by simpa only [Category.assoc, ch_toS] using h) := by
  apply pullback.hom_ext <;> simp

theorem genericPoints_range_ch : genericPoints (Gl H) ⊆ Set.range (ch H none) := by
  intro p hp
  obtain ⟨i, x, rfl⟩ := Glue.exists_chart H (secTrans H) p
  have hx : x ∈ genericPoints Y := by
    rw [mem_genericPoints_iff_scheme] at hp ⊢
    intro y hy
    exact (ch H i).isOpenEmbedding.injective (hp _ (hy.map (ch H i).continuous))
  have hdom := FibreGenerizationDense.genericPoints_subset (secTrans H i).dom_dense hx
  let a : (secTrans H i).dom.toScheme := ⟨x, hdom⟩
  refine ⟨(secTrans H i).map a, ?_⟩
  have h := dom_chart H i (𝟙 _)
  simp only [Category.id_comp] at h
  rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
  rfl

theorem genericPoints_range_chartPair : genericPoints (GG H) ⊆ Set.range (chartPair H none none) := by
  have : Smooth (toS H) := smooth_toS H
  intro p hp
  rw [chartPair, Scheme.Pullback.range_map]
  exact ⟨genericPoints_range_ch H (mapsTo_genericPoints _ (generalizingMap_of_flat _) hp),
    genericPoints_range_ch H (mapsTo_genericPoints _ (generalizingMap_of_flat _) hp)⟩

abbrev mulOpen : (GG H).Opens := chartPair H none none ''ᵁ m.domain

abbrev mulOnOpen : (mulOpen H).toScheme ⟶ Gl H :=
  ((chartPair H none none).isoImage m.domain).inv ≫ m.mul ≫ ch H none

theorem genericPoints_mulOpen : genericPoints (GG H) ⊆ mulOpen H := by
  intro p hp
  obtain ⟨q, rfl⟩ := genericPoints_range_chartPair H hp
  have hq : q ∈ genericPoints ↥(pullback g g) := by
    rw [mem_genericPoints_iff_scheme] at hp ⊢
    intro q' hq'
    exact (chartPair H none none).isOpenEmbedding.injective
      (hp _ (hq'.map (chartPair H none none).continuous))
  exact ⟨q, FibreGenerizationDense.genericPoints_subset H.strict.domain_fst hq, rfl⟩

namespace MulBarPiece

variable (i : Option (Sect g)) (d : Sect g)

/-- The open for `x` on which `τᵢ (x d)` is defined. -/
abbrev A : ((rightDom m d).toScheme).Opens := rightMap m d ⁻¹ᵁ (secTrans H i).dom

abbrev incl : (A H i d).toScheme ⟶ Y := (A H i d).ι ≫ (rightDom m d).ι

abbrev F : (A H i d).toScheme ⟶ Y :=
  (rightMap m d ∣_ (secTrans H i).dom) ≫ (secTrans H i).map

omit [IsReduced Y] [Smooth g] [IsSeparated g] [AlgebraicGeometry.IsNoetherian Y]
  [Surjective g] [QuasiCompact g] in
@[reassoc]
theorem F_comp : F H i d ≫ g = incl H i d ≫ g := by
  rw [F, Category.assoc, (secTrans H i).map_comp, morphismRestrict_ι_assoc, rightMap_comp m d]
  rfl

abbrev Q : Scheme.{u} := pullback (incl H i d ≫ g) g

abbrev e : Q H i d ⟶ GG H :=
  pullback.map (incl H i d ≫ g) g (toS H) (toS H) (incl H i d ≫ ch H i) (ch H (some d)) (𝟙 S)
    (by simp only [Category.comp_id, Category.assoc, ch_toS]) (by rw [Category.comp_id, ch_toS])

instance : IsOpenImmersion (e H i d) := by
  unfold e
  infer_instance

abbrev k : Q H i d ⟶ pullback g g :=
  pullback.map (incl H i d ≫ g) g g g (F H i d) (𝟙 Y) (𝟙 S)
    (by rw [Category.comp_id, F_comp]) (by simp)

instance : IsOpenImmersion (k H i d) := by
  unfold k
  infer_instance

variable [S.IsSeparated] (hL : HasSectionLifts g)

abbrev φ : Q H i d ⟶ Gl H := k H i d ≫ mulG H hL

/-- The additional conditions for comparing the formula to the original law. -/
abbrev W : (Q H i d).Opens :=
  (pullback.fst (incl H i d ≫ g) g ≫ incl H i d) ⁻¹ᵁ
      ((secTrans H i).dom.ι ''ᵁ ((secTrans H i).map ⁻¹ᵁ rightDom m d)) ⊓
    pullback.snd (incl H i d ≫ g) g ⁻¹ᵁ (secTrans H (some d)).dom ⊓ k H i d ⁻¹ᵁ m.domain

omit [IsReduced Y] [IsSeparated g] [AlgebraicGeometry.IsNoetherian Y]
  [Surjective g] [QuasiCompact g] [S.IsSeparated] in
theorem genericPoints_W : genericPoints (Q H i d) ⊆ W H i d := by
  intro q hq
  have hx : incl H i d (pullback.fst (incl H i d ≫ g) g q) ∈ genericPoints Y :=
    mapsTo_genericPoints _ (generalizingMap_of_isOpenImmersion (incl H i d))
      (mapsTo_genericPoints _ (generalizingMap_of_flat (pullback.fst (incl H i d ≫ g) g)) hq)
  have hy : pullback.snd (incl H i d ≫ g) g q ∈ genericPoints Y :=
    mapsTo_genericPoints _ (generalizingMap_of_flat (pullback.snd (incl H i d ≫ g) g)) hq
  let x : (secTrans H i).dom.toScheme := ⟨_,
    FibreGenerizationDense.genericPoints_subset (secTrans H i).dom_dense hx⟩
  have hx' : x ∈ genericPoints (secTrans H i).dom.toScheme := by
    rw [mem_genericPoints_iff_scheme] at hx ⊢
    intro z hz
    exact (secTrans H i).dom.ι.isOpenEmbedding.injective (hx _ (hz.map (secTrans H i).dom.ι.continuous))
  exact ⟨⟨⟨x, FibreGenerizationDense.genericPoints_subset (rightDom_dense m d H.strict)
      (mapsTo_genericPoints _ (generalizingMap_of_isOpenImmersion (secTrans H i).map) hx'), rfl⟩,
    FibreGenerizationDense.genericPoints_subset (secTrans H (some d)).dom_dense hy⟩,
    FibreGenerizationDense.genericPoints_subset H.strict.domain_fst
      (mapsTo_genericPoints _ (generalizingMap_of_isOpenImmersion (k H i d)) hq)⟩

/-- The local formula agrees with multiplication in the identity chart. -/
theorem agree {T : Scheme.{u}} (u : T ⟶ (W H i d).toScheme) (v : T ⟶ (mulOpen H).toScheme)
    (h : u ≫ (W H i d).ι ≫ e H i d = v ≫ (mulOpen H).ι) :
    u ≫ (W H i d).ι ≫ φ H i d hL = v ≫ mulOnOpen H := by
  let τ := secTrans H i
  let τd := secTrans H (some d)
  let r := u ≫ (W H i d).ι
  let a := r ≫ pullback.fst (incl H i d ≫ g) g
  let x := a ≫ incl H i d
  let y := r ≫ pullback.snd (incl H i d ≫ g) g
  have hxy : x ≫ g = y ≫ g := by
    calc x ≫ g = r ≫ (pullback.fst (incl H i d ≫ g) g ≫ (incl H i d ≫ g)) := by
          simp only [x, a, Category.assoc]
      _ = y ≫ g := by rw [pullback.condition, ← Category.assoc]
  set c := x ≫ g ≫ d.1
  have hxc : x ≫ g = c ≫ g := (section_comp_g d.1 d.2 x).symm
  have hcy : c ≫ g = y ≫ g := hxc.symm.trans hxy
  have hx : ∀ t : T, ∃ z : τ.dom.toScheme, τ.map z ∈ rightDom m d ∧ τ.dom.ι z = x t := by
    intro t
    have ht := (u t).2.1.1
    change ∃ z : τ.dom.toScheme, τ.map z ∈ rightDom m d ∧
      τ.dom.ι z = (pullback.fst (incl H i d ≫ g) g ≫ incl H i d) ((W H i d).ι (u t)) at ht
    simpa only [x, a, r, Category.assoc, Scheme.Hom.comp_apply] using ht
  have hxR : Set.range x ⊆ Set.range τ.dom.ι := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨z, _, hz⟩ := hx t
    exact ⟨z, hz⟩
  let xD := IsOpenImmersion.lift τ.dom.ι x hxR
  have hxD : xD ≫ τ.dom.ι = x := IsOpenImmersion.lift_fac _ _ _
  have hyR : Set.range y ⊆ Set.range τd.dom.ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (u t).2.1.2
  let yD := IsOpenImmersion.lift τd.dom.ι y hyR
  have hyD : yD ≫ τd.dom.ι = y := IsOpenImmersion.lift_fac _ _ _
  set xt := xD ≫ τ.map with xt_def
  set yt := yD ≫ τd.map with yt_def
  have hxt : xt ≫ g = x ≫ g := by rw [xt_def, Category.assoc, τ.map_comp, ← Category.assoc, hxD]
  have hyt : yt ≫ g = y ≫ g := by rw [yt_def, Category.assoc, τd.map_comp, ← Category.assoc, hyD]
  have hxtc : xt ≫ g = c ≫ g := hxt.trans hxc
  have hxty : xt ≫ g = yt ≫ g := hxt.trans (hxy.trans hyt.symm)
  have hxtR : Set.range xt ⊆ Set.range (rightDom m d).ι := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hx t
    have hzxD : z = xD t := τ.dom.ι.isOpenEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, hxD, hzx])
    rw [Scheme.Opens.range_ι, xt_def, Scheme.Hom.comp_apply, ← hzxD]
    exact hz
  let xtD := IsOpenImmersion.lift (rightDom m d).ι xt hxtR
  have hxtD : xtD ≫ (rightDom m d).ι = xt := IsOpenImmersion.lift_fac _ _ _
  have hdx : m.Defined x c hxc := rightDom_defined m d (a ≫ (A H i d).ι) |>.of_eq
    (by simp only [x, incl, Category.assoc]) (by simp only [c, x, incl, Category.assoc])
  have hdxt : m.Defined xt c hxtc := (rightDom_defined m d xtD).of_eq hxtD (by
    rw [hxtD, ← Category.assoc, hxt, Category.assoc])
  have hc : (yD ≫ τd.dom.ι) ≫ g ≫ d.1 = c := by
    rw [hyD, ← Category.assoc, ← hxy, Category.assoc]
  have hdy : m.Defined c y hcy := (secTrans_defined H d yD).of_eq hc hyD
  have hyt_eq : yt = m.mulPt c y hcy hdy := by
    rw [yt_def, secTrans_map_eq H d yD]
    exact m.mulPt_congr hc hyD
  set b := a ≫ (rightMap m d ∣_ τ.dom) with b_def
  have hb : b ≫ τ.dom.ι = m.mulPt x c hxc hdx := by
    rw [b_def, Category.assoc, morphismRestrict_ι, ← Category.assoc, rightMap_eq]
    exact m.mulPt_congr rfl rfl
  have hF : a ≫ F H i d = m.mulPt xt c hxtc hdxt := by
    change b ≫ τ.map = _
    have hd : m.Defined (xD ≫ τ.dom.ι) c (by rw [hxD]; exact hxc) := hdx.of_eq hxD.symm rfl
    exact τ.equivariant xD b c _ hd (hb.trans (m.mulPt_congr hxD.symm rfl)) _ hdxt
  have hk : r ≫ k H i d = pullback.lift (a ≫ F H i d) y (by
      rw [Category.assoc, F_comp, ← Category.assoc]; exact hxy) := by
    apply pullback.hom_ext
    · simp only [k, Category.assoc, pullback.lift_fst, a]
    · simp only [k, Category.assoc, pullback.lift_snd, Category.comp_id, y]
  have hleft : m.mulPt xt c hxtc hdxt ≫ g = y ≫ g := by
    rw [m.mulPt_comp_g]
    exact hxt.trans hxy
  have hdl : m.Defined (m.mulPt xt c hxtc hdxt) y hleft := by
    have hl : m.Defined (a ≫ F H i d) y (by rw [Category.assoc, F_comp, ← Category.assoc]; exact hxy) := by
      rintro _ ⟨t, rfl⟩
      rw [← hk, Scheme.Hom.comp_apply]
      exact (u t).2.2
    exact hl.of_eq hF rfl
  set v' := v ≫ ((chartPair H none none).isoImage m.domain).inv with v_def
  have hv' : v' ≫ m.domain.ι = pullback.lift xt yt hxty := by
    rw [← cancel_mono (chartPair H none none), lift_chartPair H]
    have he : v' ≫ m.domain.ι ≫ chartPair H none none = r ≫ e H i d := by
      rw [v_def, Category.assoc, Scheme.Hom.isoImage_inv_ι]
      simpa only [r, Category.assoc] using h.symm
    rw [Category.assoc, he]
    apply pullback.hom_ext
    · simp only [e, Category.assoc, pullback.lift_fst]
      change x ≫ ch H i = xt ≫ ch H none
      rw [← hxD, dom_chart H i xD]
    · simp only [e, Category.assoc, pullback.lift_snd]
      change y ≫ ch H (some d) = yt ≫ ch H none
      rw [← hyD, dom_chart H (some d) yD]
  have hdr : m.Defined xt (m.mulPt c y hcy hdy) (by simp [hxtc]) :=
    (m.pairIn_domain_of_eq v' hv'.symm).of_eq rfl hyt_eq
  have hvMul : v' ≫ m.mul = m.mulPt xt (m.mulPt c y hcy hdy) (by simp [hxtc]) hdr := by
    rw [BirationalGroupLaw.mulPt]
    congr 1
    apply m.liftDom_eq
    · rw [← Category.assoc, hv', pullback.lift_fst]
    · rw [← Category.assoc, hv', pullback.lift_snd, hyt_eq]
  change u ≫ (W H i d).ι ≫ k H i d ≫ mulG H hL =
    v ≫ ((chartPair H none none).isoImage m.domain).inv ≫ m.mul ≫ ch H none
  have hk' : r ≫ k H i d = pullback.lift (m.mulPt xt c hxtc hdxt) y hleft :=
    hk.trans (lift_congr hF rfl)
  rw [← Category.assoc u, ← Category.assoc r, hk', lift_mulG H hL _ _ _ hdl,
    m.mulPt_assoc xt c y hxtc hcy hdxt hdy hdl hdr]
  simpa only [v', Category.assoc] using congrArg (· ≫ ch H none) hvMul.symm

omit [IsReduced Y] [Smooth g] [IsSeparated g] [AlgebraicGeometry.IsNoetherian Y]
  [Surjective g] [QuasiCompact g] [S.IsSeparated] in
theorem secLift_pairFst {P : Scheme.{u}} (q : P ⟶ S) (x : P ⟶ Y) (hx : x ≫ g = q) (d : Sect g) :
    secLift q d ≫ pairFst x hx = x ≫ sectionPairRight d.1 d.2 := by
  apply pullback.hom_ext
  · simp
  · simp [← hx]

include hL in
/-- The locally defined multiplication pieces cover `G ×_S G`. -/
theorem cover (p₀ : ↥(GG H)) : ∃ i d, p₀ ∈ Set.range (e H i d) := by
  obtain ⟨i, _, hi⟩ := Glue.exists_chart H (secTrans H) (pullback.fst (toS H) (toS H) p₀)
  obtain ⟨j, _, hj⟩ := Glue.exists_chart H (secTrans H) (pullback.snd (toS H) (toS H) p₀)
  have he : p₀ ∈ Set.range (chartPair H i j) := by
    rw [chartPair, Scheme.Pullback.range_map]
    exact ⟨⟨_, hi⟩, ⟨_, hj⟩⟩
  obtain ⟨p, rfl⟩ := he
  let x := pullback.fst g g
  let y := pullback.snd g g
  let q := x ≫ g
  obtain ⟨Z, jm, hjm, hdense, hchart⟩ := chartCover H hL j q y pullback.condition.symm
  let B : Set ↥(pullback g q) :=
    pairFst x rfl ⁻¹' leftPre m (pullback.snd g g ⁻¹' ((secTrans H i).dom : Set Y))
  have hBopen : IsOpen B :=
    (isOpen_leftPre m ((secTrans H i).dom.isOpen.preimage (pullback.snd g g).continuous)).preimage
      (pairFst x rfl).continuous
  have hBdense : FibreGenerizationDense (pullback.snd g q) B :=
    fibreGenerizationDense_pairFst x rfl (fibreGenerizationDense_leftPre m H.strict.domain_fst
      (fibreGenerizationDense_snd_preimage (secTrans H i).dom_dense))
  obtain ⟨d, hd, hdB⟩ := hL _ q (Set.range jm ∩ B)
    (jm.isOpenEmbedding.isOpen_range.inter hBopen)
    (FibreGenerizationDense.inter hdense hBdense jm.isOpenEmbedding.isOpen_range) p
  let O := secLift q d ⁻¹ᵁ jm.opensRange
  have hO : Set.range (O.ι ≫ secLift q d) ⊆ Set.range jm := by
    rintro _ ⟨t, rfl⟩
    exact t.2
  have hy := hchart d O (IsOpenImmersion.lift jm _ hO) (IsOpenImmersion.lift_fac _ _ _)
    (show O.toScheme from ⟨p, hd⟩)
  change pairFst x rfl (secLift q d p) ∈ leftPre m
    (pullback.snd g g ⁻¹' ((secTrans H i).dom : Set Y)) at hdB
  rw [← Scheme.Hom.comp_apply, secLift_pairFst q x rfl, Scheme.Hom.comp_apply] at hdB
  obtain ⟨w, hw, hwx⟩ := hdB
  have hx : x p ∈ rightDom m d := by
    change sectionPairRight d.1 d.2 (x p) ∈ m.domain
    rw [← hwx]
    exact w.2
  let a : (rightDom m d).toScheme := ⟨x p, hx⟩
  have ha : (sectionPairRight d.1 d.2 ∣_ m.domain) a = w := by
    apply m.domain.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hwx]
    rfl
  have hA : a ∈ A H i d := by
    change rightMap m d a ∈ (secTrans H i).dom
    rw [rightMap, Scheme.Hom.comp_apply, ha]
    change pullback.snd g g (leftT m w) ∈ (secTrans H i).dom at hw
    rwa [← Scheme.Hom.comp_apply, m.leftT_snd] at hw
  refine ⟨i, d, ?_⟩
  rw [e, Scheme.Pullback.range_map]
  constructor
  · rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, chartPair, pullback.lift_fst, Scheme.Hom.comp_apply]
    refine ⟨(show (A H i d).toScheme from ⟨a, hA⟩), ?_⟩
    rfl
  · rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, chartPair, pullback.lift_snd, Scheme.Hom.comp_apply]
    exact hy

end MulBarPiece

variable [S.IsSeparated] (hL : HasSectionLifts g)

include hL in
theorem exists_mulBar : ∃ μ : GG H ⟶ Gl H, (mulOpen H).ι ≫ μ = mulOnOpen H :=
  exists_extension_of_pieces (mulOpen H) (dense_of_genericPoints_subset (genericPoints_mulOpen H))
    (mulOnOpen H) fun p => by
      obtain ⟨i, d, hp⟩ := MulBarPiece.cover H hL p
      exact ⟨MulBarPiece.Q H i d, MulBarPiece.e H i d, inferInstance,
        MulBarPiece.φ H i d hL, MulBarPiece.W H i d, hp, MulBarPiece.genericPoints_W H i d,
        fun _ u v h => MulBarPiece.agree H i d hL u v h⟩

/-- The multiplication of the glued scheme. -/
def mulBar : GG H ⟶ Gl H := (exists_mulBar H hL).choose

@[reassoc]
theorem mulOpen_mulBar : (mulOpen H).ι ≫ mulBar H hL = mulOnOpen H :=
  (exists_mulBar H hL).choose_spec

@[reassoc]
theorem domain_chartPair_mulBar :
    m.domain.ι ≫ chartPair H none none ≫ mulBar H hL = m.mul ≫ ch H none := by
  rw [← Scheme.Hom.isoImage_hom_ι_assoc (chartPair H none none) m.domain, mulOpen_mulBar, mulOnOpen,
    Iso.hom_inv_id_assoc]

@[reassoc]
theorem mulBar_toS : mulBar H hL ≫ toS H = pullback.fst (toS H) (toS H) ≫ toS H := by
  apply ext_of_genericPoints_subset (mulOpen H) (genericPoints_mulOpen H)
  rw [← cancel_epi ((chartPair H none none).isoImage m.domain).hom]
  simp only [← Category.assoc ((chartPair H none none).isoImage m.domain).hom,
    Scheme.Hom.isoImage_hom_ι, Category.assoc, domain_chartPair_mulBar_assoc,
    ch_toS, chartPair, pullback.lift_fst_assoc, m.mul_comp]

@[reassoc]
theorem chartPair_mulBar : chartPair H none none ≫ mulBar H hL = mulG H hL := by
  apply ext_of_genericPoints_subset m.domain
    (FibreGenerizationDense.genericPoints_subset H.strict.domain_fst)
  rw [domain_chartPair_mulBar, domain_mulG]

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
