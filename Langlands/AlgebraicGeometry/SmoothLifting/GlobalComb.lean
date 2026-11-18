import Langlands.AlgebraicGeometry.SmoothLifting.SquareZero

/-! # Global affine combinations of lifts along a square-zero thickening

For a square-zero ideal `I` of `C`, the lifts `Spec C ⟶ X` of a fixed `x₀ : Spec (C ⧸ I) ⟶ X`
over `s : Spec C ⟶ S` admit affine combinations `y₀ + ∑ cₖ (yₖ - y₀)`. They are computed in
affine charts (`Chart.comb`) on a finite standard cover of `Spec C` and glued. The result is
characterized by its restriction to every chart, and morphisms over `S` commute with it.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace Langlands.AlgebraicGeometry.SmoothLifting

variable {X S : Scheme.{u}} {f : X ⟶ S} {C : CommRingCat.{u}} {I : Ideal C}
  {x₀ : Spec (CommRingCat.of (C ⧸ I)) ⟶ X} {s : Spec C ⟶ S}

variable (f I x₀ s) in
/-- A lift of `x₀` over `s` defined on all of `Spec C`. -/
def IsGlobalLift (y : Spec C ⟶ X) : Prop :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y = x₀ ∧ y ≫ f = s

/-- Restriction of a morphism on `Spec C` to a `C`-algebra. -/
abbrev restrC (R : Type u) [CommRing R] [Algebra C R] (y : Spec C ⟶ X) :
    Spec (CommRingCat.of R) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap C R)) ≫ y

theorem IsGlobalLift.h₀ {y : Spec C ⟶ X} (hy : IsGlobalLift f I x₀ s y) :
    x₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ s := by
  rw [← hy.1, Category.assoc, hy.2]

theorem IsGlobalLift.isLift {y : Spec C ⟶ X} (hy : IsGlobalLift f I x₀ s y)
    (R : Type u) [CommRing R] [Algebra C R] : IsLift f I x₀ s R (restrC R y) := by
  constructor
  · rw [← Category.assoc, ← Spec.map_comp,
      show CommRingCat.ofHom (algebraMap C R) ≫ redMap I R =
        CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ redStruct I R from strMap_redMap I R,
      Spec.map_comp, Category.assoc, hy.1]
  · rw [Category.assoc, hy.2]
    rfl

theorem restr_restrC {R R' : Type u} [CommRing R] [Algebra C R] [CommRing R'] [Algebra C R']
    (ρ : R →ₐ[C] R') (y : Spec C ⟶ X) : restr ρ (restrC R y) = restrC R' y := by
  rw [restr, restrC, restrC, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  ext r
  exact ρ.commutes r

/-- Morphisms on `Spec R` agreeing on a standard open cover agree. -/
theorem eq_of_restr_away {R : CommRingCat.{u}} {n : ℕ} (r : Fin n → R)
    (hr : Ideal.span (Set.range r) = ⊤) {y y' : Spec R ⟶ X}
    (h : ∀ i, Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r i)))) ≫ y =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r i)))) ≫ y') : y = y' :=
  Scheme.Cover.hom_ext (Scheme.affineOpenCoverOfSpanRangeEqTop r hr).openCover _ _ h

/-- Morphisms on `Spec R` agreeing on the localizations at a family of elements generating
the unit ideal agree. -/
theorem eq_of_restr_away' {R : Type u} [CommRing R] {α : Type*} (r : α → R)
    (hr : Ideal.span (Set.range r) = ⊤) {y y' : Spec (CommRingCat.of R) ⟶ X}
    (h : ∀ a, Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r a)))) ≫ y =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r a)))) ≫ y') : y = y' := by
  classical
  obtain ⟨t, hts, htop⟩ := (Ideal.span_eq_top_iff_finite _).mp hr
  have hpre : ∀ x ∈ t, ∃ a, r a = x := fun x hx => hts hx
  choose aa haa using hpre
  let e := t.equivFin.symm
  have hspan : Ideal.span (Set.range fun i => r (aa (e i) (e i).2)) = ⊤ := by
    refine eq_top_iff.mpr (htop.symm.le.trans (Ideal.span_mono ?_))
    intro x hx
    refine ⟨e.symm ⟨x, hx⟩, (haa _ _).trans ?_⟩
    rw [Equiv.apply_symm_apply]
  exact eq_of_restr_away (R := CommRingCat.of R) (fun i => r (aa (e i) (e i).2)) hspan
    fun i => h _

section Comb

variable {ι : Type} [Fintype ι]

theorem Chart.comb_congr (hI : SqZero I) (ch : Chart f I x₀ s) {R : Type u} [CommRing R]
    [Algebra C R] (hg : IsUnit (algebraMap C R ch.g))
    {y₀ y₀' : Spec (CommRingCat.of R) ⟶ X} (hy₀ : IsLift f I x₀ s R y₀)
    (hy₀' : IsLift f I x₀ s R y₀') (e₀ : y₀ = y₀')
    {y y' : ι → (Spec (CommRingCat.of R) ⟶ X)} (hy : ∀ k, IsLift f I x₀ s R (y k))
    (hy' : ∀ k, IsLift f I x₀ s R (y' k)) (e : y = y') {c c' : ι → R} (ec : c = c') :
    ch.comb R hI hg y₀ hy₀ y hy c = ch.comb R hI hg y₀' hy₀' y' hy' c' := by
  subst e₀ e ec
  rfl

theorem Chart.comb_restr (hI : SqZero I) (ch : Chart f I x₀ s) {R R' : Type u} [CommRing R]
    [Algebra C R] [CommRing R'] [Algebra C R'] (ρ : R →ₐ[C] R')
    (hg : IsUnit (algebraMap C R ch.g)) (hg' : IsUnit (algebraMap C R' ch.g))
    (y₀ : Spec (CommRingCat.of R) ⟶ X) (hy₀ : IsLift f I x₀ s R y₀)
    (y : ι → (Spec (CommRingCat.of R) ⟶ X)) (hy : ∀ k, IsLift f I x₀ s R (y k)) (c : ι → R) :
    restr ρ (ch.comb R hI hg y₀ hy₀ y hy c) =
      ch.comb R' hI hg' (restr ρ y₀) (hy₀.restrict ρ) (fun k => restr ρ (y k))
        (fun k => (hy k).restrict ρ) (fun k => ρ (c k)) := by
  have hc := ch.comb_isLift R hI hg y₀ hy₀ y hy c
  refine ch.eq_of_rep hI hg' (hc.restrict ρ) (ch.comb_isLift R' hI hg' _ _ _ _ _) fun b => ?_
  rw [ch.rep_restr_apply hI ρ hg hg' hc _ b, ch.rep_comb_apply hI hg y₀ hy₀ y hy c hc b,
    ch.rep_comb_apply hI hg' _ _ _ _ _ _ b]
  simp only [map_add, map_sum, map_mul, map_sub]
  congr 1
  · exact (ch.rep_restr_apply hI ρ hg hg' hy₀ _ b).symm
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [ch.rep_restr_apply hI ρ hg hg' (hy k) _ b, ch.rep_restr_apply hI ρ hg hg' hy₀ _ b]

/-- The chart combination of restrictions of global lifts. -/
abbrev Chart.gcombLocal (hI : SqZero I) (ch : Chart f I x₀ s) (R : Type u) [CommRing R]
    [Algebra C R] (hg : IsUnit (algebraMap C R ch.g)) {y₀ : Spec C ⟶ X}
    (hy₀ : IsGlobalLift f I x₀ s y₀) {y : ι → (Spec C ⟶ X)}
    (hy : ∀ k, IsGlobalLift f I x₀ s (y k)) (c : ι → C) : Spec (CommRingCat.of R) ⟶ X :=
  ch.comb R hI hg (restrC R y₀) (hy₀.isLift R) (fun k => restrC R (y k))
    (fun k => (hy k).isLift R) (fun k => algebraMap C R (c k))

theorem Chart.gcombLocal_restr (hI : SqZero I) (ch : Chart f I x₀ s) {R R' : Type u}
    [CommRing R] [Algebra C R] [CommRing R'] [Algebra C R'] (ρ : R →ₐ[C] R')
    (hg : IsUnit (algebraMap C R ch.g)) (hg' : IsUnit (algebraMap C R' ch.g))
    {y₀ : Spec C ⟶ X} (hy₀ : IsGlobalLift f I x₀ s y₀) {y : ι → (Spec C ⟶ X)}
    (hy : ∀ k, IsGlobalLift f I x₀ s (y k)) (c : ι → C) :
    restr ρ (ch.gcombLocal hI R hg hy₀ hy c) = ch.gcombLocal hI R' hg' hy₀ hy c := by
  rw [Chart.gcombLocal, ch.comb_restr hI ρ hg hg']
  exact ch.comb_congr hI hg' _ _ (restr_restrC ρ y₀) _ _
    (funext fun k => restr_restrC ρ (y k)) (funext fun k => ρ.commutes (c k))

theorem Chart.gcombLocal_eq (hI : SqZero I) (ch ch' : Chart f I x₀ s) (R : Type u) [CommRing R]
    [Algebra C R] (hg : IsUnit (algebraMap C R ch.g)) (hg' : IsUnit (algebraMap C R ch'.g))
    {y₀ : Spec C ⟶ X} (hy₀ : IsGlobalLift f I x₀ s y₀) {y : ι → (Spec C ⟶ X)}
    (hy : ∀ k, IsGlobalLift f I x₀ s (y k)) (c : ι → C) :
    ch.gcombLocal hI R hg hy₀ hy c = ch'.gcombLocal hI R hg' hy₀ hy c :=
  ch.comb_eq R hI ch' hg hg' _ _ _ _ _

/-- Existence of the global affine combination, characterized on every chart. -/
theorem exists_gcomb (hI : SqZero I) {y₀ : Spec C ⟶ X} (hy₀ : IsGlobalLift f I x₀ s y₀)
    {y : ι → (Spec C ⟶ X)} (hy : ∀ k, IsGlobalLift f I x₀ s (y k)) (c : ι → C) :
    ∃ z, IsGlobalLift f I x₀ s z ∧ ∀ (ch : Chart f I x₀ s) (R : Type u) [CommRing R]
      [Algebra C R] (hg : IsUnit (algebraMap C R ch.g)),
      restrC R z = ch.gcombLocal hI R hg hy₀ hy c := by
  classical
  obtain ⟨n, chs, hspan⟩ := exists_charts hI hy₀.h₀
  let Y : ∀ i, Spec (CommRingCat.of (Loc (chs i).g)) ⟶ X := fun i =>
    (chs i).gcombLocal hI (Loc (chs i).g) (isUnit_loc _) hy₀ hy c
  have hcompat : ∀ i j, rr (dvd_mul_right (chs i).g (chs j).g) (Y i) =
      rr (dvd_mul_left (chs j).g (chs i).g) (Y j) := by
    intro i j
    dsimp only [Y, rr]
    rw [(chs i).gcombLocal_restr hI _ (isUnit_loc _) (isUnit_loc_of_dvd (dvd_mul_right _ _)),
      (chs j).gcombLocal_restr hI _ (isUnit_loc _) (isUnit_loc_of_dvd (dvd_mul_left _ _))]
    exact (chs i).gcombLocal_eq hI (chs j) _ _ _ hy₀ hy c
  obtain ⟨z, hz⟩ := exists_glue (fun i => (chs i).g) hspan Y hcompat
  have hz' : ∀ i, restrC (Loc (chs i).g) z =
      (chs i).gcombLocal hI (Loc (chs i).g) (isUnit_loc _) hy₀ hy c := hz
  have hzl : IsGlobalLift f I x₀ s z := isLift_of_cover (fun i => (chs i).g) hspan z fun i => by
    rw [hz i]; exact (chs i).comb_isLift _ hI _ _ _ _ _ _
  refine ⟨z, hzl, fun ch R _ _ hg => ?_⟩
  have hspanR : Ideal.span (Set.range fun i => algebraMap C R (chs i).g) = ⊤ := by
    rw [Set.range_comp' (algebraMap C R) (fun i => (chs i).g), ← Ideal.map_span, hspan,
      Ideal.map_top]
  refine eq_of_restr_away (R := CommRingCat.of R) (fun i => algebraMap C R (chs i).g) hspanR
    fun i => ?_
  let T := Localization.Away (algebraMap C R (chs i).g)
  let ρ : R →ₐ[C] T := IsScalarTower.toAlgHom C R T
  have huT : IsUnit (algebraMap C T (chs i).g) := by
    rw [IsScalarTower.algebraMap_apply C R T]
    exact IsLocalization.Away.algebraMap_isUnit _
  have hgT : IsUnit (algebraMap C T ch.g) := isUnit_of_algHom ρ hg
  change restr ρ (restrC R z) = restr ρ (ch.gcombLocal hI R hg hy₀ hy c)
  rw [restr_restrC, ch.gcombLocal_restr hI ρ hg hgT,
    ← restr_restrC (res (chs i).g T huT) z, hz' i,
    (chs i).gcombLocal_restr hI _ (isUnit_loc _) huT]
  exact (chs i).gcombLocal_eq hI ch T huT hgT hy₀ hy c

/-- The global affine combination `y₀ + ∑ cₖ (yₖ - y₀)` of global lifts. -/
def gcomb (hI : SqZero I) {y₀ : Spec C ⟶ X} (hy₀ : IsGlobalLift f I x₀ s y₀)
    {y : ι → (Spec C ⟶ X)} (hy : ∀ k, IsGlobalLift f I x₀ s (y k)) (c : ι → C) :
    Spec C ⟶ X :=
  (exists_gcomb hI hy₀ hy c).choose

theorem gcomb_isGlobalLift (hI : SqZero I) {y₀ : Spec C ⟶ X} (hy₀ : IsGlobalLift f I x₀ s y₀)
    {y : ι → (Spec C ⟶ X)} (hy : ∀ k, IsGlobalLift f I x₀ s (y k)) (c : ι → C) :
    IsGlobalLift f I x₀ s (gcomb hI hy₀ hy c) :=
  (exists_gcomb hI hy₀ hy c).choose_spec.1

theorem gcomb_restr (hI : SqZero I) {y₀ : Spec C ⟶ X} (hy₀ : IsGlobalLift f I x₀ s y₀)
    {y : ι → (Spec C ⟶ X)} (hy : ∀ k, IsGlobalLift f I x₀ s (y k)) (c : ι → C)
    (ch : Chart f I x₀ s) (R : Type u) [CommRing R] [Algebra C R]
    (hg : IsUnit (algebraMap C R ch.g)) :
    restrC R (gcomb hI hy₀ hy c) = ch.gcombLocal hI R hg hy₀ hy c :=
  (exists_gcomb hI hy₀ hy c).choose_spec.2 ch R hg

/-- Two global lifts agreeing on the localizations at the elements of a covering chart family
are equal. -/
theorem IsGlobalLift.ext_of_charts {n : ℕ} (chs : Fin n → Chart f I x₀ s)
    (hspan : Ideal.span (Set.range fun i => (chs i).g) = ⊤) {z z' : Spec C ⟶ X}
    (h : ∀ i, restrC (Loc (chs i).g) z = restrC (Loc (chs i).g) z') : z = z' :=
  eq_of_restr_away (fun i => (chs i).g) hspan h

end Comb

section Functoriality

variable {Y : Scheme.{u}} {fY : Y ⟶ S} (φ : X ⟶ Y) (hφ : φ ≫ fY = f)
include hφ

theorem IsGlobalLift.comp {y : Spec C ⟶ X} (hy : IsGlobalLift f I x₀ s y) :
    IsGlobalLift fY I (x₀ ≫ φ) s (y ≫ φ) :=
  ⟨by rw [← Category.assoc, hy.1], by rw [Category.assoc, hφ, hy.2]⟩

theorem IsLift.comp {R : Type u} [CommRing R] [Algebra C R] {y : Spec (CommRingCat.of R) ⟶ X}
    (hy : IsLift f I x₀ s R y) : IsLift fY I (x₀ ≫ φ) s R (y ≫ φ) :=
  ⟨by rw [← Category.assoc, hy.1, Category.assoc], by rw [Category.assoc, hφ, hy.2]⟩

/-- Chart representatives under a morphism mapping one chart into another. -/
theorem Chart.rep_comp (hI : SqZero I) (chX : Chart f I x₀ s) (chY : Chart fY I (x₀ ≫ φ) s)
    (hU : chX.U ≤ φ ⁻¹ᵁ chY.U) {R : Type u} [CommRing R] [Algebra C R]
    (hg : IsUnit (algebraMap C R chX.g)) (hg' : IsUnit (algebraMap C R chY.g))
    {z : Spec (CommRingCat.of R) ⟶ X} (hz : IsLift f I x₀ s R z) :
    chY.rep R hI hg' (z ≫ φ) (hz.comp φ hφ) = φ.appLE chY.U chX.U hU ≫ chX.rep R hI hg z hz := by
  refine chartRep_eq _ _ _ ?_
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec φ chY.hU chX.hU hU,
    ← Category.assoc, Chart.rep_spec]

/-- Chart combinations commute with a morphism mapping one chart into another. -/
theorem Chart.comb_comp {ι : Type} [Fintype ι] (hI : SqZero I) (chX : Chart f I x₀ s)
    (chY : Chart fY I (x₀ ≫ φ) s) (hU : chX.U ≤ φ ⁻¹ᵁ chY.U) {R : Type u} [CommRing R]
    [Algebra C R] (hg : IsUnit (algebraMap C R chX.g)) (hg' : IsUnit (algebraMap C R chY.g))
    (y₀ : Spec (CommRingCat.of R) ⟶ X) (hy₀ : IsLift f I x₀ s R y₀)
    (y : ι → (Spec (CommRingCat.of R) ⟶ X)) (hy : ∀ k, IsLift f I x₀ s R (y k)) (c : ι → R) :
    chX.comb R hI hg y₀ hy₀ y hy c ≫ φ =
      chY.comb R hI hg' (y₀ ≫ φ) (hy₀.comp φ hφ) (fun k => y k ≫ φ)
        (fun k => (hy k).comp φ hφ) c := by
  have hc := chX.comb_isLift R hI hg y₀ hy₀ y hy c
  refine chY.eq_of_rep hI hg' (hc.comp φ hφ) (chY.comb_isLift R hI hg' _ _ _ _ _) fun b => ?_
  have e : ∀ (z : Spec (CommRingCat.of R) ⟶ X) (hz : IsLift f I x₀ s R z),
      (chY.rep R hI hg' (z ≫ φ) (hz.comp φ hφ)).hom b =
        (chX.rep R hI hg z hz).hom ((φ.appLE chY.U chX.U hU).hom b) := fun z hz => by
    rw [chX.rep_comp φ hφ hI chY hU hg hg' hz]
    rfl
  rw [e _ hc, chY.rep_comb_apply hI hg' _ _ _ _ _ _ b, chX.rep_comb_apply hI hg _ _ _ _ _ hc,
    e _ hy₀]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [e _ (hy k)]

end Functoriality

section Refine

variable {Y : Scheme.{u}} {fY : Y ⟶ S} (φ : X ⟶ Y) (hφ : φ ≫ fY = f)
include hφ

/-- Every point of the domain of a chart of the target lies in the domain of a chart of the
source mapping into it. -/
theorem exists_refined_chart (hI : SqZero I) (chY : Chart fY I (x₀ ≫ φ) s) (q : Spec C)
    (hq : chY.g ∉ q.asIdeal) : ∃ chX : Chart f I x₀ s, chX.U ≤ φ ⁻¹ᵁ chY.U ∧ chX.g ∉ q.asIdeal := by
  obtain ⟨p, rfl⟩ := specMap_surjective (CommRingCat.ofHom (Ideal.Quotient.mk I))
    Ideal.Quotient.mk_surjective
    (by rw [CommRingCat.hom_ofHom, Ideal.mk_ker]; exact hI.le_nilradical) q
  have hpY : (x₀ ≫ φ) p ∈ chY.U := chY.hx p hq
  rw [Scheme.Hom.comp_apply] at hpY
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUφ⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x₀ p ∈ ((φ ⁻¹ᵁ chY.U : X.Opens) : Set X) from hpY) (φ ⁻¹ᵁ chY.U).2
  obtain ⟨_, ⟨_, ⟨d, rfl⟩, rfl⟩, hp₂, hsub₂⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU (x₀ ⁻¹ᵁ U).2
  obtain ⟨g₂, rfl⟩ := Ideal.Quotient.mk_surjective d
  let chX : Chart f I x₀ s :=
    { V := chY.V
      hV := chY.hV
      U := U
      hU := hU
      hUV := fun x hx => by
        show f x ∈ chY.V
        rw [← hφ, Scheme.Hom.comp_apply]
        exact chY.hUV (hUφ hx)
      g := chY.g * g₂
      hs := fun p' hp' => chY.hs p' fun h => hp' (p'.asIdeal.mul_mem_right _ h)
      hx := fun p' hp' => hsub₂ fun h => hp' (by
        rw [map_mul]; exact p'.asIdeal.mul_mem_left _ h) }
  refine ⟨chX, fun x hx => hUφ hx, fun h => ?_⟩
  rcases Ideal.IsPrime.mem_or_mem (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) p).2 h with
    h | h
  · exact hq h
  · exact hp₂ h

/-- **Functoriality of global affine combinations** under morphisms over `S`. -/
theorem gcomb_comp {ι : Type} [Fintype ι] (hI : SqZero I) {y₀ : Spec C ⟶ X}
    (hy₀ : IsGlobalLift f I x₀ s y₀) {y : ι → (Spec C ⟶ X)}
    (hy : ∀ k, IsGlobalLift f I x₀ s (y k)) (c : ι → C) :
    gcomb hI hy₀ hy c ≫ φ = gcomb hI (hy₀.comp φ hφ) (fun k => (hy k).comp φ hφ) c := by
  classical
  have hY₀ := hy₀.comp φ hφ
  obtain ⟨n, chsY, hspanY⟩ := exists_charts hI hY₀.h₀
  refine IsGlobalLift.ext_of_charts chsY hspanY fun i => ?_
  rw [gcomb_restr hI hY₀ _ c (chsY i) _ (isUnit_loc _)]
  let R := Loc (chsY i).g
  let α := {q : Spec C // (chsY i).g ∉ q.asIdeal}
  have hex : ∀ a : α, ∃ chX : Chart f I x₀ s, chX.U ≤ φ ⁻¹ᵁ (chsY i).U ∧ chX.g ∉ a.1.asIdeal :=
    fun a => exists_refined_chart φ hφ hI (chsY i) a.1 a.2
  choose chX hchU hchg using hex
  have hspanR : Ideal.span (Set.range fun a => algebraMap C R (chX a).g) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let q : Spec C := PrimeSpectrum.comap (algebraMap C R) ⟨m, hm.isPrime⟩
    have hq : (chsY i).g ∉ q.asIdeal := fun h =>
      hm.ne_top (Ideal.eq_top_of_isUnit_mem _ h (isUnit_loc _))
    exact hchg ⟨q, hq⟩ (hle (Ideal.subset_span ⟨⟨q, hq⟩, rfl⟩))
  refine eq_of_restr_away' (R := R) (fun a => algebraMap C R (chX a).g) hspanR fun a => ?_
  let T := Localization.Away (algebraMap C R (chX a).g)
  let ρ : R →ₐ[C] T := IsScalarTower.toAlgHom C R T
  have huT : IsUnit (algebraMap C T (chX a).g) := by
    rw [IsScalarTower.algebraMap_apply C R T]
    exact IsLocalization.Away.algebraMap_isUnit _
  have hgT : IsUnit (algebraMap C T (chsY i).g) := isUnit_of_algHom ρ (isUnit_loc _)
  change restr ρ (restrC R (gcomb hI hy₀ hy c) ≫ φ) =
    restr ρ ((chsY i).gcombLocal hI R (isUnit_loc _) hY₀ (fun k => (hy k).comp φ hφ) c)
  rw [(chsY i).gcombLocal_restr hI ρ (isUnit_loc _) hgT, restr, ← Category.assoc,
    show Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ restrC R (gcomb hI hy₀ hy c) =
      restrC T (gcomb hI hy₀ hy c) from restr_restrC ρ _,
    gcomb_restr hI hy₀ hy c (chX a) T huT, Chart.gcombLocal,
    (chX a).comb_comp φ hφ hI (chsY i) (hchU a) huT hgT]
  exact (chsY i).comb_congr hI hgT _ _ (Category.assoc _ _ _) _ _
    (funext fun k => Category.assoc _ _ _) rfl

end Refine

end Langlands.AlgebraicGeometry.SmoothLifting
