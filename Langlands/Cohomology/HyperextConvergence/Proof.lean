import Langlands.Cohomology.HyperextConvergence.Statement
import Langlands.Cohomology.HyperextSecondPage

/-!
# Convergence of the hyperext spectral sequence for bounded objects: proof

This module proves `HyperextConvergenceStatements` of
`Langlands.Cohomology.HyperextConvergence.Statement` (`hyperextConvergenceStatements_proof`).
Let `X` be the hyperext spectral object of `K` and `B`, with `K` in degrees `≥ a` and `≤ b`.

* `eAddEquiv` identifies, for any spectral object in abelian groups, the term
  `E^n(i ⟶ j ⟶ k ⟶ l)` with the quotient of the image of `H^n(i ⟶ k) ⟶ H^n(i ⟶ l)` by the
  image of `H^n(i ⟶ j) ⟶ H^n(i ⟶ l)`.
* Page `r` vanishes outside the rows `-b ≤ q ≤ -a` (`isZero_page_X_of_lt`,
  `isZero_page_X_of_gt`), so all differentials vanish once `r ≥ b - a + 2`
  (`hyperextPageDegeneration`).
* In the rows `-b ≤ q ≤ -a`, the object in position `(p, q)` of page `r ≥ b - a + 2` is
  isomorphic to `E^{p+q}(⊥ ⟶ q ⟶ q + 1 ⟶ ⊤)`, and the two images given by `eAddEquiv` are
  `F^p` and `F^{p+1}` (`mem_filtration_iff_exists`, `stablePageIsoOfMem`); outside these rows
  both sides vanish (`hyperextStablePage`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Pretriangulated.Opposite CategoryTheory.Triangulated Opposite
  ComposableArrows

namespace Langlands.Cohomology

namespace HyperextConvergence

universe v u

section Abstract

variable {ι : Type*} [Category ι] (X : Abelian.SpectralObject AddCommGrpCat.{v} ι)
  {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l) (fik : i ⟶ k) (hik : f₁ ≫ f₂ = fik)
  (fil : i ⟶ l) (hil : fik ≫ f₃ = fil) (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)

/-- The term `E^{n₁}(f₁, f₂, f₃)` of a spectral object in abelian groups is the quotient
`A / B`, where `A` and `B` are the images in `H^{n₁}(i ⟶ l)` of `H^{n₁}(i ⟶ k)` and of
`H^{n₁}(i ⟶ j)`. -/
def eAddEquiv (A B : AddSubgroup ((X.H n₁).obj (mk₁ fil)))
    (hA : ∀ y, y ∈ A ↔ ∃ x, (X.H n₁).map (twoδ₂Toδ₁ fik f₃ fil hil) x = y)
    (hB : ∀ y, y ∈ B ↔ ∃ x, (X.H n₁).map
      (twoδ₂Toδ₁ f₁ (f₂ ≫ f₃) fil (by rw [← hil, ← hik, Category.assoc])) x = y) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≃+ (A ⧸ B.addSubgroupOf A) := by
  let S := X.cokernelSequenceE f₁ f₂ f₃ fik hik n₀ n₁ n₂ hn₁ hn₂
  have hS : S.Exact := X.cokernelSequenceE_exact f₁ f₂ f₃ fik hik n₀ n₁ n₂ hn₁ hn₂
  have hg : Function.Surjective S.g.hom :=
    (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
  let hkMor : S.X₂ ⟶ (X.H n₁).obj (mk₁ fil) := (X.H n₁).map (twoδ₂Toδ₁ fik f₃ fil hil)
  let hjMor : (X.H n₁).obj (mk₁ f₁) ⟶ (X.H n₁).obj (mk₁ fil) := (X.H n₁).map
      (twoδ₂Toδ₁ f₁ (f₂ ≫ f₃) fil (by rw [← hil, ← hik, Category.assoc]))
  let uMor : (X.H n₁).obj (mk₁ f₁) ⟶ S.X₂ := (X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ fik hik)
  let δMor : (X.H n₀).obj (mk₁ f₃) ⟶ S.X₂ := X.δ fik f₃ n₀ n₁ hn₁
  have hcomp : uMor ≫ hkMor = hjMor := by
    change (X.H n₁).map _ ≫ (X.H n₁).map _ = (X.H n₁).map _
    rw [← Functor.map_comp]
    congr 1
    ext <;> simp
  have hδk : δMor ≫ hkMor = 0 := X.zero₁ fik f₃ fil hil n₀ n₁ hn₁
  have hinl : (biprod.inl : _ ⟶ S.X₁) ≫ S.f = uMor := biprod.inl_desc _ _
  have hinr : (biprod.inr : _ ⟶ S.X₁) ≫ S.f = δMor := biprod.inr_desc _ _
  have hfk : S.f ≫ hkMor = biprod.fst ≫ hjMor := by
    apply biprod.hom_ext'
    · exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ hkMor) hinl).trans hcomp)).trans
        (biprod.inl_fst_assoc _).symm
    · exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ hkMor) hinr).trans hδk)).trans
        ((biprod.inr_fst_assoc _).trans (zero_comp)).symm
  let hk := hkMor.hom
  let u := uMor.hom
  have hku : ∀ y, hk (u y) = hjMor.hom y := fun y => congrArg (fun φ => φ.hom y) hcomp
  let ψ : S.X₂ →+ A ⧸ B.addSubgroupOf A :=
    (QuotientAddGroup.mk' _).comp (hk.codRestrict A (fun x => (hA _).2 ⟨x, rfl⟩))
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk'_surjective _ z
    obtain ⟨x, rfl⟩ := (hA y).1 hy
    exact ⟨x, rfl⟩
  have hker : S.g.hom.ker = ψ.ker := by
    rw [← hS.ab_range_eq_ker]
    ext x
    rw [AddMonoidHom.mem_ker]
    change _ ↔ QuotientAddGroup.mk (s := B.addSubgroupOf A) ⟨hk x, _⟩ = 0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    change _ ↔ hk x ∈ B
    constructor
    · rintro ⟨z, rfl⟩
      refine (hB _).2 ⟨(biprod.fst : S.X₁ ⟶ _).hom z, ?_⟩
      exact (congrArg (fun φ => φ.hom z) hfk).symm
    · intro hx
      obtain ⟨y, hy⟩ := (hB _).1 hx
      have h0 : hk (x - u y) = 0 := by rw [map_sub, hku, hy, sub_self]
      have h0' : x - u y ∈ (X.sc₁ fik f₃ fil hil n₀ n₁ hn₁).g.hom.ker := h0
      rw [← (X.exact₁ fik f₃ fil hil n₀ n₁ hn₁).ab_range_eq_ker] at h0'
      obtain ⟨w, hw⟩ : ∃ w : (X.H n₀).obj (mk₁ f₃), δMor.hom w = x - u y := h0'
      refine ⟨(biprod.inl : _ ⟶ S.X₁).hom y + (biprod.inr : _ ⟶ S.X₁).hom w, ?_⟩
      have h1 : S.f.hom ((biprod.inl : _ ⟶ S.X₁).hom y) = u y :=
        congrArg (fun φ => φ.hom y) hinl
      have h2 : S.f.hom ((biprod.inr : _ ⟶ S.X₁).hom w) = x - u y :=
        (congrArg (fun φ => φ.hom w) hinr).trans hw
      exact (S.f.hom.map_add _ _).trans (by rw [h1, h2, add_sub_cancel])
  exact (QuotientAddGroup.quotientKerEquivOfSurjective _ hg).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective _ hψ))

end Abstract

section Concrete

open HyperextSpectralSequence HyperextAbutment Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- A term of the hyperext spectral object vanishes when the corresponding truncation of
`op K` vanishes. -/
lemma isZero_H_of_isZero (t : TStructure C) (K B : C) (n : ℤ) (D : ComposableArrows EInt 1)
    (h : IsZero (((opTStructure t).ω₁.obj D).obj (op K))) :
    IsZero (((hyperextSpectralObject t K B).H n).obj D) :=
  Functor.map_isZero ((preadditiveYoneda.obj B).shift n) h

/-- If `K` lies in degrees `≤ b`, then `H^n(⊥ ⟶ c)` vanishes for `c ≤ -b`. -/
lemma isZero_H_bot (t : TStructure C) (K B : C) (b : ℤ) [t.IsLE K b] (n : ℤ) (c : EInt)
    (hc : c ≤ ((-b : ℤ) : EInt)) :
    IsZero (((hyperextSpectralObject t K B).H n).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ c)))) := by
  have : (opTStructure t).IsGE (op K) (-b) :=
    (opTStructure_isGE_iff t (op K) (-b)).2 (by rw [neg_neg]; infer_instance)
  exact isZero_H_of_isZero t K B n _
    ((opTStructure t).isZero_eTruncLT_obj_obj (op K) (-b) c hc)

/-- If `K` lies in degrees `≥ a`, then `H^n(c ⟶ ⊤)` vanishes for `-a < c`. -/
lemma isZero_H_top (t : TStructure C) (K B : C) (a : ℤ) [t.IsGE K a] (n : ℤ) (c : EInt)
    (hc : ((-a : ℤ) : EInt) < c) :
    IsZero (((hyperextSpectralObject t K B).H n).obj
      (mk₁ (homOfLE (le_top : c ≤ (⊤ : EInt))))) := by
  have : (opTStructure t).IsLE (op K) (-a) :=
    (opTStructure_isLE_iff t (op K) (-a)).2 (by rw [neg_neg]; infer_instance)
  exact isZero_H_of_isZero t K B n _
    ((opTStructure t).isZero_eTruncGE_obj_obj (op K) (-a) c hc)

/-- If `K` lies in degrees `≤ b`, then every page vanishes in the rows `q < -b`. -/
lemma isZero_page_X_of_lt (t : TStructure C) (K B : C) (b : ℤ) [t.IsLE K b] (r : ℤ)
    (hr : 2 ≤ r) (p q : ℤ) (hq : q < -b) :
    IsZero (((hyperextSpectralSequence t K B).page r hr).X ⟨p, q⟩) := by
  have : (opTStructure t).IsGE (op K) (-b) :=
    (opTStructure_isGE_iff t (op K) (-b)).2 (by rw [neg_neg]; infer_instance)
  apply (hyperextSpectralObject t K B).isZero_spectralSequence_page_X_of_isZero_H'
    coreE₂Cohomological r hr ⟨p, q⟩
  apply isZero_H_of_isZero
  exact Functor.map_isZero ((opTStructure t).eTruncGE.obj (q : EInt))
    ((opTStructure t).isZero_eTruncLT_obj_obj (op K) (-b) ((q + 1 : ℤ) : EInt)
      (WithBotTop.coe_le_coe.2 (by lia)))

/-- If `K` lies in degrees `≥ a`, then every page vanishes in the rows `-a < q`. -/
lemma isZero_page_X_of_gt (t : TStructure C) (K B : C) (a : ℤ) [t.IsGE K a] (r : ℤ)
    (hr : 2 ≤ r) (p q : ℤ) (hq : -a < q) :
    IsZero (((hyperextSpectralSequence t K B).page r hr).X ⟨p, q⟩) := by
  have : (opTStructure t).IsLE (op K) (-a) :=
    (opTStructure_isLE_iff t (op K) (-a)).2 (by rw [neg_neg]; infer_instance)
  apply (hyperextSpectralObject t K B).isZero_spectralSequence_page_X_of_isZero_H'
    coreE₂Cohomological r hr ⟨p, q⟩
  apply isZero_H_of_isZero
  exact (opTStructure t).isZero_eTruncGE_obj_obj _ (-a) (q : EInt) (WithBotTop.coe_lt_coe.2 hq)

/-- Page degeneration: a differential of page `r ≥ b - a + 2` starting in a row `q` with
`-b ≤ q ≤ -a` ends in the row `q + 1 - r < -b`, so its source or its target is zero. -/
theorem hyperextPageDegeneration : HyperextPageDegenerationStatement.{v, u} C := by
  intro t K B a b _ _ r hr hab pq pq'
  by_cases h : (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel pq pq'
  · obtain ⟨p, q⟩ := pq
    by_cases hq : q < -b ∨ -a < q
    · obtain hq | hq := hq
      · exact (isZero_page_X_of_lt t K B b r hr p q hq).eq_of_src _ _
      · exact (isZero_page_X_of_gt t K B a r hr p q hq).eq_of_src _ _
    · obtain ⟨p', q'⟩ := pq'
      have h' : q + (1 - r) = q' := congrArg Prod.snd h
      exact (isZero_page_X_of_lt t K B b r hr p' q' (by lia)).eq_of_tgt _ _
  · exact HomologicalComplex.shape _ _ _ h

omit [IsTriangulated C] in
/-- Membership in the abutment filtration, read through the truncation of `op K` for the
opposite t-structure: when `p - n = 1 - m`, a morphism `f : K ⟶ B⟦n⟧` lies in `F^p` exactly
when it factors through `K ⟶ (τ_{< m} (op K)).unop`. -/
lemma mem_filtration_iff_exists (t : TStructure C) (K B : C) (n p m : ℤ) (hm : p - n = 1 - m)
    (f : ShiftedHom K B n) :
    f ∈ filtration t K B n p ↔ ∃ x : (((opTStructure t).truncLT m).obj (op K)).unop ⟶ B⟦n⟧,
      (((opTStructure t).truncLTι m).app (op K)).unop ≫ x = f := by
  rw [mem_filtration_iff_truncLTι_comp_eq_zero]
  let T : Triangle C := ((triangleOpEquivalence C).inverse.obj
    (((opTStructure t).triangleLTGE m).obj (op K))).unop
  have hT : T ∈ distTriang C :=
    unop_distinguished _ ((opTStructure t).triangleLTGE_distinguished m (op K))
  have : t.IsLE T.obj₁ (-m) :=
    (opTStructure_isGE_iff t (((opTStructure t).truncGE m).obj (op K)) m).1 inferInstance
  constructor
  · intro hf
    have e := t.liftTruncLT_ι T.mor₁ (-m) (p - n) (by lia)
    have h₁ : T.mor₁ ≫ f = 0 :=
      (congrArg (· ≫ f) e.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) hf).trans comp_zero))
    obtain ⟨x, hx⟩ := Triangle.yoneda_exact₂ T hT f h₁
    exact ⟨x, hx.symm⟩
  · rintro ⟨x, rfl⟩
    have : t.IsGE (((opTStructure t).truncLT m).obj (op K)).unop (-(m - 1)) :=
      (opTStructure_isLE_iff t _ (m - 1)).1 inferInstance
    rw [← Category.assoc, t.zero ((t.truncLTι (p - n)).app K ≫ _) (p - n - 1) (-(m - 1))
      (by lia), zero_comp]

/-- The map `H^n(⊥ ⟶ m) ⟶ H^n(⊥ ⟶ ⊤)` of the hyperext spectral object is precomposition with
the truncation map `K ⟶ (τ_{< m} (op K)).unop`. -/
lemma H_map_twoδ₂Toδ₁_apply (t : TStructure C) (K B : C) (n m : ℤ)
    (f : (⊥ : EInt) ⟶ (m : EInt)) (g : (m : EInt) ⟶ ⊤) (fg : (⊥ : EInt) ⟶ ⊤) (h : f ≫ g = fg)
    (x : (((opTStructure t).truncLT m).obj (op K)).unop ⟶ B⟦n⟧) :
    (((hyperextSpectralObject t K B).H n).map (twoδ₂Toδ₁ f g fg h)).hom x =
      (((opTStructure t).truncLTι m).app (op K)).unop ≫ x := by
  change ((𝟙 _ ≫ ((opTStructure t).truncLTι m).app (op K)).unop ≫ x) = _
  rw [Category.id_comp]

/-- In the rows `-b ≤ q ≤ -a`, the object in position `(p, q)` on a page `r ≥ b - a + 2` is
the graded piece `gr^p` of the abutment filtration in total degree `p + q`. -/
def stablePageIsoOfMem (t : TStructure C) (K B : C) (a b : ℤ) [t.IsGE K a] [t.IsLE K b]
    (r : ℤ) (hr : 2 ≤ r) (hab : b - a + 2 ≤ r) (p q : ℤ) (hq₁ : -b ≤ q) (hq₂ : q ≤ -a) :
    ((hyperextSpectralSequence t K B).page r hr).X ⟨p, q⟩ ≅
      AddCommGrpCat.of (graded t K B (p + q) p) :=
  (hyperextSpectralObject t K B).spectralSequencePageXIso coreE₂Cohomological r hr ⟨p, q⟩
      ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt)
      rfl rfl rfl rfl (p + q - 1) (p + q) (p + q + 1) rfl ≪≫
    ((hyperextSpectralObject t K B).isoMapFourδ₁Toδ₀' ⊥ ((q - r + 2 : ℤ) : EInt) (q : EInt)
      ((q + 1 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt) bot_le
      (WithBotTop.coe_le_coe.2 (by lia)) (WithBotTop.coe_le_coe.2 (by lia))
      (WithBotTop.coe_le_coe.2 (by lia)) (p + q - 1) (p + q) (p + q + 1)
      (isZero_H_bot t K B b _ _ (WithBotTop.coe_le_coe.2 (by lia)))).symm ≪≫
    (hyperextSpectralObject t K B).isoMapFourδ₄Toδ₃' ⊥ (q : EInt) ((q + 1 : ℤ) : EInt)
      ((q + r - 1 : ℤ) : EInt) ⊤ bot_le (WithBotTop.coe_le_coe.2 (by lia))
      (WithBotTop.coe_le_coe.2 (by lia)) le_top (p + q - 1) (p + q) (p + q + 1)
      (isZero_H_top t K B a _ _ (WithBotTop.coe_lt_coe.2 (by lia))) ≪≫
    AddEquiv.toAddCommGrpIso (Y := AddCommGrpCat.of (graded t K B (p + q) p))
      (eAddEquiv (hyperextSpectralObject t K B) (homOfLE (bot_le : (⊥ : EInt) ≤ (q : EInt)))
        (homOfLE (WithBotTop.coe_le_coe.2 (by lia) : (q : EInt) ≤ ((q + 1 : ℤ) : EInt)))
        (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤)) (homOfLE bot_le) rfl (homOfLE bot_le) rfl
        (p + q - 1) (p + q) (p + q + 1) (by lia) (by lia)
        (filtration t K B (p + q) p) (filtration t K B (p + q) (p + 1))
        (fun y => (mem_filtration_iff_exists t K B (p + q) p (q + 1) (by lia) y).trans
          (exists_congr fun x =>
            ⟨fun h => (H_map_twoδ₂Toδ₁_apply t K B (p + q) (q + 1) _ _ _ _ x).trans h,
              fun h => (H_map_twoδ₂Toδ₁_apply t K B (p + q) (q + 1) _ _ _ _ x).symm.trans h⟩))
        (fun y => (mem_filtration_iff_exists t K B (p + q) (p + 1) q (by lia) y).trans
          (exists_congr fun x =>
            ⟨fun h => (H_map_twoδ₂Toδ₁_apply t K B (p + q) q _ _ _ _ x).trans h,
              fun h => (H_map_twoδ₂Toδ₁_apply t K B (p + q) q _ _ _ _ x).symm.trans h⟩)))

omit [IsTriangulated C] in
/-- Below the rows of `K` (`q < -b`), the graded piece `gr^p` of `Hom(K, B⟦p + q⟧)` is
trivial. -/
lemma subsingleton_graded_of_lt (t : TStructure C) (K B : C) (b : ℤ) [t.IsLE K b] (p q : ℤ)
    (hq : q < -b) : Subsingleton (graded t K B (p + q) p) :=
  subsingleton_graded_of_isLE b (by lia)

omit [IsTriangulated C] in
/-- Above the rows of `K` (`-a < q`), the graded piece `gr^p` of `Hom(K, B⟦p + q⟧)` is trivial,
because `F^p = F^{p+1}`: both conditions ask a morphism to vanish on a zero truncation. -/
lemma subsingleton_graded_of_gt (t : TStructure C) (K B : C) (a : ℤ) [t.IsGE K a] (p q : ℤ)
    (hq : -a < q) : Subsingleton (graded t K B (p + q) p) := by
  refine subsingleton_graded_of_le fun f _ => (mem_filtration_iff_truncLTι_comp_eq_zero f).2 ?_
  have : t.IsGE K (p + 1 - (p + q)) := t.isGE_of_ge K _ a (by lia)
  exact (t.isZero_truncLT_obj_of_isGE _ K).eq_of_src _ _

/-- Identification of the stable pages. -/
theorem hyperextStablePage : HyperextStablePageStatement.{v, u} C := by
  intro t K B a b _ _ r hr hab p q
  by_cases hq : q < -b ∨ -a < q
  · obtain hq | hq := hq
    · have := subsingleton_graded_of_lt t K B b p q hq
      exact ⟨(isZero_page_X_of_lt t K B b r hr p q hq).iso
        (AddCommGrpCat.isZero_of_subsingleton _)⟩
    · have := subsingleton_graded_of_gt t K B a p q hq
      exact ⟨(isZero_page_X_of_gt t K B a r hr p q hq).iso
        (AddCommGrpCat.isZero_of_subsingleton _)⟩
  · exact ⟨stablePageIsoOfMem t K B a b r hr hab p q (by lia) (by lia)⟩

/-- Convergence of the hyperext spectral sequence for bounded objects. -/
theorem hyperextConvergenceStatements_proof : HyperextConvergenceStatements.{v, u} C :=
  ⟨hyperextPageDegeneration, hyperextStablePage⟩

end Concrete

end HyperextConvergence

end Langlands.Cohomology
