import Langlands.AlgebraicGeometry.Modules.CechResolution.Exact
import Langlands.Cohomology.CechCochains

/-!
# The sheafified Čech complex indexed by all tuples

For a finite family `U : ι → X.Opens` of opens of a scheme `X` and an `𝒪_X`-module `M`, the
`p`-th term is the finite biproduct over *all* maps `σ : Fin (p + 1) → ι` (repetitions allowed)
of `sheafOn M (Cech.inter U σ)`, and the differential is the alternating sum of the coface
restrictions. This is the sheafified form of the ordered Čech complex
`Langlands.Cohomology.Cech.complex`. When `U` covers `X`, the augmentation
`M[0] ⟶ allSeqComplex U M` is a quasi-isomorphism.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

open Langlands.Cohomology

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (M : X.Modules)

section Complex

/-- The intersection `U (σ 0) ⊓ ⋯ ⊓ U (σ (n - 1))`, the open `Cech.inter U σ` regarded as an
open of the scheme `X`. -/
abbrev inter {n : ℕ} (σ : Fin n → ι) : X.Opens := Cech.inter U σ

variable {U} in
lemma inter_le_comp {m n : ℕ} (σ : Fin n → ι) (θ : Fin m → Fin n) :
    inter U σ ≤ inter U (σ ∘ θ) :=
  Cech.inter_le_comp σ θ

variable {U} in
lemma inter_le_apply {n : ℕ} (σ : Fin n → ι) (a : Fin n) : inter U σ ≤ U (σ a) :=
  Cech.inter_le_apply σ a

variable [Fintype ι]

/-- The `p`-th term `⨁_{σ : Fin (p + 1) → ι} sheafOn M (inter U σ)`. -/
abbrev term (p : ℕ) : X.Modules :=
  ⨁ fun σ : Fin (p + 1) → ι => sheafOn M (inter U σ)

/-- The ordered Čech differential: its component at `τ` is
`∑ j, (-1)^j • (π_{τ ∘ j.succAbove} ≫ res)`. -/
def d (p : ℕ) : term U M p ⟶ term U M (p + 1) :=
  biproduct.lift fun τ => ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    (biproduct.π (fun σ : Fin (p + 1) → ι => sheafOn M (inter U σ)) (τ ∘ j.succAbove) ≫
      res M (inter_le_comp τ j.succAbove))

@[reassoc]
lemma d_π (p : ℕ) (τ : Fin (p + 2) → ι) :
    d U M p ≫ biproduct.π (fun σ : Fin (p + 2) → ι => sheafOn M (inter U σ)) τ =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (biproduct.π (fun σ : Fin (p + 1) → ι => sheafOn M (inter U σ))
            (τ ∘ j.succAbove) ≫ res M (inter_le_comp τ j.succAbove)) :=
  biproduct.lift_π _ _

lemma π_res_congr {p : ℕ} {σ σ' : Fin (p + 1) → ι} (h : σ = σ') {W : X.Opens}
    (hW : W ≤ inter U σ) (hW' : W ≤ inter U σ') :
    biproduct.π (fun σ : Fin (p + 1) → ι => sheafOn M (inter U σ)) σ ≫ res M hW =
      biproduct.π (fun σ : Fin (p + 1) → ι => sheafOn M (inter U σ)) σ' ≫ res M hW' := by
  subst h
  rfl

lemma d_comp_d (p : ℕ) : d U M p ≫ d U M (p + 1) = 0 := by
  refine biproduct.hom_ext _ _ fun s => ?_
  rw [Category.assoc, d_π, zero_comp, Preadditive.comp_sum]
  simp only [Preadditive.comp_zsmul, ← Category.assoc, d_π]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc, res_comp,
    Finset.smul_sum, smul_smul, ← pow_add]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  set S : Finset (Fin (p + 3) × Fin (p + 2)) := {ab | (ab.1 : ℕ) ≤ (ab.2 : ℕ)}
  rw [← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_bij
    (fun ab (hab : ab ∈ S) =>
      (ab.2.succ, Fin.castLT ab.1 (Nat.lt_of_le_of_lt (Finset.mem_filter.mp hab).2 ab.2.isLt)))
    ?hmem ?hinj ?hsurj ?hterm
  case hmem =>
    rintro ⟨a, b⟩ hab
    simp only [S, Finset.compl_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_succ, not_le, Fin.val_castLT]
    exact Nat.lt_succ_of_le (Finset.mem_filter.mp hab).2
  case hinj =>
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    have h2 := congrArg Prod.snd heq
    exact Prod.ext (Fin.eq_of_val_eq (by simpa using congrArg Fin.val h2))
      (Fin.succ_injective _ (congrArg Prod.fst heq))
  case hsurj =>
    rintro ⟨a', b'⟩ hab'
    have hlt : (b' : ℕ) < (a' : ℕ) := by
      simpa [S, Finset.compl_filter, Finset.mem_filter, not_le] using hab'
    have ha'0 : a' ≠ 0 := fun h => by simp [h] at hlt
    refine ⟨(Fin.castSucc b', a'.pred ha'0), ?_, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc,
        Fin.val_pred]
      omega
    · exact Prod.ext (Fin.succ_pred a' ha'0)
        (Fin.eq_of_val_eq (by simp only [Fin.val_castLT, Fin.val_castSucc]))
  case hterm =>
    rintro ⟨a, b⟩ hab
    have hba : (a : ℕ) ≤ (b : ℕ) := (Finset.mem_filter.mp hab).2
    set a' : Fin (p + 2) := Fin.castLT a (Nat.lt_of_le_of_lt hba b.isLt)
    have halt : a' ≤ b := Fin.le_def.mpr (by simpa [a'] using hba)
    have hacs : a'.castSucc = a := Fin.eq_of_val_eq (by simp [a'])
    have hface : (s ∘ a.succAbove) ∘ b.succAbove = (s ∘ b.succ.succAbove) ∘ a'.succAbove := by
      change s ∘ (Fin.succAbove a ∘ Fin.succAbove b) = s ∘ (Fin.succAbove b.succ ∘ Fin.succAbove a')
      rw [← hacs, succAbove_comp_succAbove halt]
    have hsign : ((-1 : ℤ) ^ ((a : ℕ) + (b : ℕ))) =
        -((-1 : ℤ) ^ (((b.succ : Fin (p + 3)) : ℕ) + (a' : ℕ))) := by
      simp only [Fin.val_succ, a', Fin.val_castLT]
      rw [show (b : ℕ) + 1 + (a : ℕ) = ((a : ℕ) + (b : ℕ)) + 1 by ring, pow_succ]
      ring
    rw [hsign, neg_smul]
    exact congrArg Neg.neg (congrArg₂ (· • ·) rfl (π_res_congr U M hface _ _))

/-- The sheafified ordered Čech complex as an `ℕ`-indexed cochain complex. -/
def complex : CochainComplex X.Modules ℕ :=
  CochainComplex.of (term U M) (d U M) (d_comp_d U M)

/-- The augmentation `M ⟶ ⨁_i sheafOn M (U i)`, built from the units. -/
def augmentation : M ⟶ term U M 0 :=
  biproduct.lift fun σ => unit M (inter U σ)

@[reassoc]
lemma augmentation_π (σ : Fin (0 + 1) → ι) :
    augmentation U M ≫ biproduct.π (fun σ : Fin (0 + 1) → ι => sheafOn M (inter U σ)) σ =
      unit M (inter U σ) :=
  biproduct.lift_π _ _

lemma augmentation_d : augmentation U M ≫ d U M 0 = 0 := by
  refine biproduct.hom_ext _ _ fun t => ?_
  rw [Category.assoc, d_π, zero_comp, Preadditive.comp_sum]
  simp only [Preadditive.comp_zsmul, augmentation_π_assoc, unit_res]
  rw [Fin.sum_univ_two]
  simp

/-- The augmentation as a morphism of cochain complexes `M[0] ⟶ complex U M`. -/
def aug : (CochainComplex.single₀ X.Modules).obj M ⟶ complex U M :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨augmentation U M, by
    have h : (complex U M).d 0 1 = d U M 0 :=
      CochainComplex.of_d (term U M) (d U M) 0
    rw [h]
    exact augmentation_d U M⟩

/-- The augmented complex `M ⟶ C⁰ ⟶ C¹` in degree zero. -/
def augSc : ShortComplex X.Modules :=
  ShortComplex.mk (augmentation U M) (d U M 0) (augmentation_d U M)

/-- The complex `Cⁿ ⟶ Cⁿ⁺¹ ⟶ Cⁿ⁺²`. -/
def sc (n : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (d U M n) (d U M (n + 1)) (d_comp_d U M n)

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation is a quasi-isomorphism once it is a monomorphism and the augmented complex
is exact in every degree. -/
theorem quasiIso_aug_of_exact (hmono : Mono (augmentation U M)) (h0 : (augSc U M).Exact)
    (hn : ∀ n, (sc U M n).Exact) : QuasiIso (aug U M) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 ⟨h0, hmono⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp [augSc, aug])
        (by simpa [augSc, complex] using
          (CochainComplex.of_d (term U M) (d U M) 0).symm)
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
      refine (ShortComplex.exact_iff_of_iso ?_).1 (hn n)
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp [sc, complex]) (by simp [sc, complex])
    · exact CochainComplex.exactAt_succ_single_obj _ _

end Complex

section Sections

/-- The open `inter U σ ⊓ W`, written as an image of a preimage. -/
abbrev secOpen {p : ℕ} (σ : Fin (p + 1) → ι) (W : X.Opens) : X.Opens :=
  (inter U σ).ι ''ᵁ ((inter U σ).ι ⁻¹ᵁ W)

lemma secOpen_eq {p : ℕ} (σ : Fin (p + 1) → ι) (W : X.Opens) :
    secOpen U σ W = inter U σ ⊓ W :=
  image_preimage_eq _ _

/-- Families of sections `σ ↦ c σ ∈ M(inter U σ ⊓ W)`: the sections over `W` of the
`p`-th term. -/
abbrev Sec (p : ℕ) (W : X.Opens) : Type u := ∀ σ : Fin (p + 1) → ι, Γ(M, secOpen U σ W)

variable {U M}

/-- The restriction of the `σ`-component of `c` to a smaller open. -/
def cr {p : ℕ} {W : X.Opens} (c : Sec U M p W) (σ : Fin (p + 1) → ι) {W' : X.Opens}
    (h : W' ≤ secOpen U σ W) : Γ(M, W') :=
  M.presheaf.map (homOfLE h).op (c σ)

lemma cr_def {p : ℕ} {W : X.Opens} (c : Sec U M p W) (σ : Fin (p + 1) → ι) {W' : X.Opens}
    (h : W' ≤ secOpen U σ W) : cr c σ h = M.presheaf.map (homOfLE h).op (c σ) := rfl

lemma cr_congr {p : ℕ} {W : X.Opens} (c : Sec U M p W) {σ σ' : Fin (p + 1) → ι} (e : σ = σ')
    {W' : X.Opens} (h : W' ≤ secOpen U σ W) (h' : W' ≤ secOpen U σ' W) :
    cr c σ h = cr c σ' h' := by
  subst e
  rfl

lemma map_cr {p : ℕ} {W : X.Opens} (c : Sec U M p W) (σ : Fin (p + 1) → ι) {W' W'' : X.Opens}
    (h : W' ≤ secOpen U σ W) (h' : W'' ≤ W') :
    M.presheaf.map (homOfLE h').op (cr c σ h) = cr c σ (h'.trans h) := by
  rw [cr_def, cr_def, ← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  rfl

lemma cr_self {p : ℕ} {W : X.Opens} (c : Sec U M p W) (σ : Fin (p + 1) → ι) :
    cr c σ le_rfl = c σ := by
  rw [cr_def, show (homOfLE (le_refl (secOpen U σ W))).op = 𝟙 _ from rfl, M.presheaf.map_id]
  rfl

/-- The ordered Čech differential on families of sections. -/
def dSec {p : ℕ} {W : X.Opens} (c : Sec U M p W) : Sec U M (p + 1) W := fun τ =>
  ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    cr c (τ ∘ j.succAbove) (image_preimage_mono (inter_le_comp τ j.succAbove) W)

/-- The augmentation on families of sections: restriction from `W` to each `U i ⊓ W`. -/
def aug0 {W : X.Opens} (m : Γ(M, W)) : Sec U M 0 W := fun σ =>
  M.presheaf.map (homOfLE ((inter U σ).ι.image_preimage_le W)).op m

variable (k : ι) {W : X.Opens} (hW : W ≤ U k)

lemma inter_cons {p : ℕ} (σ : Fin (p + 1) → ι) :
    inter U (Fin.cons k σ : Fin (p + 2) → ι) = U k ⊓ inter U σ := by
  apply le_antisymm
  · exact le_inf (inter_le_apply _ 0)
      (le_iInf fun a => (inter_le_apply _ a.succ).trans (by simp))
  · refine le_iInf fun a => ?_
    refine Fin.cases ?_ (fun b => ?_) a
    · simp
    · simpa using inf_le_right.trans (inter_le_apply σ b)

include hW in
lemma secOpen_le_cons {p : ℕ} (σ : Fin (p + 1) → ι) :
    secOpen U σ W ≤ secOpen U (Fin.cons k σ : Fin (p + 2) → ι) W := by
  rw [secOpen_eq, secOpen_eq, inter_cons]
  exact le_inf (le_inf (inf_le_right.trans hW) inf_le_left) inf_le_right

include hW in
lemma le_secOpen_const : W ≤ secOpen U (fun _ : Fin (0 + 1) => k) W := by
  rw [secOpen_eq]
  exact le_inf (hW.trans (le_iInf fun _ => le_rfl)) le_rfl

/-- The contracting homotopy over `W ≤ U k`: `(contr c) σ = c (k, σ)|`. -/
def contr {p : ℕ} (c : Sec U M (p + 1) W) : Sec U M p W := fun σ =>
  cr c (Fin.cons k σ) (secOpen_le_cons k hW σ)

lemma cons_comp_succAbove_zero {p : ℕ} (σ : Fin (p + 1) → ι) :
    (Fin.cons k σ : Fin (p + 2) → ι) ∘ (0 : Fin (p + 2)).succAbove = σ := by
  funext x
  simp

lemma cons_comp_succAbove_succ {p : ℕ} (σ : Fin (p + 2) → ι) (j : Fin (p + 2)) :
    (Fin.cons k σ : Fin (p + 3) → ι) ∘ j.succ.succAbove =
      Fin.cons k (σ ∘ j.succAbove) := by
  funext x
  refine Fin.cases ?_ (fun y => ?_) x
  · simp
  · simp [Fin.succ_succAbove_succ]

include hW in
/-- The cocycle condition of `c` at `(k, τ)`, restricted to `inter U τ ⊓ W`. -/
lemma cocycle_cons {p : ℕ} (c : Sec U M p W) (hc : dSec c = 0) (τ : Fin (p + 1) → ι) :
    c τ + ∑ j : Fin (p + 1), ((-1 : ℤ) ^ ((j : ℕ) + 1)) •
      cr c (Fin.cons k τ ∘ j.succ.succAbove)
        ((secOpen_le_cons k hW τ).trans
          (image_preimage_mono (inter_le_comp _ _) W)) = 0 := by
  have h := congrArg (fun z => M.presheaf.map (homOfLE (secOpen_le_cons k hW τ)).op z)
    (congrFun hc (Fin.cons k τ))
  simp only [Pi.zero_apply, map_zero, dSec] at h
  rw [map_sum, Fin.sum_univ_succ] at h
  simp only [map_zsmul, map_cr] at h
  rw [cr_congr c (cons_comp_succAbove_zero k τ) _ le_rfl, cr_self] at h
  simpa only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ] using h

include hW in
/-- Exactness of the section complex over `W ≤ U k` in positive degrees. -/
theorem dSec_contr {p : ℕ} (c : Sec U M (p + 1) W) (hc : dSec c = 0) :
    dSec (contr k hW c) = c := by
  funext τ
  have h := cocycle_cons k hW c hc τ
  rw [eq_neg_of_add_eq_zero_left h, ← Finset.sum_neg_distrib]
  simp only [dSec]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cr_def (contr k hW c), contr, map_cr, pow_succ, mul_neg_one, neg_smul, neg_neg]
  congr 1
  exact cr_congr c (cons_comp_succAbove_succ k τ j).symm _ _

include hW in
/-- Exactness of the augmented section complex over `W ≤ U k` in degree zero. -/
theorem aug0_cr_const (c : Sec U M 0 W) (hc : dSec c = 0) :
    aug0 (cr c (fun _ => k) (le_secOpen_const k hW)) = c := by
  funext σ
  simp only [aug0]
  rw [map_cr]
  have h := cocycle_cons k hW c hc σ
  rw [Fin.sum_univ_one] at h
  have hσ : (Fin.cons k σ : Fin (0 + 1 + 1) → ι) ∘ (0 : Fin (0 + 1)).succ.succAbove = fun _ => k := by
    funext x
    have hx : x = 0 := Subsingleton.elim _ _
    subst hx
    rfl
  rw [cr_congr c hσ _ (((inter U σ).ι.image_preimage_le W).trans
    (le_secOpen_const k hW))] at h
  simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_smul] at h
  exact (add_neg_eq_zero.1 h).symm

end Sections

section Sheaf

variable {U M} [Fintype ι]

/-- The components over `W` of a section of the `p`-th term. -/
def toSec {p : ℕ} (W : X.Opens) (x : Γ(term U M p, W)) : Sec U M p W := fun σ =>
  (biproduct.π (fun σ : Fin (p + 1) → ι => sheafOn M (inter U σ)) σ).app W x

lemma toSec_injective {p : ℕ} (W : X.Opens) :
    Function.Injective (toSec (U := U) (M := M) (p := p) W) := fun _ _ h =>
  biproduct_ext_app _ fun σ => congrFun h σ

lemma toSec_surjective {p : ℕ} (W : X.Opens) :
    Function.Surjective (toSec (U := U) (M := M) (p := p) W) := fun b =>
  let ⟨x, hx⟩ := biproduct_exists_app (fun σ : Fin (p + 1) → ι => sheafOn M (inter U σ))
    W b
  ⟨x, funext fun σ => hx σ⟩

lemma toSec_zero {p : ℕ} (W : X.Opens) : toSec (U := U) (M := M) (p := p) W 0 = 0 := by
  funext σ
  simp only [toSec, Pi.zero_apply, map_zero]
  rfl

lemma toSec_d {p : ℕ} (W : X.Opens) (x : Γ(term U M p, W)) :
    toSec W ((d U M p).app W x) = dSec (toSec W x) := by
  funext τ
  change (d U M p ≫ biproduct.π
    (fun σ : Fin (p + 2) → ι => sheafOn M (inter U σ)) τ).app W x = _
  rw [d_π, sum_app_apply]
  simp only [dSec]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [zsmul_app_apply]
  rfl

lemma toSec_augmentation (W : X.Opens) (m : Γ(M, W)) :
    toSec W ((augmentation U M).app W m) = aug0 m := by
  funext σ
  change (augmentation U M ≫ biproduct.π
    (fun σ : Fin (0 + 1) → ι => sheafOn M (inter U σ)) σ).app W m = _
  rw [augmentation_π]
  rfl

variable (hU : ⨆ i, U i = ⊤)
include hU

omit [Fintype ι] in
lemma exists_mem_U (x : X) : ∃ k, x ∈ U k :=
  TopologicalSpace.Opens.mem_iSup.1
    (show x ∈ ⨆ i, U i by rw [hU]; exact TopologicalSpace.Opens.mem_top x)

/-- The augmentation is a monomorphism: sections agreeing on every `U i ⊓ V` agree. -/
theorem mono_augmentation : Mono (augmentation U M) := by
  refine mono_of_app_injective _ fun V x y hxy => ?_
  have h := congrArg (toSec V) hxy
  rw [toSec_augmentation, toSec_augmentation] at h
  have hcover : V ≤ ⨆ i, secOpen U (fun _ : Fin (0 + 1) => i) V := by
    intro z hz
    obtain ⟨i, hi⟩ := exists_mem_U hU z
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    have hle : U i ⊓ V ≤ secOpen U (fun _ : Fin (0 + 1) => i) V := by
      rw [secOpen_eq]
      exact inf_le_inf_right V (le_iInf fun _ => le_rfl)
    exact hle (TopologicalSpace.Opens.mem_inf.2 ⟨hi, hz⟩)
  exact TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
    (fun i => secOpen U (fun _ : Fin (0 + 1) => i) V) V
    (fun i => homOfLE ((inter U (fun _ : Fin (0 + 1) => i)).ι.image_preimage_le V)) hcover x y
    fun i => congrFun h (fun _ => i)

omit hU in
lemma d_locally_exact {n : ℕ} (k : ι) {W : X.Opens} (hW : W ≤ U k)
    (c : Γ(term U M (n + 1), W)) (hc : (d U M (n + 1)).app W c = 0) :
    ∃ b : Γ(term U M n, W), (d U M n).app W b = c := by
  have hc' : dSec (toSec W c) = 0 := by
    rw [← toSec_d, hc, toSec_zero]
  obtain ⟨b, hb⟩ := toSec_surjective W (contr k hW (toSec W c))
  exact ⟨b, toSec_injective W (by rw [toSec_d, hb, dSec_contr k hW _ hc'])⟩

omit hU in
lemma augmentation_locally_exact (k : ι) {W : X.Opens} (hW : W ≤ U k)
    (c : Γ(term U M 0, W)) (hc : (d U M 0).app W c = 0) :
    ∃ m : Γ(M, W), (augmentation U M).app W m = c := by
  have hc' : dSec (toSec W c) = 0 := by
    rw [← toSec_d, hc, toSec_zero]
  exact ⟨cr (toSec W c) (fun _ => k) (le_secOpen_const k hW), toSec_injective W
    (by rw [toSec_augmentation, aug0_cr_const k hW _ hc'])⟩

theorem exact_sc (n : ℕ) : (sc U M n).Exact := by
  refine exact_of_locally _ fun V (c : Γ(term U M (n + 1), V)) hc x hx => ?_
  obtain ⟨k, hk⟩ := exists_mem_U hU x
  have hW : V ⊓ U k ≤ V := inf_le_left
  obtain ⟨b, hb⟩ := d_locally_exact k (inf_le_right : V ⊓ U k ≤ U k)
    ((term U M (n + 1)).presheaf.map (homOfLE hW).op c)
    (by rw [app_map_apply, show (d U M (n + 1)).app V c = 0 from hc, map_zero])
  exact ⟨V ⊓ U k, hW, TopologicalSpace.Opens.mem_inf.2 ⟨hx, hk⟩, b, hb⟩

theorem exact_augSc : (augSc U M).Exact := by
  refine exact_of_locally _ fun V (c : Γ(term U M 0, V)) hc x hx => ?_
  obtain ⟨k, hk⟩ := exists_mem_U hU x
  have hW : V ⊓ U k ≤ V := inf_le_left
  obtain ⟨b, hb⟩ := augmentation_locally_exact k (inf_le_right : V ⊓ U k ≤ U k)
    ((term U M 0).presheaf.map (homOfLE hW).op c)
    (by rw [app_map_apply, show (d U M 0).app V c = 0 from hc, map_zero])
  exact ⟨V ⊓ U k, hW, TopologicalSpace.Opens.mem_inf.2 ⟨hx, hk⟩, b, hb⟩

variable (U M) in
/-- For a covering family, the augmentation `M[0] ⟶ complex U M` is a quasi-isomorphism. -/
theorem quasiIso_aug : QuasiIso (aug U M) :=
  quasiIso_aug_of_exact U M (mono_augmentation hU) (exact_augSc hU) (exact_sc hU)

end Sheaf

end Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
