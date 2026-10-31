import Langlands.AlgebraicGeometry.Modules.CechResolution.Basic
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology

/-!
# The sheafified alternating Čech complex of an ordered affine cover

For an ordered affine cover `𝒰` of `X` and an `𝒪_X`-module `M`, the `p`-th term is the finite
biproduct over strictly increasing `(p+1)`-tuples `s` of `sheafOn M (𝒰.inter s)`, and the
differential is the alternating sum of the face restrictions, as in the alternating Čech cochains
`OModulePresheaf.cochain`/`OModulePresheaf.d`. The augmentation `M ⟶ cechTerm 0` collects the
units `M ⟶ sheafOn M (𝒰.U i)`. The last result reduces the quasi-isomorphism property of the
augmentation to exactness of the augmented complex.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

variable {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (M : X.Modules)

/-- The `p`-th term `⨁_{s} sheafOn M (𝒰.inter s)` of the sheafified alternating Čech complex,
indexed by strictly increasing tuples `s : Fin (p + 1) → 𝒰.ι`. -/
abbrev cechTerm (p : ℕ) : X.Modules :=
  ⨁ fun s : 𝒰.Idx p => sheafOn M (𝒰.inter s)

/-- The alternating Čech differential: its component at `t` is
`∑ j, (-1)^j • (π_{face t j} ≫ res)`. -/
def cechD (p : ℕ) : cechTerm 𝒰 M p ⟶ cechTerm 𝒰 M (p + 1) :=
  biproduct.lift fun t => ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    (biproduct.π (fun s : 𝒰.Idx p => sheafOn M (𝒰.inter s)) (𝒰.face t j) ≫
      res M (𝒰.inter_le_inter_face t j))

@[reassoc]
lemma cechD_π (p : ℕ) (t : 𝒰.Idx (p + 1)) :
    cechD 𝒰 M p ≫ biproduct.π (fun s : 𝒰.Idx (p + 1) => sheafOn M (𝒰.inter s)) t =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (biproduct.π (fun s : 𝒰.Idx p => sheafOn M (𝒰.inter s)) (𝒰.face t j) ≫
          res M (𝒰.inter_le_inter_face t j)) :=
  biproduct.lift_π _ _

lemma π_res_congr {p : ℕ} {t t' : 𝒰.Idx p} (h : t = t') {W : X.Opens} (hW : W ≤ 𝒰.inter t)
    (hW' : W ≤ 𝒰.inter t') :
    biproduct.π (fun s : 𝒰.Idx p => sheafOn M (𝒰.inter s)) t ≫ res M hW =
      biproduct.π (fun s : 𝒰.Idx p => sheafOn M (𝒰.inter s)) t' ≫ res M hW' := by
  subst h
  rfl

/-- The simplicial identity `δ_{j+1} ∘ δ_i = δ_i ∘ δ_j` for `i ≤ j`, on face maps of `Fin`. -/
lemma succAbove_comp_succAbove {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) :
    Fin.succAbove j.succ ∘ Fin.succAbove i = Fin.succAbove i.castSucc ∘ Fin.succAbove j := by
  ext k
  simp only [Function.comp_apply, Fin.succAbove]
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  rcases k with ⟨k, hk⟩
  simp only [Fin.le_def] at h
  simp only [Fin.lt_def, Fin.castSucc_mk, Fin.succ_mk, Fin.val_castSucc]
  split_ifs <;> simp_all only [Fin.val_succ, Fin.val_castSucc] <;> omega

lemma cechD_comp_cechD (p : ℕ) : cechD 𝒰 M p ≫ cechD 𝒰 M (p + 1) = 0 := by
  refine biproduct.hom_ext _ _ fun s => ?_
  rw [Category.assoc, cechD_π, zero_comp, Preadditive.comp_sum]
  simp only [Preadditive.comp_zsmul, ← Category.assoc, cechD_π]
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
    have hface : 𝒰.face (𝒰.face s a) b = 𝒰.face (𝒰.face s b.succ) a' := by
      apply Subtype.ext
      change s.1 ∘ (Fin.succAbove a ∘ Fin.succAbove b) =
        s.1 ∘ (Fin.succAbove b.succ ∘ Fin.succAbove a')
      rw [← hacs, succAbove_comp_succAbove halt]
    have hsign : ((-1 : ℤ) ^ ((a : ℕ) + (b : ℕ))) =
        -((-1 : ℤ) ^ (((b.succ : Fin (p + 3)) : ℕ) + (a' : ℕ))) := by
      simp only [Fin.val_succ, a', Fin.val_castLT]
      rw [show (b : ℕ) + 1 + (a : ℕ) = ((a : ℕ) + (b : ℕ)) + 1 by ring, pow_succ]
      ring
    rw [hsign, neg_smul]
    exact congrArg Neg.neg (congrArg₂ (· • ·) rfl (π_res_congr 𝒰 M hface _ _))

/-- The sheafified alternating Čech complex as an `ℕ`-indexed cochain complex. -/
def cechComplex : CochainComplex X.Modules ℕ :=
  CochainComplex.of (cechTerm 𝒰 M) (cechD 𝒰 M) (cechD_comp_cechD 𝒰 M)

/-- The augmentation `M ⟶ ⨁_i sheafOn M (𝒰.U i)`, built from the units. -/
def augmentation : M ⟶ cechTerm 𝒰 M 0 :=
  biproduct.lift fun s => unit M (𝒰.inter s)

@[reassoc]
lemma augmentation_π (s : 𝒰.Idx 0) :
    augmentation 𝒰 M ≫ biproduct.π (fun s : 𝒰.Idx 0 => sheafOn M (𝒰.inter s)) s =
      unit M (𝒰.inter s) :=
  biproduct.lift_π _ _

lemma augmentation_cechD : augmentation 𝒰 M ≫ cechD 𝒰 M 0 = 0 := by
  refine biproduct.hom_ext _ _ fun t => ?_
  rw [Category.assoc, cechD_π, zero_comp, Preadditive.comp_sum]
  simp only [Preadditive.comp_zsmul, augmentation_π_assoc, unit_res]
  rw [Fin.sum_univ_two]
  simp

/-- The augmentation as a morphism of cochain complexes `M[0] ⟶ cechComplex 𝒰 M`. -/
def cechAug : (CochainComplex.single₀ X.Modules).obj M ⟶ cechComplex 𝒰 M :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨augmentation 𝒰 M, by
    have h : (cechComplex 𝒰 M).d 0 1 = cechD 𝒰 M 0 :=
      CochainComplex.of_d (cechTerm 𝒰 M) (cechD 𝒰 M) 0
    rw [h]
    exact augmentation_cechD 𝒰 M⟩

/-- The augmented Čech complex `M ⟶ C⁰ ⟶ C¹` in degree zero. -/
def augSc : ShortComplex X.Modules :=
  ShortComplex.mk (augmentation 𝒰 M) (cechD 𝒰 M 0) (augmentation_cechD 𝒰 M)

/-- The Čech complex `Cⁿ ⟶ Cⁿ⁺¹ ⟶ Cⁿ⁺²`. -/
def cechSc (n : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (cechD 𝒰 M n) (cechD 𝒰 M (n + 1)) (cechD_comp_cechD 𝒰 M n)

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation is a quasi-isomorphism once it is a monomorphism and the augmented complex is
exact in every degree. -/
theorem quasiIso_cechAug_of_exact (hmono : Mono (augmentation 𝒰 M)) (h0 : (augSc 𝒰 M).Exact)
    (hn : ∀ n, (cechSc 𝒰 M n).Exact) : QuasiIso (cechAug 𝒰 M) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 ⟨h0, hmono⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp [augSc, cechAug])
        (by simpa [augSc, cechComplex] using
          (CochainComplex.of_d (cechTerm 𝒰 M) (cechD 𝒰 M) 0).symm)
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
      refine (ShortComplex.exact_iff_of_iso ?_).1 (hn n)
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp [cechSc, cechComplex]) (by simp [cechSc, cechComplex])
    · exact CochainComplex.exactAt_succ_single_obj _ _

end Langlands.AlgebraicGeometry.Modules.CechResolution
