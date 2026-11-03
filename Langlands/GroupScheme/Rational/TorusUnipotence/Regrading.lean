import Langlands.GroupScheme.Rational.TorusUnipotence.BigCell
import Langlands.GroupScheme.Rational.TorusUnipotence.Rigidity
import Mathlib.Algebra.Module.Submodule.Bilinear
import Mathlib.Order.CompactlyGenerated.Basic

/-! # Coarsening a weight grading to a `ℤ`-grading -/

noncomputable section

universe u

open TensorProduct

namespace Langlands.GroupScheme.TorusUnipotence

section Coarsen

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]
  {X : Type*} [AddCommGroup X]

/-- The `ℤ`-grading obtained from a family of weight spaces by a homomorphism `w` to `ℤ`:
degree `d` is the sum of the weight spaces whose weight is sent to `d`. -/
def regrade (W : X → Submodule k M) (w : X →+ ℤ) (d : ℤ) : Submodule k M :=
  ⨆ (χ : X) (_ : w χ = d), W χ

variable {W : X → Submodule k M} {w : X →+ ℤ}

theorem le_regrade {χ : X} {d : ℤ} (h : w χ = d) : W χ ≤ regrade W w d :=
  le_iSup₂_of_le (f := fun χ (_ : w χ = d) => W χ) χ h le_rfl

theorem regrade_le_iff {d : ℤ} {P : Submodule k M} :
    regrade W w d ≤ P ↔ ∀ χ, w χ = d → W χ ≤ P :=
  iSup₂_le_iff

theorem regrade_neg (d : ℤ) : regrade W (-w) d = regrade W w (-d) := by
  simp only [regrade, AddMonoidHom.neg_apply, neg_eq_iff_eq_neg]

/-- Coarsening preserves independence. -/
theorem iSupIndep_regrade (hW : iSupIndep W) : iSupIndep (regrade W w) := by
  intro d
  have h : ⨆ (e : ℤ) (_ : e ≠ d), regrade W w e = ⨆ χ ∈ {χ | w χ ≠ d}, W χ := by
    apply le_antisymm
    · refine iSup₂_le fun e he => regrade_le_iff.2 fun χ hχ => ?_
      exact le_iSup₂_of_le (f := fun χ (_ : χ ∈ {χ | w χ ≠ d}) => W χ) χ
        (show w χ ≠ d from hχ ▸ he) le_rfl
    · exact iSup₂_le fun χ hχ => le_iSup₂_of_le (w χ) hχ (le_regrade rfl)
  rw [h]
  exact hW.disjoint_biSup_biSup (s := {χ | w χ = d}) (Set.disjoint_left.2 fun _ h h' => h' h)

/-- Coarsening preserves the total sum. -/
theorem iSup_regrade : ⨆ d, regrade W w d = ⨆ χ, W χ :=
  le_antisymm (iSup_le fun _ => iSup₂_le fun χ _ => le_iSup W χ)
    (iSup_le fun χ => le_iSup_of_le (w χ) (le_regrade rfl))

theorem isInternal_regrade (hind : iSupIndep W) (htop : ⨆ χ, W χ = ⊤) :
    DirectSum.IsInternal (regrade W w) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_regrade hind)
    (by rw [iSup_regrade, htop])

/-- A comultiplication compatible with the weight spaces is compatible with the coarsened
grading. -/
theorem regrade_comul {Δ : M →ₗ[k] M ⊗[k] M}
    (hΔ : ∀ χ, ∀ a ∈ W χ, Δ a ∈ ⨆ α, Submodule.map₂ (TensorProduct.mk k M M) (W α) (W (χ - α)))
    (d : ℤ) {a : M} (ha : a ∈ regrade W w d) :
    Δ a ∈ ⨆ e, Submodule.map₂ (TensorProduct.mk k M M) (regrade W w e) (regrade W w (d - e)) := by
  have hle : regrade W w d ≤ (⨆ e, Submodule.map₂ (TensorProduct.mk k M M) (regrade W w e)
      (regrade W w (d - e))).comap Δ := by
    refine regrade_le_iff.2 fun χ hχ b hb => ?_
    have hsup : (⨆ α, Submodule.map₂ (TensorProduct.mk k M M) (W α) (W (χ - α))) ≤
        ⨆ e, Submodule.map₂ (TensorProduct.mk k M M) (regrade W w e) (regrade W w (d - e)) := by
      refine iSup_le fun α => le_iSup_of_le (w α)
        (Submodule.map₂_le_map₂ (le_regrade rfl) (le_regrade ?_))
      rw [map_sub, hχ]
    exact hsup (hΔ χ b hb)
  exact hle ha

end Coarsen

section Algebra

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
  {X : Type*} [AddCommGroup X] {W : X → Submodule k A} {w : X →+ ℤ}

theorem regrade_mul_le (hmul : ∀ χ ψ, W χ * W ψ ≤ W (χ + ψ)) (d e : ℤ) :
    regrade W w d * regrade W w e ≤ regrade W w (d + e) := by
  simp only [regrade, Submodule.iSup_mul, Submodule.mul_iSup]
  refine iSup₂_le fun χ hχ => iSup₂_le fun ψ hψ => ?_
  refine (hmul _ _).trans (le_iSup₂_of_le (f := fun χ (_ : w χ = d + e) => W χ) _ ?_ le_rfl)
  rw [map_add]
  omega

theorem gradedMonoid_regrade (h1 : (1 : A) ∈ W 0) (hmul : ∀ χ ψ, W χ * W ψ ≤ W (χ + ψ)) :
    SetLike.GradedMonoid (regrade W w) where
  one_mem := le_regrade (map_zero w) h1
  mul_mem d e _ _ ha hb := regrade_mul_le hmul d e (Submodule.mul_mem_mul ha hb)

/-- The coarsened grading of an internally graded algebra is a graded algebra. -/
@[instance_reducible]
def gradedAlgebraRegrade (hind : iSupIndep W) (htop : ⨆ χ, W χ = ⊤) (h1 : (1 : A) ∈ W 0)
    (hmul : ∀ χ ψ, W χ * W ψ ≤ W (χ + ψ)) : GradedAlgebra (regrade W w) :=
  { toGradedMonoid := gradedMonoid_regrade h1 hmul
    toDecomposition := (isInternal_regrade hind htop).chooseDecomposition }

variable {ε : A →ₐ[k] k}

/-- An augmentation vanishing on nonzero weights vanishes in nonzero coarse degrees. -/
theorem regrade_augmentation (hε : ∀ χ, χ ≠ 0 → ∀ a ∈ W χ, ε a = 0) (d : ℤ) (hd : d ≠ 0)
    {a : A} (ha : a ∈ regrade W w d) : ε a = 0 := by
  have hle : regrade W w d ≤ LinearMap.ker ε.toLinearMap := by
    refine regrade_le_iff.2 fun χ hχ b hb => hε χ ?_ b hb
    rintro rfl
    exact hd (by rw [← hχ, map_zero])
  exact hle ha

/-- If every weight space of coarse degree zero meets the augmentation ideal inside its
square, then so does the coarse degree-zero part. -/
theorem regrade_zero_mem_sq (h1 : (1 : A) ∈ W 0) (hε : ∀ χ, χ ≠ 0 → ∀ a ∈ W χ, ε a = 0)
    (hsq : ∀ χ, w χ = 0 → ∀ a ∈ W χ, ε a = 0 → a ∈ RingHom.ker ε ^ 2)
    {a : A} (ha : a ∈ regrade W w 0) (haε : ε a = 0) : a ∈ RingHom.ker ε ^ 2 := by
  have hle : regrade W w 0 ≤
      Submodule.span k {1} ⊔ (RingHom.ker ε ^ 2).restrictScalars k := by
    refine regrade_le_iff.2 fun χ hχ f hf => ?_
    have hf' : f - algebraMap k A (ε f) ∈ W χ := by
      by_cases hχ0 : χ = 0
      · subst hχ0
        refine Submodule.sub_mem _ hf ?_
        rw [Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ _ h1
      · rw [hε χ hχ0 f hf, map_zero, sub_zero]
        exact hf
    have hsq' := hsq χ hχ _ hf' (by
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self])
    rw [show f = algebraMap k A (ε f) + (f - algebraMap k A (ε f)) by ring]
    refine Submodule.add_mem_sup ?_ hsq'
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self 1)
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hle ha)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hzε : ε z = 0 := Ideal.pow_le_self two_ne_zero hz
  have hc : c = 0 := by
    rw [map_add, map_smul, map_one, hzε, add_zero, smul_eq_mul, mul_one] at haε
    exact haε
  rw [hc, zero_smul, zero_add]
  exact hz

end Algebra

section Rigid

variable {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A] [IsDomain A]
  [IsNoetherianRing A] [Algebra.FormallySmooth k A]
  {X : Type*} [AddCommGroup X] {W : X → Submodule k A}

/-- **Top-weight rigidity for a coarsened grading.** For a formally smooth Noetherian domain
with weight spaces `W`, an augmentation `ε` vanishing on nonzero weights and a comultiplication
`Δ` satisfying both counit laws, let `w : X →+ ℤ` be such that every weight space with
`w χ = 0` meets the augmentation ideal inside its square. Then a coarse degree-zero element
whose comultiplication is killed by every functional vanishing in nonnegative coarse degrees on
the second factor is a scalar. -/
theorem exists_eq_smul_one_of_regrade (hind : iSupIndep W) (htop : ⨆ χ, W χ = ⊤)
    (h1 : (1 : A) ∈ W 0) (hmul : ∀ χ ψ, W χ * W ψ ≤ W (χ + ψ)) (ε : A →ₐ[k] k)
    (hε : ∀ χ, χ ≠ 0 → ∀ a ∈ W χ, ε a = 0) (Δ : A →ₐ[k] A ⊗[k] A)
    (hl : (Algebra.TensorProduct.lid k A).toAlgHom.comp
      ((Algebra.TensorProduct.map ε (AlgHom.id k A)).comp Δ) = AlgHom.id k A)
    (hr : (Algebra.TensorProduct.rid k k A).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id k A) ε).comp Δ) = AlgHom.id k A)
    (w : X →+ ℤ) (hsq : ∀ χ, w χ = 0 → ∀ a ∈ W χ, ε a = 0 → a ∈ RingHom.ker ε ^ 2)
    {a : A} (ha : a ∈ regrade W w 0)
    (hm : ∀ m : Module.Dual k A, (∀ d : ℤ, 0 ≤ d → ∀ b ∈ regrade W w d, m b = 0) →
      TensorProduct.rid k A (m.lTensor A (Δ a)) = 0) :
    ∃ c : k, a = c • 1 := by
  let _ : GradedAlgebra (regrade W (-w)) := gradedAlgebraRegrade hind htop h1 hmul
  have hε' : ∀ d : ℤ, d ≠ 0 → ∀ b ∈ regrade W (-w) d, ε b = 0 :=
    fun d hd b hb => regrade_augmentation hε d hd hb
  have hsq' : ∀ b ∈ regrade W (-w) 0, ε b = 0 → b ∈ RingHom.ker ε ^ 2 :=
    fun b hb hbε => regrade_zero_mem_sq h1 hε
      (fun χ hχ => hsq χ (by rwa [AddMonoidHom.neg_apply, neg_eq_zero] at hχ)) hb hbε
  have hinj := gradedBigCellInjectivity k A (regrade W (-w)) ε Δ hε' hl hr hsq'
  have ha' : a ∈ regrade W (-w) 0 := by rwa [regrade_neg, neg_zero]
  refine ⟨ε a, ?_⟩
  rw [← Algebra.algebraMap_eq_smul_one]
  refine eq_algebraMap_of_lTensor_eq_zero hinj hε' (fun x => AlgHom.congr_fun hr x) ha'
    fun m hm' => hm m fun d hd b hb => hm' (-d) (by omega) b ?_
  rwa [regrade_neg, neg_neg]

end Rigid

end Langlands.GroupScheme.TorusUnipotence
