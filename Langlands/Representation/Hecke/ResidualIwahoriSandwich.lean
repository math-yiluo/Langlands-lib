import Langlands.Representation.Hecke.IwahoriSandwich
import Langlands.Representation.Hecke.ResidualCosetStabilization
import Mathlib.Algebra.BigOperators.Pi

/-! # Residual Iwahori multiplication and finite generation -/

noncomputable section

namespace Langlands.Hecke

universe uG uΔ

variable {G : Type uG} [Group G]

/-- The lower subgroup after backward conjugation by a positive element. -/
def iwahoriLowerConjugate (L : Subgroup G) (a : G) : Subgroup G :=
  L.map (MulAut.conj a⁻¹).toMonoidHom

theorem mem_iwahoriLowerConjugate (L : Subgroup G) (a x : G) :
    x ∈ iwahoriLowerConjugate L a ↔ ∃ l ∈ L, x = a⁻¹ * l * a := by
  simp only [iwahoriLowerConjugate, Subgroup.mem_map, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
  exact exists_congr fun l => and_congr_right fun _ => eq_comm

variable [TopologicalSpace G]

namespace TestFunction

/-- Equality of the actual residual coset sets supplies the missing lower
factor in a positive-times-residual double-coset multiplication. -/
theorem mul_mem_doubleCosetSet_of_residualCosets
    (K : OpenSubgroup G) (N M Nbar : Subgroup G)
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar,
      ∃ m ∈ K.toSubgroup ⊓ M, ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (a b f : G)
    (hup : ∀ u ∈ K.toSubgroup ⊓ N, a * u * a⁻¹ ∈ K)
    (hmid : ∀ m ∈ K.toSubgroup ⊓ M, a * m * a⁻¹ ∈ K)
    (hcos : residualCosets K (iwahoriLowerConjugate (K.toSubgroup ⊓ Nbar) b) f =
      residualCosets K (iwahoriLowerConjugate (K.toSubgroup ⊓ Nbar) (a * b)) f)
    (k : G) (hk : k ∈ K) :
    a * k * (b * f) ∈ doubleCosetSet K (a * b * f) := by
  obtain ⟨l, hl, m, hm, u, hu, hprod⟩ := hfactor k⁻¹ (K.inv_mem hk)
  have hkprod : k = u⁻¹ * m⁻¹ * l⁻¹ := by
    rw [← inv_inv k, hprod]
    group
  have hmem : QuotientGroup.mk (b⁻¹ * l⁻¹ * b * f) ∈
      residualCosets K (iwahoriLowerConjugate (K.toSubgroup ⊓ Nbar) b) f :=
    ⟨b⁻¹ * l⁻¹ * b,
      (mem_iwahoriLowerConjugate _ _ _).2
        ⟨l⁻¹, (K.toSubgroup ⊓ Nbar).inv_mem hl, rfl⟩, rfl⟩
  rw [hcos] at hmem
  obtain ⟨v, hv, heq⟩ := hmem
  obtain ⟨l', hl', rfl⟩ := (mem_iwahoriLowerConjugate _ _ _).1 hv
  let k' := (((a * b)⁻¹ * l' * (a * b)) * f)⁻¹ * (b⁻¹ * l⁻¹ * b * f)
  have hk' : k' ∈ K := QuotientGroup.eq.mp heq
  have hreplace : b⁻¹ * l⁻¹ * b * f =
      (a * b)⁻¹ * l' * (a * b) * f * k' := by
    dsimp [k']
    group
  refine (mem_doubleCosetSet K _ _).2
    ⟨(a * u⁻¹ * a⁻¹) * (a * m⁻¹ * a⁻¹) * l',
      K.mul_mem
        (K.mul_mem (hup _ ((K.toSubgroup ⊓ N).inv_mem hu))
          (hmid _ ((K.toSubgroup ⊓ M).inv_mem hm))) hl'.1,
      k', hk', ?_⟩
  calc
    a * k * (b * f) =
        (a * u⁻¹ * a⁻¹) * (a * m⁻¹ * a⁻¹) * (a * b) *
          (b⁻¹ * l⁻¹ * b * f) := by rw [hkprod]; group
    _ = _ := by rw [hreplace]; group

end TestFunction

variable [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Backward contraction makes the lower conjugates decrease throughout
the positive orthant. -/
theorem antitone_iwahoriLowerConjugate {Δ : Type uΔ}
    (L : Subgroup G) (e : Multiplicative (Δ → ℕ) →* G)
    (hlow : ∀ n, ∀ l ∈ L,
      (e (Multiplicative.ofAdd n))⁻¹ * l * e (Multiplicative.ofAdd n) ∈ L) :
    Antitone (fun n => iwahoriLowerConjugate L (e (Multiplicative.ofAdd n))) := by
  intro m n hmn x hx
  obtain ⟨l, hl, rfl⟩ := (mem_iwahoriLowerConjugate _ _ _).1 hx
  have he : e (Multiplicative.ofAdd n) =
      e (Multiplicative.ofAdd (n - m)) * e (Multiplicative.ofAdd m) := by
    rw [← map_mul]
    congr 1
    change n = (n - m) + m
    funext i
    exact (Nat.sub_add_cancel (hmn i)).symm
  refine (mem_iwahoriLowerConjugate _ _ _).2
    ⟨_, hlow (n - m) l hl, ?_⟩
  rw [he]
  group

variable [T2Space G] [MeasurableSpace G] [BorelSpace G]

open MeasureTheory

namespace HeckeAlgebra.Corner

/-- The residual coset equality gives an exact identity of mass-one
Hecke indicators, with no normalization assumption on the residual. -/
theorem massIndicator_mul_of_residualCosets
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (μ : Measure G) [μ.IsHaarMeasure]
    (N M Nbar : Subgroup G)
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar,
      ∃ m ∈ K.toSubgroup ⊓ M, ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (a b f : G)
    (hup : ∀ u ∈ K.toSubgroup ⊓ N, a * u * a⁻¹ ∈ K)
    (hmid : ∀ m ∈ K.toSubgroup ⊓ M, a * m * a⁻¹ ∈ K)
    (hcos : residualCosets K (iwahoriLowerConjugate (K.toSubgroup ⊓ Nbar) b) f =
      residualCosets K (iwahoriLowerConjugate (K.toSubgroup ⊓ Nbar) (a * b)) f) :
    massIndicator K hK μ a * massIndicator K hK μ (b * f) =
      massIndicator K hK μ (a * b * f) := by
  rw [mul_assoc a b f]
  apply massIndicator_mul K hK μ
  simpa only [mul_assoc] using
    TestFunction.mul_mem_doubleCosetSet_of_residualCosets K N M Nbar
      hfactor a b f hup hmid hcos

/-- Every residual translate in an orthant is a positive mass indicator
times one of finitely many residual mass indicators. -/
theorem exists_finite_residual_massIndicator_frontier {Δ : Type uΔ} [Finite Δ]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (μ : Measure G) [μ.IsHaarMeasure]
    (N M Nbar : Subgroup G)
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar,
      ∃ m ∈ K.toSubgroup ⊓ M, ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (e : Multiplicative (Δ → ℕ) →* G)
    (he : ∀ n, e (Multiplicative.ofAdd n) ∈
      iwahoriPositiveMonoid K.toSubgroup N M Nbar)
    (hmid : ∀ n, ∀ m ∈ K.toSubgroup ⊓ M,
      e (Multiplicative.ofAdd n) * m * (e (Multiplicative.ofAdd n))⁻¹ ∈ K)
    (f : G) :
    ∃ S : Set (Δ → ℕ), S.Finite ∧ ∀ n, ∃ m ∈ S, m ≤ n ∧
      massIndicator K hK μ (e (Multiplicative.ofAdd (n - m))) *
        massIndicator K hK μ (e (Multiplicative.ofAdd m) * f) =
      massIndicator K hK μ (e (Multiplicative.ofAdd n) * f) := by
  let U := fun n => iwahoriLowerConjugate
    (K.toSubgroup ⊓ Nbar) (e (Multiplicative.ofAdd n))
  have hU : ∀ n, U n ≤ K.toSubgroup := by
    intro n x hx
    obtain ⟨l, hl, rfl⟩ := (mem_iwahoriLowerConjugate _ _ _).1 hx
    exact ((he n).2.1 l hl).1
  have hanti : Antitone U :=
    antitone_iwahoriLowerConjugate _ e (fun n => (he n).2.1)
  obtain ⟨S, hS, hfront⟩ :=
    exists_finite_residualCoset_frontier K hK U hU hanti f
  refine ⟨S, hS, fun n => ?_⟩
  obtain ⟨m, hm, hmn, hcos⟩ := hfront n
  have heq : e (Multiplicative.ofAdd n) =
      e (Multiplicative.ofAdd (n - m)) * e (Multiplicative.ofAdd m) := by
    rw [← map_mul]
    congr 1
    change n = (n - m) + m
    funext i
    exact (Nat.sub_add_cancel (hmn i)).symm
  refine ⟨m, hm, hmn, ?_⟩
  change residualCosets K (iwahoriLowerConjugate _ (e (Multiplicative.ofAdd m))) f =
    residualCosets K (iwahoriLowerConjugate _ (e (Multiplicative.ofAdd n))) f at hcos
  rw [heq] at hcos ⊢
  exact massIndicator_mul_of_residualCosets K hK μ N M Nbar hfactor _ _ f
    (fun u hu => ((he (n - m)).1 u hu).1) (hmid (n - m)) hcos

end HeckeAlgebra.Corner

end Langlands.Hecke
