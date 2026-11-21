import Langlands.GroupScheme.Quaternionic.QuadraticHermitianGram

/-! # Orthogonal pairs from one represented value in rank three -/

noncomputable section

universe u v

open Matrix

namespace Langlands.GroupScheme.Quaternionic.HermitianPairing

open HermitianMatrix SU3Root

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
  {V : Type v} [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]

local notation "κ" => SU3Root.conjugation F E
local notation "τ" => quadraticConjugationInvolution F E

variable (G : V →ₗ[E] (V →ₛₗ[(SU3Root.conjugation F E).toRingHom] E))

private theorem exists_orthogonalBasis_from_vector [FiniteDimensional E V]
    (hV : Module.finrank E V = 3) (hG : ∀ x y, κ (G x y) = G y x)
    (hsep : ∀ x, (∀ y, G x y = 0) → x = 0) (w : V) (hw : G w w ≠ 0) :
    ∃ b : Module.Basis (Fin 3) E V, b 0 = w ∧
      (∀ i j, i ≠ j → G (b i) (b j) = 0) ∧ (∀ i, G (b i) (b i) ≠ 0) := by
  obtain ⟨r, hr, hrconj⟩ := exists_ne_zero_add_conjugation_eq_zero F E
  have hr' : κ r = -r := eq_neg_of_add_eq_zero_right hrconj
  let A := toAntihermitian G r hr' hG
  have hA : A.toBilin.SeparatingLeft := toAntihermitian_separating G r hr' hG hr hsep
  have hwA : A w w ≠ 0 := mul_ne_zero hr hw
  let Z := A.orthogonalLine w
  let e := A.splitLine w hwA
  have hZ : Module.finrank E Z = 2 := by
    have h := e.finrank_eq
    simp only [Module.finrank_prod, Module.finrank_self, hV] at h
    change 1 + Module.finrank E Z = 3 at h
    omega
  obtain ⟨t, ht⟩ := exists_conjugation_ne F E
  obtain ⟨b, hb, hd⟩ := AntihermitianForm.orthogonalBasis F E τ Z (A.pullback Z.subtype) ⟨t, ht⟩
    (A.orthogonalLine_separatingLeft hA w hwA)
  let c := b.reindex (finCongr hZ)
  let d := ((Module.Basis.singleton (Fin 1) E).prod c).map e
  let p : Fin 1 ⊕ Fin 2 ≃ Fin 3 := finSumFinEquiv
  have hleft (i : Fin 1) : d (Sum.inl i) = w := by simp [d, e, Z]
  have hright (i : Fin 2) : d (Sum.inr i) = (c i : V) := by simp [d, e, Z]
  have hrleft (i : Fin 2) : G (c i) w = 0 := by
    have h : A (c i) w = 0 := (c i).property
    exact (mul_eq_zero.mp h).resolve_left hr
  have hb' (i j : Fin 2) (hij : i ≠ j) : G (c i) (c j) = 0 := by
    have h := hb ((finCongr hZ).symm i) ((finCongr hZ).symm j) ((finCongr hZ).symm.injective.ne hij)
    have h' : r * G (c i) (c j) = 0 := by
      simp only [c, Module.Basis.reindex_apply]
      exact h
    exact (mul_eq_zero.mp h').resolve_left hr
  have hd' (i : Fin 2) : G (c i) (c i) ≠ 0 := by
    intro hi
    apply hd ((finCongr hZ).symm i)
    have h : r * G (c i) (c i) = 0 := by rw [hi, mul_zero]
    change r * G (b ((finCongr hZ).symm i)) (b ((finCongr hZ).symm i)) = 0
    simpa only [c, Module.Basis.reindex_apply] using h
  refine ⟨d.reindex p, ?_, ?_, ?_⟩
  · rw [Module.Basis.reindex_apply, show p.symm 0 = Sum.inl 0 by decide, hleft]
  · intro i j hij
    obtain ⟨i, rfl⟩ := p.surjective i
    obtain ⟨j, rfl⟩ := p.surjective j
    have hn : i ≠ j := fun h => hij (congrArg p h)
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, p.symm_apply_apply, p.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · exact (hn (congrArg Sum.inl (Subsingleton.elim i j))).elim
    · rw [hleft, hright, ← hG, hrleft, map_zero]
    · rw [hright, hleft, hrleft]
    · rw [hright, hright]
      exact hb' i j (fun h => hn (congrArg Sum.inr h))
  · intro i
    obtain ⟨i, rfl⟩ := p.surjective i
    rw [Module.Basis.reindex_apply, p.symm_apply_apply]
    rcases i with i | i
    · rw [hleft]
      exact hw
    · rw [hright]
      exact hd' i

/-- A rank-three separating Hermitian pairing which represents negative its
  Gram determinant times `d` admits an orthogonal pair with opposite weighted values. -/
def RankThreeHermitianValueStatement : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (V : Type v) [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
    (G : V →ₗ[E] (V →ₛₗ[(SU3Root.conjugation F E).toRingHom] E))
    (b : Module.Basis (Fin 3) E V),
    (∀ x y, SU3Root.conjugation F E (G x y) = G y x) →
    (∀ x, (∀ y, G x y = 0) → x = 0) →
    ∀ d : E, d ≠ 0 → (gram G b).det ≠ 0 →
    ∀ w : V, G w w = -(gram G b).det * d →
    ∃ u v : V, v ≠ 0 ∧ G u v = 0 ∧ G u u + d * G v v = 0

/-- Split off the vector of prescribed value and rescale a basis vector of its
  binary orthogonal complement using the determinant of the basis change. -/
theorem rankThreeHermitianValue : RankThreeHermitianValueStatement.{u,v} := by
  intro F E _ _ _ _ _ V _ _ _ _ G b hG hsep d hd hdet w hw
  let : FiniteDimensional E V := Module.Finite.of_basis b
  have hV : Module.finrank E V = 3 := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hw0 : G w w ≠ 0 := by rw [hw]; exact mul_ne_zero (neg_ne_zero.mpr hdet) hd
  obtain ⟨c, hc, horth, hvals⟩ := exists_orthogonalBasis_from_vector G hV hG hsep w hw0
  let a := G (c 1) (c 1)
  let β := G (c 2) (c 2)
  let p := (b.toMatrix c).det
  let ρ := (gram G b).det
  have ha : a ≠ 0 := hvals 1
  have hdet' : (-ρ * d) * a * β = ρ * (p * SU3Root.conjugation F E p) := by
    have h := det_gram_change_basis G b c
    rw [det_gram_eq_prod G c horth, Fin.prod_univ_three, hc, hw] at h
    exact h
  have hnorm : p * SU3Root.conjugation F E p = -(d * a * β) := by
    apply mul_left_cancel₀ hdet
    calc
      ρ * (p * SU3Root.conjugation F E p) = (-ρ * d) * a * β := hdet'.symm
      _ = ρ * -(d * a * β) := by ring
  refine ⟨(p / a) • c 1, c 2, c.ne_zero 2, ?_, ?_⟩
  · rw [G.map_smul, LinearMap.smul_apply, horth 1 2 (by decide), smul_zero]
  · have hak : SU3Root.conjugation F E a = a := hG (c 1) (c 1)
    rw [G.map_smul, LinearMap.smul_apply, (G (c 1)).map_smulₛₗ]
    change (p / a) * (SU3Root.conjugation F E (p / a) * a) + d * β = 0
    rw [map_div₀, hak, div_mul_cancel₀ _ ha, div_mul_eq_mul_div, hnorm,
      show -(d * a * β) = -(d * β) * a by ring, mul_div_cancel_right₀ _ ha, neg_add_cancel]

end Langlands.GroupScheme.Quaternionic.HermitianPairing
