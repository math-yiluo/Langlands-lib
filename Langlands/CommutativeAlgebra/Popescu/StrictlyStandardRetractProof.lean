import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardRetractStatement
import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardCriterion
import Langlands.CommutativeAlgebra.Popescu.ConormalSection
import Langlands.CommutativeAlgebra.Popescu.SymRetractConormal

/-! # Proof of Stacks Lemmas 3.1 and 3.7(e): smooth elements become strictly standard -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open MvPolynomial SymRetract

namespace SymRetract

variable {R : Type*} [CommRing R] {n m : ℕ}
  (I : Ideal (MvPolynomial (Fin n) R)) (F : Fin m → MvPolynomial (Fin n) R)
  (P : Matrix (Fin n) (Fin m) (MvPolynomial (Fin n) R)) (u : MvPolynomial (Fin n) R)
  (Θ : Fin m → Fin m → Fin m → MvPolynomial (Fin n) R)

theorem Hk_mem (hFI : ∀ k, F k ∈ I) (hE1 : ∀ k, u * F k - ∑ l, Et F P k l * F l ∈ I ^ 2)
    (k : Fin m) : Hk F P u Θ k ∈ symIdeal I F := by
  rw [← qC_eq_zero_iff]
  simp [Hk, map_add, map_sub, map_mul, map_sum, qC_F I F hFI, qC_Gk I F P u hE1]

/-- The quotient map `R[x, y] → C` as an algebra map. -/
noncomputable def qCₐ : MvPolynomial (Fin (n + m)) R →ₐ[R] SymAlg I F :=
  Ideal.Quotient.mkₐ R (symIdeal I F)

theorem qCₐ_apply (x : MvPolynomial (Fin (n + m)) R) : qCₐ I F x = qC I F x := rfl

theorem qCₐ_surjective : Function.Surjective (qCₐ I F) :=
  Ideal.Quotient.mkₐ_surjective R _

theorem ker_qCₐ : RingHom.ker (qCₐ I F) = symIdeal I F := Ideal.Quotient.mkₐ_ker R _

end SymRetract

/-- Stacks Lemma 3.1 (07CE) together with Lemma 3.7(e) (07EZ): the symmetric algebra
`C = Sym_B(I/I²)` is a retract of `B` in which every element `a` with `B_a` smooth has a strictly
standard power. -/
theorem strictlyStandardRetract : StrictlyStandardRetractStatement.{u} := by
  intro R B _ _ _ _ _
  classical
  obtain ⟨n, φ, hφ, hfg⟩ := Algebra.FinitePresentation.out (R := R) (A := B)
  obtain ⟨m, F, hF⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  have hker : RingHom.ker φ = Ideal.span (Set.range F) := hF.symm
  set I := RingHom.ker φ
  have hFI : ∀ k, F k ∈ I := fun k => by rw [hker]; exact Ideal.subset_span ⟨k, rfl⟩
  have hIF : I ≤ Ideal.span (Set.range F) := hker.le
  -- the algebra `C`
  have hJfg : (symIdeal I F).FG := IsNoetherian.noetherian _
  have : Algebra.FinitePresentation R (SymAlg I F) :=
    show Algebra.FinitePresentation R (MvPolynomial (Fin (n + m)) R ⧸ symIdeal I F) from
      Algebra.FinitePresentation.quotient hJfg
  -- the maps `g : B → C` and `r : C → B`
  let ψ : MvPolynomial (Fin n) R →ₐ[R] SymAlg I F := (qCₐ I F).comp (ιx (m := m))
  have hψ : RingHom.ker φ.toRingHom ≤ RingHom.ker ψ.toRingHom := by
    intro p hp
    rw [RingHom.mem_ker]
    change qC I F (ιx p) = 0
    exact (qC_eq_zero_iff I F _).mpr (ιx_mem_symIdeal I F hp)
  let g : B →ₐ[R] SymAlg I F := AlgHom.liftOfSurjective φ hφ ψ hψ
  have hg : ∀ p, g (φ p) = qC I F (ιx p) := fun p => AlgHom.liftOfSurjective_apply φ hφ ψ hψ p
  let v : Fin (n + m) → B := Fin.append (fun i => φ (X i)) (fun _ => 0)
  have hvx : ∀ p : MvPolynomial (Fin n) R, aeval v (ιx (m := m) p) = φ p := by
    intro p
    rw [aeval_rename]
    have : v ∘ Fin.castAdd m = fun i => φ (X i) := by
      funext i; simp [v]
    rw [this]
    conv_rhs => rw [MvPolynomial.aeval_unique φ]
    rfl
  have hvy : ∀ j : Fin m, aeval v (yv (n := n) (R := R) j) = 0 := by
    intro j; simp [yv, v]
  have hJr : symIdeal I F ≤ RingHom.ker (aeval v : MvPolynomial (Fin (n + m)) R →ₐ[R] B) := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker, hvx]
      exact hp
    · rw [Ideal.span_le]
      rintro _ ⟨κ, -, rfl⟩
      simp [symGen, hvy]
  let r : SymAlg I F →ₐ[R] B := Ideal.Quotient.liftₐ (symIdeal I F) (aeval v) hJr
  have hr : ∀ x, r (qC I F x) = aeval v x := fun x => rfl
  refine ⟨SymAlg I F, inferInstance, inferInstance, inferInstance, g, r, ?_, ?_⟩
  · apply AlgHom.ext
    intro b
    obtain ⟨p, rfl⟩ := hφ b
    rw [AlgHom.comp_apply, hg, hr, hvx, AlgHom.id_apply]
  -- the strictly standard powers
  intro a ha
  obtain ⟨h, rfl⟩ := hφ a
  obtain ⟨t, P, hP⟩ := exists_conormal_section φ hφ F hker h
  set u := h ^ t
  have hE1 : ∀ k, u * F k - ∑ l, Et F P k l * F l ∈ I ^ 2 := hP
  have hΘ' : ∀ k j, ∃ θ : Fin m → MvPolynomial (Fin n) R,
      Et F P k j * u - ∑ l, Et F P k l * Et F P l j = ∑ p, θ p * F p := by
    intro k j
    obtain ⟨θ, hθ⟩ := Ideal.mem_span_range_iff_exists_fun.mp
      (hIF (Et_sq_sub F P I u hFI hE1 k j))
    exact ⟨θ, hθ.symm⟩
  choose Θ hΘ using hΘ'
  -- generators of `J`
  obtain ⟨M, Fg, hFg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJfg
  have hkerC : RingHom.ker (qCₐ I F) = Ideal.span (Set.range Fg) := by
    rw [ker_qCₐ]; exact hFg.symm
  have hs : ∀ j, ιx u ^ 8 * Fg j ∈
      Ideal.span (Set.range (Hk F P u Θ)) ⊔ RingHom.ker (qCₐ I F) ^ 2 := by
    intro j
    rw [ker_qCₐ]
    have : Fg j ∈ symIdeal I F := by rw [← hFg]; exact Ideal.subset_span ⟨j, rfl⟩
    exact u8_mem I F P u Θ hFI hIF hE1 hΘ this
  have hΨ : Matrix.of (fun k i => qCₐ I F (pderiv i (Hk F P u Θ k))) * ΨC I F P u =
      uC I F u ^ 5 • (1 : Matrix (Fin m) (Fin m) (SymAlg I F)) :=
    JC_mul_ΨC I F P u Θ hFI hE1 hΘ
  have hstd := isStrictlyStandard_of_conormal (qCₐ I F) (qCₐ_surjective I F) Fg hkerC
    (Hk F P u Θ) (fun k => by rw [ker_qCₐ]; exact Hk_mem I F P u Θ hFI hE1 k)
    (Nat.le_add_left m n) (ιx u ^ 8) hs (ΨC I F P u) (uC I F u ^ 5) hΨ
  refine ⟨8 * t + 5 * t * m, ?_⟩
  have heq : g (φ h) ^ (8 * t + 5 * t * m) =
      qCₐ I F (ιx u ^ 8) * (uC I F u ^ 5) ^ m := by
    rw [hg, qCₐ_apply, uC, map_pow, map_pow, map_pow, ← pow_mul, ← pow_mul, ← pow_mul,
      ← pow_add]
    ring_nf
  rw [heq]
  exact hstd

end Langlands.CommutativeAlgebra.Popescu
