import Langlands.Representation.Archimedean.ComplexExponentDeformation
import Langlands.Representation.Archimedean.ComplexStandardUnlinkedSwapReduction
import Langlands.Representation.Archimedean.ComplexGLTwoUnlinkedIrreducibleProof

/-! # Affine deformation of an adjacent complex swap -/

noncomputable section

open scoped Matrix TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexExponentDeformation

open Langlands.LocalFactor.Archimedean

private abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Shifts of the exponent of `d` for which the two exponents have different imaginary parts. -/
def swapParameters (d e : ComplexCharacterData) : Set ℂ :=
  {z | z.im ≠ e.exponent.im - d.exponent.im}

theorem swapParameters_infinite (d e : ComplexCharacterData) : (swapParameters d e).Infinite := by
  let c : ℝ := e.exponent.im - d.exponent.im
  let f (j : ℕ) : ℂ := (j : ℂ) + (↑(c + 1) : ℂ) * Complex.I
  have hf : Function.Injective f := by
    intro a b hab
    have h : (a : ℂ) = (b : ℂ) := add_right_cancel hab
    exact_mod_cast h
  apply (Set.infinite_range_of_injective hf).mono
  rintro _ ⟨j, rfl⟩
  change (f j).im ≠ c
  simp only [f, Complex.add_im, Complex.natCast_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.ofReal_im, zero_mul, add_zero, zero_add]
  linarith

private theorem unlinked_shift {d e : ComplexCharacterData} {z : ℂ}
    (hz : z ∈ swapParameters d e) : ¬ IsComplexLinked (shiftCharacter d z) e := by
  rintro ⟨p, _, _, hp, _⟩
  have him := congrArg Complex.im hp
  simp only [shiftCharacter, ComplexBlock.twist, characterOfParams_exponent, characterOfParams_weight,
    Complex.sub_im, Complex.add_im, Complex.div_ofNat_im, Complex.intCast_im, zero_div,
    add_zero] at him
  exact hz (by linarith)

private theorem exists_shiftEquiv {n : ℕ} {ds es : List ComplexCharacterData}
    (hds : ds.length = n) (p : Fin n) (z : ℂ) (he : shiftAt ds p z = es) :
    ∃ E : KF n ds ≃ₗ[ℂ] KF n es,
      (∀ k f, E (complexStandardRep n ds k f) = complexStandardRep n es k (E f)) ∧
      ∀ (X : Mat n) f,
        E ((complexStandardLie n ds (1 ⊗ₜ X) + z •
          (transportedDerivative ds hds p 1 X - complexStandardLie n ds (1 ⊗ₜ X))) f) =
            complexStandardLie n es (1 ⊗ₜ X) (E f) := by
  subst es
  refine ⟨shiftEquiv ds hds p z, shiftEquiv_rep hds p z, fun X f => ?_⟩
  rw [← transportedDerivative_affine hds p z X]
  simp [transportedDerivative]

/-- After identification of the compact spaces, the two adjacent orders give affine Lie
families with the original Lie operators at zero. At every parameter in `swapParameters`,
there is an equivalence intertwining the compact actions and both deformed Lie actions. -/
theorem exists_affine_swap (n : ℕ) (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (hn : (pre ++ d :: e :: post).length = n) :
    ∃ (D : Mat n → Module.End ℂ (KF n (pre ++ e :: d :: post)))
      (D' : Mat n → Module.End ℂ (KF n (pre ++ d :: e :: post))),
      ∀ z ∈ swapParameters d e, ∃ T : KF n (pre ++ e :: d :: post) ≃ₗ[ℂ]
          KF n (pre ++ d :: e :: post),
        (∀ k f, T (complexStandardRep n (pre ++ e :: d :: post) k f) =
          complexStandardRep n (pre ++ d :: e :: post) k (T f)) ∧
        ∀ (X : Mat n) f,
          T ((complexStandardLie n (pre ++ e :: d :: post) (1 ⊗ₜ X) + z • D X) f) =
            (complexStandardLie n (pre ++ d :: e :: post) (1 ⊗ₜ X) + z • D' X) (T f) := by
  let ds := pre ++ d :: e :: post
  let es := pre ++ e :: d :: post
  have hes : es.length = n := (ComplexPermutation.length_swap pre post d e).trans hn
  have hp : pre.length + 2 ≤ n := by
    rw [← hn, List.length_append, List.length_cons, List.length_cons]
    omega
  let p : Fin n := ⟨pre.length, by omega⟩
  let q : Fin n := ⟨pre.length + 1, by omega⟩
  refine ⟨fun X => transportedDerivative es hes q 1 X - complexStandardLie n es (1 ⊗ₜ X),
    fun X => transportedDerivative ds hn p 1 X - complexStandardLie n ds (1 ⊗ₜ X), ?_⟩
  intro z hz
  have hd : shiftAt ds p z = pre ++ shiftCharacter d z :: e :: post :=
    shiftAt_append_cons pre (e :: post) d z
  have he : shiftAt es q z = pre ++ e :: shiftCharacter d z :: post := by
    simpa only [es, q, List.append_assoc, List.singleton_append, List.length_append,
      List.length_singleton] using shiftAt_append_cons (pre ++ [e]) post d z
  have hnz : (pre ++ shiftCharacter d z :: e :: post).length = n := by
    rw [← hd, length_shiftAt]
    exact hn
  obtain ⟨A, hA, hAK, hAL⟩ := complexStandardUnlinkedSwapReduction
    complexGLTwoUnlinkedIrreducible n pre post (shiftCharacter d z) e hnz (unlinked_shift hz)
  obtain ⟨E₁, hE₁K, hE₁L⟩ := exists_shiftEquiv hes q z he
  obtain ⟨E₂, hE₂K, hE₂L⟩ := exists_shiftEquiv hn p z hd
  let T := E₁.trans ((LinearEquiv.ofBijective A hA).trans E₂.symm)
  have hAi : IsComplexStandardIntertwining n
      (complexStandardRep n (pre ++ shiftCharacter d z :: e :: post))
      (complexStandardLie n (pre ++ shiftCharacter d z :: e :: post))
      (pre ++ e :: shiftCharacter d z :: post) A := ⟨hAK, hAL⟩
  change ∃ T : KF n es ≃ₗ[ℂ] KF n ds, _
  refine ⟨T, fun k f => E₂.injective ?_, fun X f => E₂.injective ?_⟩
  · rw [hE₂K]
    simp only [T, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.ofBijective_apply]
    rw [hE₁K, hAi.map_rep]
  · rw [hE₂L]
    simp only [T, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.ofBijective_apply]
    rw [hE₁L, hAi.map_lie]

end Langlands.Archimedean.ComplexExponentDeformation
