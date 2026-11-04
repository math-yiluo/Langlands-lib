import Langlands.GroupScheme.Rational.TorusVectorLinearization.PointActionInstance
import Langlands.GroupScheme.Rational.TorusVectorLinearization.CharacteristicSplit

/-! # Torus linearization from the linearization of abstract point actions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorusLinearization

/-- If a point pulls the new coordinates `Φ` back to `B`-linear combinations of
themselves, then the action read in the coordinates `Φ` (with inverse `Q`) commutes
with scalars. -/
theorem PointAction.act_smul_of_pull_eq_sum {k K : Type u} [Field k] [Field K] [Algebra k K]
    {I : Type u} {n : ℕ} (a : PointAction k K I n) (Φ Q : Fin n → MvPolynomial (Fin n) k)
    (hQΦ : ∀ i, aeval Q (Φ i) = X i) {B : Type u} [CommRing B] [Algebra k B] (t : a.Pt B)
    (b : Fin n → Fin n → B)
    (hb : ∀ i, a.pull t (Φ i) = ∑ j, b i j • MvPolynomial.map (algebraMap k B) (Φ j))
    (c : B) (y : Fin n → B) :
    (fun i => aeval (a.act t (fun j => aeval (c • y) (Q j))) (Φ i)) =
      c • fun i => aeval (a.act t (fun j => aeval y (Q j))) (Φ i) := by
  have key : ∀ w : Fin n → B,
      (fun i => aeval (a.act t (fun j => aeval w (Q j))) (Φ i)) = fun i => ∑ j, b i j * w j := by
    intro w
    funext i
    rw [← a.aeval_pull, hb i, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, aeval_map_algebraMap, ← comp_aeval_apply, hQΦ, aeval_X, smul_eq_mul]
  rw [key, key]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end Langlands.GroupScheme.TorusLinearization

namespace Langlands.GroupScheme.RelativeRoot

open TorusLinearization

/-- Every torus action on a vector group is linear in suitable natural coordinates,
once every abstract point action in prime characteristic is linearized by mutually
inverse additive polynomials over the ground field. -/
theorem torusVectorActionLinearization_of_linearizing
    (hcore : ∀ (k K I : Type u) [Field k] [Field K] [Algebra k K] (p : ℕ) [Fact p.Prime]
      [CharP k p] [Finite I] (n : ℕ) (a : PointAction k K I n),
      ∃ Φ Q : Fin n → MvPolynomial (Fin n) k,
        (∀ i, IsAddPoly (Φ i)) ∧ (∀ j, aeval Φ (Q j) = X j) ∧ (∀ i, aeval Q (Φ i) = X i) ∧
        ∀ (B : Type u) [CommRing B] [Algebra k B] (t : a.Pt B),
          ∃ b : Fin n → Fin n → B,
            ∀ i, a.pull t (Φ i) = ∑ j, b i j • MvPolynomial.map (algebraMap k B) (Φ j)) :
    TorusVectorActionLinearizationStatement.{u} := by
  refine torusVectorActionLinearization_of_charP ?_
  intro k _ p _ _ T V n hT hV a
  obtain ⟨e, he⟩ := hV
  obtain ⟨K, _, _, I, _, ⟨s⟩⟩ := hT
  obtain ⟨Φ, Q, hΦ, hΦQ, hQΦ, hmat⟩ := hcore k K I p n (torusPointAction s a he)
  refine exists_isAffineLinear_of_polynomials he Φ Q hΦ hQΦ hΦQ ?_
  intro B _ _ t c y
  obtain ⟨b, hb⟩ := hmat B t
  exact (torusPointAction s a he).act_smul_of_pull_eq_sum Φ Q hQΦ t b hb c y

end Langlands.GroupScheme.RelativeRoot
