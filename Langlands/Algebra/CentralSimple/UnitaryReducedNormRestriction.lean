import Langlands.Algebra.ReducedNormSubfield
import Langlands.Algebra.ReducedNormRegular
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Restriction of reduced norm to a maximal subfield after scalar extension -/

noncomputable section

open scoped TensorProduct

namespace Langlands.CentralSimple

universe u

private theorem tensor_law_eq {K A : Type u} [Field K] [Infinite K] [Ring A] [Algebra K A]
    [FiniteDimensional K A]
    (f g : ∀ (R : Type u) [CommRing R] [Algebra K R], R ⊗[K] A → R)
    (hf : ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
      (φ : R →ₐ[K] S) (x : R ⊗[K] A),
      f S (Algebra.TensorProduct.map φ (AlgHom.id K A) x) = φ (f R x))
    (hg : ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
      (φ : R →ₐ[K] S) (x : R ⊗[K] A),
      g S (Algebra.TensorProduct.map φ (AlgHom.id K A) x) = φ (g R x))
    (h : ∀ x : K ⊗[K] A, f K x = g K x)
    (R : Type u) [CommRing R] [Algebra K R] (x : R ⊗[K] A) : f R x = g R x := by
  classical
  let I := Fin (Module.finrank K A)
  let V := MvPolynomial I K
  let b := Module.finBasis K A
  let gen : V ⊗[K] A := ∑ i : I, MvPolynomial.X i ⊗ₜ[K] b i
  have hgen : f V gen = g V gen := by
    apply MvPolynomial.funext
    intro y
    rw [← MvPolynomial.aeval_eq_eval, ← hf, ← hg, h]
  let φ : V →ₐ[K] R := MvPolynomial.aeval ((b.baseChange R).repr x)
  have hx : Algebra.TensorProduct.map φ (AlgHom.id K A) gen = x := by
    simp only [gen, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    change ∑ i : I, (MvPolynomial.aeval ((b.baseChange R).repr x)) (MvPolynomial.X i) ⊗ₜ[K] b i = x
    simp only [MvPolynomial.aeval_X]
    exact Langlands.ReducedNorm.sum_coordinates_tmul b R x
  rw [← hx, hf, hg, hgen]

/-- The reduced norm on a maximal subfield is the determinant field norm after
any commutative change of coefficients. -/
theorem reducedNorm_eq_field_norm_tensor (K B : Type u) [Field K] [Infinite K]
    [Ring B] [Algebra K B] [FiniteDimensional K B] [Algebra.IsCentral K B] [IsSimpleRing B]
    {P : Type u} [Field P] [Algebra K P] [FiniteDimensional K P]
    (ε : P →ₐ[K] B) (hdeg : Module.finrank K P = reducedDegree K B)
    (R : Type u) [CommRing R] [Algebra K R] (x : R ⊗[K] P) :
    reducedNorm K B R (Algebra.TensorProduct.map (AlgHom.id K R) ε x) = Algebra.norm R x := by
  refine tensor_law_eq (fun S _ _ y =>
    reducedNorm K B S (Algebra.TensorProduct.map (AlgHom.id K S) ε y))
    (fun S _ _ y => Algebra.norm S y) ?_ (norm_baseChange_naturality (Module.finBasis K P)) ?_ R x
  · intro S T _ _ _ _ φ y
    rw [← reducedNorm_naturality]
    congr 1
    induction y using TensorProduct.inductionOn with
    | tmul s p => rfl
    | add y z hy hz => simp only [map_add, hy, hz]
  · intro y
    have hsurj : Function.Surjective (fun p : P => (1 : K) ⊗ₜ[K] p) :=
      (Algebra.TensorProduct.lid K P).symm.surjective
    obtain ⟨p, rfl⟩ := hsurj y
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      reducedNorm_eq_field_norm K B ε hdeg]
    simpa only [Algebra.TensorProduct.lid_tmul, one_smul] using
      Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.lid K P) ((1 : K) ⊗ₜ[K] p)

end Langlands.CentralSimple
