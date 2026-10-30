# Proof of the norm laws on the base change of a finite field extension

`Langlands.Algebra.tensorFiniteExtensionNorm.{u}` proves the Library
proposition `Langlands.Algebra.TensorFiniteExtensionNormStatement.{u}`,
imported from `Langlands.Algebra.TensorFiniteExtensionNormStatement`. Its type
is exactly that closed proposition, with the single universe level `u`. The
statement pair is unchanged.

Worker 928 wrote this proof. The algebraic lemmas it reuses were published
earlier in `Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNormProof`.

## Statement proved

Let `K L : Type u` be fields with `[Algebra K L]` and `[FiniteDimensional K L]`,
and let `A : Type u` be any commutative `K`-algebra, possibly the zero ring.
Write `n = Module.finrank K L`. For Mathlib's `Algebra.norm A` on the
`A`-algebra `A ⊗[K] L`:

1. for every commutative `K`-algebra `B : Type u`, every `φ : A →ₐ[K] B` and
   every `f : A ⊗[K] L`,
   `φ (Algebra.norm A f) = Algebra.norm B (Algebra.TensorProduct.map φ (AlgHom.id K L) f)`;
2. for every `a : A`, `Algebra.norm A (algebraMap A (A ⊗[K] L) a) = a ^ n`;
3. for every `f : A ⊗[K] L` and every `p : PrimeSpectrum A`,
   `Algebra.norm A f ∉ p.asIdeal` holds iff `f ∉ q.asIdeal` for every
   `q : PrimeSpectrum (A ⊗[K] L)` with
   `PrimeSpectrum.comap (algebraMap A (A ⊗[K] L)) q = p`.

## Reused lemmas

The proof opens the namespace
`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNorm` and uses three
published theorems from it. All three are stated for commutative rings and an
algebra `B` over `A` with a basis indexed by a finite type `ι`:

- `norm_map_of_basis b b' σ φ hφ hb f`: let `b` be an `A`-basis of `B` and
  `b'` an `A'`-basis of `B'`. Let `σ : A →+* A'` and `φ : B →+* B'` be ring maps
  with `φ (algebraMap A B a) = algebraMap A' B' (σ a)` for every `a` and
  `φ (b i) = b' i` for every `i`. Then
  `σ (Algebra.norm A f) = Algebra.norm A' (φ f)`. The proof compares the
  determinant formulas `Algebra.norm_eq_matrix_det` in the two bases.
- `norm_mem_comap b f Q hf`: if `f ∈ Q` for an ideal `Q` of `B`, then
  `Algebra.norm A f ∈ Q.comap (algebraMap A B)`. It holds because `f` divides
  the image of its norm in `B`, which is the Cayley–Hamilton argument.
- `exists_prime_over_of_norm_mem b f P hf`: if `P` is a prime of `A` and
  `Algebra.norm A f ∈ P`, then some prime `Q` of `B` lies over `P` and contains
  `f`. Its proof applies going up for the integral extension `B / A` to the
  ideal `span {f}`.

## Proof

Fix `K`, `L` and `A`, and let `b := Module.finBasis K L`, a `K`-basis of `L`
indexed by `Fin n`. For every commutative `K`-algebra `C`, Mathlib's
`Algebra.TensorProduct.basis C b` is the `C`-basis of `C ⊗[K] L` with
`i ↦ 1 ⊗ₜ b i` (`Algebra.TensorProduct.basis_apply`). It exists for every
`C`, including the zero ring.

1. **Base change.** Apply `norm_map_of_basis` with the bases
   `Algebra.TensorProduct.basis A b` and `Algebra.TensorProduct.basis B b`,
   with `σ := φ.toRingHom`, and with the ring map underlying
   `Algebra.TensorProduct.map φ (AlgHom.id K L)`. Both side conditions are
   closed by `simp`. The image of `algebraMap A (A ⊗[K] L) a = a ⊗ₜ 1` is
   `φ a ⊗ₜ 1` (`Algebra.TensorProduct.algebraMap_apply`). The image of
   `1 ⊗ₜ b i` is `φ 1 ⊗ₜ b i = 1 ⊗ₜ b i`.
2. **Degree.** Mathlib's `Algebra.norm_algebraMap_of_basis` with the basis
   `Algebra.TensorProduct.basis A b` gives
   `Algebra.norm A (algebraMap A (A ⊗[K] L) a) = a ^ Fintype.card (Fin n)`.
   `Fintype.card_fin` turns the exponent into `n = Module.finrank K L`. This
   route does not go through `Module.finrank A (A ⊗[K] L)`, so it is uniform
   in `A`.
3. **Fibre support.**
   - (`→`) Suppose `Algebra.norm A f ∉ p.asIdeal`, and let `q` lie over `p`
     with `f ∈ q.asIdeal`. Rewriting `p` as the contraction of `q`,
     `norm_mem_comap` puts the norm in `p.asIdeal`, a contradiction.
   - (`←`) Suppose `f` lies in no prime over `p`, and suppose
     `Algebra.norm A f ∈ p.asIdeal`. Then `exists_prime_over_of_norm_mem`
     gives a prime `Q` with `Q.comap (algebraMap A (A ⊗[K] L)) = p.asIdeal`
     and `f ∈ Q`. The point `⟨Q, _⟩` of `PrimeSpectrum (A ⊗[K] L)` lies over
     `p` (`PrimeSpectrum.ext`), which contradicts the hypothesis.

No separability, reducedness, domain, noetherianity or nontriviality
assumption on `A` is used. The proof uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Route compared with the source

The statement's Markdown motivates these laws by Stacks Project Lemma 31.18.6
(tag 0BD2), where the norm is the determinant of multiplication in a local
basis. This proof follows the same determinant idea for clauses 1 and 2. For
clause 3 it does not base change to residue fields as the source does.
Instead it uses divisibility of the norm (direction `→`) and going up for the
integral extension `A → A ⊗[K] L` (direction `←`).
