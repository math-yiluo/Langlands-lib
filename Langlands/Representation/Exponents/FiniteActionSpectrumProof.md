# Proof of the finite spectrum of a commutative action with finite operator span

Author: Worker 23.

The theorem `Langlands.finiteActionCommutativeSpectrum` has the complete
unapplied type `Langlands.FiniteActionCommutativeSpectrumStatement.{uA,uV}`,
imported from `Langlands.Representation.Exponents.FiniteActionSpectrumStatement`.
It adds no hypotheses. The group universe `uA` and the carrier universe `uV`
stay independent. The zero vector space and the trivial group are covered by
the same argument. For `V = 0` the operator algebra is the zero algebra; it has
no characters, every vector is zero, and all three clauses hold.

The proof is project-internal algebra. It uses the standard structure of a
finite-dimensional commutative algebra over `ℂ`: it is Artinian, it has finitely
many characters, and its Jacobson radical is nilpotent. These facts come from
Mathlib. Finite dimensionality is used only for the algebra of operators, never
for the carrier `V`.

## Finite-dimensional commutative algebras

The section `Algebra` of namespace `Langlands.FiniteActionSpectrum` works with a
commutative ring `R` that is a finite-dimensional `ℂ`-algebra. A *character* is
an algebra homomorphism `φ : R →ₐ[ℂ] ℂ`.

- `exists_algHom_ker_eq`: every maximal ideal `m` is the kernel of a character.
  The quotient `R ⧸ m` is finite dimensional over `ℂ`, hence integral over `ℂ`.
  Since `ℂ` is algebraically closed, `algebraMap ℂ (R ⧸ m)` is bijective
  (`IsAlgClosed.algebraMap_bijective_of_isIntegral`). The inverse of this
  bijection, composed with the quotient map, is a character with kernel `m`.
- `algHom_eq_of_ker_eq`: two characters with the same kernel are equal. For
  every `x`, the element `x - algebraMap ℂ R (φ x)` lies in `ker φ = ker ψ`, so `ψ x = φ x`.
  This lemma does not use finite dimensionality.
- `finite_algHom`: there are finitely many characters. The ring `R` is Artinian
  (`IsArtinianRing.of_finite`), so it has finitely many maximal ideals
  (`IsArtinianRing.setOfPred_isMaximal_finite`). The kernel of a character is
  maximal because the character is surjective. By `algHom_eq_of_ker_eq`, the
  map `φ ↦ ker φ` into the maximal ideals is injective.
- `exists_separating`: for distinct characters `φ ≠ ψ` there is `r` with
  `φ r = 1` and `ψ r = 0`. Choose `s` with `φ s ≠ ψ s` and put
  `r = (φ s - ψ s)⁻¹ • (s - algebraMap ℂ R (ψ s))`. This lemma does not use finite
  dimensionality.
- `exists_decomposition`: assuming a `Fintype` instance on the characters, there
  are `N : ℕ` and elements `h φ`, one for each character `φ`, such that
  `∑ φ, h φ` is a unit and `y * h φ = 0` for every `y ∈ (ker φ) ^ N`.

  Proof of `exists_decomposition`. Let `J` be the intersection of all character
  kernels. By `exists_algHom_ker_eq`, every maximal ideal is a character kernel,
  so `J` lies in the Jacobson radical `jacobson ⊥`. The Jacobson radical of an
  Artinian ring is nilpotent (`IsArtinianRing.isNilpotent_jacobson_bot`). Choose
  `N₀` with `(jacobson ⊥) ^ N₀ = 0`; then also `(jacobson ⊥) ^ (N₀ + 1) = ⊥`.
  For each character `φ`, let `g φ` be the product, over the characters `ψ ≠ φ`,
  of the separating elements of `exists_separating` with value `1` at `φ` and
  `0` at `ψ`. Then `φ (g φ) = 1` and `ψ (g φ) = 0` for `ψ ≠ φ`. Put
  `h φ = g φ ^ (N₀ + 1)` and `N = N₀ + 1`.

  Every character `ψ` sends `∑ φ, h φ - 1` to `1 - 1 = 0`. So this element lies
  in `J`, hence in the Jacobson radical, and `∑ φ, h φ = 1 + (∑ φ, h φ - 1)` is
  a unit (`Ideal.mem_jacobson_bot`). For the annihilation, the ideal product
  `ker φ * span {g φ}` lies in `J`. Indeed, `φ` kills the first factor and every
  `ψ ≠ φ` kills `g φ`. Hence for `y ∈ (ker φ) ^ N` the product
  `y * g φ ^ N = y * h φ` lies in `(ker φ * span {g φ}) ^ N`. That ideal is
  contained in `(jacobson ⊥) ^ (N₀ + 1) = ⊥`, so `y * h φ = 0`.

## The spectrum of an action through such an algebra

The section `Representation` considers a commutative group `A`, a complex
vector space `V` and a commutative `ℂ`-algebra `R`.

- `algebraCharacter ρ' φ : A →* ℂˣ` is the character `a ↦ φ (ρ' a)` for a monoid
  homomorphism `ρ' : A →* R` and a character `φ` of `R`. Its values are units
  because `A` is a group (`MonoidHom.toHomUnits`); `algebraCharacter_apply`
  records the value.
- `eq_zero_of_pow_sub_smul`: if `(T - α • 1) ^ k` and `(T - β • 1) ^ l` both kill
  `w` and `α ≠ β`, then `w = 0`. This is the disjointness of distinct
  generalized eigenspaces of one operator (`Module.End.disjoint_genEigenspace`).
- `subrepresentation_mem_bot_iff` and `subrepresentation_exists_ne_zero` are
  small facts about the zero subrepresentation: its only vector is `0`, and a
  nonzero subrepresentation contains a nonzero vector.

`spectrum_of_algebra` proves the three clauses of the statement for a
representation `ρ` of a topological commutative group `A` under these
hypotheses: an algebra homomorphism `ι : R →ₐ[ℂ] Module.End ℂ V` and a monoid
homomorphism `ρ' : A →* R` with `ι (ρ' a) = ρ a`, the span of the range of `ρ'`
is all of `R`, `ρ'` is locally constant, and `R` is finite dimensional. Write
`χ_φ = algebraCharacter ρ' φ`. Take `N`, `h` from `exists_decomposition` and let
`w` be the inverse of the unit `∑ φ, h φ`. The proof uses these steps.

1. Every `ι r` commutes with every `ρ a`, because `R` is commutative and
   `ρ a = ι (ρ' a)`. Hence `ι r` commutes with every power of `ρ a - c • 1`.
   Consequently every generalized component
   `generalizedCommutativeCharacterSpace ρ θ` is stable under each `ι r`.
2. `ρ a - χ_φ a • 1 = ι (ρ' a - algebraMap ℂ R (φ (ρ' a)))`, and
   `ρ' a - algebraMap ℂ R (φ (ρ' a))` lies in `ker φ`. Its `N`-th power lies in `(ker φ) ^ N` and so annihilates `h φ`.
   Therefore `(ρ a - χ_φ a • 1) ^ N (ι (h φ) v) = 0` for every `a` and every
   `v`: each vector `ι (h φ) v` lies in `commutativeCharacterSpace ρ χ_φ N`.
3. Every vector decomposes as `v = ∑ φ, ι (h φ) (ι w v)`, because
   `(∑ φ, h φ) * w = 1`.
4. Distinct characters `φ ≠ ψ` give distinct characters `χ_φ ≠ χ_ψ` of `A`. Two
   characters of `R` that agree on the range of `ρ'` agree on its span, which is
   `R` (`LinearMap.ext_on_range`).
5. If `v` lies in the generalized component of a character `θ` of `A` and
   `θ ≠ χ_ψ`, then `ι (h ψ) v = 0`. Choose `a` with `θ a ≠ χ_ψ a`. By step 1 the
   vector `ι (h ψ) v` is killed by a power of `ρ a - θ a • 1`; by step 2 it is
   killed by `(ρ a - χ_ψ a • 1) ^ N`. Apply `eq_zero_of_pow_sub_smul`.
6. Every character `θ` with `commutativeCharacterSpace ρ θ 1 ≠ ⊥` equals some
   `χ_φ`. Otherwise take a nonzero eigenvector `v`. It lies in the generalized
   component of `θ`, and so does `ι w v` by step 1. By steps 3 and 5,
   `v = ∑ ψ, ι (h ψ) (ι w v) = 0`, a contradiction.
7. Each `χ_φ` has open kernel. The kernel is the fibre over `1` of the locally
   constant function `φ ∘ ρ'`.
8. Let `t ≠ 0` be a vector killed by `ι y` for every `y ∈ (ker φ) ^ N`. Then
   `χ_φ` has a nonzero ordinary eigenvector. Take the least `j` such that `ι y`
   kills `t` for all `y ∈ (ker φ) ^ j` (`Nat.find`). Here `j ≠ 0`, since
   `(ker φ) ^ 0` contains `1` and `t ≠ 0`. Write `j = i + 1`. By minimality
   there is `y ∈ (ker φ) ^ i` with `e = ι y t ≠ 0`. For every `a`, the product
   `(ρ' a - algebraMap ℂ R (φ (ρ' a))) * y` lies in `(ker φ) ^ (i + 1)`, so it kills `t`. By
   step 2 this says `(ρ a - χ_φ a • 1) e = 0`, that is `ρ a e = χ_φ a • e`.

The three clauses then follow.

- Finiteness: by step 6, the occurring characters lie in the range of
  `φ ↦ χ_φ`, a function on the finite type of characters of `R`.
- Uniform index: an occurring character is some `χ_φ` by step 6. Let `v` lie in
  its generalized component. By steps 3, 4 and 5, every term of the
  decomposition except the `φ`-term vanishes, so `v = ι (h φ) (ι w v)`. By
  step 2, `v ∈ commutativeCharacterSpace ρ χ_φ N`. The published criterion
  `commutativeCharacterNilpotenceIndex_le_iff` gives
  `commutativeCharacterNilpotenceIndex ρ χ_φ ≤ N`, so the index is `< ⊤`.
- Spanning: decompose an arbitrary `v` as in step 3. A zero term lies in every
  submodule. A nonzero term `t = ι (h φ) (ι w v)` lies in the generalized
  component of `χ_φ` by step 2. The character `χ_φ` occurs. Its kernel is open
  by step 7. It has a nonzero ordinary eigenspace by step 8, because `ι y t = 0`
  for every `y ∈ (ker φ) ^ N` by `exists_decomposition`. So `t` lies in the
  supremum, and so does `v`.

## The main theorem

`Langlands.finiteActionCommutativeSpectrum` reduces the statement to
`spectrum_of_algebra`. Let `S = Submodule.span ℂ (Set.range ρ)` inside
`Module.End ℂ V`. It contains every `ρ a` and the identity `ρ 1`. Two
`Submodule.span_induction` arguments show that `S` is closed under
multiplication and that any two elements of `S` commute. The first proves
`ρ a * x ∈ S` and `x * ρ a = ρ a * x` for `x ∈ S`, using
`ρ a * ρ b = ρ (a * b) = ρ (b * a)` in the commutative group `A`. The second
extends this to products `x * y` of arbitrary elements of `S`.

Hence `B = S.toSubalgebra` is a subalgebra of `Module.End ℂ V`, with a
commutative ring structure given by this commutativity. Its underlying
submodule is `S`, which is finite dimensional by hypothesis 1, so
`Module.Finite ℂ B`. The corestriction `ρ' = ρ.codRestrict B` satisfies
`B.val (ρ' a) = ρ a`. The span of its range is all of `B`, by span induction on
the elements of `S`. It is locally constant, because composing it with the
injective inclusion `Subtype.val` gives the locally constant map `ρ` of
hypothesis 2 (`IsLocallyConstant.desc`). `spectrum_of_algebra`, applied with
`ι = B.val`, gives the three clauses.

The theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
