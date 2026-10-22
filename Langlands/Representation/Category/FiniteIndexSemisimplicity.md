# Semisimplicity ascends from a normal subgroup of finite index (proof)

Author: Worker 285. This module proves the published proposition
`Langlands.FiniteIndexSemisimplicityAscent` from
`Langlands.Representation.Category.FiniteIndexSemisimplicityStatement`.
That statement pair is imported unchanged.

## Closing theorem

`Langlands.finiteIndexSemisimplicityAscent :
FiniteIndexSemisimplicityAscent.{uR, uG, uV}`.

Its type is exactly the published proposition, with the same three independent
universes. It takes no hypotheses. The universally quantified data are
therefore those of the statement: a field `R` of characteristic zero, a group
`G`, an `R`-module `V`, a subgroup `H` with `[H.Normal]` and `[H.FiniteIndex]`,
and a representation `ρ : Representation R G V`. From
`Representation.IsSemisimpleRepresentation (ρ.comp H.subtype)` the theorem
concludes `Representation.IsSemisimpleRepresentation ρ`. Nothing else is
assumed: there is no topology, smoothness, finiteness of `G`, finite dimension
of `V`, irreducibility or finite length.

The proof does not use the instance `[H.Normal]`. The averaging argument below
works for any subgroup of finite index. The statement keeps the hypothesis, as
in the source, and the theorem proves exactly that statement.

## Source

I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group GL(n,F)
where F is a non-Archimedean local field*, Russian Math. Surveys 31:3 (1976),
1–68; registered source `bernstein-zelevinsky-1976-representations-gln`.
Lemma 2.9(a) and its proof are on printed page 17 (PDF page 17). The proof
takes coset representatives `g₁, …, g_l` of `G/H`. A `G`-submodule `E₁` has an
`H`-complement `E₁'`. With `A` the projection of `E` onto `E₁` along `E₁'`, it
sets `A₀ = (1/l) Σᵢ π(gᵢ) A π(gᵢ)⁻¹`. Then `A₀` projects `E` onto `E₁` and
commutes with `G`, so `Ker A₀` is a `G`-complement of `E₁`.

The Lean proof follows this argument over any field of characteristic zero
instead of `ℂ`. The only division is by the index `l`, and `l ≠ 0` in `R`
because `R` has characteristic zero and `H.FiniteIndex` holds.

## Helper declarations (namespace `Langlands.FiniteIndexSemisimplicity`)

- `isCompl_toSubmodule` and `isCompl_of_isCompl_toSubmodule`: two
  subrepresentations of a monoid representation are complementary exactly when
  their underlying submodules are. Both directions hold because Mathlib defines
  the meet, join, bottom and top of `Subrepresentation` from those of
  `Submodule`, and `Subrepresentation.toSubmodule_injective` holds.
- `conj ρ P g`: the linear endomorphism `ρ g ∘ P ∘ ρ g⁻¹` of `V`, for a linear
  endomorphism `P` and `g : G`. `conj_apply` unfolds it.
- `conj_mul_of_mem`: if `P (ρ h v) = ρ h (P v)` for all `h ∈ H` and all `v`,
  then `conj ρ P (g * h) = conj ρ P g` for `h ∈ H`. So the conjugate depends only
  on the left coset `gH`. The proof applies the hypothesis to `h⁻¹ ∈ H`.
- `conj_mul_apply`: `conj ρ P (x * g) v = ρ x (conj ρ P g (ρ x⁻¹ v))`.
- `cosetSum ρ H P`: for a `Fintype (G ⧸ H)` instance, the sum
  `Σ_{q : G ⧸ H} conj ρ P q.out`. Here `q.out` is Mathlib's chosen
  representative of the coset `q`. `cosetSum_apply` evaluates it at a vector.
- `cosetSum_apply_apply`: if `P` is `H`-equivariant as above, then
  `cosetSum ρ H P (ρ x v) = ρ x (cosetSum ρ H P v)` for every `x : G`. The proof
  writes `(x • q).out = x * q.out * h` with `h ∈ H`
  (`QuotientGroup.mk_out_eq_mul`), so `conj ρ P (x • q).out = conj ρ P
  (x * q.out)` by `conj_mul_of_mem`. It then reindexes the sum along the
  permutation `q ↦ x • q` of `G ⧸ H` (`Equiv.sum_comp`) and uses
  `conj_mul_apply`.

## Proof of the closing theorem

A `Fintype (G ⧸ H)` instance is chosen from Mathlib's
`Subgroup.finite_quotient_of_finiteIndex`. Let `W` be a subrepresentation of
`ρ`; the proof constructs a complementary subrepresentation.

1. **Restriction.** `W` is also a subrepresentation `W'` of `ρ.comp H.subtype`,
   with the same submodule. Semisimplicity of the restriction gives a
   subrepresentation `C` of `ρ.comp H.subtype` complementary to `W'`. By
   `isCompl_toSubmodule`, the submodules of `W` and `C` are complementary.
2. **The `H`-equivariant projection.** Let `P` be Mathlib's
   `Submodule.projection` of `V` onto `W` along `C`, a linear endomorphism of
   `V`. Its values lie in `W` (`projection_apply_mem`), it fixes `W`
   (`projection_apply_of_mem_left`), and it kills `C`
   (`projection_apply_of_mem_right`). For `h ∈ H`, write
   `ρ h v = ρ h (P v) + ρ h (v - P v)`. The first term lies in `W`, since `W` is
   `G`-stable. The second lies in `C`, since `v - P v ∈ C`
   (`sub_projection_mem`) and `C` is `H`-stable. Hence
   `P (ρ h v) = ρ h (P v)`.
3. **Averaging.** Let `A = (H.index : R)⁻¹ • cosetSum ρ H P`.
   - Each `conj ρ P g v = ρ g (P (ρ g⁻¹ v))` lies in `W`, so `A v ∈ W`.
   - For `w ∈ W`, the vector `ρ g⁻¹ w` lies in `W` and is fixed by `P`, so
     `conj ρ P g w = w`. The sum has `Nat.card (G ⧸ H) = H.index` terms
     (`Subgroup.index_eq_card`), so `A w = (H.index)⁻¹ • (H.index • w) = w`. Here
     `(H.index : R) ≠ 0` by `CharZero R` and `Subgroup.FiniteIndex.index_ne_zero`.
   - `A (ρ x v) = ρ x (A v)` for every `x : G`, by `cosetSum_apply_apply`.
4. **The complement.** The kernel of `A` is `G`-stable by the last property, so
   it is a subrepresentation `K` of `ρ`. The corestriction of `A` to `W` fixes
   every element of `W`. So Mathlib's `LinearMap.isCompl_of_proj` shows that
   `W` and the kernel of this corestriction are complementary submodules. This
   kernel is the kernel of `A` (`LinearMap.ker_codRestrict`). Finally
   `isCompl_of_isCompl_toSubmodule` makes `W` and `K` complementary
   subrepresentations.

So every subrepresentation of `ρ` has a complement, which is
`Representation.IsSemisimpleRepresentation ρ`.

## Checks

The module imports only the statement module and
`Mathlib.LinearAlgebra.Projection`. It compiles in Lean environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with no errors or warnings. Inspecting
`Langlands.finiteIndexSemisimplicityAscent` reports the axioms `propext`,
`Classical.choice` and `Quot.sound` only, and level parameters `uR uG uV`.
