# Coalgebra criteria for unipotence

Authors: Worker 1450 and Worker 572 (Lean definitions and first Markdown
draft); Worker 1411 (Markdown revision and submission).

These definitions provide an algebraic interface for proving that closed
subgroup schemes of unipotent group schemes are unipotent. They apply to a
bialgebra `B` over an arbitrary field `k`, with `k` and `B` in arbitrary,
independent universes. They impose no finite-dimensionality,
finite-generation, commutativity, antipode, perfection or characteristic
condition on `k` or `B`.

All names are in `Langlands.GroupScheme.CoalgebraUnipotence`. The ambient
hypotheses are `[Field k] [Ring B] [Bialgebra k B]`; the `k`-algebra structure
is the one contained in `Bialgebra`.

## Coefficient matrices

`IsCoefficientMatrix (k := k) a`, for an `n` by `n` matrix `a` with entries in
`B`, means that for all indices `i` and `j`

- `comul (a i j) = ∑ l, a i l ⊗ₜ[k] a l j`, and
- `counit (a i j) = (1 : Matrix (Fin n) (Fin n) k) i j`, that is, `1` if
  `i = j` and `0` otherwise.

These are the coefficient identities of an `n`-dimensional right
`B`-comodule `V` with basis `e 0, …, e (n-1)` and coaction
`e j ↦ ∑ i, e i ⊗ a i j`, the form in which Milne writes the coaction of a
finite-dimensional comodule in the proof of Theorem 4.9: the first identity is
coassociativity of the coaction and the second is counitality, written on the
basis. This explanation is not formalized here; the Lean definition is only the
conjunction of the two displayed families of equations.

## Matrix unipotence

`IsMatrixUnipotent k B` means: for every `n > 0` and every coefficient matrix
`a : Matrix (Fin n) (Fin n) B`, there is a vector `v : Fin n → k` with
`v ≠ 0` and
`∑ j, v j • a i j = v i • (1 : B)` for every row `i`.

For the comodule with coaction `e j ↦ ∑ i, e i ⊗ a i j`, the vector
`∑ j, v j • e j` has coaction `∑ i, e i ⊗ (∑ j, v j • a i j)`, so the condition
says exactly that this nonzero vector `x` satisfies `x ↦ x ⊗ 1`, i.e. is a
fixed vector. This is the coefficient form of Milne's description of
unipotence in §14.b (every nonzero representation has a nonzero fixed vector,
and `V^G ≠ 0` means that some nonzero `v` has coaction `v ⊗ 1`), restricted to
nonzero finite-dimensional comodules presented by a basis.

## The reduced-translation filtration

`reducedLevel k B : ℕ → Submodule k B` is defined by recursion:

- `reducedLevel k B 0 = ⊥`, the zero subspace;
- `reducedLevel k B (n + 1)` is the infimum, over all linear functionals
  `f : Module.Dual k B` with `f 1 = 0` (indexed as the subtype
  `{f : Module.Dual k B // f 1 = 0}`), of the inverse images
  `(reducedLevel k B n).comap (AffineLinearEmbedding.rightAct f)`.

Thus `b` lies in level `n + 1` exactly when `rightAct f b` lies in level `n`
for every functional `f` vanishing at `1`. Here `rightAct` is the published
operator `Langlands.GroupScheme.AffineLinearEmbedding.rightAct` from
`AffineLinearEmbedding.Comodule`, used unchanged: in Sweedler notation
`comul b = ∑ b₁ ⊗ b₂`, it sends `b` to `∑ f (b₂) • b₁`. Because each level is an
intersection of inverse images of subspaces under linear maps, every level is a
`k`-subspace. Unfolding the recursion, membership in level `n` means that
every composition of `n` right translations by functionals vanishing at `1`
sends the element to `0`; this reading is an explanation of the recursive
definition, and the module does not state or prove a separate word-action
theorem.

`IsLocallyConilpotent k B` means `∀ b : B, ∃ n, b ∈ reducedLevel k B n`: the
levels exhaust `B`.

## Relation to Milne's coconnected filtration

This filtration is an internal construction. It is **not** Milne's
coconnected filtration, and `IsLocallyConilpotent` is **not** a transcription of
Milne's Definition 14.4. The differences are as follows.

- Milne (Definition 14.4) calls a Hopf algebra `A` coconnected if there
  *exists* a filtration `C₀ ⊂ C₁ ⊂ C₂ ⊂ ⋯` by subspaces with `C₀ = k`,
  `⋃ C_r = A` and `Δ(C_r) ⊂ ∑_{i=0}^{r} C_i ⊗ C_{r-i}`. That filtration is
  extra data, constrained directly through the comultiplication `Δ`.
- `reducedLevel k B` is a single canonical filtration determined by `B`. It is
  not chosen, and it is defined through the right translation operators
  `rightAct f` for functionals `f` with `f 1 = 0`, not through a condition
  on `comul` of the form `Δ(C_r) ⊂ ∑ C_i ⊗ C_{r-i}`.
- The indexing differs: `reducedLevel k B 0 = ⊥`, whereas Milne's `C₀ = k`.
- Milne works with the Hopf algebra of an algebraic group; here `B` is only a
  bialgebra, with no antipode and no finiteness or commutativity assumption.

The intended use is the argument of Milne's proof of Theorem 14.5, where the
direction (c) ⇒ (a) uses an exhaustive filtration of the coordinate algebra
to produce fixed vectors in comodules. No equivalence between
`IsLocallyConilpotent`, Milne's coconnectedness, `IsMatrixUnipotent` or
unipotence of a group scheme, and no preservation theorem (for quotients,
subbialgebras or closed subgroups), is stated or proved in this module.

## Provenance

These are internal (derived) definitions, chosen as a field-level algebraic
interface for the consumer task on closed subgroups of unipotent group
schemes. Their motivation is J. S. Milne, *Algebraic Groups: The Theory of
Group Schemes of Finite Type over a Field* (Cambridge University Press, 2017),
registered source `milne-2017-algebraic-groups`:

- Proposition 4.7 (printed p. 86) and Theorem 4.9 (printed p. 87): comodule
  coefficients and the coaction `Δ(e_j) = ∑_i e_i ⊗ a_ij` on a
  finite-dimensional subcomodule, the source of the coefficient identities in
  `IsCoefficientMatrix`;
- §14.b (printed p. 280): unipotence as the existence of nonzero fixed vectors,
  with fixed vectors characterized by the coaction `v ↦ v ⊗ 1`, the source of
  `IsMatrixUnipotent`;
- Definition 14.4 and Theorem 14.5 (printed p. 281, the proof of (c) ⇒ (a)
  continuing on p. 282): the coconnected filtration and its use, which
  motivates, but is distinct from, the reduced-translation filtration.
