# Proof of the finite complex character theory used by Henniart

Author: Worker 84, who wrote the proof and this explanation.

The theorem `Langlands.FiniteCharacter.finiteCharacterTheory G V W` proves the
unchanged Library proposition `Langlands.FiniteCharacterTheoryStatement G V W`
from `Langlands.Representation.Finite.CharacterStatement`. It keeps the three
independent universes `uG`, `uV`, `uW` of the target. Its hypotheses are the
target's: `G` is a group with a `Fintype` instance, and `V`, `W` are
finite-dimensional complex vector spaces. The proof adds no hypotheses,
definitions of new mathematical objects, or axioms. The declaration check uses
only `propext`, `Classical.choice` and `Quot.sound`.

The target conjoins nine propositions. The one-carrier components
(normalization, complete reducibility, norm one) are proved once for an
arbitrary carrier and used for both `V` and `W`.

## Imports

Besides the target module, the file imports the public Library module
`Langlands.Representation.Category.FiniteIndexRestriction`. From it the proof
uses `FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom`: an atom
of the subrepresentation lattice is an irreducible representation. It also uses
`Langlands.Subrepresentation.toSubmodule_iSup` from
`Langlands.Representation.SubrepresentationLattice`, which that module imports.
The remaining imports are Mathlib modules: complex polynomials, semisimple
endomorphisms, projections, irreducible representations, Maschke's theorem and
simple modules.

## Normalization

`normalization` proves `FiniteCharacterNormalizationStatement G V`. The
identity, conjugation and dual parts are Mathlib's `Representation.char_one`,
`Representation.char_conj` and `Representation.char_dual`.

The inverse part is `character_inv_eq_star`. Let `n = |G|`, so `ρ g ^ n = 1`.
The polynomial `X^n - 1` is separable over `ℂ`, hence squarefree. It
annihilates `ρ g`, so `ρ g` is a semisimple endomorphism. Over the
algebraically closed field `ℂ` its eigenspaces are independent and span `V`.
Collecting bases of the eigenspaces gives a basis `v` of `V` with
`ρ g (v i) = μ i • v i`. Each eigenvalue satisfies `μ i ^ n = 1`, so it is
nonzero and `ρ g⁻¹ (v i) = (μ i)⁻¹ • v i`. The helper
`trace_eq_sum_of_eigenbasis` computes the trace of a map that is diagonal in a
basis as the sum of the diagonal entries. Thus the character at `g⁻¹` is
`∑ (μ i)⁻¹`. Each `μ i` has norm one (`Complex.norm_eq_one_of_pow_eq_one`), so
`(μ i)⁻¹` is its complex conjugate (`Complex.inv_eq_conj`). Hence the sum is
the conjugate of `∑ μ i`, which is the character at `g`.

## Lattice helpers

The section `Lattice` transports facts between subrepresentations and their
underlying submodules. Independence and complementarity pass to submodules,
and a nonzero subrepresentation has a nonzero submodule. `prodEquivOfIsCompl`
turns a complementary pair `p`, `q` into an intertwining equivalence from the
product representation `p × q` to `ρ`; it is Mathlib's
`Submodule.prodEquivOfIsCompl` together with an intertwining check.
`equivRange` turns an injective intertwining map into an equivalence onto its
range. `prodCongr` takes the product of two equivalences. `character_prod`
says that the character of a product is the sum of the characters, by
`LinearMap.trace_prodMap'`.

## Complete reducibility

`completeReducibility` proves `FiniteCompleteReducibilityStatement G V`. Since
`|G|` is nonzero in `ℂ`, Maschke's theorem in Mathlib makes `ρ` a semisimple
representation; this is the first conjunct, obtained by instance search.

For the decomposition, `exists_decomposition` uses the corresponding semisimple
`MonoidAlgebra ℂ G`-module. That module is Noetherian because `V` is
finite-dimensional. Mathlib's
`IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top` gives an
independent set of simple submodules with supremum `⊤`. The set is finite
(`WellFoundedGT.finite_of_sSupIndep`), so it can be indexed by `Fin n`. The
order isomorphism `Subrepresentation.subrepresentationSubmoduleOrderIso`
carries it to an independent family of atoms `S : Fin n → Subrepresentation ρ`
with supremum `⊤`. Each `(S i).toRepresentation` is irreducible by the
imported atom lemma. The underlying submodules form an internal direct sum, so
`DirectSum.coeLinearMap` is bijective. The resulting linear equivalence from
`⨁ i, S i` to `V` commutes with the action. This checks on each summand,
giving the required `Representation.Equiv` from
`Representation.directSum (fun i => (S i).toRepresentation)` to `ρ`. The
empty family (`n = 0`) occurs for the zero representation.

`exists_isAtom` extracts one atom when `finrank ℂ V ≠ 0`. If the
decomposition were empty, `⊤` would equal `⊥` and `V` would have rank zero.

## Hom dimension and orthogonality

`card_inv_mul_sum_eq_finrank` (and the conjunct `homDimension`) is Mathlib's
`Representation.card_inv_mul_sum_char_mul_char_eq_finrank`. It is restated with
`Fintype.card` in place of `Nat.card` and the two factors in each summand
swapped.

`orthogonality` uses that formula. If `ρ ≃ σ`, then `σ` has the character of
`ρ` (`Representation.char_iso`). The pairing is then
`finrank (ρ →ᵢ ρ) = 1` by Schur's lemma for irreducibles
(`Representation.IsIrreducible.finrank_intertwiningMap_self`). If there is no
equivalence, a Mathlib instance in `Mathlib.RepresentationTheory.Irreducible`
(irreducible target, empty type of equivalences) makes the space of
intertwining maps `ρ → σ` a subsingleton, so its rank and the pairing are `0`.

## Isomorphism

`isomorphism` proves `FiniteCharacterIsomorphismStatement G V W`. The reverse
direction is `Representation.char_iso`. The forward direction is
`nonempty_equiv_of_character_eq`, by strong induction on `finrank ℂ V`. The
carriers `V` and `W` stay in their separate universes throughout.

- If `finrank ℂ V = 0`, evaluating the characters at `1` gives
  `finrank ℂ W = 0`. Both carriers are subsingletons, and
  `LinearEquiv.ofSubsingleton` is an intertwining equivalence.
- Otherwise choose an atom `T` of the subrepresentation lattice of `ρ`, so `T`
  is irreducible and nonzero. The inclusion `T → ρ` is a nonzero intertwining
  map. By the Hom-dimension formula and the equality of characters,
  `finrank (T →ᵢ σ) = finrank (T →ᵢ ρ) > 0`. Hence there is a nonzero
  intertwining map `f : T → σ`. It is injective by Schur's lemma
  (`Representation.IsIrreducible.injective_or_eq_zero`).
- Choose an invariant complement `C` of `T` in `ρ` and `C'` of `f.range` in
  `σ` (`exists_isCompl`, available from semisimplicity). By `character_prod`,
  `χρ = χT + χC` and `χσ = χ(f.range) + χC'`. Also `χ(f.range) = χT` through
  `equivRange f`, so `χC = χC'` by cancellation.
- `finrank C < finrank V`, since `T` and `C` are complementary and `T` is
  nonzero. Induction gives `C ≃ C'`. The composite
  `ρ ≃ T × C ≃ f.range × C' ≃ σ` is the required equivalence.

## Norm one

`normOne` proves `FiniteCharacterNormOneStatement G V`. By the Hom-dimension
formula the normalized norm equals `finrank (ρ →ᵢ ρ)`, cast to `ℂ`, so the
statement becomes `finrank (ρ →ᵢ ρ) = 1 ↔ ρ` irreducible. Irreducible
implies rank one by Schur's lemma. For the converse, assume the rank is one:

- `V` is nontrivial, since for `V = 0` the intertwiner space has rank `0`.
  Hence `⊥ ≠ ⊤` in the subrepresentation lattice.
- Suppose `ρ` is not irreducible. Then some subrepresentation `p` is neither
  `⊥` nor `⊤`. Take an invariant complement `q`, which is nonzero.
- Through `prodEquivOfIsCompl`, the projection onto `p` along `q` is an
  intertwining endomorphism `π`. It fixes `p` and kills `q`.
- The identity is nonzero, and the intertwiner space has rank one. So
  `π = c • id` for some `c` (`finrank_eq_one_iff_of_nonzero'`). Evaluating at
  a nonzero `y ∈ q` gives `c = 0`. Evaluating at a nonzero `x ∈ p` then gives
  `x = 0`, a contradiction.

This route differs from Serre's proof of Theorem 5, which writes `ρ` as a sum
of irreducibles with multiplicities and computes the norm as the sum of
squared multiplicities. The Lean proof uses the intertwiner rank and a
projection instead.

## Main theorem

`finiteCharacterTheory` assembles the nine conjuncts in the order of the
target: `normalization` for `V` and `W`, `completeReducibility` for `V` and
`W`, `homDimension`, `orthogonality`, `isomorphism`, and `normOne` for `V` and
`W`.

## Provenance

The mathematics is standard finite-group character theory over `ℂ`. The target
statement's Markdown cites Jean-Pierre Serre, *Linear Representations of Finite
Groups*, GTM 42, Springer, 1977, §§1.3–1.4 and 2.1–2.3 (literature ID
`serre-1977-linear-representations`). Henniart uses these facts before the
Brauer-induction step of *Une preuve simple des conjectures de Langlands pour
GL(n) sur un corps p-adique* (2000), §3.7. The Lean proof follows its own route
as described above. The Hom-dimension formula is quoted from Mathlib rather
than derived from Serre's argument.
