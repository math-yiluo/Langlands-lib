# Real unitarization of actual supercuspidal GL representations

Authors: Worker 163 (statement draft), Worker 246.

`Langlands.SupercuspidalRealUnitarizationStatement.{uF,uV}` is a closed
proposition definition. It states that every actual irreducible
supercuspidal representation of `GL_n(F)` becomes unitarizable on its
original carrier after a real power of the normalized determinant
absolute value. The file provides no proof.

## Quantifiers and hypotheses

The statement quantifies over every prime `p` (with `Fact p.Prime`), finite
p-adic extension `F : PadicField.{uF} p`, supplied compatible local-field
realization `T : F.TopologicalData`, and rank `n` with `0 < n`. It installs
`T.topology` on `F.Carrier` with `letI`; the topology on
`GeneralLinear n F.Carrier` is the one the existing instances derive from
it. It then quantifies over every complex vector space `V : Type uV` and
every actual representation
`ρ : Representation ℂ (GeneralLinear n F.Carrier) V`. The field universe
`uF` and the carrier universe `uV` are independent.

There are exactly two hypotheses on `ρ`:

- `Representation.IsIrreducible ρ`, Mathlib's algebraic irreducibility
  (the subrepresentation lattice is a simple order);
- `GeneralLinear.IsSupercuspidal ρ`, which is `IsAdmissible ρ` together with
  subsingleton actual Jacquet coinvariants for the conjugated unipotent
  radical of every proper ordered block parabolic and every conjugating
  element. This predicate does not include irreducibility, which is why
  irreducibility is a separate hypothesis.

There is no further hypothesis: no topology, norm, completion or
finite-dimensionality on `V`, no central-character, unitarity,
coefficient-compactness or square-integrability premise, and no
theorem-valued premise.

## Conclusion, carrier and sign

The conclusion is

`∃ t : ℝ, IsUnitarizable (realPowerTwist (T.determinantNorm n) t ρ)`.

Here `T.determinantNorm n g` is the positive unit `|det g|_F`, where
`|x|_F = q^(-ord x)` is the residue-normalized absolute value
`T.normalizedAbs`. The twist `realPowerTwist` acts on the same carrier `V`
by `(realPowerTwist (T.determinantNorm n) t ρ) g v = |det g|_F^t • ρ g v`,
so the exponent sign is `+t`. `IsUnitarizable ω` is
`Nonempty (InvariantPositiveForm ω)`: an `InnerProductSpace.Core ℂ V` on
the given carrier (a positive definite Hermitian form, conjugate-linear in
the first argument) preserved by every operator `ω g`. Nothing is said
about completeness of that form. The statement does not assert uniqueness
or a sign of `t`, nor that the twisted representation is again irreducible
or supercuspidal.

## Provenance (internal derived specialization)

This proposition is an internal specialization of the published
`Langlands.LeviCuspidalRealUnitarizationStatement` to the actual one-block
Levi `CuspidalSupport.LeviAdmissibility.oneBlock n hn` of `GL_n`. The
published Library supplies the comparison facts behind this
specialization: `GeneralLinear.BlockShape.singleBlock_leviEmbedding_surjective`
says the single-block Levi embedding is surjective, and
`CuspidalSupport.singleBlockCuspidalityClause` says that Levi cuspidality of
the pulled-back representation is equivalent to `GeneralLinear.IsSupercuspidal`.
On the single block, the Levi character `∏ᵢ |det mᵢ|_F^(tᵢ)` is the
ordinary `|det g|_F^(t 0)`; this is a direct matrix computation, not a
published lemma. The original-literature route is the one recorded in the
Levi statement's Markdown for a general p-adic reductive group, applied to
`GL_n(F)` itself: Casselman, *Introduction to the theory of admissible
representations of p-adic reductive groups* (draft of 1 May 1995,
registered `casselman-1995-admissible-representations`), Lemma 5.2.5 (a
positive character making the central character unitary; for `GL_n` the
positive characters factoring through `T/T₀` are the real powers of
`|det|_F`) and Corollary 5.2.3 (an irreducible absolutely cuspidal
representation with unitary central character is unitary), with §2.1's
definition of unitarity by an invariant definite Hermitian form on `V`
itself. The single-block reduction is our derived step and is not text in
Casselman.

This file is a statement unit only. It supplies no proof of
unitarization and makes no claim about adjacent product reducibility or
the other analytic steps of Zelevinsky 1980, Proposition 1.11, which it is
intended to feed.

## Planned proof successor

The proof is to be supplied by a separate `lean.proof@1` task, transporting
the proved Levi theorem `Langlands.leviCuspidalRealUnitarization` along the
surjective single-block embedding. That task is also to provide an
object-level corollary for `GeneralLinear.SupercuspidalRep`, whose class
compatibility uses `supercuspidalClassRealPowerTwist` from
`Classification/SupercuspidalTwist`. The corollary is not part of this
proposition and does not strengthen it.
