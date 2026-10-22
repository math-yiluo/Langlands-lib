# Core opposite-radical canonical Jacquet lift statements

Author: Worker 253.

This module states the opposite-radical mirror of the two core assertions in
`Langlands.Representation.Jacquet.CanonicalLiftStatement`. It uses only the
published constructions in `CanonicalLiftDefinitions`, `BlockIwahoriDefinitions`
and `OppositeBlocks`. All three new declarations are Prop-valued definitions,
not proofs. Their namespace is `Langlands.Jacquet`. The module does not import
the upper statement module, and it does not change any existing Library pair.

## Parameters and hypotheses

Every declaration keeps the parameters of the upper template, with the same
binders and in the same order:

- an arbitrary prime `p` with `[Fact p.Prime]`;
- every finite p-adic field `F : PadicField.{uF} p`;
- a supplied `T : F.TopologicalData`;
- every natural rank `n` and every ordered block shape
  `B : GeneralLinear.BlockShape n`;
- a complex representation carrier `V : Type uV`.

The field universe `uF` and the carrier universe `uV` are independent. Each
clause installs precisely `T.topology` and `T.generalLinearTopologicalGroup n`.
It does not quantify over a replacement topology or topological-group structure.

For every representation `ρ` of the actual `GeneralLinear n F.Carrier` on `V`,
`hAdmissible : IsAdmissible ρ` supplies the smoothness witness
`hρ := hAdmissible.1`. The remaining hypotheses are:

- an actual open subgroup `K` with compactness witness `hK`;
- the existing predicate `B.HasBlockIwahoriFactorization T K`;
- a scalar tuple `a : Fin B.length → F.Carrierˣ` satisfying the existing
  `B.IsStrictlyContracting T a`.

These are all the hypotheses, and they are the hypotheses of the upper clauses.
No new opposite chamber predicate, opposite factorization predicate, abstract
lift object or replacement quotient is introduced.

## The opposite radical and the inverse scalar

The clauses set

- `g := (B.blockScalar F.Carrier a)⁻¹`, the inverse of the actual block scalar
  matrix of the same tuple `a`;
- `N̄ := B.oppositeUnipotentSubgroup F.Carrier`, the actual block-lower
  unitriangular radical in the ambient group;
- `M := B.leviSubgroup F.Carrier`, the common embedded Levi.

The normalizer inclusion is the published
`B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier`. In Lean,
`N̄` and `M` are written out in place, as `N` and `M` are in the upper template.
Only `g` is bound by `let`.

The tuple `a` is the original upper strictly contracting tuple. Its strict
contraction means `|a_i/a_j| < 1` for every pair of blocks `i < j`, with the
normalized absolute value of `T`. For a block-diagonal matrix `d`,
conjugation `x ↦ d x d⁻¹` multiplies the block `(i,j)` of `x` by `d_i d_j⁻¹`.
With `d = g`, a lower block `(i,j)` with `i > j` is multiplied by
`a_i⁻¹ a_j = a_j/a_i`. Since `j < i`, this factor has absolute value less than
one, so `g` strictly contracts the opposite radical. The statement does not
also impose strict contraction on `a⁻¹`. That would be the opposite chamber
condition, and together with the original condition it would be impossible
whenever there are at least two blocks.

The existing factorization predicate already contains both conjugation
directions. For every weakly contracting tuple `b`, it requires that
`blockScalar b` conjugates `K ∩ N` into itself and that `(blockScalar b)⁻¹`
conjugates `K ∩ N̄` into itself, where `N` is the upper radical. At `b = a`
these say that `g (K ∩ N̄) g⁻¹ ⊆ K ∩ N̄` and `g⁻¹ (K ∩ N) g ⊆ K ∩ N`. These are
Casselman's containments (b) for the opposite parabolic and the element `g`.
The predicate states bijectivity of the product map in the order lower radical,
Levi, upper radical. The opposite parabolic needs the reverse order. Because the
three factors are subgroups, inversion turns one product into the other. That
derivation belongs to the eventual proofs. It is neither a hypothesis nor a
result of this module.

## The two assertions

Write `X := fixedVectors ρ K.toSubgroup` and
`C̄ := compressedAction ρ hρ K hK g`. This is the existing endomorphism of `X`
that applies `ρ g = ρ((blockScalar a)⁻¹)` and then the normalized compact
average.

`BlockOppositePowerKernelJacquetClause F T B V` states the equality of
submodules of `X`

\[
  \sup_{r\in\mathbb N}\ker(\bar C^r)
  =\ker\bigl(\texttt{fixedJacquetMap}\;ρ\;\bar N\;M\;h_{M\bar N}\;K\bigr).
\]

The left side is exactly the published `powerKernelSup ρ hρ K hK g`. The right
side is the kernel of the actual opposite quotient map restricted to `K`-fixed
vectors. In ambient terms these are exactly the fixed vectors in the actual
opposite Jacquet relation submodule.

`BlockOppositeStableImageJacquetBijectiveClause F T B V` states
`Function.Bijective (stableImageJacquetMap ρ hρ K hK g N̄ M hMN̄)`.
Its domain is exactly the published
`stableImage ρ hρ K hK g = ⨅ r : ℕ, LinearMap.range (C̄ ^ r)`.
Its existing codomain is

```lean
fixedVectors (Jacquet.action ρ (B.oppositeUnipotentSubgroup F.Carrier)
  (B.leviSubgroup F.Carrier)
  (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier))
  (K.toSubgroup.comap (B.leviSubgroup F.Carrier).subtype)
```

Here `K.toSubgroup.comap M.subtype` is `M ∩ K` regarded as a subgroup of `M`.
The descended action is **unnormalized**. The published evaluation law
`stableImageJacquetMap_apply` identifies this map with the actual opposite
quotient of the stable-image vector in `V`. So bijectivity gives a unique
stable-image lift, for the opposite radical, of each vector in that codomain.
No inverse is selected or supplied as input.

`BlockOppositeCanonicalLiftStatement F T B V` is exactly the conjunction of
these two clauses, in this order. Kernel equality, surjectivity, invertibility,
admissibility of the Jacquet module, canonical lifts and pairings are not
hypotheses. There is no positive-rank, nonempty-block, proper-parabolic or
nonzero-representation condition. Rank zero, empty and one-block shapes, and
the zero representation are all included. For at most one block the strict
inequalities are vacuous, as in the existing contraction predicate.

## Source and provenance

Bill Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter III: *Induced representations and the Jacquet module*, revision
April 29, 2019. Registered source: `casselman-2019-jacquet-module`; SHA256:
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
Retained original:
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.

These are **derived** statements. Section 4 (p.5) defines an Iwahori
factorization with respect to a parabolic `P`. Section 5 (pp.5–7) fixes "an
opposing pair of parabolic subgroups" `P, P̄`, a compact open `K₀` with
factorization with respect to this pair, and a contracting element `a` of
`A_P^{--}`. It then proves Lemma III.5.4 (generalized kernel of `τ_a` equals
`V^{K₀} ∩ V(N)`) and Proposition III.5.5 (the canonical complement maps
isomorphically onto `V_N^{M₀}`). Page 7 restricts the coefficients to a field
from that point on; this module uses `ℂ`. The present clauses are these two
results with the roles of `P` and `P̄` exchanged. The radical is `N̄`, and the
contracting element is `a⁻¹`, which lies in `A_{P̄}^{--}`. Section 6
(III.6.1–III.6.3, pp.7–8) needs this exchanged case for the canonical pairing.
There the inverse operator `τ_{a⁻¹}` acts on the contragredient and is used
on the opposite side, and III.6.2 adds "Similarly with the roles of V and Ṽ
reversed". The overbars distinguishing `N` and `N̄` do not survive text
extraction of pp.7–8, and no page renderer was available to this author. The
`N̄` reading of III.6.1 comes from the adjoint relation: the adjoint of
`π(char(K₀ a K₀))` is `π̃(char(K₀ a⁻¹ K₀))`, and `a⁻¹` contracts `N̄`. The
section 5 statements themselves are symmetric in the opposing pair. No separate
project errata file for this source was found.

As in the upper module, the operator is translated rather than copied.
Casselman's `τ_{a⁻¹}` is the unnormalized sum over `K₀ a⁻¹ K₀ / K₀`. By
III.5.1 with the roles exchanged, it is a coset sum over
`K₀ / (K₀ ∩ g K₀ g⁻¹)` applied to `π(g)v`, for `g = a⁻¹`. The implemented `C̄`
uses normalized averaging. Transferring the source argument needs two further
results. The first is the comparison `τ_{a⁻¹} = d C̄`, where `d` is the positive
finite index `[K₀ : K₀ ∩ g K₀ g⁻¹]` viewed in `ℂ`. The second is
finite-dimensional stabilization, which identifies the intersection of all
ranges with the source's sufficiently high power image. Neither is assumed here
or proved here. The source normalizes the Jacquet action in its quotient
formulas, but the codomain here uses the existing unnormalized descended action.
Identifying the compact-Levi fixed vectors of the two actions would need a
proved restriction of the modulus to the compact subgroup. That identification
is not imposed here.

The statement reuses the generic `N`, `M` and `g` parameters of
`CanonicalLiftDefinitions`, so no new carrier is defined. The upper
`BlockPowerKernelJacquetClause` and `BlockStableImageJacquetBijectiveClause`,
and their published proofs in `BlockPowerKernelProof` and
`CanonicalLiftBijectivityProof`, are not hypotheses of these clauses. One
possible proof is a transport. The inverse transpose (`Group.GL.Maps`,
including `T.generalLinearInverseTranspose n`) exchanges the two radicals,
preserves the common Levi as a set and inverts the block scalar. Block reversal
(`Group.GL.ReverseBlocks`) supplies reversed shapes and matrices and conjugacies
of both radicals. Any substantive transport proposition needs its own statement
and publication first.

## Scope

Nothing in this module proves either clause. The following remain separate
statements and proof obligations:

- independence of the contracting tuple;
- compatibility under nested compact subgroups and averaging;
- normalized-action compatibility;
- construction of the canonical pairing and its nondegeneracy;
- the full opposite Jacquet duality of `Langlands.Parabolic.OppositeDualityStatement`.

That last statement is the intended consumer, through task `5068d03e`.
