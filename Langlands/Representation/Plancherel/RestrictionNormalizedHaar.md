# Haar measure normalized by a finite-kernel restriction

This derived construction implements the measure convention in Waldspurger,
*La formule de Plancherel pour les groupes p-adiques* (2003), I.1, printed
p.239 (PDF p.5). The target unitary character group of the split component
has Haar mass one. The character group of the ambient group carries the
measure for which restriction locally preserves measures.

The cardinality formula is an internal derivation of this source convention.
The source does not display that formula. The present pair supplies generic
measure constructions and their intrinsic laws, using the existing
`IsLocallyMeasurePreserving` predicate.

## Objects and hypotheses

Let \(C,D\) be compact Hausdorff commutative topological groups with their
Borel measurable spaces, and let \(f:C\to D\) be a continuous group
homomorphism with finite kernel \(S\). The group universes are independent.
`restrictionNormalizedHaar f` is the measure

\[
  \lambda_f=|S|\,h_C,
\]

where `Langlands.HarishChandraSchwartz.normalizedHaar C` supplies Haar
measure \(h_C\) of total mass one. No surjectivity premise is required for
this definition or its Haar and total-mass laws. Surjectivity is required
for the pushforward and local-preservation theorems. No second-countability
or finite-rank hypothesis is imposed.

The definition of `restrictionNormalizedHaar` itself only uses the source's
compact topological group and Borel structures and the continuous map and
finite kernel. The section's separation and target measure assumptions
are used where needed by the subsequent local-preservation proof.

## Construction laws and implemented proof

The `IsHaarMeasure (restrictionNormalizedHaar f)` instance follows by scaling
the existing probability Haar measure by the positive finite scalar
`Nat.card f.toMonoidHom.ker`. A kernel contains the identity, so its finite
cardinality is positive.

`restrictionNormalizedHaar_apply` evaluates every set as its probability
Haar measure times the kernel cardinality. `restrictionNormalizedHaar_univ`
therefore gives total mass \(|S|\).

For surjective \(f\), `map_restrictionNormalizedHaar` proves

\[
  f_*\lambda_f=|S|\,h_D.
\]

It uses Mathlib's `MonoidHom.measurePreserving` for the two probability Haar
measures: the continuous surjective homomorphism pushes \(h_C\) to \(h_D\).
Measure pushforward commutes with the scalar factor.

`isLocallyMeasurePreserving_restrictionNormalizedHaar` proves the local
condition with source measure \(\lambda_f\) and target measure \(h_D\).
Its private homeomorphism identifies \(C/S\) with \(D\) using the first
isomorphism theorem. The induced bijection is continuous by the quotient
topology; its domain is compact and its codomain is Hausdorff, so its inverse
is continuous as well.

The existing `finiteCharacterQuotientMeasure S lambda_f` is
\(|S|^{-1}q_*\lambda_f\). Pushing it through that homeomorphism gives \(h_D\),
by the preceding pushforward formula and cancellation of the positive finite
cardinality. The existing finite-quotient local-preservation theorem supplies
an open injectivity chart for \(q\) at each point. The target homeomorphism
preserves injectivity and makes the image of every measurable subset of a
chart measurable. The pushforward identity then identifies the target
measure of that image with its \(\lambda_f\) measure. This proves every clause
of `IsLocallyMeasurePreserving`; it assumes no local-preservation assertion.

## Scope and remaining adapters

This pair constructs the scale required for a continuous finite-kernel
surjection of compact Hausdorff commutative groups. Its specialization to
the actual unitary unramified character restriction of a split component
is separate. The actual restriction's surjectivity and kernel finiteness
must be proved or explicitly supplied by that adapter; they are not
consequences of this generic measure argument.

The pair does not identify character-image rank, construct complex parameter
periods, choose reductive group or parabolic quotient measures, or prove
complex-integral convergence. It does not construct coefficient tensors,
formal degrees, intertwining normalizations, wave packets, spectral
finiteness, inversion or the Plancherel theorem.
