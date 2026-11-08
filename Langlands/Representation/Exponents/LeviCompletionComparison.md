# The represented-parabolic completion comparison from compression data

Author: Worker 1775. This derived supporting construction assembles the
completion comparison underlying Renard VI.9.7 for actual rational
parabolic data with a common Levi, retaining the contraction-basis,
stationary-image and stable Jacquet bijectivity inputs. It does not establish the
unconditional parent statement. Source: Renard 2026,
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
VI.9.7, printed pp.205–206 / PDF pp.211–212.

The two actual radical images and Levi image are used throughout. Compact
covering of the fixed radical is derived from its published limit-of-compact-
subgroups theorem, applied to a singleton and mapped into the ambient group.
Equality of the two Levi morphisms transports the normalizer inclusion.
Closedness of the radical and Levi images is supplied by their actual closed
immersions. The remaining data are a single central contracting element with
an opposite Iwahori contraction basis, stationarity at its basis indices for
the given representation, and bijectivity of the genuine stable-image Jacquet
map at those indices. The two parabolics are actual morphisms `p : P → G` and
`pbar : Pbar → G` over an arbitrary nonarchimedean local field `k : Type u`;
the two geometric radicals are `n : N → P` and `nbar : Nbar → Pbar`. The second
Levi morphism `mbar : M → Pbar` is rational, its multiplication with `nbar`
is an isomorphism, and `mbar ≫ pbar = m ≫ p` for `m : M → P`.
The first Levi's rationality and its multiplication isomorphism are not used
by this assembly. The ambient affine group has its canonical rational-point
topology, with local compactness and a nonarchimedean-group instance.
Hausdorffness of `k` is assumed. Carrier universe `v` is arbitrary.

`leviCompletionComparisonEquiv` composes `fixedCompletionJacquetEquiv` with
`leviJacquetCompletionTransportEquiv`, obtaining a complex linear equivalence
from the actual radical-fixed ambient completion to completion of the normalized
opposite Jacquet functor on actual Levi rational points. In the generic
comparison, the quotient radical is the literal image of `nbar ≫ pbar`,
the Levi is the literal image of `mbar ≫ pbar`, and the fixed radical is the
literal image of `n ≫ p`. Thus the two parabolics have exactly the exchanged
roles required in the proof of VI.9.7. The Levi topology and
nonarchimedean-group instance in the target are the published ones.

`leviCompactIndex_transport_eq` identifies every actual Levi compact open
subgroup `KM` satisfying
`y ∈ KM ↔ (leviPointsEquiv pbar mbar … y : G(k)) ∈ K` with the subgroup index
`K ∩ M(k)` used by the generic comparison. The proof is subgroup extensionality
and the inverse identity of the genuine Levi-point equivalence.

`leviCompletionComparisonEquiv_apply_of_factor` then gives the target's
localized-quotient formula at every compact open `K` with the factorization
`K = (K ∩ N)(K ∩ M)(K ∩ Nbar)`, and every `KM` satisfying that membership
condition:

`(leviCompletionComparisonEquiv … x)_{KM} = Jacquet.Localization.mk … 1 (x_K)`.

This characterization needs only the stated factorization at the test index.
In particular, its test index need not belong to the construction's basis
or have the same contracting element `g`. An `IsIwahoriContraction` as in
the parent statement supplies this factorization. The proof rewrites the
transport component formula and the transported index, applies
`fixedCompletionJacquetEquiv_apply_of_factor`, and uses the inverse
trivial-character quotient comparison on the actual class of `x_K`.

`leviCompletionComparisonEquiv_natural` treats two smooth representations
in the arbitrary common carrier universe `v`, each with the stationary-image
and stable-map-bijectivity inputs. If `f : π → σ` relates every ambient
component of `x` and `y`, the actual normalized functor's map relates every
Levi component of their comparisons. The proof composes
`fixedCompletionJacquetEquiv_natural` with
`leviJacquetCompletionTransportEquiv_natural`; all quotient maps are the
ones induced by `SmoothRep.hom f`.

No opposite-intersection hypothesis is needed for this conditional assembly:
its supplied basis already contains the group-theoretic contraction data it
uses. Deriving that basis and central element from the original opposite
parabolic hypotheses, and proving the retained stationary-image and
stable-map-bijectivity inputs unconditionally, remain obligations of the parent
theorem and the separately owned structural and VI.9.1 tasks. This file proves
neither exact parent proposition.
