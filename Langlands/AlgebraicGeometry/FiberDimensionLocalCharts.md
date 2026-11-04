# Local fibre dimension and actual principal charts

This is a derived algebraic construction toward the pure-dimensional fibre
assertion in Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp. 5–6, Theorem 3.4(2). Conrad's theorem is a
filtered-descent assertion and does not state this internal construction.
The present module supplies actual source neighbourhoods and their dimension
bounds.

## Local dimension realized by a principal neighbourhood

Let R and S be arbitrary commutative rings, let S be an R-algebra, and let
q be a prime of S above a prime p of R. Write F = κ(p) ⊗[R] S and let x be
the actual point of Spec F corresponding to q under
`PrimeSpectrum.preimageHomeomorphFiber`. The local dimension at x is the
minimum of the dimensions of its open neighbourhoods, as defined by
`topologicalKrullDimAt`.

`exists_away_fiber_dimension_eq_at` proves that there is r in S outside q
such that

    dim(κ(p) ⊗[R] S[1/r]) = topologicalKrullDimAt x.

This lemma requires no finite-type or Noetherian hypothesis. The ring
universes are independent, and the value lies in `WithBot ℕ∞`, so the
argument does not first assume that the local dimension is finite.

The proof chooses an open U attaining the minimum, then a basic open D(f)
containing x and contained in U. Dimension monotonicity and the definition
of the minimum give dim D(f) = dim U. Mathlib's fibre denominator-clearing
lemma provides a in R outside p and r in S with a • f = 1 ⊗ r. The image of
a in F is a unit, because it is the image of a nonzero residue-field
element. Therefore D(f) = D(1 ⊗ r). The actual tensor-localization algebra
equivalence identifies κ(p) ⊗[R] S[1/r] with F[1/(1 ⊗ r)], whose spectrum is
homeomorphic to this basic open. Contracting x back to q proves r outside q.

## Constructed chart with a uniform original-base fibre bound

Assume now that S is of finite type over R, and let p be the contraction
of q. `FiberDimensionLocalChart R S q` records the following actual data:

* An element r outside q and the corresponding prime q' of T = S[1/r],
  with its contraction equality q' ↦ q.
* A `FiberDimensionPrincipalChart R T q'`. This supplies coordinates in T,
  an element t of T outside q', and a quasi-finite polynomial evaluation
  map R[X₁,…,Xₙ] → T[1/t]. It retains the finite injective normalization of
  κ(p) ⊗[R] T and its dimension equality.
* An equality between n and the local dimension at x in the original
  fibre κ(p) ⊗[R] S.

`fiberDimensionLocalChart` constructs all these data. It first applies the
local-realization lemma, lifts q through the principal-open homeomorphism,
and uses `fiberDimensionPrincipalChart` on T at q'. The scalar-tower identity
identifies q's original contraction with that of q'. The first
localization's fibre dimension equals the original local dimension, while
the inherited normalization gives that same fibre dimension as n. These
two proved equalities establish the new rank field. Classical choice is
applied only after existence of the complete record is proved.

`FiberDimensionLocalChart.sourceMap` is the composite of the two actual
prime-contraction maps Spec(T[1/t]) → Spec T → Spec S. The theorem
`sourceMap_isOpenEmbedding` proves that it is an open embedding, and
`mem_range_sourceMap` proves that its image contains q. The construction
uses two successive principal localizations; it does not identify their
composite ring with a chosen single principal localization of S.

For every prime p₀ of the original base R,
`FiberDimensionLocalChart.fiber_dimension_le` proves

    dim(κ(p₀) ⊗[R] T[1/t]) ≤ topologicalKrullDimAt x.

It rewrites the inherited uniform fibre bound using the constructed rank
equality. In particular, the bound uses the original local dimension at q,
not the total dimension of the original fibre of S. Other fibres may be
empty. No domain, faithful-action or original-map injectivity premise is
added.

## Retained obligations

This module does not prove general relative-dimension sublevel openness or
retrocompactness, geometric-connectedness constructibility, or filtered
descent. The chart and its map are constructed, but the comparison of local
dimension at all points in its image with that of the original varying
family remains a separate step. Conrad Theorem 3.4(2) and whole-paper
coverage remain obligations.
