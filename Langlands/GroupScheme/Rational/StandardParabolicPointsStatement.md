# Standard parabolics on rational points

`StandardParabolicPointsStatement` consists of four assertions about actual
subgroups of the categorical rational-point group
`Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X`.

- A point belongs to `P_J(k)` exactly when it is `p*n*q`, with `p,q` in the
  minimal parabolic and `n` an actual normalizing point whose class lies in
  `standardRelativeWeylGroup i ν J`.
- A subgroup contains the minimal parabolic precisely when it is `P_J(k)` for
  a subset `J ⊆ Δ`.
- Each `P_J(k)` equals its set normalizer in `G(k)`.
- For `J,K ⊆ Δ` there is an equivalence from `W_J \ W / W_K` to
  `P_J(k) \ G(k) / P_K(k)`. Its value on the class of every normalizing point
  `n` is the double coset of the underlying point `n` in `G(k)`.

The last clause uses Mathlib's actual `DoubleCoset.Quotient` on the published
Weyl quotient and the actual rational-point subgroups. The representative
formula specifies the induced bijection; it asserts more than the existence of
an unspecified equivalence between two sets.

Every field `k : Type u` is quantified over. The group scheme `G` is assumed
`IsConnectedReductive`, the homomorphism `i : T.toGrp ⟶ G` is assumed
`IsMaximalSplitTorus`, and `ν : cocharacterLattice T` is assumed
`IsGenericCocharacter i ν`. Affineness and the monomorphism of `i` are obtained
from those assumptions. Write `Δ = simpleRelativeRoots i ν`. Subsets are actual
sets of characters, with explicit containment in `Δ`. There is no assumption of
reducedness, characteristic, perfectness, splitness or quasi-splitness; `Δ` may
be empty.

The sources are Borel–Tits §5.17, §5.18(i–ii) (printed p.101) and §5.20
(printed p.102), respectively. Renard V.4.5, Lemma (printed pp.119–120), records
the double-coset bijection over nonarchimedean local fields. Borel–Tits supplies
the arbitrary-field scope. Expressing the Weyl representatives through
`normalizerPoints` and the quotient-image subgroup and importing
cocharacter-based positivity/intersection definitions are **derived**
realizations; the displayed rational-point assertions are the cited source
content.

This file defines a proposition target. It supplies no proof or structural
axiom, and no instance asserting the proposition. The general proof remains an
obligation of the reductive-group program.

Source IDs: `borel-tits-1965-groupes-reductifs`, `renard-2026-representations-groupes-reductifs-padiques`.
