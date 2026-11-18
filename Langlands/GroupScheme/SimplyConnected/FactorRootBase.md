# The ambient simple base induces an actual factor base

This derived internal construction keeps the actual ambient split pinning,
product factors, compatible tori and supplied actual factor root datum.
Distinct factor-torus blocks have zero cross projection. Consequently an
ambient root assigned to another factor restricts to zero on this factor torus.

Project the ambient positive cocharacter to the factor torus. Its pairing with
a factor root is the original positive scale times the height of the
corresponding ambient root, so it is regular on every factor root. The
published integral cocharacter-face base construction yields a genuine base
on the factor's original lattices. Its positive roots correspond exactly to
the positive ambient roots carried by the factor.

An ambient simple root carried by the factor is simple for this base: a
positive decomposition into factor roots would inflate to a positive
ambient decomposition, contradicting ambient simplicity. Conversely, restrict
the integral expression of any ambient root in its ambient simple roots.
Simple roots in other factors restrict to zero, and those in this factor
become its actual roots. Thus all factor roots are integrally spanned by the
factor roots whose ambient indices are simple. These are already simple for
the induced base; independence of that base forces every simple root to lie
in this subset. `mem_inducedBase_iff` gives the exact equality of simple supports.

No field characteristic or universe restriction is imposed. The construction
uses actual roots and actual torus maps throughout.

`simpleRootIndexEquiv` packages the exact equivalence of simple vertices
with the ambient factor fibre. `pairing_simpleRootIndexEquiv` preserves every
ordered integral root-coroot entry under that equivalence.
