# Interlaced equivalences retaining their actual Frobenius formulas

This module strengthens the published construction in
`RealCharacterInducedInterlaced` by retaining its exact two-Frobenius function
formula in the existence conclusion. It adapts that module's implemented
tail-first and tail-second proofs and leaves every published pair unchanged.
The underlying tail constructions originate in `RealCharacterInducedSwap`,
whose internal provenance is described in those Library modules.

Let c be a real character, let d be a complex character datum, and write
L=|d.weight|, A=chA(d) and B=chB(d). Suppose 0<m<L and
B.exponent−c.exponent=−m. There is no extra parity or real-exponent-order
hypothesis. The actual mixed source and target are [character c,induced d]
and [induced d,character c]. The intermediate full-character lists are
M=[A,c,B], P=[c,A,B] and Q=[A,B,c].

`FirstTailData` records actual Frobenius data from [d,c] to M at position one
with multiplier tail(m,c.parity,(-1)^c.parity). `FirstGenericData` records
actual data M→P at position zero with multiplier
generic(L−m,pairParity(c,A)). The stated data include the actual target,
parity and symmetry sign; no formal swap placeholder is used.

`SecondTailData` records actual data [c,d]→M at position zero with multiplier
tail(L−m,pairParity(c,A),sigma0(c,A)). `SecondGenericData` records actual data
M→Q at position one with multiplier generic(m,pairParity(B,c)).

`exists_visible_tail_first` applies when m+c.parity is odd. It constructs a
bijective exact map T:[d,c]→[c,d] whose underlying function is precisely the
first-tail map followed by the first-generic map. The full-character output
is restricted to [c,d], so equality is asserted on the underlying functions.
`exists_visible_tail_second` applies when m+c.parity is even and constructs
a bijective exact E:[c,d]→[d,c] with the second-tail/second-generic formula.

Each proof retains the published construction: its recurrence parameters
prove exact intertwining; the proved integral landing theorem supplies the
induction-block Fourier condition; the nonvanishing generic multiplier and
two-axis uncertainty prove injection; the actual compact degree-layer
comparison upgrades injection to surjection. There is no landing,
uncertainty, or representation-theoretic assertion left as a premise.

`HasFormula` specifies the even forward formula or the odd inverse formula.
`exists_visible_equiv` packages a linear equivalence [c,d]≃[d,c], exact
intertwining and `HasFormula`, by taking the second-tail map in the even case
and the inverse first-tail map in the odd case.
`RealVisibleInterlacedStatement` is this proposition for all the stated
inputs, and `realVisibleInterlaced` proves it.

`equiv` chooses from this stronger existence statement, so `equiv_formula`,
`equiv_forward_formula` and `equiv_inverse_formula` retain the exact
Frobenius formulas after choice. `equiv_exact` and `equiv_symm_exact` prove
exact intertwining of both directions. The latter uses surjective descent of
the identity through the equivalence.

The canonical signs in these formulas are preserved literally. This result
makes no identification with a differential-sign polynomial word, no equality
with the older chosen `interlacedEquiv`, and no formula expressing an inverse
as a pseudo-inverse tail. It proves no full braid or GL4 kernel-image
containment. The unrestricted two-induction-block filtration,
`RealInducedInducedFiltrationStatement`, is not proved here; the theorem
`realInducedInducedFiltration` of `RealInducedInducedFiltrationProof` proves it.
