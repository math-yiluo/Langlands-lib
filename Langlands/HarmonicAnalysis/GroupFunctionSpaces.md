# Fixed and uniformly invariant function spaces on a group

This definition unit gives all twelve fixed spaces and their twelve uniform
unions from Renard II.3.5, printed pp.45–46 / PDF pp.51–52, in
`Langlands.HarmonicAnalysis.GroupFunctionSpaces`. The source is David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, registered
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The carriers are the existing `LocallyConstant G ℂ`, `SchwartzBruhat G`,
`Distribution G` and `Distribution.compactlySupported`. The last is used as a
submodule of the full distribution space, so its fixed levels are intersections
inside that same space. The given topology and group operations are used
throughout. For the compact-distribution levels the scope is Hausdorff,
locally compact and totally disconnected, precisely the published compact
support interface's hypotheses and Renard's t.d. condition.

The suffixes `Left`, `Right` and `Both` mean invariance for `l`, `r`, and both
actions. `functions*`, `tests*`, `distributions*` and
`compactDistributions*` correspond respectively to the source's `C∞`, `D`,
`D′` and `E′` spaces. For locally constant functions the fixed submodule
of all scalar functions is pulled back along Mathlib's injective
`LocallyConstant.coeFnₗ ℂ`. For tests and distributions the actions are the
published `GroupAction.leftTests`, `rightTests`, `leftDistributions` and
`rightDistributions`. Thus the source's dual action conventions are retained,
including `r(g)f(x) = f(xg)`.

`fixed ρ K` abbreviates Mathlib's `Representation.invariants` for the actual
restricted representation `ρ.comp K.subtype`. Its membership formula is
definitional. The two-sided test space abbreviates the already published
`Hecke.TestFunction.biInvariant K K`; `testsBoth_eq_inf` proves its equality
with the intersection of the two restricted-representation fixed spaces.
This uses the existing `mem_biInvariant_iff`; the group actions reduce to the
published translations. No second test-function carrier is introduced.

`uniform` is exactly the set-theoretic union over compact open subgroups,
expressed by existence of an `OpenSubgroup` with compact underlying set.
Each `uniform*` abbreviation applies this union to the corresponding levels.
No closure or linear span is added. This unit does not prove the II.3.5
Lemma or Corollary, including the assertions that every compactly supported
test function lies in all three uniform test unions.
