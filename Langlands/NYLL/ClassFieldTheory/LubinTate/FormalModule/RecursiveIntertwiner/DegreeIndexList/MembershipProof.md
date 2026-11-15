# NYLL M353.005: proof of fixed-degree enumeration membership

This module proves the published proposition
`Langlands.NYLL.PortInternal.M353.d005Statement` as
`Langlands.NYLL.PortInternal.M353.d005`. It imports the exact published
`RecursiveIntertwiner.DegreeIndexList.Statements` module, which in turn
imports the list `Langlands.NYLL.PortInternal.M353.d003` from the sibling
`Definitions` module. Neither imported pair is edited.

## Statement and parameters

For an arbitrary universe `w`, let `sigma : Type w` carry a `Fintype`
instance. For every explicit degree `m : ℕ` and every explicit exponent
vector `d : {d : sigma →₀ ℕ // d.degree = m}` of total degree `m`, the
theorem has conclusion `d005Statement (sigma := sigma) m d`. By definition,
this says `d ∈ d003 (sigma := sigma) m`. That is, `d` occurs in the fixed list
of all degree-`m` exponent vectors. The list is the published `d003`; no other
enumeration or ordering is used.

The binder profile is that of the target: `sigma` is implicit, `Fintype sigma`
is an instance binder, and `m` and the subtype-valued `d` are explicit, in
that order. The only universe is `w`. There are no local-field,
coefficient-ring, uniformizer or Lubin–Tate-series parameters, matching the
target, whose source section variables do not occur in the elaborated type.
The final Lean `example` assigns the unapplied `@d005` to the fully quantified
proposition
`∀ {sigma : Type w} [Fintype sigma] (m : ℕ) (d : {d : sigma →₀ ℕ // d.degree = m}), d005Statement (sigma := sigma) m d`.

## Implemented proof

The proof is `classical` followed by `simp [d005Statement, d003]`.
Unfolding `d005Statement` turns the goal into `d ∈ d003 m`. Unfolding `d003`
turns it into membership of `d` in `Finset.univ.toList`, where `Finset.univ`
uses the `Fintype` instance `(Finsupp.finite_of_degree_eq m).fintype`
installed by `d003`. The simp lemma `Finset.mem_toList` reduces this to
`d ∈ Finset.univ`, and `Finset.mem_univ` closes it. The `classical` line is
kept from the source; this proof does not need it. The proof does not use
the nodup target M353.004 or any other result from the recursive-intertwiner
construction. The Lean check reports only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Source and modification record

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`,
private theorem `LubinTate.SameUniformizer.mem_degreeIndexList`, unit
M353.005, lines 62–66: statement at 62–64 and proof at 65–66. Its effective
section parameters are the universe `w` (line 29) and
`{sigma : Type w} [Fintype sigma]` (line 38). The file SHA-256 is
`627cad1b4ca585bb98d54d4dc97a88735e737576155b62e00476e824862983f6`.

The readable pinned source is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the current Library's `notes/errata/`.

Worker 722 extracted this proof on 15 November 2026. The changes are:

- the private source name is replaced by the public `PortInternal.M353.d005`;
- the section variables are written into the theorem's own binders;
- the conclusion is stated as the published `d005Statement` target;
- the source simp set `[degreeIndexList]` becomes `[d005Statement, d003]`,
  since the target definition must also be unfolded and the list is
  published as `d003`;
- the two broad source imports are replaced by the published Statements
  module.

A theorem docstring, focused module overview, modification notice and the
whole-type `example` are added. The source's `classical` step, universe,
binder kinds and proposition are unchanged. No patch10 edit affects this
source module, and no new definitions or instances are introduced.

The original 2026 copyright, Apache-2.0 release and author header are
retained verbatim. The existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are unchanged.
