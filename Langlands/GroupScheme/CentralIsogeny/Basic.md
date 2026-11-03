# Central isogenies and their scheme-theoretic kernels

This module works over an arbitrary scheme `S : Scheme.{u}`. It reuses the
Library's `GroupScheme S = Grp (Over S)`, actual pullback kernel from
`Langlands.AbelianScheme.Kernel`, `IsIsogeny` from
`Langlands.AbelianScheme.Isogeny`, and all-test `center` and `IsCentral` from
`Langlands.GroupScheme.Rational.Characters`.

`IsCentralIsogeny f` requires the actual morphism of schemes underlying `f`
to be finite, flat, surjective and locally of finite presentation, and requires
`IsCentral (kernelι f)`. Thus its finite fppf condition is about the morphism of
schemes. No surjectivity on points over an arbitrary field or test scheme is
asserted. Centrality uses every scheme-valued point and every restriction of
such a point; the kernel and centre retain their possible nonreduced structure.

The source convention is Conrad, *Reductive group schemes* (2014), Definition
3.3.9, PDF p.103: for smooth affine group schemes an isogeny is finite, flat and
surjective, and is central when its kernel is central. The Lean interface makes
local finite presentation explicit, so it applies over general bases without
an implicit smoothness or finite-presentation premise. In the source's smooth
finite-type field-group setting that extra condition is automatic. Milne,
*Algebraic Groups* (2017), Definition 18.1, printed p.387 (PDF p.403), gives the
same central-kernel condition for connected group varieties. The official
registered Milne errata snapshot of 2026-11-02 was read in full: its correction
on printed p.388 concerns the reductivity hypothesis in Remark 18.4, and its
printed p.389 correction makes the factorization arrow in 18.8 land in `G'`.
Neither changes Definition 18.1. No project errata note for the Conrad source
was found in the current Library.

The remaining declarations are internal consequences of these definitions.
`mem_range_kernelι_iff` uses the published natural equivalence
`kernelPointsEquiv`: a point lies in the range of the actual kernel inclusion
exactly when `f` kills it. `isCentral_iff_range_le_center` and
`isCentral_kernelι_iff` translate centrality into inclusion of the full range
functor or its equivalent killed-point condition. The kernel is finite, flat
and locally of finite presentation over `S` by the published kernel pullback
square and stability under base change. The projection lemmas and `fppf`
expose the defining scheme conditions. With local finite presentation already
available, `isCentralIsogeny_iff` recovers the existing isogeny predicate plus
central kernel. Every isomorphism, and in particular every identity, satisfies
the definition because its kernel has only identity points on every test scheme.

No existence, representability of the centre, smoothness of the kernel,
classification or nontrivial structure theorem is claimed here.
