# Local comparison of rigidified and ordinary line-bundle classes

This helper constructs rigidifications locally on the test scheme and studies
the published canonical forgetful map. The schemes, morphism `f`, section `ε`
and section law are arbitrary in universe `u`. No quasi-compactness,
quasi-separatedness or structure-sheaf hypothesis is used.

`forgetClasses_injective` proves that forgetting rigidification is injective
on actual isomorphism classes. Equality of ordinary Picard classes supplies
an isomorphism of the underlying line bundles. The published
`nonempty_iso_of_forget_iso` corrects that isomorphism to respect the
rigidifications, using the retraction of the section on the base change.
Quotient soundness gives equality of rigidified classes.

`relativeSectionPullbackIso` combines pullback composition, naturality of
the actual relative section, and inverse pullback composition. It identifies
restriction along the section after relative pullback with pullback of the
original section restriction. `rigidifyPullback` uses this isomorphism and a
supplied trivialization to rigidify the actual pulled-back line bundle.
`exists_forgetClasses_eq_map_classOf` applies this construction on an open
of the test scheme, using the comparison between restriction of a module and
pullback along the open immersion. Its ordinary class is precisely the
published geometric pullback class.

`forgetClassNatTrans_isLocallySurjective_zariski` chooses an ordinary
line-bundle representative, restricts it to the section, and uses that line
bundle's trivializing open cover of the test scheme. On each member the
previous construction gives a rigidified class with the required ordinary
image. Thus the image sieve is Zariski covering.
`forgetClassNatTrans_isLocallySurjective` uses the inclusion of the Zariski
precoverage in the fppf precoverage and the induced slice topologies.

These are internal consequences of the published line-bundle, rigidification,
pullback and site constructions. Their mathematical role is the local
comparison in Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft, Chapter VI §1, (6.2), printed pp.88–89 / PDF pp.92–93.
The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Worker 149 read these pages and Definition (6.1) on PDF p.91. The implemented
local proof does not require global normalization by an inverse bundle.

This module does not prove that rigidified classes form an fppf sheaf, or
that their comparison with the Picard sheaf is an isomorphism. Those require
the separate descent and sheaf arguments.
