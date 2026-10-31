# Canonical restriction arrows and factorization of actual quotient morphisms

This internal construction uses `VariableActionSpace K`: an actual topological
group acting with norm-continuous algebra-element orbits on a finite
positive-polyradius closed-ideal quotient. A geometric arrow retains a continuous
source-to-target group homomorphism and a bounded target-to-source `K`-algebra
homomorphism satisfying equivariance. The field occupies universe `u` and the
groups an independent universe `v`.

For an object `X` and continuous homomorphism `f : H → X.groupType`, `restrict X f`
uses the existing action restriction. Its algebra, quotient norm and topology are
the original ones; its action is `h ↦ X.ρ (f h)`. `restrictionMap X f` is the
canonical geometric arrow from this restricted object to `X`. Its group map is
`f`, and its algebra pullback is the bounded identity. Its equivariance equation
is therefore definitional. Restriction applies to every continuous group
homomorphism; no injectivity or subgroup hypothesis is imposed.

`restrictIdIso` compares identity restriction with the original object. Its
forward arrow is the canonical restriction arrow. Both arrows have identity
group and bounded algebra maps. `restrictCompIso X f g` compares restriction
first along `f` and then along `g` with restriction along `f.comp g`. Both its
directions again use identity maps. The action equations hold by evaluation of
composition, and extensionality in the retained maps proves both inverse laws.
`restrictionMap_comp` proves that this comparison identifies the successive
canonical restriction arrows with the canonical arrow for the composite.

For any geometric arrow `f : X → Y`, `fixedFactor f` embeds the opposite of the
existing `restrictedAlgebraHom f` into the varying-group category. Its target is
`restrict Y f.groupHom`, its group map is the identity of the source group, and
its algebra map is exactly `f.algebraMap`. `fixedFactor_comp_restrictionMap`
proves that this arrow followed by the canonical restriction arrow is `f`.
`fixedFactor_unique` proves uniqueness among factors with identity group map:
projection of a factorization equality to algebra maps recovers the original
algebra map, and two-map extensionality finishes the proof.

`ofFixed_comp_spectrumFunctor` is an equality of complete functors. It says that
taking actual continuous spectra before or after the fixed-group embedding gives
the same retained groups and continuous seminorm maps. `spectrumRestrictIso`
uses the already constructed `NormContinuousAction.spectrumRestrictIso` and the
fixed-group topological embedding. It identifies the continuous spectrum of the
restricted algebra action with restriction of the original continuous spectrum
action. Its forward and inverse space maps are the identity on actual bounded
multiplicative seminorms. The previously published comparison derives
equivariance using preservation of inversion by the continuous group
homomorphism; this file reuses that result rather than assuming the comparison.

The spectrum image of `restrictionMap` is the original group homomorphism and
the identity on spectrum points, as follows from the bounded identity pullback.
`spectrumFunctor_fixedFactor` identifies the first spectrum factor with the
embedded fixed-group continuous spectrum map of `restrictedAlgebraHom`.
`spectrumFunctor_factorization` proves the complete geometric spectrum
factorization by applying the spectrum functor to the algebraic factorization
and using its composition law. All continuity is supplied by the existing actual
spectrum and continuous-action constructions.

The source motivation remains Berkovich's unfinished *Etale equivariant sheaves
on p-adic analytic spaces* (1996), section 1.1, printed/PDF pp.2–3, which uses a
continuous group homomorphism and compatible geometric map, with the identity
group homomorphism for fixed-group arrows. Registered source
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder digest
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf`, member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
These precise canonical arrows, uniqueness and spectrum equations are internally
derived from the actual quotient-action and category APIs, rather than claimed
as a numbered theorem of that source. They require only an ultrametric normed
coefficient field, with no completeness or nontrivial valuation hypothesis.
They do not construct the full analytic automorphism topology, a varying-field
analytic category, atlases, etale or quasi-etale sites, coverings or cohomology.
