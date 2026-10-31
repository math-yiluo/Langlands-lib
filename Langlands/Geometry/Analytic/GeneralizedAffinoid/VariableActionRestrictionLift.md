# Universal lifting through actual quotient-action restriction

This internal construction extends the canonical restriction arrows of
`VariableActionSpace` to arbitrary compatible continuous group maps. Objects
remain actual finite positive-polyradius closed-ideal quotient algebras with
norm-continuous operator actions. A geometric arrow has a source-to-target
continuous group homomorphism and a contravariant bounded algebra map.

For `f : H → X.groupType`, an actual arrow `h : Z → X`, and a continuous
homomorphism `k : Z.groupType → H` with `f.comp k = h.groupHom`,
`restrictionLift f h k hgroup` constructs an arrow from `Z` to `restrict X f`.
Its group map is `k`; its bounded algebra map is exactly `h.algebraMap`.
Equivariance follows by substituting the given equality of group maps into the
existing equivariance of `h`. The retained quotient, its norm and topology do
not change. No injectivity of `f` is required.

`restrictionLift_comp_restrictionMap` proves that composition with the canonical
restriction arrow gives the original full arrow `h`. Its group component is the
assumed equality and its algebra component is composition with the bounded
identity. `restrictionLift_unique` proves uniqueness with the prescribed group
map: projection of a competing factorization to bounded algebra maps determines
that component, and two-map extensionality proves equality of arrows.
`restrictionLift_existsUnique` states the resulting explicit universal property.

`restrictionHomEquiv` packages composition with the canonical restriction arrow
as an equivalence between arrows into the restricted object having group map
`k` and arrows into `X` having group map `f.comp k`. Its inverse is the
constructed lift. The inverse laws follow from extensionality and the proved
factorization. The two application formulas expose the actual arrow maps of
this equivalence.

The identity-group lift is the existing `fixedFactor`.
`restrictionLift_restrictionMap` proves that lifting the canonical restriction
arrow with identity intermediate group map gives the identity arrow.
`restrictionLift_precomp` proves that lifting commutes with precomposition by
any actual quotient arrow. `restrictionLift_comp` compares two successive lifts
with the lift for the composite continuous group homomorphism, using the
existing canonical comparison `restrictCompIso`. These equations follow by
comparing the retained group and bounded algebra maps, with the same original
algebra pullback on each side.

Taking actual continuous bounded multiplicative spectra preserves the prescribed
group map `k`. The continuous space map of a lifted arrow is exactly the
continuous space map of the original arrow, since the restricted object retains
the same quotient. The evaluation formula sends a seminorm `x` to
`a ↦ x (h.algebraMap a)`. The final spectrum factorization follows from the
composition law of the genuine continuous spectrum functor and the proved
geometric factorization. Continuity and the inverse-operator spectrum action
are supplied by that existing functor, not assumed as extra output data.

The motivation is Berkovich's unfinished *Etale equivariant sheaves on p-adic
analytic spaces* (1996), section 1.1, printed/PDF pp.2–3. The source defines
morphisms of spaces with operators using a continuous source-to-target group
homomorphism and a compatible geometric map, and observes on p.3 that this
category is fibred over topological groups. Registered source
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf`, member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The precise lift, morphism-set equivalence, coherence equations and spectrum
formulas here are derived from the concrete quotient-action APIs. They are the
explicit universal lifting calculation for this fixed-field quotient category,
not a numbered theorem quoted from the manuscript or a formal Mathlib
`IsFibered` instance.

The field has only `NormedField` and `IsUltrametricDist` assumptions, in universe
`u`; the actual topological groups occupy the independent universe `v`. No
completeness or nontrivial valuation is assumed. This unit does not identify
norm-orbit continuity with the source's full analytic automorphism topology,
and does not construct varying-field analytic spaces, geometric fiber products,
atlases, analytic domains, etale or quasi-etale sites, coverings or cohomology.
