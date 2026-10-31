# Continuous group restriction of positive-polyradius spectra

Authors: Worker 56 and Worker 36.

This derived construction adapts the continuous-spectrum comparison from the
published strict `EquivariantFiniteEtaleRestriction` implementation to the
actual arbitrary positive-polyradius quotient action category. It applies to
every object of that category, without a relative finite-étale hypothesis.

## Objects, actions, and hypotheses

Let `K` be an ultrametric normed field, let `G` and `H` be topological groups,
and let `f : H →ₜ* G` be a continuous group homomorphism. The field and both
groups occupy independent universes. An object
`X : PresentedAffinoidAlgebra.NormContinuousAction K G` is an action by bounded
automorphisms on the actual closed-ideal quotient of a finite
positive-polyradius restricted-series algebra, with continuous forward
orbits of every algebra element in its quotient norm.

The imported `NormContinuousAction.restrict f` retains the quotient algebra
and every bounded equivariant arrow and evaluates the original action at
`f h`. Its orbit continuity is proved by composition with the continuous
map `f`. The imported `spectrum` constructs the actual bounded multiplicative
spectrum, with its evaluation topology and inverse-pullback left action.
Joint continuity is proved there from continuous algebra orbits and
continuous group inversion.

## The comparison and its naturality

`NormContinuousAction.spectrumRestrictIso f X` has source the continuous
`H`-action on the spectrum of the restricted algebra action. Its target is
`(ContAction.res TopCat f).obj (spectrum X)`, the restriction of the original
continuous spectrum action.

The underlying topological space is the same spectrum in both constructions.
The comparison uses its identity isomorphism. To prove equivariance, the
implemented proof evaluates both inverse-pullback actions on a seminorm `x`
and algebra element `a`. The two evaluations are

```text
x (ρ (f (h⁻¹)) a)       and       x (ρ ((f h)⁻¹) a).
```

They agree by the group-homomorphism identity `map_inv`. The proof does not
assume that the two spectrum actions are equal or introduce continuity data
for a desired output. `Action.mkIso` packages the proved equivariance, and
`ObjectProperty.isoMk` lifts it to the actual continuous-action category.
`spectrumRestrictIso_hom_apply` and `spectrumRestrictIso_inv_apply` state
that both directions are the identity on seminorms.

`NormContinuousAction.spectrumRestrictionIso f` is a natural isomorphism

```text
(restrict f).op ⋙ spectrumFunctor
    ≅ spectrumFunctor ⋙ ContAction.res TopCat f.
```

Its component at `X` is the preceding identity spectrum comparison.
Naturality holds for every bounded equivariant algebra map: both paths are
pullback along that same bounded map. The proof uses full-subcategory,
action-morphism, and topological-map extensionality, followed by reflexivity
on each spectrum point. The opposite category supplies the required
contravariant algebra-to-space direction.

The file installs
`Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget` locally.
This is the shared identity forgetful functor on `TopCat`, so the target
continuous actions use the actual spectrum topology. Downstream files
spelling these targets can install the same local instance.

## Sources, provenance, and scope

Berkovich's unfinished *Étale equivariant sheaves on p-adic analytic spaces*
(1995–1996), section 1.1, printed/PDF pp. 1–3, defines continuous analytic
actions and morphisms changing acting groups along continuous
homomorphisms. The morphism's group homomorphism goes from the source
acting group to the target acting group, as does `f : H →ₜ* G` here.
Registered literature:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The exact comparison and proof are internal derived infrastructure,
adapting Worker 36's strict comparison to the published generalized
quotient category and its already constructed spectrum functor. The cited
source supplies motivation, rather than a numbered theorem asserting
this particular norm-orbit comparison.

The construction fixes `K`; it allows arbitrary continuous `f`, with no
injectivity or surjectivity requirement. No coefficient completeness,
nontrivial valuation, common operator bound, reducedness, or nonempty
spectrum is assumed. For incomplete `K`, the objects have their stated
normed-quotient meaning; the manuscript uses complete nonarchimedean fields.
The manuscript's analytic automorphism topology also uses compact analytic
domains and analytic functions. This comparison does not identify that
topology with continuity of algebra-element orbits. It does not construct
analytic atlases, all-domain analytic étaleness, coverings, or the
equivariant sites of section 1.2.
