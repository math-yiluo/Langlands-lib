# Canonical operators as varying-group quotient automorphisms

Berkovich's category of spaces with operators retains both a space and its
topological operator group. In section 1.1, printed/PDF p.3, the original action
of an element `g` on a space extends to the object with operators, with group
homomorphism `h ↦ g h g⁻¹`. This module realizes that construction on the
existing actual finite positive-polyradius closed-ideal quotient actions and
derives its compatibility with the actual quotient category and spectra.

`operatorConjugation X g` is the continuous group homomorphism
`h ↦ g * h * g⁻¹` on the retained group of `X`. The homomorphism laws follow
from the group identities, and continuity uses multiplication by the fixed
elements `g` and `g⁻¹`. `algebraAction_mul_apply` records the existing forward
algebra action's multiplication formula by applying its homomorphism law.

The geometric arrow `operatorTranslation X g` has that conjugation group map
and the original bounded algebra action at `g⁻¹` as its contravariant algebra
pullback. Its equivariance is constructed from
`g⁻¹ * (g * h * g⁻¹) = h * g⁻¹`, applying the algebra action and its
multiplication formula. The boundedness comes from the original action's
bounded algebra endomorphism; it is not an additional hypothesis.

The operator at the group unit is the entire identity geometric arrow. The
composition formula is
`operatorTranslation X g ≫ operatorTranslation X h =
operatorTranslation X (h * g)`, in the category's diagrammatic order.
Equality of the group components follows from the conjugation formula, and
equality of the algebra components follows from the action multiplication
formula and `(h * g)⁻¹ = g⁻¹ * h⁻¹`. `operatorIso X g` uses the operator at
`g⁻¹` as its inverse; the composition and unit formulas prove both inverse
laws. `operatorAction X` bundles these isomorphisms as a genuine monoid
homomorphism from the original group to `Aut X`. Mathlib's automorphism
multiplication uses functional composition, so the same proved composition
formula gives its multiplicativity.

`operatorTranslation_naturality` says that every varying-group geometric
arrow `f : X → Y` intertwines the operator at `g` with the operator at
`f.groupHom g`. On group homomorphisms this is preservation of products and
inverses. On bounded algebras it is the original equivariance equation for `f`
at `g⁻¹`, with preservation of inversion by its group map. This is equality of
complete arrows, not just a statement on spectrum points. The restriction
compatibility formula is its specialization to the actual canonical
restriction arrow along any continuous group homomorphism; it needs no
injectivity assumption.

On actual bounded multiplicative spectra the canonical operator retains the
conjugation group homomorphism. Its point map is exactly the original jointly
continuous inverse-pullback action at `g`. The point equality is proved by
evaluating on every algebra element, identifying the original action at
`g⁻¹` with the inverse bounded automorphism at `g`, and applying spectrum
extensionality. The final complete spectrum naturality equation is the image
of the proved geometric naturality equation under the actual spectrum functor,
using its composition law.

Source: Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*,
unfinished manuscript (1996), section 1.1, printed/PDF pp.2–3, especially the
paragraph on p.3 before Example 1.1.3. Registered source
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf`, member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The original supplies the operator-extension construction and its conjugation
group map. The precise quotient action, bounded pullbacks, inverse and category
calculations, arbitrary-arrow compatibility, and actual spectrum formulas are
derived here from the existing quotient category and genuine spectrum functor.

The coefficient field has only `NormedField` and `IsUltrametricDist`
assumptions in universe `u`; the actual topological groups have independent
universe `v`. Completeness and a nontrivial valuation are not assumed.
The module constructs concrete algebra and topology prerequisites; it does not
identify norm-orbit continuity with the original analytic automorphism-group
topology, construct full analytic atlases or sites, or assert a topology on the
category's entire automorphism group.
