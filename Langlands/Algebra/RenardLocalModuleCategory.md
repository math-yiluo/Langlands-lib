# The actual full subcategory of local modules

Authors: Worker 709 and Worker 1158. Worker 709 prepared the construction;
Worker 1158 checked the original passages, the imported interface and the
category and universe conventions, and prepared this definition submission
under whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857` revision 2.
It extends the published linear-map bridge of Worker 618 and Worker 6,
`Langlands.Algebra.RenardModuleLocalization`, without changing that interface.
The definitions provide the full subcategory, inclusion, canonical structured
arrow and an explicit factor candidate. They do not prove initiality of the
structured arrow. That assertion requires separate statement and proof units.

## Source and provenance

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.III.1,
printed pp.251–252 / one-based PDF257–258, especially example 4 on PDF258.
Registered identifier:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF257 defines a right universal problem; example 4 uses the full
subcategory of modules on which every denominator acts invertibly, included
into modules over the original ring. The localized module is explicitly
regarded as a module over that original ring.

The false parenthetical equivalence with a scalar inverse at each vector is
not adopted. The imported `IsSLocal` uses invertibility of the actual scalar
endomorphism, and the imported integer/rational counterexample explains the
discrepancy. The supplementary 2010-edition corrections
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF18–19, contain no correction of this parenthesis. This is a bounded
observation about those pages, not an exhaustive errata claim.

The object-property implementation and explicit universe lifts are internal
derived formulations. The source makes no choice of Lean universes or
particular full-subcategory representation. There is no new localization
quotient, replacement action or assumed localization certificate.

## Categories and locality

All declarations are in `Langlands.Renard.ModuleLocalization`.
Let `R : Type u` be any commutative unital ring and `S : Submonoid R`.
For any independent carrier universe `v`,
`localModuleProperty S : ObjectProperty (ModuleCat.{v} R)` is exactly
`fun N => IsSLocal S N`.
`LocalModuleCat S` is its `ObjectProperty.FullSubcategory`.
Its morphisms are all ambient R-linear maps between the corresponding
modules, with no additional condition on morphisms.

`localModuleInclusion S` is the actual `ObjectProperty.ι` into
`ModuleCat.{v} R`. `localModuleInclusionFullyFaithful S` supplies the existing
fully faithful structure: its preimage merely wraps the same ambient map.
This construction targets modules over R, rather than modules over
`Localization S`.

`isSLocal_ulift_iff S N` proves
`IsSLocal S (ULift.{w} N) ↔ IsSLocal S N`
for independently variable `u`, `v` and `w`. The proof uses the published
equivalence with bijectivity of scalar multiplication and transports its
injectivity and surjectivity along `ULift.up` and `ULift.down`.

## Explicit universe conventions and canonical data

Let `M : Type v` have an additive commutative group and a unital R-module
structure. The ring universe `u`, source universe `v` and enlargement
universe `w` are independent. Write `κ = max u v w`.

The actual type `LocalizedModule S M` lives in `Type (max u v)`.
Consequently a same-universe category containing M need not contain this
localization. The construction raises carriers explicitly into the common
ambient category `ModuleCat.{κ} R`:

| Name | Actual underlying object or map |
| --- | --- |
| `raisedSource M` | `ModuleCat.of R (ULift.{max u w} M)` |
| `canonicalLocalObject S M` | `ModuleCat.of R (ULift.{w} (LocalizedModule S M))`, together with its locality proof |
| `canonicalModuleMap S M` | `ULift.up ∘ LocalizedModule.mkLinearMap S M ∘ ULift.down`, as an ambient categorical morphism |
| `canonicalStructuredArrow S M` | `StructuredArrow.mk (canonicalModuleMap S M)` for the actual local-module inclusion at carrier universe κ |

Every lift has the explicit R-linear equivalence `ULift.moduleEquiv` back
to the original carrier. These are universe raises, with no `Small`
assumption, shrinking, identification of independent universes or restriction
on the cardinality of M. Every independently sized target can likewise be
raised into a common ambient universe by taking w to include its carrier
universe. Initiality, when separately proved, will quantify over *every*
local object in the common ambient category.

The canonical locality proof uses `isSLocal_ulift_iff` and the imported
`localizedModule_isSLocal` of the actual construction.
`canonicalModuleMap_up S M m` states the displayed map formula at every
raised source vector and is definitional.
`canonicalLocalObject_subsingleton S M h0`, with sole extra assumption
`h0 : (0 : R) ∈ S`, transports the imported subsingleton result for the
actual localization through ULift. Thus the zero-denominator boundary is
retained.

## Factor candidate and proof boundary

For any `N : LocalModuleCat.{u,κ} S` and ambient morphism
`f : raisedSource M ⟶ N.obj`, `canonicalFactor S M N f` is a morphism
from the actual canonical local object to N. Its underlying linear map is

```text
factor S N.property (f.hom ∘ ULift.up) ∘ ULift.down.
```

The function named `factor` here is the already published
`LocalizedModule.lift` bridge; `N.property` is exactly the required locality
hypothesis. `canonicalFactor_apply` exposes the formula and is definitional.
The present file provides no categorical factorization or uniqueness theorem
and no `IsInitial`, `IsUniversal` or adjunction structure. A focused
Prop-valued statement must first be published before such a proof is submitted.
Mathlib's `StructuredArrow.IsUniversal` is initiality data, so a proposition
target should express its existence with `Nonempty`.

The source's right universal problem has equation
`canonicalModuleMap ≫ localModuleInclusion.map g = f`, with this arrow
direction. The independent-universe linear-map theorem in the imported
module remains available unchanged. Ring-localization example 3,
polynomial-module/endomorphism equivalence and example 5, exactness, general
adjunction theory and the remainder of Appendix A remain parent obligations.
The source comparison remark applies only to isomorphisms compatible with
the canonical maps; it does not assert uniqueness among all isomorphisms.

The ring may be the zero ring and S may contain zero. No nontriviality,
faithful-action, domain, finite-generation or finite-dimensionality premise
is imposed. The construction uses pinned Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, principally
`Algebra/Module/ULift.lean`, `CategoryTheory/ObjectProperty/FullSubcategory.lean`
and `CategoryTheory/Comma/StructuredArrow/Basic.lean`.
