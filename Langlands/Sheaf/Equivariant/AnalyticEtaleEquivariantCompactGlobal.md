# Equivariant compact and ordinary étale cohomology on compact bases

## Provenance

This is an internal construction for the compact-base case of the
analytic étale compact-support spectral sequence. The source functors
are in Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(1995–1996 unfinished manuscript), §1.2, pp. 4–5 (invariant and smooth
ordinary sections and their derived functors) and §1.5, p. 11 (the same
with compact support). Printed and PDF pagination agree. Registered
literature ID `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The manuscript takes support in the underlying analytic space. On a
compact base all sections meet its compact support condition. The Lean
construction adapts this observation to the Library's point-support
model, extending `AnalyticEtaleCompactGlobal` from underlying modules to
the actual equivariant functors. It is not a separate theorem numbered
in the source.

## Inputs and scope

`X : LocalizedCategory.{u,v,v} (K := K)` is an analytic space over a
complete ultrametric normed field, with `ρ : G →* Aut X` over the fixed
field `K`. `L : Type uL` is a normed field with `NormedAlgebra K L`;
`h` supplies `EtaleSite.PointAxioms L x` for every `L`-valued point `x`
of `X`. The coefficients are modules over a commutative ring
`R : Type (max u (v + 1) uL)`. No extension `L` or geometric point
family is constructed here.

The **support-dropping map** is defined for any such space and action.
To make it invertible, the constructions assume `CompactSpace` on
`localizedSpaceFunctor.obj X` and surjectivity of `pointProjection L X`.
The latter lets one take the whole underlying space as the compact
superset in the point-support condition. Here no global Hausdorffness
or analytic continuity of `ρ` is needed for that argument; Berkovich's
ambient convention is Hausdorff `G`-spaces with continuous action
(§1.1, pp. 1–2), allowing base-field automorphisms. These are
identifications inside the Library models, without any equivalence
of the models with the source equivariant sites.

The smooth and invariant declarations use a topological group `G`.
Deriving the isomorphisms among étale `G`-sheaves uses the usual
`Small` and `HasAdmissibleRefinements` assumptions of their Library
models. The complex construction uses an independent universe for
the morphisms in the smooth-representation derived category.

## Constructions

The declarations are in `Langlands.Sheaf.Equivariant.Analytic`.

- `etaleCompactSectionsRepInclusion` sends the representation of
  compactly supported sections of a sheaf on the twisted étale site to
  the representation of all sections. The underlying map is the
  canonical inclusion of `AnalyticEtaleCompactGlobal`. It intertwines
  the actions because the compact-support action is the restriction
  of the global action (along the base endomorphism with twist
  `g⁻¹`). Naturality is the compatibility of section restriction
  with that inclusion. The isomorphism test is the published
  bijectivity of the inclusion on underlying modules, reflected in
  representations.
- `etaleGSheafCompactSectionsIsoOfCompactSpace` applies the smooth-part
  functor to this isomorphism and evaluates on the full subcategory
  `EtaleGSheaf`. `etaleGSheafInvariantCompactSectionsIsoOfCompactSpace`
  then takes `G`-invariants of the smooth representations.
- `etaleGSheafCompactCohomologyIsoOfCompactSpace` and
  `etaleGSheafInvariantCompactCohomologyIsoOfCompactSpace` apply the
  right-derived natural transformation in each degree to the
  respective section isomorphisms and their inverses. The first is an
  isomorphism of functors valued in smooth representations, the
  second in modules. Neither changes the source category of sheaves.
- `etaleGSheafCompactComplexIsoOfCompactSpace` compares the actual
  bounded-below complexes at a single sheaf. It computes both on the
  same injective resolution by `DerivedPlus.derivedComplexIso`, forms
  the cochain isomorphism from the smooth-section isomorphism in each
  degree (using its naturality for differentials), then localizes.
  Naturality of this last isomorphism in the sheaf is not asserted here.

In particular, this supplies the compact-base identification of the
smooth input complex and the invariant abutment groups with their
ordinary counterparts. It does **not** assert the compact-support
comparison to ordinary sheaves after restriction (`etaleCompactComparison`),
a spectral sequence, or any analogue for noncompact bases.
