# The actual geometric rational Tate representation functor

Author: Worker 142.

This module constructs the rational linear Tate functor into the category of
representations of the actual geometric-fibre automorphism group. It supplies
the published proofs of geometric fibre finiteness and finite etaleness of
positive invertible abelian-scheme torsion. Its underlying modules and maps are
the already published rational Tate construction.

## Sources and derived provenance

- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
  (2001), Chapter I, printed p.18 / PDF p.26. Registered source
  `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
  This page defines the full and away Tate limits, their rationalizations over
  the integers, Hom⁰, End⁰, and an isogeny as an invertible rational homomorphism.
- Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary version built
  2012-02-08, Chapter X (10.1)–(10.3), printed pp.141–142 / PDF pp.145–146;
  first paragraph of (10.5), printed p.143 / PDF p.147; Definitions
  (10.25)–(10.26), printed p.150 / PDF p.154. Registered source
  `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
  `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
  The first passages construct field-level Tate representations from torsion
  and describe equivariance of the coordinate maps induced by homomorphisms.
  The last passages specify finite étale covers, their geometric-fibre
  functor, and its automorphism group.

These original passages were read directly and their file hashes checked.
No source-specific errata directory was present in the available Library.
The construction here is **derived**: it specializes the published
`RationalMonodromy` implementation using `FiniteEtale.geometricFiberFinite`
and `AbelianScheme.torsionFiniteEtale`, and bundles the existing equivariant
rational homomorphism maps as a functor into Mathlib's `Rep`. The selected
relative functor and its categorical packaging are not attributed verbatim to
the sources. No field-level rank theorem is used or proved in this module.

## Geometric inputs and carrier

The namespace is `Langlands.AbelianScheme.Tate.Geometric`. Fix a scheme
`S : Scheme.{u}`, an algebraically closed field `Ω : Type u`, an actual point
`s : Spec (.of Ω) ⟶ S`, and a predicate `P : ℕ → Prop`. The remaining order
hypothesis is

```lean
hunit : ∀ n : GroupScheme.Tate.Index P, IsUnit (n.val : Γ(S, ⊤))
```

`Index P` includes positivity. The acting group is exactly

```lean
FiniteEtale.FundamentalGroup s (FiniteEtale.geometricFiberFinite s)
```

It is the existing automorphism group of the actual finite-fibre functor on
finite étale covers. No group action, fibre-finiteness assertion, or torsion
finite-etaleness assertion is supplied as additional output data. For the
Harris–Taylor application the base is connected and locally noetherian, as in
EVM's fundamental-group definition. The implemented automorphism-group
construction and this functor are defined for arbitrary `S`; this wider scope
does not assert a Galois-category classification theorem.

For each actual `A : AbelianScheme S`, the carrier remains

```lean
Rational A (Over.mk s) P = ℚ ⊗[ℤ] Integral A (Over.mk s) P
```

The integral module is the existing coherent family of actual torsion sections
with the divisibility transitions. The opposite tensor order in Harris–Taylor
is already related by `GroupScheme.Tate.rationalTensorComm`.

## Representation and functor

`rationalRepresentation` is a `Representation ℚ` on this carrier. It uses
`rationalMonodromyMap` with the two geometric proofs supplied. Its one and
multiplication fields follow from the published rational action laws by
linear-map extensionality. Thus its convention is the left action

```text
ρ(1)(v) = v,             ρ(g*h)(v) = ρ(g)(ρ(h)(v)).
```

`rationalRepresentation_tmul` identifies its action as
`ρ(g)(q ⊗ x) = q ⊗ integralMonodromy(g)(x)`. The integral action is actual
evaluation on torsion-kernel fibres, applied coordinatewise to their limit.
`rationalRepresentation_toRational` gives the formula at the canonical
integral-to-rational map. Both formulas are definitional equalities.
`rationalRep` bundles this representation as an object of `Rep ℚ`.

`rationalRepMap` takes every element of `Rationalization.Hom A B` to the
existing `rationalHomMap`, bundled as a morphism of representations.
Its intertwining proof is the symmetry of `rationalMonodromy_homMap` after
linear-map extensionality. `rationalRepMap_toLinearMap` identifies the
underlying map exactly. No equivariance hypothesis is imposed on the rational
homomorphism.

`rationalRepFunctor` has domain `Rationalization (AbelianScheme S)`.
It sends an object with underlying abelian scheme `A` to `rationalRep A` and
uses these maps. Identity and composition follow from
`rationalHomMap_identity` and `rationalHomMap_comp`, using extensionality for
representation morphisms and intertwining maps. Its `Additive` and `Linear ℚ`
instances follow directly from linearity of `rationalHomMap` in its rational
homomorphism argument.

`rationalRepForgetIso` is a natural isomorphism from this functor followed by
`forget₂` to the existing `rationalizedFunctor (Over.mk s) P`. Its components
are identities; naturality is definitional equality of the underlying linear
maps. This comparison fixes the relation to the published functor, without
introducing another Tate module or rationalization.

The final formulas show that the functor maps an integral homomorphism to
`rationalMap`, a pure tensor `q ⊗ f` to `q • rationalMap f`, and an invertible
rational homomorphism to the existing `rationalIso` on underlying vectors.
They use `rationalHomMap_ofHom` or definitional equality.

## Scope

The choices `P(n) = True` and `P(n) = Nat.Coprime n m` give full and away
functors with their respective order-unit hypotheses. No finite rank, basis,
faithfulness, restricted-product identification, Weil pairing, or independence
of geometric base point is asserted. `Rep` here is the algebraic category of
representations. This module makes no continuity assertion and supplies no
topology on an automorphism group; the full and away rational topologies and
joint continuity are separate existing constructions available for geometric
specialization.
