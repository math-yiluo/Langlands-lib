# Invariants of ℓ-divisible systems of complexes

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem.Sections`
(left exact functors applied degreewise to `ℓ`-divisible systems of complexes,
and the section complexes of the truncated resolutions), and through it on
`Langlands.Cohomology.DivisibleSystem.LeftExact`, `…DivisibleSystem.Truncation`
and the earlier modules of the series. It also uses the Library's
`Langlands.Representation.Category.Abelian` (the abelian category
`SmoothRep R G`) and Mathlib's `Rep.quotientToInvariantsFunctor`. Write `K m`
for `K.obj m` and `j` for the projections `K.projection h : K m ⟶ K m'`
(`m' ≤ m`), as in the parent module.

On p.305 Harris chooses an open normal pro-`p` subgroup `H ⊂ S(ẽ)` acting
trivially on all `H_c^q(U(ẽ)_F̄, ℤ/ℓ^mℤ)`. Since `p` is prime to `ℓ`, the
functor `H⁰(H, ·)` is exact on `ℓ`-primary torsion modules, so the inclusion
`G_m^•(U(ẽ)_F̄)^H ⊂ G_m^•(U(ẽ)_F̄)` is a quasi-isomorphism. He concludes that the
cohomology "is thus canonically calculated by an ℓ-divisible system of
finite-length complexes of `ℤ/ℓ^mℤ[S(ẽ)/H]`-modules, in the obvious sense";
here `S(ẽ)/H` is a finite group.

This module takes `H`-invariants of an `ℓ`-divisible system of complexes of
smooth representations of `G`, for a normal subgroup `H`, and obtains an
`ℓ`-divisible system of complexes of representations of `G ⧸ H`. The condition
that every projection stays an epimorphism after taking `H`-invariants is an
explicit hypothesis. The module also gives the inclusion of the invariants as a
morphism of systems, and the instance for the truncated smooth Godement
resolutions. It proves neither the exactness of pro-`p` invariants nor that
the inclusion is a quasi-isomorphism.

## Taking invariants under a normal subgroup

`k` is a commutative ring, `G` a group, `H : Subgroup G` normal. Mathlib's
`Rep.quotientToInvariantsFunctor k H : Rep k G ⥤ Rep k (G ⧸ H)` sends a
representation `A` to the representation of `G ⧸ H` on the `H`-invariants of
`A`, and a morphism to its restriction. Mathlib has no `Additive` or limit
preservation instances for it. The following are in the namespace
`Langlands.Cohomology`.

- Instance `quotientToInvariantsFunctor_additive`: the functor is additive;
  `f + g` restricts to the sum of the restrictions (proved by `ext` and
  `rfl`).
- Instance `quotientToInvariantsFunctor_preservesLimits`: the functor preserves
  limits (`PreservesLimitsOfSize.{w, w}` for `Rep.{w}`). The composite with the
  forgetful functor `forget₂ (Rep k (G ⧸ H)) (ModuleCat k)` is, by definition,
  the restriction functor `Rep.resFunctor H.subtype` followed by Mathlib's
  `Rep.invariantsFunctor k H`. Both preserve limits (the invariants functor is
  a right adjoint), and the forgetful functor reflects limits, so Mathlib's
  `preservesLimits_of_reflects_of_preserves` applies.
- `quotientInvariantsInclusion k H`, imported from
  `Langlands.Representation.Induction.QuotientAdjunction` with its original
  `Langlands.Cohomology` namespace, is the natural transformation from
  `Rep.quotientToInvariantsFunctor k H ⋙ Rep.resFunctor (QuotientGroup.mk' H)`
  (invariants, inflated back to `G` along the quotient map) to the identity
  functor of `Rep k G`. Its component at `A` is the inclusion of the invariant
  submodule, Mathlib's `A.ρ.quotientToInvariants_lift H`.

## Smooth representations

`R` is a commutative ring and `G` a topological group; `SmoothRep R G` is the
Library's full subcategory of smooth representations, with inclusion
`SmoothRep.toRep`.

- Instance `smoothRep_toRep_preservesFiniteLimits`: `SmoothRep.toRep`
  preserves finite limits. The Library's object property
  `smoothRepProperty R G` is closed under kernels, so the inclusion preserves
  kernels (Mathlib's `ObjectProperty.preservesKernels_ι`), hence finite
  limits (Mathlib's `Functor.preservesFiniteLimits_of_preservesKernels`).
- `smoothQuotientInvariants R H := SmoothRep.toRep ⋙
  Rep.quotientToInvariantsFunctor R H : SmoothRep R G ⥤ Rep R (G ⧸ H)`. It is
  additive and preserves finite limits by the instances above.
- `smoothQuotientInvariantsInclusion R H` is `quotientInvariantsInclusion`
  restricted to smooth representations: the inclusion of the inflated
  invariants into `SmoothRep.toRep`.

## Systems of complexes

The following are in the namespace `Langlands.Cohomology.DivisibleSystem`.
`C`, `E` are abelian categories and `ℓ : ℕ`.

- `mapLeftExactNatTrans T α hF hF'`: for `T : DivisibleSystem C ℓ`, additive
  functors `F`, `F'` preserving finite limits with the epimorphism hypotheses of
  the LeftExact module's `mapLeftExact`, a natural transformation `α : F ⟶ F'`
  gives the morphism `T.mapLeftExact F hF ⟶ T.mapLeftExact F' hF'` with
  components `α` at each level; it commutes with the inclusions by the
  naturality of `α`.
- `mapComplexesNatTrans K α hΦ hΦ'`: the same for an `ℓ`-divisible system of
  cochain complexes `K` and the Sections module's `mapComplexes`, using `α`
  degreewise (Mathlib's `NatTrans.mapHomologicalComplex`).
  `mapComplexesNatTrans_tower_app_f` says that its degree-`q` component at level
  `m` is `α` at `(K m).X q` (by `rfl`).

Now `K : DivisibleSystem (CochainComplex (SmoothRep R G) ℕ) ℓ`.

- `epi_projection_f`: every degree of every projection of `K` is an
  epimorphism (the projections of the degree-`q` system are epimorphisms by
  the parent module). `epi_toRep_map_projection_f`: this persists under
  `SmoothRep.toRep`.
- `toRepComplexes K` is `mapComplexes K SmoothRep.toRep`, the same system with
  the smoothness forgotten.
- `quotientInvariantsComplexes K H hK` is
  `mapComplexes K (smoothQuotientInvariants R H) hK`, an `ℓ`-divisible system
  of complexes of representations of `G ⧸ H`. The hypothesis `hK h q` says that
  the `H`-invariants of the degree-`q` component of the projection
  `j : K m ⟶ K m'` form an epimorphism (equivalently a surjection), for all
  `m' ≤ m` and `q`. `quotientInvariantsComplexes_obj_X` identifies its terms
  with `(Rep.quotientToInvariantsFunctor R H).obj (SmoothRep.toRep.obj
  ((K m).X q))` (by `rfl`).
- `epi_inflatedQuotientInvariants_map_projection_f`: under `hK`, the projections
  stay epimorphisms after inflation along `G ⟶ G ⧸ H`, since both sides are
  surjectivity of the same linear map (Mathlib's `Rep.epi_iff_surjective`).
- `inflatedQuotientInvariantsComplexes K H hK` is the system of complexes of
  representations of `G` obtained by inflating the invariants: `mapComplexes`
  along `smoothQuotientInvariants R H ⋙ Rep.resFunctor (QuotientGroup.mk' H)`.
- `quotientInvariantsComplexesInclusion K H hK :
  inflatedQuotientInvariantsComplexes K H hK ⟶ toRepComplexes K` is
  `mapComplexesNatTrans` of `smoothQuotientInvariantsInclusion R H`: at each
  level `m`, the inclusion of the subcomplex of `H`-invariants into `K m`, and
  these inclusions commute with the inclusions `i` of the systems.
  `quotientInvariantsComplexesInclusion_tower_app_f` gives its degree-`q`
  component at level `m` as the inclusion of the invariant submodule.

## The truncated smooth Godement resolutions

`R`, `G`, `X`, `T : SmoothSheafDivisibleSystem R G X ℓ` and `D : ℕ` are as in
the smooth section of the Sections module, with `h` a proof of Worker 3's
unproved proposition `SmoothGodementZeroExactStatement R G X`, and
`H : Subgroup G` normal.

- `smoothGodementTruncatedQuotientInvariantSectionsSystem h T D H hterm hres`
  is the Sections module's `truncatedResolutionSectionsSystem` for the smooth
  Godement functor and the functor
  `smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H`: the
  `H`-invariants of the compact sections of the truncated resolutions, as an
  `ℓ`-divisible system of finite-length complexes of representations of
  `G ⧸ H`. The hypotheses `hterm` and `hres` say that this functor maps the
  projections of the term systems `F^q` (`q ≤ D`) and of the residual system
  `R (D + 1)` to epimorphisms.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed p.305. Worker 61 read the
page in the scanned original.

1. The obvious sense. The `ℓ`-divisible system "of complexes of
   `ℤ/ℓ^mℤ[S(ẽ)/H]`-modules" is formalized as an `ℓ`-divisible system, in the
   sense of the parent module, in the abelian category of cochain complexes of
   representations of `G ⧸ H` over `R`, as in the Resolution and Sections
   modules. Each level `m` is killed by `ℓ^m` by the parent module's axioms, so
   it is a complex of `ℤ/ℓ^mℤ[G ⧸ H]`-modules. The target is Mathlib's ordinary
   category `Rep R (G ⧸ H)`, with no topology on `G ⧸ H`; Harris's `S(ẽ)/H` is
   finite, and finiteness of `G ⧸ H` is neither assumed nor used.
2. The surjectivity. For the system of invariants to be `ℓ`-divisible the
   projections must stay surjective on `H`-invariants. In Harris this follows
   from the exactness of `H⁰(H, ·)` on `ℓ`-primary torsion modules for a pro-`p`
   group `H` with `p ≠ ℓ`. Here it is the explicit hypothesis `hK` (or `hterm`,
   `hres`). Worker 3's `ProPInvariantsExactStatement` in
   `Langlands.Cohomology.ProPInvariants.Statement` states such an exactness
   for representations of a profinite pro-`p` group; this module neither
   proves nor uses it, and does not derive `hK` from it.
3. The inclusion. `quotientInvariantsComplexesInclusion` is Harris's inclusion
   `G_m^•(U(ẽ)_F̄)^H ⊂ G_m^•(U(ẽ)_F̄)` for all `m` at once, as a morphism of
   `ℓ`-divisible systems after inflating the invariants back to `G`. Harris's
   claim that it is a quasi-isomorphism is the content of Worker 3's separate
   `ProPInvariantSubcomplexStatement`; it is not addressed here.
4. Sections. As in the Sections module, the smooth instance uses compactly
   supported sections of smooth equivariant sheaves in the Library's
   topological framework, standing in for sections over `U(ẽ)_F̄`, and `H` is
   any normal subgroup of the topological group `G` rather than an open normal
   pro-`p` subgroup of `S(ẽ)`.

The definitions `quotientInvariantsComplexes`,
`quotientInvariantsComplexesInclusion` and
`smoothGodementTruncatedQuotientInvariantSectionsSystem` are the formal
counterpart of Harris's system of invariants and its inclusion, with the
surjectivity as a hypothesis. The functor instances, the natural
transformations, the epimorphism lemmas and the component identities are
derived.

## Scope

The module does not prove the exactness of invariants under any subgroup, any
surjectivity of projections on invariants, or any quasi-isomorphism. It does
not use finiteness of `G ⧸ H` or the pro-`p` property of `H`. The free
resolutions (2.4)–(2.5), the complexes `C_{m,H}^•` and `C_m^•` of p.306, the
direct limit over `H` and Lemma 2.8 are not part of it.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
