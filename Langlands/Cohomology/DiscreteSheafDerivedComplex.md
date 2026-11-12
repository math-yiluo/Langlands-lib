# Derived section complexes of discrete sheaves on sites

Author: Worker 26. Specializes Worker 13's `Langlands.Cohomology.DerivedPlus`
(`derivedComplex`, `homologyIso`, `isZero_homology_of_neg`) to section functors
published by Worker 26: `discreteSectionsSmooth` and `discreteDerived` of
`Langlands.Sheaf.Equivariant.LocalActionCohomology`, `sheafCompactSections` and
`compactDerived` of `Langlands.Sheaf.PointSupport`, `discreteCompactSections` and
`discreteCompactDerived` of `Langlands.Sheaf.Equivariant.TwistedCompactSupport`,
and `discreteInvariantCompactSections` and `discreteInvariantCompactDerived` of
`Langlands.Sheaf.Equivariant.TwistedCompactComparison`. The model is Worker 13's
`Langlands.Cohomology.SmoothSheafDerivedComplex`, which does the same for smooth
equivariant sheaves on topological spaces.

For an additive functor `F` out of an abelian category with enough injectives,
`DerivedPlus.derivedComplex F` places an object in degree zero and applies
Mathlib's right derived functor on bounded below derived categories
(`DerivedCategory.Plus`). `DerivedPlus.homologyIso F (injectiveResolution A) q`
identifies its degree `q` cohomology, for `q : ℕ`, with `(F.rightDerived q).obj A`,
using Mathlib's chosen injective resolution `injectiveResolution A`.
Each derived category below is chosen by an instance `HasDerivedCategory` with
its own universe parameter (`w'` for the source, `w''` for the target); Mathlib's
`HasDerivedCategory.standard` supplies one.

## Sections over an object with a local action

Setting of `LocalActionCohomology`: `T : Type u` with `Category.{v} T`, a group
`G : Type uG` with a topology, a commutative ring `R : Type uR`, a local action
system `L : LocalActionSystem T G`, a Grothendieck topology `J` on `T` with
`[HasSheafify J (ModuleCat.{w} R)]`, `[L.HasFiniteEquivariantRefinements J]` and
`[EnoughInjectives (Sheaf J (ModuleCat.{w} R))]`, an object `U`, an open subgroup
`H` of `G` and `a : H →* (End U)ᵐᵒᵖ` with `ha : L.IsAdmissible U H a`.

- `sectionsComplex R L J ha`: the derived complex of
  `discreteSectionsSmooth R L J ha`, a functor from discrete module sheaves
  `L.DiscreteSheaf (ModuleCat.{w} R) J` to
  `DerivedCategory.Plus (SmoothRep.{uR, uG, w} R H)`.
- `sectionsComplexHomologyIso R L J ha F q`: its degree `q` cohomology at `F` is
  `(discreteDerived R L J ha q).obj F`.
- `isZero_sectionsComplex_homology`: its cohomology in degrees `n < 0` is zero.

## Compactly supported sections on a site with points

Setting of `PointSupport`: `C : Type u` with `Category.{v} C` and
`[LocallySmall.{w} C]`, a Grothendieck topology `J`, points `Φ : I → J.Point.{w}`
indexed by a topological space `I`, a commutative ring `R : Type w`,
`[HasSheafify J (ModuleCat.{w} R)]` and `[EnoughInjectives (Sheaf J (ModuleCat.{w} R))]`,
and an object `X₀`.

- `sheafCompactComplex J Φ R X₀`: the derived complex of
  `sheafCompactSections J Φ R X₀` (sections over `X₀` whose support in `I` is
  contained in a compact set), from `Sheaf J (ModuleCat.{w} R)` to
  `DerivedCategory.Plus (ModuleCat.{w} R)`.
- `sheafCompactComplexHomologyIso J Φ R X₀ F q`: its degree `q` cohomology at
  `F` is `(compactDerived J Φ R X₀ q).obj F`.
- `isZero_sheafCompactComplex_homology`: vanishing in degrees `n < 0` (this
  result does not need `LocallySmall`).

## Compactly supported sections on a twisted site

Setting of `TwistedCompactSupport`: a twisted site `twistedTopology ρ J` built
from `C`, a morphism property `P` (`[P.RespectsIso]`, `[P.ContainsIdentities]`),
an object `X`, `ρ : G →* Aut X` and a translation-invariant topology `J` on
`P.Over ⊤ X` with `[LocallySmall.{w} (P.Over ⊤ X)]`; points `Φ : I → J.Point.{w}`
with `[MulAction G I]`, `[TopologicalSpace I]`, `[ContinuousConstSMul G I]` and
`E : PointEquivariance ρ Φ`; `G` a topological group; a commutative ring
`R : Type w`; `L : LocalActionSystem (TwistedOver P ρ) G` with
`[HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]`,
`[L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]` and
`[EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))]`.

- `compactComplex J R L E`: the derived complex of
  `discreteCompactSections J R L E` (smooth compactly supported global
  sections), from discrete module sheaves on the twisted site to
  `DerivedCategory.Plus (SmoothRep.{w, uG, w} R G)`.
  `compactComplexHomologyIso J R L E F q`: its degree `q` cohomology at `F` is
  `(discreteCompactDerived J R L E q).obj F`. `isZero_compactComplex_homology`:
  vanishing in degrees `n < 0`.
- `invariantCompactComplex J R L E`: the derived complex of
  `discreteInvariantCompactSections J R L E` (the `G`-invariants of the smooth
  compactly supported global sections), with values in
  `DerivedCategory.Plus (ModuleCat.{w} R)`.
  `invariantCompactComplexHomologyIso J R L E F q`: its degree `q` cohomology
  at `F` is `(discreteInvariantCompactDerived J R L E q).obj F`.
  `isZero_invariantCompactComplex_homology`: vanishing in degrees `n < 0`.

All cohomology isomorphisms are stated objectwise; their naturality in `F` is
not proved.

## Provenance and scope

Derived infrastructure. Sources, read in the original by Worker 26:

- Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
  1995–1996 manuscript), §1.5, printed p.11 = PDF p.11: the cohomology groups
  `H^q_c(X(G), F)` and `H^q_c(X{G}, F)` are "the values of the high direct
  images" of the functors `Γ_{c,X(G)}` and `Γ_{c,X{G}} = lim_→ Γ_{c,X(N)}`.
- Harris, *Galois properties of cohomological automorphic forms on GL(n)*
  (1999), §2, printed p.304 = PDF p.6: compactly supported cohomology
  `H^q_c(U(ẽ)_{F̄}, F(T))` of étale sheaves in smooth `Z/ℓ^m Z[S(ẽ)]`-modules
  over `U(ẽ)`, computed with Berkovich's acyclic embedding (the functor
  `RΓ_c`). Proposition 4.4, printed p.309 = PDF p.11: a spectral sequence
  `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̆_N, 𝒪_m(n-1)), 𝒜_ℓ(GJ, ℒ, K(m))) ⟹
  H^{i+j}(S̄_{K(N,m)}, ℒ̃)`, where "`Ext^i` denotes the `i`-th derived functor
  of Hom in the category of smooth `𝒪_m[GJ]`-modules".

Correspondence. As recorded in `LocalActionCohomology`,
`TwistedCompactSupport` and `TwistedCompactComparison`, `discreteDerived` is
cohomology over an object with coefficients in a discrete sheaf as a smooth
representation, `discreteCompactDerived` has the shape of `H^q_c(X{G}, F)`,
`discreteInvariantCompactDerived` that of `H^q_c(X(G), F)`, and
`compactDerived J Φ R X₀ q` that of compactly supported cohomology on a site
with points. The complexes defined here are single objects of bounded below
derived categories whose cohomology is these derived functors, the form of
input to an `Ext` against compactly supported cohomology in the category of
smooth representations (Harris, Proposition 4.4). Packaging them in the derived
category is our construction; neither source states it in this form.

Differences and omissions: as in the modules specialized, an arbitrary site with
a local action system or group action and an arbitrary family of points replace
the analytic étale site and its geometric points, and derived functors are taken
among discrete sheaves. Not constructed or proved here: boundedness above, any
comparison between these complexes (in particular a derived-category version of
Berkovich's Corollary 1.5.2(i) or of the edge map), naturality of the cohomology
isomorphisms, Harris's spectral sequence, and any analytic instance.

Universes: `T, C : Type u` with `Category.{v}`, `G : Type uG`, `I : Type uI`;
in the first section `R : Type uR` with modules in `Type w`; in the other two
`R : Type w` (needed by `PointSupport`); derived categories in universes `w'`
and `w''`.

Source registrations: Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`.
Harris, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, file
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
