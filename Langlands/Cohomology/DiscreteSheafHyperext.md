# Hyperext spectral sequences for equivariant compactly supported cohomology

Author: Worker 26. Applies the published hyperext spectral sequence to Worker 26's
derived complex `RΓ_c(X{G}, F)` of smooth compactly supported sections of discrete
sheaves on a twisted site
(`Langlands.Cohomology.DiscreteSheafDerivedComplex`: `compactComplex`,
`compactComplexHomologyIso`, `isZero_compactComplex_homology`). Uses
`Langlands.Cohomology.HyperextSpectralSequence` (`hyperextSpectralObject`,
`hyperextSpectralSequence`, `abutmentIso`),
`Langlands.Cohomology.HyperextSecondPage` (`secondPageExtIso`,
`isZero_secondPage_of_neg`) and
`Langlands.Cohomology.SmoothHyperextSecondPage` (`SmoothHyperext.secondPageAddEquiv`),
with Worker 13's smooth Ext (`SmoothExt.ext`, `SmoothExt.bifunctor`,
`SmoothExt.extZeroIso`), and Worker 26's
`Langlands.Sheaf.Equivariant.TwistedCompactSupport` (`discreteCompactSections`,
`discreteCompactDerived`, `discreteCompactDerivedZeroIso`). The construction
follows Worker 13's `compactHyperextSpectralSequence` on induced rational spectra
(`Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalDerivedComplex`).

All names are in the namespace `Langlands.Cohomology.DiscreteSheafHyperext`.

## Two general facts

Let `A` be an abelian category.

- `subsingleton_ext_of_isZero`: for a zero object `Y`, every Mathlib group
  `Ext^n(Y, Z)` has at most one element. Every class equals its composite with
  `mk₀ (𝟙 Y)`, and `𝟙 Y = 0`.
- `isZero_secondPage_of_isZero_homology K W p q`: with a derived category of `A`,
  on page 2 of the hyperext spectral sequence of `K` and `W` placed in degree `0`
  (standard t-structure), the object in position `(p, q)` is zero when
  `H^{-q}(K)` is zero. For `p < 0` this is the published `isZero_secondPage_of_neg`.
  For `p ≥ 0` the object is `Ext^p(H^{-q}(K), W)` (published `secondPageExtIso`),
  which vanishes by the previous fact.

## The twisted site

The setting is that of the section `TwistedCompact` of
`DiscreteSheafDerivedComplex`, with variables in the same order: a twisted site
built from `C`, `P`, `X`, `ρ : G →* Aut X` and a translation-invariant topology
`J`, points `Φ : I → J.Point.{w}` with an action of `G` on `I` by homeomorphisms,
a local action system `L` with finite equivariant refinements, `R : Type w`,
enough injectives among sheaves of `R`-modules on the twisted site, and derived
categories of discrete sheaves (universe `w'`) and of smooth representations
(universe `w''`). Unlike that module, the group has `G : Type w`, in the universe
of `R`. The published second-page identification for smooth representations is
stated for `SmoothRep.{u, u, u} R G` with `R` and `G` in one universe `u`. Here
`E : PointEquivariance ρ Φ`, `F` is a discrete sheaf of `R`-modules on the twisted
site, `W` is a smooth representation of `G` over `R`, and `d : ℤ`.

- `compactObject J R L E`: `compactComplex J R L E` followed by the inclusion
  `DerivedCategory.Plus.ι`, so `RΓ_c(X{G}, F)` in the unbounded derived category
  of smooth representations.
- `compactObjectHomologyIso J R L E F q`: for `q : ℕ`, its cohomology in degree
  `q` is `(discreteCompactDerived J R L E q).obj F`, Berkovich's
  `H^q_c(X{G}, F)` in shape. This is the published `compactComplexHomologyIso`.
- `isZero_compactObject_homology`: its cohomology vanishes in negative degrees.
- `compactObjectShiftHomologyIso J R L E F d n q h`: when `d + n = q`, the
  cohomology of the shift `RΓ_c(X{G}, F)⟦d⟧` in degree `n` is `H^q_c(X{G}, F)`.
  It uses Mathlib's shift isomorphism for the homology functors of the derived
  category (`Functor.shiftIso`).
- `isZero_compactObject_shift_homology`: that cohomology vanishes when
  `d + n < 0`.
- `compactHyperextSpectralSequence J R L E d F W`: the hyperext spectral sequence of
  `RΓ_c(X{G}, F)⟦d⟧` and `W` placed in degree `0`, for the standard t-structure.
  It is an `E₂` cohomological spectral sequence of abelian groups
  (`AddCommGrpCat.{w''}`).
- `compactHyperextAbutmentIso J R L E d F W n`: its intended abutment in total
  degree `n` (the term of the spectral object for the arrow `⊥ ⟶ ⊤`) is the group
  of morphisms `RΓ_c(X{G}, F)⟦d⟧ ⟶ W⟦n⟧` in the derived category. The two are
  equal by definition.
- `compactHyperextSecondPageAddEquiv J R L E d F W p q k h`: for `p k : ℕ`,
  `q : ℤ` and `h : q + k = d`, the object in position `(p, q)` on page 2 is
  additively equivalent to the smooth `Ext^p(H^k_c(X{G}, F), W)`, the `p`-th
  right derived functor of equivariant Hom out of `H^k_c(X{G}, F)`, at `W`. It
  composes `SmoothHyperext.secondPageAddEquiv` with `Ext^p` applied to
  `compactObjectShiftHomologyIso` in degree `-q`.
- `compactHyperextSecondPageZeroColumnAddEquiv`: in position `(0, q)` with
  `q + k = d`, the group of equivariant maps `H^k_c(X{G}, F) ⟶ W`.
- `compactHyperextSecondPageSectionsAddEquiv`: in position `(p, d)`, the smooth
  `Ext^p(Γ_c(X{G}, F), W)` of the smooth compactly supported sections
  `(discreteCompactSections J R L E).obj F`. This one also assumes sheafification
  of `R`-module presheaves for `J`, which `discreteCompactDerivedZeroIso` requires.
- `isZero_compactHyperextSecondPage`: the objects in positions `(p, q)` with
  `d < q` are zero, because `H^{d-q}_c(X{G}, F)` is zero in negative degree `d - q`.

So `E₂^{p,q} = Ext^p(H^{d-q}_c(X{G}, F), W)` for `q ≤ d`, the page vanishes for
`q > d`, and the intended abutment is `Hom(RΓ_c(X{G}, F)⟦d⟧, W⟦p + q⟧)`.

## Provenance and scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)* (1999),
Proposition 4.4, printed p.309 = PDF p.11, read in the original by Worker 26:

> There is a spectral sequence of `𝒪_m`-modules
> (4.4.1) `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̆_N, 𝒪_m(n-1)), 𝒜_ℓ(GJ, ℒ, K(m))) ⇒ H^{i+j}(S̄_{K(N,m)}, ℒ̃)`.
> Here `Ext^i` denotes the `i`-th derived functor of `Hom` in the category of smooth
> `𝒪_m[GJ]`-modules.

For `d = 2(n - 1)`, position `(i, j)` of `compactHyperextSpectralSequence` is
`Ext^i(H^{2(n-1)-j}_c(X{G}, F), W)`, Harris's `E_2^{i,j}` with `X{G}` in place of
the Drinfeld space `M̆_N` and `W` in place of the space of algebraic automorphic
forms `𝒜_ℓ(GJ, ℒ, K(m))`. Harris's `Ext^i` is the same derived functor
(`SmoothExt.ext`). The construction is derived, not a definition from the source:
a published general construction applied to Worker 26's derived complex. Harris
constructs (4.4.1) from a complex of projective smooth modules computing
`H^*_c(M̆_N, 𝒪_m)` (proof of Prop. 4.4, p.310), not from a t-structure; that
the two agree is not claimed here.

Not constructed or proved here: convergence of the spectral sequence, the
identification of the abutment with the cohomology `H^{i+j}(S̄_{K(N,m)}, ℒ̃)` of
the Shimura variety (which needs the uniformization (4.3) and duality), the
Drinfeld space and its group actions, the Tate twist `(n - 1)`, and any analytic
instance of the twisted site.

Universes: `C : Type u` with morphisms in `v`, `I : Type uI`, `G` and `R` in
`Type w`, derived categories of discrete sheaves in `w'` and of smooth
representations in `w''`. In the first section `A : Type uA` with morphisms in
`vA`, Mathlib `Ext` in `w'` and the derived category of `A` in `w''`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`.
