# Cohomology and base change for line bundles with fibre cohomology in degree zero

Module `Langlands.AlgebraicGeometry.Modules.FibreCohomologyBaseChange`.

Let `R` be a commutative ring and `f : X ⟶ Spec R` a smooth proper morphism.
Let `L` be a line bundle on `X` whose cohomology on every geometric fibre is
concentrated in degree zero, with an `r`-dimensional space of sections. Then the
`R`-module of sections `Γ(X, L)` is finite projective of constant rank `r`, and
forming it commutes with every affine base change.

## Definition

`GeometricFibreCohomologyDegreeZero f L r` is the fibre hypothesis. It takes
`R : CommRingCat.{u}`, `f : X ⟶ Spec R`, a line bundle `L : LineBundle X` and
`r : ℕ`. It says the following for every algebraically closed field `k : Type u`,
every ring map `φ : R ⟶ CommRingCat.of k`, and every pullback square
`IsPullback p f' f (Spec.map φ)` with `p : X' ⟶ X` and
`f' : X' ⟶ Spec (CommRingCat.of k)`:

- `(relativeCohomology f' i).obj ((Scheme.Modules.pullback p).obj L.obj)` is
  zero for every `i > 0`;
- the `Module.finrank k` of the degree-zero cohomology
  `(relativeCohomology f' 0).obj ((Scheme.Modules.pullback p).obj L.obj)` is
  `r`.

The hypothesis quantifies over every pullback square, not only Mathlib's chosen
fibre product. So it does not depend on a choice of fibre product.

## Main result

`sections_of_geometricFibreCohomologyDegreeZero f L h` assumes `[Smooth f]`,
`[IsProper f]` and `h : GeometricFibreCohomologyDegreeZero f L r`. Write
`M = (relativeGlobalSections f).obj L.obj` for the `R`-module of sections. The
theorem proves four statements:

1. `Module.Finite R M`;
2. `Module.Projective R M`;
3. `Module.rankAtStalk M p = r` for every `p : PrimeSpectrum R`;
4. for every `T : CommRingCat.{u}`, every `φ : R ⟶ T` and every pullback square
   `hp : IsPullback p f' f (Spec.map φ)`, the Library base-change map on
   sections `scalarSectionsBaseChangeMap φ f f' p hp.w L.obj` is an
   isomorphism. This map is `T ⊗_R Γ(X, L) ⟶ Γ(X', p^* L)`.

## Auxiliary result

`geometricFibresDegreeZero_of_universalPerfectModel h hK a hbc` transfers the
fibre hypothesis to a complex. Let `K` be a strictly perfect complex of
`R`-modules with a derived morphism `a : K ⟶ RΓ_R(X, L)`. Suppose every
base-changed model `perfectModelBaseChange hp L hK a` is an isomorphism. Then
`K` satisfies `ModuleComplex.GeometricFibresDegreeZero K r`, the ring-level
hypothesis of `Langlands.Cohomology.ModuleComplex.GeometricFibreDegreeZero`.

## Proof

**Auxiliary result.** Let `k` be algebraically closed and `φ : R →+* k`. Use
Mathlib's fibre product of `f` and `Spec k ⟶ Spec R`. The base-changed model is
an isomorphism `k ⊗_R K ≅ RΓ_k(X_k, p^* L)` in the derived category. In degrees
`n ≥ 0`, the Library isomorphism
`DerivedPlus.homologyIsoOfIsoDerivedComplex` identifies `H^n(k ⊗_R K)` with
`(relativeCohomology f' n).obj (p^* L)`. So the fibre hypothesis gives vanishing
for `n > 0` and dimension `r` for `n = 0`. In negative degrees, homology is
invariant under the derived isomorphism, and the Library lemma
`DerivedPlus.isZero_homology_of_neg` shows that the target has no negative
cohomology.

**Main result.** The Library theorem `universalPerfectModel f L` gives a
strictly perfect `K` with a derived isomorphism `a : K ≅ RΓ_R(X, L)` whose base
changes along all pullback squares are isomorphisms. By the auxiliary result,
`K` satisfies `GeometricFibresDegreeZero K r`. The ring-level theorem
`ModuleComplex.homology_zero_of_geometricFibresDegreeZero` then shows two
things:

- `H^0(K)` is finite projective of constant rank `r`;
- every degree-zero comparison `baseChangeDerivedHomologyMap φ K 0` is an
  isomorphism.

Composing `homologyIsoOfIsoDerivedComplex` in degree zero with
`relativeCohomologyZeroIso` gives an `R`-linear isomorphism
`H^0(K) ≅ Γ(X, L)`. This transfers finiteness, projectivity and the rank at
stalks (`Module.rankAtStalk_eq_of_equiv`), proving (1)–(3). For (4), the
Library theorem `isIso_scalarSectionsBaseChangeMap_iff_of_perfectModel` reduces
the claim to the comparison `baseChangeDerivedHomologyMap φ K 0`, which is an
isomorphism.

## Provenance

This is an internal affine form of Grothendieck's cohomology and base change
for the zeroth direct image:

- Mumford, *Abelian Varieties*, Chapter II, §5: Corollary 2 (pp.50–52) and
  Corollary 3 (p.53);
- the Stacks Project, Derived Categories of Schemes (`perfect.tex`),
  `lemma-flat-proper-perfect-direct-image-general`, for proper perfect direct
  images and arbitrary base change.

Here it is specialised to a line bundle on a smooth proper scheme over an
affine base. The fibre hypothesis is stated over all algebraically closed
fields. The geometric input is the Library's universal perfect model. The
module adds no new geometric theorem beyond combining that model with the
ring-level result.
