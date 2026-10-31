# Vanishing of cohomology from a perfect representative and its quotient fibres

Module `Langlands.AlgebraicGeometry.Modules.PerfectFibreVanishing`. The generic derived
category lemmas are in the namespace `Langlands.Cohomology.DerivedPlus`. The scheme results
are in `Langlands.AlgebraicGeometry.Modules.DerivedSections`, with the local instance
`HasDerivedCategory.standard`, as in the published `UniversalPerfectSectionsStatement`.

## Definitions

```lean
def idealQuotientHom {R : CommRingCat.{u}} (m : Ideal R) : R ⟶ CommRingCat.of (R ⧸ m) :=
  CommRingCat.ofHom (Ideal.Quotient.mk m)
```

The quotient map `R → R ⧸ m` of a commutative ring by an ideal, as a morphism of
`CommRingCat`. `Spec.map (idealQuotientHom m) : Spec (R ⧸ m) ⟶ Spec R` is the closed
immersion of `V(m)`. For a maximal ideal `m` this is the inclusion of the closed point `m`
with its residue field `κ(m) = R ⧸ m`.

```lean
def homologyIsoOfIsoDerivedComplex {K : CochainComplex D ℤ} {X : C}
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Plus.ι.obj ((derivedComplex F).obj X))
    (n : ℕ) :
    K.homology n ≅ (F.rightDerived n).obj X
```

Here `C` and `D` are abelian categories with derived categories, `C` has enough injectives,
`F : C ⥤ D` is additive, and `derivedComplex F` is the published
`DerivedPlus.derivedComplex` (`X` placed in degree zero, then the right derived functor on
bounded below derived categories). If a cochain complex `K` is isomorphic in `D(D)` to the
derived complex of `X`, then `Hⁿ(K) ≅ (F.rightDerived n).obj X` for `n : ℕ`. The isomorphism
is Mathlib's `DerivedCategory.homologyFunctorFactors`, then `e`, then the published
`DerivedPlus.homologyIso`.

The module also adds the instance

```lean
instance instAdditiveRelativeGlobalSectionsOf {X : Scheme.{u}} {A : Type u} [CommRing A]
    (g : X ⟶ Spec (CommRingCat.of A)) : (relativeGlobalSections g).Additive
```

It is the published additivity instance for `relativeGlobalSections`, restated for a base
`Spec (CommRingCat.of A)`. Lean's instance search does not find the published instance for
such a base, because `↑(CommRingCat.of A)` reduces to `A`. The instance is needed to form
`derivedComplex` over `Spec (R ⧸ m)` in the main theorem.

## Main results

Generic lemmas, in `Langlands.Cohomology.DerivedPlus`, with `F`, `K`, `X` and `e` as above:

```lean
theorem acyclic_of_iso_derivedComplex (e : ...)
    (h : ∀ n : ℕ, IsZero ((F.rightDerived n).obj X)) : K.Acyclic

theorem isZero_rightDerived_of_iso_derivedComplex (e : ...)
    (hK : K.Acyclic) (n : ℕ) : IsZero ((F.rightDerived n).obj X)
```

So `K` is acyclic exactly when every `(F.rightDerived n).obj X` (with `n : ℕ`) is zero.

Scheme results, in `Langlands.AlgebraicGeometry.Modules.DerivedSections`.
`relativeGlobalSections` and `relativeCohomology` are the published `R`-module global
sections and cohomology over a base `Spec R`. `ModuleComplex.IsStrictlyPerfect` and
`ModuleComplex.baseChange` are the published bounded finite projective complexes and ordinary
degreewise extension of scalars.

```lean
theorem isZero_relativeCohomology_of_quotient_fibres
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (M : X.Modules)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : ModuleComplex.IsStrictlyPerfect K)
    (e : DerivedCategory.Q.obj K ≅
      DerivedCategory.Plus.ι.obj ((derivedComplex (relativeGlobalSections f)).obj M))
    (eq : ∀ m : Ideal R, m.IsMaximal →
      Nonempty (DerivedCategory.Q.obj
          ((ModuleComplex.baseChange (idealQuotientHom m).hom).obj K) ≅
        DerivedCategory.Plus.ι.obj
          ((derivedComplex
            (relativeGlobalSections (pullback.snd f (Spec.map (idealQuotientHom m))))).obj
              ((Scheme.Modules.pullback (pullback.fst f (Spec.map (idealQuotientHom m)))).obj
                M))))
    (hfib : ∀ m : Ideal R, m.IsMaximal → ∀ n : ℕ,
      IsZero ((relativeCohomology (pullback.snd f (Spec.map (idealQuotientHom m))) n).obj
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (idealQuotientHom m)))).obj M)))
    (n : ℕ) :
    IsZero ((relativeCohomology f n).obj M)
```

Let `f : X ⟶ Spec R` be any morphism of schemes and `M` any `𝒪_X`-module. Suppose that:

- `K` is a strictly perfect complex of `R`-modules isomorphic in `D(R)` to `RΓ(X, M)`;
- for every maximal ideal `m`, the ordinary scalar extension `K ⊗_R R ⧸ m` is isomorphic in
  `D(R ⧸ m)` to `RΓ(X_m, M_m)`. Here `X_m` is the actual fibre product
  `pullback f (Spec.map (idealQuotientHom m))` over `Spec (R ⧸ m)`, and `M_m` is the module
  pullback of `M` along its first projection;
- `Hⁿ(X_m, M_m) = 0` for every maximal `m` and every `n : ℕ`.

Then `Hⁿ(X, M) = 0` as an `R`-module for every `n : ℕ`. The isomorphisms are hypotheses: no
comparison map between `K ⊗ R ⧸ m` and the fibre is required.

```lean
theorem isZero_relativeCohomology_of_universalPerfectSections
    (hups : UniversalPerfectSectionsStatement.{u})
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) [Smooth f] [IsProper f]
    (L : Picard.LineBundle X)
    (hfib : ∀ m : Ideal R, m.IsMaximal → ∀ n : ℕ,
      IsZero ((relativeCohomology (pullback.snd f (Spec.map (idealQuotientHom m))) n).obj
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (idealQuotientHom m)))).obj L.obj)))
    (n : ℕ) :
    IsZero ((relativeCohomology f n).obj L.obj)
```

This takes the published proposition `UniversalPerfectSectionsStatement` as a hypothesis
`hups`; it does not prove it. Given `hups`, for a smooth proper `f : X ⟶ Spec R` and a line
bundle `L` on `X`, if the cohomology of the pullback of `L` to every fibre `X_m` over a maximal
ideal vanishes in every degree, then `Hⁿ(X, L) = 0` for every `n : ℕ`.

## Provenance

`idealQuotientHom`, `homologyIsoOfIsoDerivedComplex` and the instance are internal adapters
with no literature counterpart.

The generic lemmas restate the published `DerivedPlus.homologyIso` and
`DerivedPlus.isZero_homology_of_neg`: the derived complex has cohomology `Rⁿ F(X)` in degree
`n ≥ 0` and none in negative degrees.

`isZero_relativeCohomology_of_quotient_fibres` is a derived consequence of Stacks, More on
Algebra, Lemma `lemma-check-perfect-pointwise` (tag 068V). Its proof of (3) ⇒ (1) first shows
`Hⁱ(K) = 0` for `i ∉ [a, b]`. When every reduction `K ⊗ κ(m)` is acyclic, condition (3) holds
for every interval, and an interval that omits a given degree `i` gives `Hⁱ(K) = 0`. See `more-algebra.tex` at git commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, lines 20031–20062, in the registered source
`stacks-perfect-complexes-a04446e5`. It enters through the published
`ModuleComplex.acyclic_of_isStrictlyPerfect_of_residue_acyclic`, whose Markdown states the
specializations (strictly perfect complexes and the ordinary tensor product with `R ⧸ m`).
Here they are applied to the complex that computes `RΓ(X, M)`.

The hypothesis `e` together with `eq` is the shape of the conclusion of
`UniversalPerfectSectionsStatement`. That statement is a specialization of Stacks, Derived
Categories of Schemes, Lemma `lemma-flat-proper-perfect-direct-image-general` (tag 0B91),
part (1): `Rf_* E` is perfect and its formation commutes with arbitrary base change. See
`perfect.tex` lines 7524–7544 of the same source. The last theorem only combines that
statement with the previous theorem. The formal statements and their combination are
internal.

## Proof

- `homologyIsoOfIsoDerivedComplex` composes the three isomorphisms described above.
- `acyclic_of_iso_derivedComplex`: an integer degree `n` is either `n < 0` or `n = m` for some
  `m : ℕ`. In the first case `Hⁿ(K)` is isomorphic, through `homologyFunctorFactors` and `e`,
  to cohomology of the derived complex in a negative degree, which vanishes by
  `DerivedPlus.isZero_homology_of_neg`. In the second case `Hᵐ(K) ≅ (F.rightDerived m).obj X`,
  which vanishes by hypothesis. Then `HomologicalComplex.exactAt_iff_isZero_homology` gives
  exactness at `n`.
- `isZero_rightDerived_of_iso_derivedComplex`: `(F.rightDerived n).obj X ≅ Hⁿ(K)`, which is
  zero because `K` is exact at `n`.
- `isZero_relativeCohomology_of_quotient_fibres`: `relativeCohomology f n` is by definition
  `(relativeGlobalSections f).rightDerived n`. By `isZero_rightDerived_of_iso_derivedComplex`
  and `e`, it suffices that `K` is acyclic. By the published
  `ModuleComplex.acyclic_of_isStrictlyPerfect_of_residue_acyclic`, it suffices that
  `K ⊗ R ⧸ m` is acyclic for every maximal `m`. This follows from
  `acyclic_of_iso_derivedComplex`, the isomorphism from `eq`, and `hfib`.
  `(idealQuotientHom m).hom` is `Ideal.Quotient.mk m` by definition.
- `isZero_relativeCohomology_of_universalPerfectSections`: `hups` applied to `R`, `X`, `f` and
  `L` gives `K`, its strict perfectness, `e`, and an isomorphism for every ring map
  `φ : R ⟶ T`. Take `φ = idealQuotientHom m` and apply the previous theorem.

The module uses no `sorry` and no axioms beyond Lean's standard `propext`, `Classical.choice`
and `Quot.sound`.

## Intended use

This is the algebraic core of a proof of the open-local rational-fibre statement
(`RationalFibreAcyclicityStatement`, task `3bbaeb61-b856-4adf-9f01-4b03a336b13c`), which feeds
the proof of `Langlands.AbelianScheme.AlgClosedFieldSquareFirstProjectionAcyclicityStatement`
(task `651d1a6b-549e-4d79-ae47-19627b02f30d`). Applied over an affine open `Spec A` of the
base, it reduces vanishing of `Hⁿ(f⁻¹(Spec A), L)` to vanishing on the fibres over the closed
points of `Spec A`. Still missing: identifying these fibres with the fibres over rational
points (by the Nullstellensatz, `A ⧸ m` is the base field when `A` is of finite type over an
algebraically closed field), the affine-open localization, and a proof of
`UniversalPerfectSectionsStatement`.
