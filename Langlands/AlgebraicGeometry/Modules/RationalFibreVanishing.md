# Vanishing of higher direct images from rational fibres

Module `Langlands.AlgebraicGeometry.Modules.RationalFibreVanishing`, namespace
`Langlands.AlgebraicGeometry.Modules.DerivedSections`. `cohomology`, `relativeCohomology` and
`higherDirectImage` are the published sheaf cohomology `Hⁿ(X, M)` (a `Γ(X, ⊤)`-module), its
`R`-module version for a morphism `X ⟶ Spec R`, and the higher direct images `Rⁿ f_*`.
`idealQuotientHom m : R ⟶ CommRingCat.of (R ⧸ m)` is the published quotient map from
`PerfectFibreVanishing`.

## Definition

```lean
def affineRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) {V : Y.Opens} (hV : IsAffineOpen V) :
    (f ⁻¹ᵁ V).toScheme ⟶ Spec Γ(Y, V) :=
  f ∣_ V ≫ hV.isoSpec.hom
```

For an affine open `V` of `Y`, the restriction `f⁻¹ V ⟶ V` of `f`, followed by Mathlib's
isomorphism `V ≅ Spec Γ(Y, V)`. The module adds the instances `Smooth (affineRestrict f hV)`
when `f` is smooth and `IsProper (affineRestrict f hV)` when `f` is proper. The theorem
`isPullback_affineRestrict` states that the square with sides `(f ⁻¹ᵁ V).ι`,
`affineRestrict f hV`, `f` and `hV.fromSpec : Spec Γ(Y, V) ⟶ Y` is a pullback. So `f⁻¹ V` is
the fibre product `X ×_Y Spec Γ(Y, V)`.

## Main results

**Base independence.** For any `f : X ⟶ Spec R`, any `n : ℕ` and any `M : X.Modules`:

```lean
theorem isZero_cohomology_iff_relativeCohomology (f : X ⟶ Spec R) (n : ℕ) (M : X.Modules) :
    IsZero ((cohomology X n).obj M) ↔ IsZero ((relativeCohomology f n).obj M)

theorem isZero_relativeCohomology_iff (f₁ : X ⟶ Spec R₁) (f₂ : X ⟶ Spec R₂) (n : ℕ)
    (M : X.Modules) :
    IsZero ((relativeCohomology f₁ n).obj M) ↔ IsZero ((relativeCohomology f₂ n).obj M)
```

Whether `Hⁿ(X, M)` vanishes does not depend on the ring over which it is regarded as a module.

**Transport along fibre products.**

```lean
theorem isZero_relativeCohomology_pullback_of_iso (E : P₂ ≅ P₁) (a : P₁ ⟶ X)
    (s₁ : P₁ ⟶ Spec R₁) (s₂ : P₂ ⟶ Spec R₂) (M : X.Modules) (n : ℕ)
    (h : IsZero ((relativeCohomology s₁ n).obj ((Scheme.Modules.pullback a).obj M))) :
    IsZero ((relativeCohomology s₂ n).obj ((Scheme.Modules.pullback (E.hom ≫ a)).obj M))

theorem isZero_relativeCohomology_of_isPullback (f : X ⟶ Y)
    (h₁ : IsPullback a₁ b₁ f y₁) (h₂ : IsPullback a₂ b₂ f y₂)
    (e : T₂ ≅ T₁) (he : e.hom ≫ y₁ = y₂) (s₁ : P₁ ⟶ Spec R₁) (s₂ : P₂ ⟶ Spec R₂)
    (M : X.Modules) (n : ℕ)
    (h : IsZero ((relativeCohomology s₁ n).obj ((Scheme.Modules.pullback a₁).obj M))) :
    IsZero ((relativeCohomology s₂ n).obj ((Scheme.Modules.pullback a₂).obj M))
```

The first: vanishing of the cohomology of a pulled-back module is unchanged by an isomorphism
`P₂ ≅ P₁` over `X`, whatever affine bases are used. The second: let `P₁` and `P₂` be fibre
products of `f` with `y₁ : T₁ ⟶ Y` and `y₂ : T₂ ⟶ Y`, where `y₂ = e.hom ≫ y₁` for an
isomorphism `e : T₂ ≅ T₁`. Then vanishing on `P₁` of the cohomology of the pullback of `M`
gives the same vanishing on `P₂`.

**Rational points (Nullstellensatz).** Let `K` be an algebraically closed field (any
characteristic, `K : Type u`), `g : Y ⟶ Spec (CommRingCat.of K)` locally of finite type, `V`
an affine open of `Y` with `hV : IsAffineOpen V`, and `m` a maximal ideal of `Γ(Y, V)`.

```lean
theorem exists_iso_rationalPoint (m : Ideal Γ(Y, V)) [m.IsMaximal] :
    ∃ e : Spec (CommRingCat.of K) ≅ Spec (CommRingCat.of (Γ(Y, V) ⧸ m)),
      e.hom ≫ Spec.map (idealQuotientHom m) ≫ hV.fromSpec ≫ g = 𝟙 _

theorem exists_rationalPoint_of_le {U : Y.Opens} (hVU : V ≤ U) (m : Ideal Γ(Y, V))
    [m.IsMaximal] :
    ∃ (e : Spec (CommRingCat.of K) ≅ Spec (CommRingCat.of (Γ(Y, V) ⧸ m)))
      (x : Spec (CommRingCat.of K) ⟶ U.toScheme),
      x ≫ U.ι = e.hom ≫ Spec.map (idealQuotientHom m) ≫ hV.fromSpec ∧
        x ≫ U.ι ≫ g = 𝟙 _
```

The closed point `m` of `Spec Γ(Y, V)` has residue field `Γ(Y, V) ⧸ m`, and the ring map
`K → Γ(Y, V) ⧸ m` induced by `g` is an isomorphism. So `Spec K ≅ Spec (Γ(Y, V) ⧸ m)`, and the
closed point composed with this isomorphism is a section of `g`, that is, a `K`-rational point
of `Y`. If `V ≤ U`, the point lies in `U`: `x : Spec K ⟶ U` is a `K`-rational point of the
open subscheme `U` whose composite with `U.ι` is the closed point `m`.

**Quotient fibres from rational fibres.** For any `f : X ⟶ Y`, any `M : X.Modules`, an ideal
`m` of `Γ(Y, V)` and `y : T ⟶ Y`:

```lean
theorem isZero_relativeCohomology_quotientFibre {T : Scheme.{u}} (y : T ⟶ Y)
    (m : Ideal Γ(Y, V)) (e : T ≅ Spec (CommRingCat.of (Γ(Y, V) ⧸ m)))
    (he : e.hom ≫ Spec.map (idealQuotientHom m) ≫ hV.fromSpec = y) (M : X.Modules) (n : ℕ)
    {R : CommRingCat.{u}} (s : pullback f y ⟶ Spec R)
    (h : IsZero ((relativeCohomology s n).obj
      ((Scheme.Modules.pullback (pullback.fst f y)).obj M))) :
    IsZero ((relativeCohomology
        (pullback.snd (affineRestrict f hV) (Spec.map (idealQuotientHom m))) n).obj
      ((Scheme.Modules.pullback
          (pullback.fst (affineRestrict f hV) (Spec.map (idealQuotientHom m)))).obj
        ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj M)))
```

Suppose `y` is `T ≅ Spec (Γ(Y, V) ⧸ m) ⟶ Spec Γ(Y, V) ⟶ Y`, and `Hⁿ` of the pullback of `M`
to the actual fibre product `pullback f y` vanishes (as a module over any `R`). Then `Hⁿ`
vanishes, as a `Γ(Y, V) ⧸ m`-module, for the following fibre: the fibre of
`affineRestrict f hV` over `Spec (Γ(Y, V) ⧸ m)`, with the pullback of `M|_{f⁻¹ V}` along its
first projection. This fibre is the shape required by the published
`isZero_relativeCohomology_of_universalPerfectSections`. Taking `T = Spec K` and `y = x ≫ U.ι`
from `exists_rationalPoint_of_le`, the hypothesis is vanishing on the fibre over a rational
point, regarded as a `K`-module through `pullback.snd f (x ≫ U.ι)`. The change of coefficient
ring from `K` to `Γ(Y, V) ⧸ m` is handled by base independence.

**Main theorem.**

```lean
theorem isZero_pullback_higherDirectImage_of_rationalFibres
    (hups : UniversalPerfectSectionsStatement.{u})
    (K : Type u) [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType g]
    (f : X ⟶ Y) [Smooth f] [IsProper f] (Q : Picard.LineBundle X) (U : Y.Opens)
    (hQ : ∀ x : Spec (CommRingCat.of K) ⟶ U.toScheme,
      x ≫ U.ι ≫ g = 𝟙 (Spec (CommRingCat.of K)) → ∀ n : ℕ,
        IsZero ((relativeCohomology (pullback.snd f (x ≫ U.ι)) n).obj
          ((Scheme.Modules.pullback (pullback.fst f (x ≫ U.ι))).obj Q.obj)))
    (n : ℕ) :
    IsZero ((Scheme.Modules.pullback U.ι).obj ((higherDirectImage f n).obj Q.obj))
```

This takes the published proposition `UniversalPerfectSectionsStatement` as a hypothesis
`hups`; it does not prove it. Given `hups`, let `K` be algebraically closed, `Y` locally of
finite type over `K`, `f : X ⟶ Y` smooth and proper, `Q` a line bundle on `X` and `U` an open
of `Y`. Suppose that for every `K`-rational point `x` of `U` and every `n`, `Hⁿ` of the pullback
of `Q` to the fibre `X ×_Y Spec K` over `x` vanishes. Then every higher direct image
`Rⁿ f_* Q` restricts to zero on `U`. The hypotheses and the conclusion are those of the
proposition `RationalFibreAcyclicityStatement` drafted for task
`3bbaeb61-b856-4adf-9f01-4b03a336b13c`, there with `LocallyOfFiniteType g`, `Smooth f` and
`IsProper f` as explicit arguments.

## Provenance

`affineRestrict`, its instances and pullback square, base independence and the two transport
lemmas are internal adapters with no literature counterpart.

`exists_iso_rationalPoint` is the case of an algebraically closed base field of Stacks,
Morphisms of Schemes, Lemma `lemma-closed-point-fibre-locally-finite-type` (tag 01TF): for `f`
locally of finite type, `x` is a closed point of its fibre exactly when `κ(x)/κ(f(x))` is
finite. Its proof uses the Hilbert Nullstellensatz. See `morphisms.tex` at git commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, lines 3594–3630, in the registered source
`stacks-affine-morphisms-relative-vanishing-a04446e5`. Here the base is `Spec K`, the point is
the closed point `m` of an affine open, and the finite extension of an algebraically closed
field is trivial. The Lean proof uses Mathlib's Nullstellensatz
`RingHom.finite_iff_finiteType_of_isJacobsonRing` (a finite type map from a Jacobson ring to a
field is finite) and `IsAlgClosed.ringHom_bijective_of_isIntegral`. `exists_rationalPoint_of_le`
only factors the point through an open immersion.

The main theorem is a derived consequence. Over each affine open `V ⊆ U`, it combines the
published local-to-global detection `isZero_pullback_higherDirectImage_of_affineOpens`, whose
Markdown cites Stacks, Cohomology of Sheaves, Lemma `lemma-describe-higher-direct-images` (tag
01E4), with the published `isZero_relativeCohomology_of_universalPerfectSections`, a derived
consequence of Stacks tags 068V and 0B91. The combination is internal.

## Proof

- `isZero_cohomology_iff_relativeCohomology`: the published
  `relativeCohomologyRestrictScalarsIso` identifies the relative `R`-module cohomology with
  the restriction of scalars of the absolute `Γ(X, ⊤)`-module `Hⁿ(X, M)` along
  `structureRingHom f : R ⟶ Γ(X, ⊤)`. Restriction of scalars does not change the underlying
  additive group, and a module is zero exactly when it is a subsingleton.
  `isZero_relativeCohomology_iff` applies this twice.
- `isZero_relativeCohomology_pullback_of_iso`: change the base of `s₂` to `E.hom ≫ s₁` by base
  independence. Then the published `relativeCohomologyPullbackIso E s₁` and
  `Scheme.Modules.pullbackComp E.hom a` identify the module with the cohomology of the
  pullback along `a`.
- `isZero_relativeCohomology_of_isPullback`: `P₂` with `a₂` and `b₂ ≫ e.hom` is a pullback of
  `f` and `y₁`. This pastes `h₂` with the square with sides `𝟙 P₂`, `b₂ ≫ e.hom`, `b₂` and
  `e.inv`, which is a pullback because its horizontal maps are isomorphisms. By
  `IsPullback.isoIsPullback_hom_fst`, `a₂` is the composite of an isomorphism `P₂ ≅ P₁` with
  `a₁`, and the previous lemma applies.
- `affineRestrict`: the instances follow from the restriction instances for `f ∣_ V` and the
  isomorphism. `isPullback_affineRestrict` pastes Mathlib's `isPullback_morphismRestrict`
  with the square formed by `hV.isoSpec`, and uses `hV.isoSpec_inv ≫ V.ι = hV.fromSpec`.
- `exists_iso_rationalPoint`: let
  `θ : K ⟶ Γ(Spec K, ⊤) ⟶ Γ(Y, V) ⟶ Γ(Y, V) ⧸ m` be the inverse of `Scheme.ΓSpecIso`,
  then `g.appLE ⊤ V`, then the quotient. Each factor is of finite type: the first is
  bijective, the second because `g` is locally of finite type
  (`HasRingHomProperty.appLE` on the affine opens `⊤` and `V`), and the third is surjective.
  Since `K` is a field, hence Jacobson, and `Γ(Y, V) ⧸ m` is a field
  (`Ideal.Quotient.field`), `θ` is finite, hence integral. So `θ` is bijective because `K` is
  algebraically closed, and `Spec.map θ` is an isomorphism. Take `e` to be its inverse. The
  equation follows from `Spec.map (idealQuotientHom m) ≫ hV.fromSpec ≫ g = Spec.map θ`. This
  holds by Mathlib's `IsAffineOpen.SpecMap_appLE_fromSpec`, together with `fromSpec_top` and
  `isoSpec_Spec_inv`.
- `exists_rationalPoint_of_le`: `y = e.hom ≫ Spec.map (idealQuotientHom m) ≫ hV.fromSpec` has
  image in the range of `hV.fromSpec`, which is `V ⊆ U` (`range_fromSpec`, `range_ι`). So it
  lifts through the open immersion `U.ι` (`IsOpenImmersion.lift`, `lift_fac`). The equation
  `x ≫ U.ι ≫ g = 𝟙` is the equation of `exists_iso_rationalPoint`.
- `isZero_relativeCohomology_quotientFibre`: the fibre of `affineRestrict f hV` over
  `Spec (Γ(Y, V) ⧸ m)` is a pullback of `f` along `Spec.map (idealQuotientHom m) ≫ hV.fromSpec`.
  This pastes `IsPullback.of_hasPullback` with `isPullback_affineRestrict`, and the first
  projection becomes `pullback.fst _ _ ≫ (f ⁻¹ᵁ V).ι`. Apply
  `isZero_relativeCohomology_of_isPullback` with `e.symm`, then
  `Scheme.Modules.pullbackComp` to split the pullback along this composite.
- `isZero_pullback_higherDirectImage_of_rationalFibres`: by
  `isZero_pullback_higherDirectImage_of_affineOpens`, it suffices that
  `Hⁿ(f⁻¹ V, Q|_{f⁻¹ V}) = 0` for every affine open `V ≤ U`. Here the restriction uses
  `restrictFunctor`, which `Scheme.Modules.restrictFunctorIsoPullback` identifies with the
  pullback along `(f ⁻¹ᵁ V).ι`. By base independence this is `relativeCohomology` of
  `affineRestrict f hV`, which is smooth and proper. Apply
  `isZero_relativeCohomology_of_universalPerfectSections` to `hups` and the pulled-back line
  bundle `(Picard.LineBundle.pullback (f ⁻¹ᵁ V).ι).obj Q`. Its fibre hypothesis at a maximal
  ideal `m` follows from `exists_rationalPoint_of_le`, `isZero_relativeCohomology_quotientFibre`
  and `hQ` at the rational point `x`.

The module uses no `sorry` and no axioms beyond Lean's standard `propext`, `Classical.choice`
and `Quot.sound`.

## Intended use

Once `UniversalPerfectSectionsStatement` (proof task `5056e5fc-5861-489e-adae-be84a23164c5`)
is proved, the main theorem proves `RationalFibreAcyclicityStatement`
(task `3bbaeb61-b856-4adf-9f01-4b03a336b13c`), which feeds the proof of
`Langlands.AbelianScheme.AlgClosedFieldSquareFirstProjectionAcyclicityStatement`
(task `651d1a6b-549e-4d79-ae47-19627b02f30d`).
