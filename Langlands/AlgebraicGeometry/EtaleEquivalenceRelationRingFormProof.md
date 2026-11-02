# Ring form of an affine étale equivalence relation

Author: Worker 424.

The theorem in this module proves the published proposition
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationRingFormStatement.{u}`
with the theorem `Langlands.AlgebraicGeometry.etaleEquivalenceRelationRingForm`.
The universe `u` is arbitrary and no hypotheses are added.

```lean
theorem etaleEquivalenceRelationRingForm :
    EtaleEquivalenceRelationRingFormStatement.{u}
```

Write `B = Γ(E.U, ⊤)`, `C = Γ(E.R, ⊤)`, `t♯ = E.t.appTop.hom` and
`s♯ = E.s.appTop.hom`. The conclusion uses exactly the algebra structure on
`C` given by `s♯.toAlgebra`. Both published structures,
`EtaleEquivalenceRelation` and `RingEtaleEquivalenceRelation`, and the
published target statement are imported unchanged.

## Affine points and equivalence relation laws

The published equivalence `FiniteEtale.affinePointEquiv X T`, for an affine scheme `X`
and a commutative ring object `T`, identifies morphisms `Spec T ⟶ X` with
ring morphisms `Γ(X, ⊤) ⟶ T`. Its forward map is
`r ↦ Spec.preimage (r ≫ X.isoSpec.hom)` and its inverse is
`φ ↦ Spec.map φ ≫ X.isoSpec.inv`. The two inverse identities follow from
full faithfulness of `Spec` and the inverse identities of `X.isoSpec`.

The published naturality lemma `FiniteEtale.affinePointEquiv_comp` states

```text
point(r ≫ f) = f.appTop ≫ point(r).
```

It follows by applying the faithful `Spec.map` and then using
`Scheme.isoSpec_hom_naturality`. These affine-duality constructions are reused directly from
`Langlands.AlgebraicGeometry.FiniteEtale.AffineQuotientCoconeProof`;
this module introduces no separate copy of them.

For each arbitrary commutative ring `T : Type u`, the final proof applies
`E.refl`, `E.symm` and `E.trans` to the test scheme
`Spec (CommRingCat.of T)`. It transports the resulting witnesses by
`FiniteEtale.affinePointEquiv`. The naturality lemma translates the equations after
composition with `E.t` and `E.s` into composition with `t♯` and `s♯`.
For transitivity, injectivity of the point equivalence first translates the
assumed equality of the middle ring points into the composability equation
of the two scheme points. Passing from `CommRingCat` morphisms to their
underlying `RingHom`s then gives precisely the three fields required by
`RingEtaleEquivalenceRelation`.

## Generation by the target map

The private lemma `ringForm_adjoin_eq_top` applies to any two maps
`t, s : R ⟶ U` between affine schemes for which `prod.lift t s` is a
closed immersion. Give `C = Γ(R, ⊤)` its `B = Γ(U, ⊤)`-algebra structure
through `s.appTop.hom`, and put

```text
D = Algebra.adjoin B (Set.range t.appTop.hom) ⊆ C.
```

The map `t.appTop.hom` factors through `D` by `Algebra.subset_adjoin`.
The source map factors through `D` as its `B`-algebra structure map.
Write `i : D → C` for the inclusion and `p = Spec.map i`. The two
factor maps define

```text
q : Spec D ⟶ U × U.
```

The factorization identity proved by the two product projections is

```text
R.isoSpec.hom ≫ p ≫ q = prod.lift t s.
```

The scheme `Spec D` is affine, hence separated; every morphism from it,
including `q`, is separated. Since the displayed composite is a closed
immersion, `IsClosedImmersion.of_comp` makes `R.isoSpec.hom ≫ p` a closed
immersion. Composing with `R.isoSpec.inv` shows that `p` itself is a
closed immersion.

Mathlib's `IsClosedImmersion.isAffine_surjective_of_isAffine` now makes
`p.appTop` surjective. The natural isomorphisms `Scheme.ΓSpecIso` identify
the inclusion `i` with

```text
(ΓSpecIso D).inv ≫ p.appTop ≫ (ΓSpecIso C).hom.
```

Thus `i` is surjective. Every element of `C` belongs to `D`, which proves
`D = ⊤`. No equivalence relation law or étaleness is needed in this lemma.

## Étaleness and provenance

The final two fields apply
`HasRingHomProperty.iff_of_isAffine (P := @Etale)` to `E.etale_s` and
`E.etale_t`. For the local algebra structure, `algebraMap B C` is
definitionally `s♯`, so these give the required source and target
`RingHom.Etale` properties.

This is a derived affine translation of the published statement, as
explained in its companion Markdown. Its equivalence relation conventions
are those already fixed by the two imported Library structures. The proof
uses no further result from the literature. Its Mathlib inputs are affine
duality (`AffineScheme.lean` and `GammaSpecAdjunction.lean`), étaleness
(`Morphisms/Etale.lean` and `Morphisms/RingHomProperties.lean`), closed
immersions (`Morphisms/ClosedImmersion.lean`) and separated morphisms
(`Morphisms/Separated.lean`). The field `E.mono_lift` is not needed by the
implemented argument.
