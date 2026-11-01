# Reverse coefficient comparisons and canonical cohomology recovery

The paired module constructs reverse geometric/restriction comparisons for
derived-section, ordinary-cohomology and section diagrams. It then proves that
the forward and reverse comparisons respect the existing canonical recovery
isomorphisms, both on each coefficient diagram and as functors of coefficients.
All declarations are in
`Langlands.Geometry.EtaleGeometricDiagram.CoefficientDiagram`.

## Input and conventions

Let `R : Type u` be any commutative ring, `J : Type v` have
`Category.{w} J`, and `S : J ⥤ Scheme.{u}ᵒᵖ`. Write `X_i = (S.obj i).unop`.
An arrow `a : i ⟶ j` gives a scheme morphism `X_j ⟶ X_i`, which is required
to be etale for every `a`. The actual coefficient categories use small-etale
sheaves valued in `ModuleCat.{u} R`. The schemes, ring and module carriers
therefore share `u`; the index object and morphism universes are independent.
Coefficient transition morphisms need not be isomorphisms. No field,
finiteness, Noetherian or local-constancy condition is imposed.

All declarations retain a common `HasDerivedCategory.{wS}` universe for the
vertex sheaf categories, and an independent
`HasDerivedCategory.{wR} (ModuleCat.{u} R)`. These assumptions also occur in the
ordinary-cohomology and section comparisons because the geometric diagrams
are constructed by transport from derived homology. Ordinary cohomology degrees
`q` are natural numbers, viewed as integer homology degrees when necessary.

Use the following notation in this explanation:

- `T` is `toRestrictionFunctor`, from geometric coefficient diagrams to
  restriction coefficient diagrams.
- `U` is `ofRestrictionFunctor`, in the reverse direction.
- `G`, `C_q`, and `A` are the derived-section, ordinary degree-`q` cohomology,
  and actual section diagram functors. Subscripts `g` and `r` distinguish
  geometric and restriction coefficients.
- `H_q` is `DerivedCategory.Plus.homologyFunctor (ModuleCat R) q`.
- `eta_q` and `zeta` are the existing `derivedSectionsHomologyIso` and
  `derivedSectionsZeroIso`, respectively, in the indicated coefficient category.

The transports preserve the actual sheaves at every vertex and the component
sheaf morphisms. Their transition maps use the hom or inverse of the constructed
inverse-image/restriction comparison. Thus no cohomological objects or desired
comparison laws are additional input fields.

## Reverse comparisons

For a geometric coefficient diagram `D`,
`toRestrictionDerivedSectionsIso D` has direction

```text
G_r(T D) ≅ G_g(D).
```

It is the inverse of the existing forward comparison at `T D`, followed by
`G_g` applied to `geometricRoundTripIso D : U(T D) ≅ D`. Both factors are
actual diagram isomorphisms, so their composition retains naturality along
every scheme-diagram arrow.

`toRestrictionCohomologyIso D q` and `toRestrictionSectionsIso D` use the same
construction with `C_q,g` and `A_g`. Their directions are

```text
C_q,r(T D) ≅ C_q,g(D),       A_r(T D) ≅ A_g(D).
```

The three `_hom_app` theorems show that every forward map of these reverse
comparison isomorphisms is the identity at each vertex. Indeed, the inverse
forward comparison has identity components; the geometric round trip has
identity sheaf morphisms, and the cohomological functors preserve identities.

`toRestrictionDerivedSectionsFunctorIso`,
`toRestrictionCohomologyFunctorIso q`, and `toRestrictionSectionsFunctorIso`
assemble these into natural isomorphisms

```text
T ⋙ G_r ≅ G_g,       T ⋙ C_q,r ≅ C_q,g,       T ⋙ A_r ≅ A_g.
```

The coefficient-naturality equations reduce at each vertex to identity laws
for the same actual derived-section, cohomology or section map of the component
sheaf morphism. The restriction section functor was defined through ordinary
degree-zero cohomology, so its proved `sectionsFunctor_map_app` formula is used
to identify that map with actual sections.

## Compatibility with canonical recovery

Write `c_G(D)`, `c_C(D,q)` and `c_A(D)` for the existing forward comparisons on
a restriction coefficient diagram `D`. The theorems
`ofRestrictionDerivedSectionsIso_homology D q` and
`ofRestrictionDerivedSectionsIso_zero D` prove equalities of diagram
isomorphisms:

```text
H_q(c_G(D)) ; eta_q,r(D) = eta_q,g(U D) ; c_C(D,q)
H_0(c_G(D)) ; zeta_r(D)  = zeta_g(U D)  ; c_A(D).
```

Here `H_q(c)` means `Functor.isoWhiskerRight c H_q`, and `;` is composition in
the displayed order. These are equalities for the existing recovery maps;
no recovery map is replaced by one chosen to force compatibility.

For a geometric coefficient diagram `D`, write `d_G(D)`, `d_C(D,q)` and
`d_A(D)` for the reverse comparisons constructed here. The theorems
`toRestrictionDerivedSectionsIso_homology D q` and
`toRestrictionDerivedSectionsIso_zero D` prove

```text
H_q(d_G(D)) ; eta_q,g(D) = eta_q,r(T D) ; d_C(D,q)
H_0(d_G(D)) ; zeta_g(D)  = zeta_r(T D)  ; d_A(D).
```

The homology proofs use extensionality of isomorphisms and natural
transformations, then the identity comparison components. The remaining
vertex map is exactly
`EtaleDerivedSectionsPlus.homologyNatIso X_i R q` at the unchanged coefficient
sheaf. Degree zero uses
`homologyZeroIso = homologyNatIso 0 ≪≫ cohomologyZeroIso`. The restriction
diagram recovery is defined as the same two factors, whereas the geometric
recovery uses `homologyZeroIso` directly. Consequently the two vertex maps
are definitionally the same composite after functor identity laws.

The four corresponding theorems with
`DerivedSectionsFunctorIso_homology` or `DerivedSectionsFunctorIso_zero` in
their names assert these equations as equalities of natural isomorphisms on
the whole coefficient category. Postcomposition by `H_q` is expressed using
`Functor.whiskeringRight`; the geometric or restriction recovery comparison is
precomposed with `U` or `T`, respectively. Extensionality in the coefficient
diagram reduces each functor equation to its preceding diagram equation.

## Provenance and remaining scope

This is an internal categorical construction using
`EtaleCoefficientEquivalence`, `EtaleCoefficientDiagramComparison`,
`EtaleGeometricCoefficientDiagram`, `EtaleDerivedDiagram`, and
`EtaleDerivedSectionsPlus`. The reverse isomorphisms come from the actual
coefficient round trip and the existing forward comparisons; their components
and recovery equations are proved from those definitions. No external
literature assertion or new geometric existence theorem is claimed here.

Scalar change, tower limits, compact supports, smooth equivariance, Galois
actions, arithmetic coefficient systems and Harris specialization remain
separate construction or theorem obligations. This group provides a compatible
bridge between the genuine geometric and restriction diagram frameworks;
it does not complete the host Harris framework task.
