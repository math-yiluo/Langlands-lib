# Scalar extension and restriction on compatible coefficient diagrams

`Langlands.Geometry.EtaleScalarDiagramAdjunction` constructs the adjunction
between the existing scalar-extension and scalar-restriction functors on
compatible equivariant small-etale coefficient diagrams. The declarations lie
in `Langlands.Geometry.EtaleCohomologyAction`; all but the first geometric
lemma lie in its `EquivariantCoefficientDiagram` namespace.

## Parameters and provenance

The coefficient rings `R A : Type u` are arbitrary commutative rings, with a
unital homomorphism `φ : R →+* A`. Schemes and module carriers share universe
`u`. The category `J` has object universe `v` and morphism universe `w`.
Supply `S : J ⥤ Scheme.{u}ᵒᵖ`, with each map

```text
f_a := (S.map a).unop : (S.obj j).unop ⟶ (S.obj i).unop
```

etale for `a : i ⟶ j`. A fixed group `G : Type t`, in an independent
universe, acts through `ρ i : G →* (Aut (S.obj i).unop)ᵐᵒᵖ`. The supplied
geometric equivariance equations are

```text
f_a ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ f_a.
```

These are precisely the parameters of the existing coefficient category.
No flatness of the ring map or topology on the group is required. The
coefficient transitions need not be invertible.

This is an internal categorical construction from
[diagram extension](EtaleScalarExtensionDiagram.md),
[diagram restriction](EtaleScalarDiagram.md), the
[pointwise equivariant adjunction](EtaleEquivariantScalarExtension.md), and
[its geometric pullback comparison](EtaleEquivariantScalarExtensionPullback.md).
The underlying extension is sectionwise tensor followed by sheafification
on the actual small-etale site. The implementation supplies the new
compatibility proofs and applies Mathlib's `Adjunction.mkOfHomEquiv`.
No external theorem is transcribed and no desired adjunction or comparison
is assumed.

Write `L_i` and `U_i` for pointwise extension and restriction, `η_i` for
their unit, and `P_a^R`, `P_a^A` for geometric restriction. The existing
comparison maps have the directions

```text
β_a(F) : P_a^A(L_i F) ⟶ L_j(P_a^R F),
r_a(E) : P_a^R(U_i E) ⟶ U_j(P_a^A E).
```

Below, `;` denotes composition in order of application.

## Universal lifts and geometric restriction

`scalarExtensionLift_equivariantPullback` applies to any equivariant
etale scheme map `f : Y ⟶ X` with source and target group actions. For
`a : F ⟶ U_X E`, it proves

```text
β_f(F) ; lift_Y(P_f^R.map(a) ; r_f(E)) = P_f^A.map(lift_X(a)).
```

The proof first shows that
`β_f.inv(F) ; P_f^A.map(lift_X(a))` is the universal lift of the displayed
restricted map. It applies pointwise lift uniqueness. The previously
proved pullback-unit equation, cancellation of the comparison and its
inverse, naturality of `r_f`, and the unit/lift equation establish the
required unit factorization. Composing with `β_f.hom` gives the stated
formula. Thus compatibility of universal lifts with geometry is proved.

## Compatible units and lifts

`extensionUnitApp φ D : D ⟶ restrictScalars φ (extendScalars φ D)` has
component `η_i(D.obj i)`. Its transition square is proved after forgetting
to ordinary sheaves: the pullback-unit comparison and naturality of the
ordinary unit give the equation. `extensionUnit φ` packages these maps
as a natural transformation from the identity to extension followed by
restriction. Its naturality is the pointwise equivariant unit naturality.

For a compatible map `α : D ⟶ restrictScalars φ E`, `extensionLift φ α`
is a morphism `extendScalars φ D ⟶ E` with component
`scalarExtensionLift φ (ρ i) (α.app i)`. To prove transition compatibility,
the proof uses naturality of pointwise lifts under source precomposition,
the given equation `α.comm`, naturality under target postcomposition,
and the geometric lift formula above.

`extensionUnit_lift` proves the factorization equation

```text
extensionUnitApp φ D ; restrictScalarsFunctor.map(extensionLift φ α) = α.
```

`extensionLift_unique` proves that any compatible `β` with this unit
factorization equals `extensionLift φ α`. Both proofs reduce to the
corresponding pointwise facts using extensionality of diagram morphisms.

## The adjunction

`extensionHomEquiv φ D E` is the actual bijection

```text
(extendScalars φ D ⟶ E) ≃ (D ⟶ restrictScalars φ E).
```

Its forward map sends `β` to the diagram unit followed by restriction
of `β`; its inverse is `extensionLift`. Lift uniqueness proves the left
inverse, and the unit/lift equation proves the right inverse.
`extensionHomEquiv_app` and `extensionHomEquiv_symm_app` identify its
components with the existing pointwise equivariant correspondence and
universal lift, respectively.

`extensionRestrictionAdj φ` constructs

```text
extendScalarsFunctor φ ⊣ restrictScalarsFunctor φ.
```

The hom correspondence is natural: the inverse correspondence respects
source precomposition by pointwise lift naturality, and the forward
correspondence respects target postcomposition by the pointwise
adjunction's naturality. Mathlib's constructor derives the unit, counit
and both triangle identities from this natural equivalence. An
`IsLeftAdjoint` instance is supplied for diagram extension.

`extensionRestrictionAdj_homEquiv` identifies the packaged adjunction's
correspondence with `extensionHomEquiv`. The further component lemmas
`extensionRestrictionAdj_unit_app` and
`extensionRestrictionAdj_counit_app` identify its unit with
`extensionUnitApp` and its evaluated counit with the pointwise
`scalarExtensionCounit`. Their proofs use the hom correspondence on
identity morphisms, together with functorial identity preservation for
the unit and the pointwise adjunction identity for the counit.

## Scope

The construction is an adjunction on the supplied compatible diagram
categories, for arbitrary indexing categories and the etale geometric
maps specified above. It adds no exactness, flatness, injective preservation,
cohomological comparison, or commutation of scalar extension with global
sections or higher cohomology. Coefficient identity/composition coherence
at the diagram level, mixed geometric/ring coherence, ideal reduction,
inverse systems and inverse-limit comparisons remain separate work.
No topology or smoothness condition on group actions, compact support,
actual Harris coefficient system, Shimura tower specialization or Harris
comparison theorem is constructed in this unit.
