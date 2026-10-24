# Scalar coherence on etale cohomology

This module applies actual cohomology functors to scalar identity and
composition comparisons on coefficient sheaves. It constructs six natural
isomorphisms, at the sheaf, geometric-action and varying-scheme diagram levels.
Their degree-zero components satisfy the identity and composition equations for
the canonical scalar cohomology comparisons constructed in
`EtaleScalarCohomologyZero`.

## Provenance

This is an internal construction from published project definitions and
categorical functoriality. It does not transcribe a theorem from Harris or
Berkovich. `EtaleScalarCoherence` and `EtaleScalarDiagramCoherence` provide
the genuine scalar identity and composition isomorphisms on coefficients.
`EtaleScalarSectionsCoherence` proves their compatibility with canonical
ordinary sections; `EtaleScalarDiagramSectionsCoherence` supplies the target
comparisons on diagrams of module actions. `EtaleScalarCohomologyZero`
constructs the canonical degree-zero comparisons and their section squares.
The present module transports those equations through the canonical
degree-zero identifications. None of its new compatibility equations is an
input assumption.

## Inputs and conventions

Let `R`, `A` and `B` be commutative rings in `Type u`, with arbitrary ring maps
`φ : R →+* A` and `ψ : A →+* B`. The scheme `X` and module carriers use the same
universe `u`. Scalar restriction runs from `B` through `A` to `R`.
The degree `q` is any natural number in the six constructions and their
component formulas.

At the geometric-action level, `G : Type t` is a group with a supplied
`ρ : G →* (Aut X)ᵐᵒᵖ`. The opposite-automorphism convention means that the
scheme automorphism for `g * h` is the categorical composite of that for
`g` followed by that for `h`. No topology or smoothness condition on `G`
is used.

For diagrams, `J : Type v` has morphisms in universe `w` and
`S : J ⥤ Scheme.{u}ᵒᵖ`. Writing `Xᵢ = (S.obj i).unop`, an arrow `a : i ⟶ j`
gives an etale map `fₐ : Xⱼ ⟶ Xᵢ`. Each vertex has an action `ρᵢ`, and the
supplied equivariance equation is
`fₐ ≫ aut(ρᵢ,g).hom = aut(ρⱼ,g).hom ≫ fₐ`.
An `EquivariantCoefficientDiagram` consists of actual small-etale equivariant
module sheaves with compatible coefficient transition maps. Its cohomology
diagram is the published construction from geometric pullback and those maps.

## Cohomology of coefficient comparisons

Write `Tφ` for restriction of coefficient sheaves and `H_R^q` for cohomology
over `R` at the relevant categorical level. The input coefficient comparisons
are

```text
t_id   : T_id ≅ Id
t_φ,ψ  : T_(ψ.comp φ) ≅ T_ψ ⋙ T_φ.
```

The new isomorphisms have types

```text
T_id ⋙ H_R^q        ≅ H_R^q
T_(ψ.comp φ) ⋙ H_R^q ≅ T_ψ ⋙ T_φ ⋙ H_R^q.
```

They apply `Functor.isoWhiskerRight` to `t_id` or `t_φ,ψ`, then compose
with the left unitor or associator. Thus their naturality and inverse
identities come from actual natural isomorphisms. The following table gives
the declaration names; the first four are in
`Langlands.Geometry.EtaleCohomologyAction`, and the last two are in its
`EquivariantCoefficientDiagram` namespace.

| Level | Identity | Composition |
| --- | --- | --- |
| Small-etale module sheaves | `sheafScalarCohomologyIdIso` | `sheafScalarCohomologyCompIso` |
| Geometric equivariant sheaves | `actionScalarCohomologyIdIso` | `actionScalarCohomologyCompIso` |
| Compatible coefficient diagrams | `scalarCohomologyIdIso` | `scalarCohomologyCompIso` |

Each has a `_hom_app` lemma identifying its component with
`H_R^q.map (t_id.hom.app F)` or `H_R^q.map (t_φ,ψ.hom.app F)`.
The proof removes the identity component of the unitor or associator using
`Category.comp_id`. On diagrams these are equalities of natural transformations
with values in module actions; all transition compatibility is retained.

These constructions use cohomology over `R` on both sides. In particular,
the composition isomorphism in positive degree does not compare `H_R^q`
with the scalar restriction of `H_B^q`.

## Canonical degree-zero compatibility

Write `rφ` for scalar restriction on modules, module actions, or their
`J`-diagrams as appropriate. Its identity and composition comparisons are
`c_id : r_id ≅ Id` and `c_φ,ψ : r_(ψ.comp φ) ≅ r_ψ ⋙ r_φ`.
Let `κφ(F)` be the forward canonical degree-zero comparison

```text
H_R^0(Tφ F) ⟶ rφ(H_A^0 F).
```

The module proves the following two equations at all three levels:

```text
H_R^0(t_id(F)) =
  κ_id(F) ≫ c_id(H_R^0 F)

H_R^0(t_φ,ψ(F)) ≫ κφ(Tψ F) ≫ rφ(κψ(F)) =
  κ_(ψ.comp φ)(F) ≫ c_φ,ψ(H_B^0 F).
```

The composition equation has common source `H_R^0(T_(ψ.comp φ) F)`
and common target `rφ(rψ(H_B^0 F))`. At the sheaf level the declarations
are `scalarRestrictionCohomologyZero_id` and
`scalarRestrictionCohomologyZero_comp`. At the action level they are
`scalarRestrictionCohomologyZeroFunctor_id` and
`scalarRestrictionCohomologyZeroFunctor_comp`. In the diagram namespace they
are `restrictScalarsCohomologyZero_id` and
`restrictScalarsCohomologyZero_comp`.
Together with the `_hom_app` lemmas, these equations identify the degree-zero
components of the six constructed isomorphisms with the canonical scalar
comparison paths.

For the implemented proof, let `e_R : H_R^0 ≅ Γ_R` be the canonical
identification with ordinary sections and let `σφ` be the canonical scalar
section comparison. The published section square is

```text
κφ(F) ≫ rφ(e_A(F)) = e_R(Tφ F) ≫ σφ(F).
```

The identity proof postcomposes both sides with `e_R(F)`, which is
an isomorphism and hence cancellable. Naturality of `e_R` and `c_id`,
the section square, and the published section identity equation give equality.
The composition proof postcomposes with `rφ(rψ(e_B(F)))`, again an isomorphism.
Functoriality and the section square first reduce the successive comparisons
to ordinary sections. Naturality of `e_R` handles the coefficient composition
map. The published section composition equation and naturality of `c_φ,ψ`
then identify the direct comparison path. Associativity and the section square
complete the proof. These arguments are carried out both in modules and
directly in the category of module actions.

For diagrams, `NatTrans.ext` reduces each equation to the action equation at
the vertex `D.obj i`. The published component formulas for the coefficient,
degree-zero and target-diagram comparisons make those goals precisely the
proved action equations. Equality therefore retains geometric equivariance and
compatibility with every diagram transition.

## Scope

The new degree-zero compatibility equations require no injective-preservation
or flatness hypothesis. This module does not construct a cross-ring comparison
in positive cohomological degree, tensor extension, ideal reduction, inverse
limits, smooth group actions, analytic sites, compact supports or a Shimura
specialization of Harris's construction. Those remain separate obligations.
