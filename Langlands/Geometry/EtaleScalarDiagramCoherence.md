# Scalar coherence for equivariant coefficient diagrams

This module lifts the identity and composition comparisons for scalar
restriction of equivariant étale sheaves to compatible coefficient diagrams.
The comparisons respect every transition map and are natural in coefficient
diagram morphisms. Both unit laws and associativity hold as equalities of
diagram morphisms.

## Provenance

This is an internal construction from the published
`Langlands.Geometry.EtaleScalarDiagram` and
`Langlands.Geometry.EtaleScalarCoherence` modules. The first constructs the
actual scalar-restriction functor on compatible equivariant coefficient
diagrams. The second constructs the identity and composition comparisons
on actual sheaves and equivariant sheaves using Mathlib's module comparisons.
Here those existing equivariant comparisons are used at every vertex.
Compatibility with transitions is proved from their sectionwise formulas;
no diagram comparison or compatibility law is supplied as a hypothesis.
No external literature theorem is transcribed.

## Parameters and conventions

The coefficient rings `R`, `A`, `B`, and `C` are commutative rings in `Type u`.
The ring maps have directions `φ : R →+* A`, `ψ : A →+* B`, and
`χ : B →+* C`. They need not be injective, surjective, or flat.
Scalar restriction along `φ` goes from `A`-coefficients to `R`-coefficients.

The index category is `J : Type v` with morphisms in universe `w`.
The supplied functor `S : J ⥤ Scheme.{u}ᵒᵖ` determines schemes
`X_i = (S.obj i).unop`. An arrow `a : i ⟶ j` determines the morphism
`f_a = (S.map a).unop : X_j ⟶ X_i`, assumed étale.
Section-module carriers also lie in universe `u`.

The group `G : Type t` has no supplied topology. Its actions are supplied as
`ρ i : G →* (Aut X_i)ᵐᵒᵖ`, with the Library convention
`aut (ρ i) (g * h) = aut (ρ i) g ≪≫ aut (ρ i) h`.
The hypothesis `hρ` says that each `f_a` is equivariant:
`f_a ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ f_a`.

An `EquivariantCoefficientDiagram R S ρ hρ` consists of actual
equivariant sheaves of `R`-modules on these small étale sites and compatible
transition maps from the geometric restriction of the source coefficient to
the target coefficient. Its morphisms are vertexwise equivariant sheaf maps
commuting with these transitions.

All declarations below are in
`Langlands.Geometry.EtaleCohomologyAction.EquivariantCoefficientDiagram`.

## Identity and composition comparisons

Write `T_φ` for `restrictScalarsFunctor φ`.
The definition `restrictScalarsIdIso` constructs a natural isomorphism
`T_id ≅ 𝟭` on the category of `R`-coefficient diagrams.
For each coefficient diagram `D`, its forward and inverse maps at a vertex
`i` are the corresponding maps of `scalarRestrictionIdIso (ρ i)` at `D.obj i`.
The ring action after identity restriction is compared by this constructed
isomorphism; it is not assumed definitionally equal to the original action.

The definition `restrictScalarsCompIso φ ψ` constructs
`T_(ψ.comp φ) ≅ T_ψ ⋙ T_φ`.
Its source is the category of `B`-coefficient diagrams and its target is the
category of `R`-coefficient diagrams. For each `D` and `i`, the forward and
inverse maps are those of `scalarRestrictionCompIso φ ψ (ρ i)` at `D.obj i`.
Thus the direction is from direct restriction to restriction first along
`ψ` and then along `φ`.

For both definitions, the proof that each forward or inverse map commutes
with a diagram transition forgets to the underlying sheaf map and evaluates
at an arbitrary étale object and section element. The scalar comparison maps
preserve elements, while scalar restriction retains the underlying additive
transition. Both sides therefore evaluate to the same transition applied to
that element. The inverse identities and naturality in `D` are inherited
vertexwise from the published equivariant sheaf isomorphisms using
`EquivariantCoefficientDiagram.Hom.ext`.

The four lemmas ending in `hom_app_app` or `inv_app_app` record these
vertex formulas for `restrictScalarsIdIso` and `restrictScalarsCompIso`.
Consequently, evaluation gives precisely the existing equivariant sheaf
comparison, including its inverse.

## Unit and associativity laws

Write `η_D` for the forward identity comparison and `c_(φ,ψ),D`
for the forward composition comparison. Composition below is in the order
of Lean's `≫`.

The lemma `restrictScalarsCompIso_id_left φ D` proves

```text
c_(id_R,φ),D ≫ η_(T_φ D) = 𝟙_(T_φ D).
```

It splits the identity at the source ring and then removes the outer
identity restriction. The lemma `restrictScalarsCompIso_id_right φ D` proves

```text
c_(φ,id_A),D ≫ T_φ(η_D) = 𝟙_(T_φ D).
```

It splits the identity at the target ring and then removes that identity
under restriction along `φ`.

For a `C`-coefficient diagram, `restrictScalarsCompIso_assoc φ ψ χ D` proves

```text
c_(φ,χ.comp ψ),D ≫ T_φ(c_(ψ,χ),D)
  = c_(ψ.comp φ,χ),D ≫ c_(φ,ψ),(T_χ D).
```

The two routes start at restriction along the triple composite and end at
successive restriction along `χ`, `ψ`, and `φ`. The ring-composite expressions
have definitionally matching endpoints. Each law is proved by diagram
morphism extensionality followed by the corresponding published equivariant
sheaf law at every vertex.

## Scope

This module supplies scalar identity and composition coherence on actual
compatible equivariant coefficient diagrams. Compatibility with the canonical
ordinary-section scalar comparison, change of index, and restriction of the
acting group are separate coherence obligations. No derived scalar comparison,
preservation of injectives, tensor extension, ideal reduction, inverse limit,
smoothness, analytic site, compact-support construction, or Harris
specialization is asserted here.
