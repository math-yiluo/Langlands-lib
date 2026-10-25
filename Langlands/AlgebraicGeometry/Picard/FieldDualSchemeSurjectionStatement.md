# A surjection from an abelian variety onto its chosen dual parameter scheme

`Langlands.AbelianScheme.FieldDualSchemeSurjectionStatement` is a proposition
definition. For every field `k : Type u`, every existing
`A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))`, and
every proof `hA : HasDualScheme A`, it asserts exactly

```text
∃ f : A.X ⟶ dualScheme A hA, Surjective f.left
```

Both `A.X` and `dualScheme A hA` are objects of `Over (Spec k)`, so `f` is
a morphism over the field. Its underlying scheme morphism `f.left` is
surjective in Mathlib's `AlgebraicGeometry.Surjective` sense: its map of
underlying points is surjective. No compatibility with a group law on the
target is asserted.

The declaration is universe-polymorphic in `u` and retains arbitrary fields,
including imperfect fields. Its hypotheses do not include projectivity,
an ample line bundle, tensor or pullback coherence, inverse-bundle inputs,
or finiteness assumptions on the parameter scheme.

## Original source and derived formulation

The registered source is B. Edixhoven, G. van der Geer and B. Moonen,
*Abelian Varieties*, preliminary version of the first chapters,
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The printed page number is the PDF page number minus four.

Chapter VI §3, printed p.95 (PDF p.99), admits the Picard group scheme of
an abelian variety over a field, with projective connected components, and
identifies its functor with rigidified line-bundle classes. It constructs
the Poincaré bundle and the morphism `φ_L` classifying the Mumford bundle,
with point formula `x ↦ [t_x^*L ⊗ L⁻¹]`, and observes that this morphism
factors through `Pic⁰`. Theorem (6.18), printed p.96 (PDF p.100), says
that `φ_L : A → Pic⁰` is an isogeny for every ample line bundle `L`.
Definition (6.19) on that page names `Pic⁰` the dual abelian variety.

Paragraph (6.2), printed p.88 (PDF p.92), specifies the rigidified universal
property by actual pullback of a Poincaré bundle. Corollary (7.22),
printed p.106 (PDF p.110), identifies `Pic⁰` with the kernel of the
line-bundle homomorphism `φ`. Proposition (7.21), printed pp.105–106
(PDF pp.109–110), provides the relevant point description: over an
algebraically closed field, an ample `L` and a line bundle `M` with
`φ_M = 0` admit `x` such that `M ≅ t_x^*L ⊗ L⁻¹`.

This is a derived formulation about the Library's chosen universal
parameter scheme, rather than a verbatim theorem about the source's
Picard-scheme identity component. The existing `HasDualScheme A` asserts
that an actual parameter scheme carries an `IsUniversalPicardZero A`
family. This universal property classifies rigidified Picard-zero
classes over every test scheme by actual pullback. Its membership
predicate is translation invariance on algebraically closed field-valued
fibres. `dualScheme A hA` chooses that parameter scheme; this module
does not change the predicate or the choice.

The expected witness is the classifier of an ample line bundle's
rigidified Mumford family. A proof along this route must construct an
ample line bundle without adding it as a hypothesis, establish the
family's geometric Picard-zero membership, and justify lifting
algebraically closed field-valued points of the chosen parameter scheme
using the source's translation-invariant description. Passing from
line-bundle isomorphism to the rigidified classes used by the universal
property is part of that comparison. These are proof obligations;
the source statements alone are not a formal identification of the
Library functor with `Pic⁰`.

## Role and status

Together with `FieldDualSchemeSmoothStatement` and
`FieldDualSchemeSeparatedStatement`, this supplies the intended
surjection input to the parent `FieldDualSchemeGeometryStatement`.
Universal closedness of the chosen dual descends from the proper source
along the surjection; geometric connectedness descends along its base
changes.

The Lean declaration is reused from Worker 268's shared draft for the
parent geometry proof, with the provenance explanation expanded here.
This module supplies a statement only. It gives no proof or new axiom;
the exact proposition remains a separate proof obligation.
