# Statement: the fibral isomorphism criterion

Worker 75.

`Langlands.AlgebraicGeometry.FibralIsomorphismStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition in `Langlands.AlgebraicGeometry.FibralIsomorphismStatement`. This
module does not prove it, and it adds no other definitions, theorems or axioms. It imports
only Mathlib: `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
`Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Mathlib.AlgebraicGeometry.ResidueField` and
`Mathlib.CategoryTheory.Comma.Over.Pullback`.

## Statement

For every scheme `S : Scheme.{u}`, objects `Y Y' : Over S` and morphism `h : Y ⟶ Y'` of
`S`-schemes, assume:

1. the structure morphism `Y.hom : Y.left ⟶ S` is `LocallyOfFinitePresentation`;
2. the structure morphism `Y'.hom : Y'.left ⟶ S` is `LocallyOfFinitePresentation`;
3. `Y.hom` is `Flat`;
4. for every point `s : S`, the fibre morphism
   `((Over.pullback (S.fromSpecResidueField s)).map h).left` is an isomorphism (`IsIso`).

Then the underlying scheme morphism `h.left : Y.left ⟶ Y'.left` is an isomorphism.

The predicates are Mathlib's scheme-morphism classes `AlgebraicGeometry.Flat` and
`AlgebraicGeometry.LocallyOfFinitePresentation`, used here as ordinary hypotheses, and
`CategoryTheory.IsIso` in the category of schemes. Since the forgetful functor
`Over S ⥤ Scheme` reflects isomorphisms, `IsIso h.left` is equivalent to `h` being an
isomorphism of `S`-schemes.

## The fibre morphism

`S.fromSpecResidueField s : Spec κ(s) ⟶ S` is Mathlib's canonical morphism from the spectrum
of the residue field at `s`. The functor
`Over.pullback (S.fromSpecResidueField s) : Over S ⥤ Over (Spec κ(s))` is the categorical
base change. It sends `Y` to the fibre `Y_s = Y ×_S Spec κ(s)` and `h` to the induced morphism
`h_s : Y_s ⟶ Y'_s` of `κ(s)`-schemes; its `.left` is the scheme morphism `h_s`. The fibres are
formed exactly as in the published
[`FiberwiseFlatnessStatement`](FiberwiseFlatnessStatement.md) and in
`isOpenImmersion_of_fiberwise` ([`FiberwiseOpenImmersion`](FiberwiseOpenImmersion.md)). The
quantifier ranges over all points `s : S`, not only closed points.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
printed page numbers.

- Lemma B.3.1, p.288: "Let h : Y → Y′ be a map between locally finitely presented schemes
  over a scheme S, and assume that Y is S-flat. If h_s is an isomorphism for all s ∈ S then
  h is an isomorphism."

Conrad's proof is the citation "This is part of [EGA, IV₄, 17.9.5] (or see Exercise 3.4.3)".
Exercise 3.4.3 (p.104) outlines a direct proof in the noetherian case. Conrad calls this the
"fibral isomorphism criterion" and uses it throughout the notes, for example in the proofs of
Theorem 3.3.4 (p.99) and Proposition 3.3.8 (p.102).

## Derivation from the source

| Conrad Lemma B.3.1 | Lean |
| --- | --- |
| `S` a scheme; `h : Y → Y′` a map of `S`-schemes | `S : Scheme.{u}`, `Y Y' : Over S`, `h : Y ⟶ Y'` |
| `Y`, `Y′` locally finitely presented over `S` | `LocallyOfFinitePresentation Y.hom`, `LocallyOfFinitePresentation Y'.hom` |
| `Y` is `S`-flat | `Flat Y.hom` |
| `h_s` an isomorphism for all `s ∈ S` | `∀ s : S, IsIso ((Over.pullback (S.fromSpecResidueField s)).map h).left` |
| conclusion: `h` is an isomorphism | `IsIso h.left` |

In Conrad's notes, the fibre `h_s` at a point `s ∈ S` is the base change to `Spec κ(s)`. The
base `S` is arbitrary; the statement adds no noetherian, quasi-compactness, separatedness or
group-structure hypothesis, and does not assume that `Y'` is flat over `S`. The universe is a
single parameter `u`, the universe of `Scheme.{u}`.

## Provenance

The statement is derived from the source lemma. It is a general scheme-theoretic result that
the group-scheme theory of the Library uses repeatedly. The Library already proves the
corresponding criterion for open immersions, `isOpenImmersion_of_fiberwise`, under the
weaker hypothesis that `Y'` is locally of finite type over `S`.

## Proof boundary

This module defines a proposition; it proves nothing. A separate exact-target proof must
show that `h.left` is an isomorphism for every stated `S`, `Y`, `Y'` and `h`. One route: the
fibres of `h` are open immersions, so `h.left` is an open immersion by
`isOpenImmersion_of_fiberwise`; the fibres are surjective, so `h.left` is surjective; a
surjective open immersion is an isomorphism.
