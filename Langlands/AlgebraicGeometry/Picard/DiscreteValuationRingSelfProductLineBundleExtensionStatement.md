# Extension of self-product line bundles over a discrete valuation ring

`Langlands.AbelianScheme.DiscreteValuationRingSelfProductLineBundleExtensionStatement.{u}`
defines the following proposition. For an abelian scheme over the spectrum of
a discrete valuation ring, every line bundle on its generic self-product is
the restriction of an actual line bundle on the total self-product, up to an
actual isomorphism of module sheaves. This module states the proposition and
supplies no proof or new axiom.

Worker 513 authored this specialization of the trait extension input used in
Raynaud's proof of Lemme XI 1.5.

## Formal statement

Fix a universe `u`. Quantify over every `R : Type u` with instances
`CommRing R`, `IsDomain R` and `IsDiscreteValuationRing R`, every chosen
fraction field `K : Type u` with its specified `Field K`, `Algebra R K` and
`IsFractionRing R K` instances, and every Library abelian scheme
`A : AbelianScheme (Spec (CommRingCat.of R))`.

Write

```text
S = Spec R, T = Spec K,
b = Spec.map (CommRingCat.ofHom (algebraMap R K)) : T ⟶ S,
B = (baseChange b).obj A,
π = pullback.fst A.X.hom b : B.X.left ⟶ A.X.left.
```

The products are the actual Library schemes

```text
P   = (mumfordProduct A).left = A ×_S A,
P_K = (mumfordProduct B).left = B ×_T B.
```

The explicit `pullback.map` in Lean defines `q : P_K ⟶ P` using `π` on
both factors and `b` on the base. Its two base equations are the actual
base-change pullback conditions. This is exactly the formula for `q` in the
published `ValuationRingTwoAxisExtensionStatement`; it also agrees with
`mumfordProductBaseChangeMap A b` in `SelfProductBaseChange`. The latter
module proves that this self-product after base change is canonically
isomorphic to `P ×_S T`, and identifies `q` with its projection.

For every `D : LineBundle P_K`, the conclusion is

```text
∃ E : LineBundle P,
  Nonempty (((LineBundle.pullback q).obj E).obj ≅ D.obj).
```

`LineBundle` is the Library full subcategory of actual module sheaves
locally free of rank one. Its pullback lifts the ordinary pullback of
module sheaves. Thus both the witness `E` and the asserted restriction
isomorphism are about actual sheaves.

There is no hypothesis on the restrictions of `D` to the unit axes. There
is no ampleness, projectivity, polarization, henselianity, completeness,
residue-field or characteristic assumption. No uniqueness or extension of
chosen trivializations is asserted.

Mathlib's `IsDiscreteValuationRing` is a local principal ideal domain whose
maximal ideal is nonzero. It excludes fields. In particular its spectrum is
a trait, and the statement is restricted to this trait case. It does not
assert the extension result over general valuation domains of arbitrary
rank, including fields, required by `ValuationRingTwoAxisExtensionStatement`.
Even though its hypothesis on `D` is weaker, the restriction on the base
prevents it from proving that general statement by specialization.

## Original source and specialization

Michel Raynaud, *Faisceaux amples sur les schémas en groupes et les espaces
homogènes*, Lecture Notes in Mathematics 119 (1970), project copy second
corrected printing (1986), registered source
`provided-5d5546c6572c2556d06cb8181d9d78944bca00a4138a3ab39df0a5810f0fd485`,
SHA256 `29bce9a9be67396fd1bd8f0396e57d5ff08325eed53819e240eb14155711f38d`.
The relevant passage is the proof of Lemme XI 1.5, rendered PDF pp.165–166
(printed pp.161–162), specifically the trait paragraph on printed p.162.

After reducing to a noetherian base in that proof, Raynaud considers a trait
`T` over that base. He states that every invertible sheaf on the generic
fibre of `G ×_T G` extends to an invertible sheaf on `G ×_T G`: smoothness
of `G` makes the local rings of this self-product regular. The passage has
no axis-triviality hypothesis. The correspondence argument and its
rigidification requirements are subsequent, separate steps.

For the present specialization, take the trait to be `Spec R` and the
abelian scheme to be the Library `A`. Its structure morphism is smooth.
The self-product is smooth over `Spec R`, which is regular and noetherian
because `R` is a DVR. The regularity argument in the cited passage
therefore applies. The specified `IsFractionRing R K` identifies `Spec K`
over `Spec R` with the generic point, so its generic self-product is the
actual `P_K` above, with restriction along precisely `q`. An invertible
sheaf is expressed by the Library's locally free rank-one module-sheaf
bundle. These identifications explain the source specialization; this
statement module does not implement the extension argument.

The cited passage was checked in the rendered source. No source-specific
Raynaud errata note was found by the bounded filename checks in the
workspace, project notes and current Library notes. This records those
checks without claiming that no errata exist.

## Remaining proof obligations and role

A proof must construct an actual extending line bundle and the displayed
isomorphism for the specified fraction field and canonical map. One route
is to implement regularity and local factoriality of the smooth total
self-product over the DVR, extend a divisor from the generic fibre, and
construct the resulting invertible sheaf with its restriction
isomorphism. The source's explanation of regularity does not supply any
of those Lean constructions.

This is an independent prerequisite for the trait step in the proof of
the arbitrary-valuation extension statement. No correspondence representer,
ordinary or fppf Picard comparison, noetherian approximation, or passage
from traits to arbitrary valuation bases is constructed or assumed here.
The imports are `MumfordBundle` and Mathlib's DVR interface; no downstream
valuative or ample extension statement is used.
