# Valuative existence for the chosen dual over a quasi-separated base

`Langlands.AbelianScheme.RelativeDualSchemeValuativeExistenceStatement` is a
proposition definition. For every `S : Scheme.{u}` with
`[QuasiSeparatedSpace S]`, every `A : AbelianScheme S` and every proof
`hA : HasDualScheme A`, it asserts

```text
ValuativeCriterion.Existence (dualScheme A hA).hom
```

that is, the structural morphism `(dualScheme A hA).hom : (dualScheme A hA).left ⟶ S`
of the actual chosen parameter scheme satisfies the existence part of
Mathlib's valuative criterion. This unit only defines the proposition. It
does not prove it, and it introduces no axiom.

## Exact Lean assertion

Mathlib's `ValuativeCriterion.Existence f` says that every
`ValuativeCommSq f` has a lift. Here `f` is `(dualScheme A hA).hom`. Such a
square consists of:

- a type `R : Type u` with `CommRing`, `IsDomain` and `ValuationRing`
  instances, so `R` is a valuation domain of arbitrary rank;
- a field `K : Type u` with `Algebra R K` and `IsFractionRing R K`, so `K` is
  the fraction field of `R`;
- a morphism `i₁ : Spec K ⟶ (dualScheme A hA).left` and a morphism
  `i₂ : Spec R ⟶ S`, where `Spec K` and `Spec R` are the spectra of the
  actual rings (`Spec ↧K` and `Spec ↧R` in Mathlib);
- a proof of `CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (dualScheme A hA).hom i₂`, that is,
  `i₁ ≫ (dualScheme A hA).hom = Spec.map (algebraMap R K) ≫ i₂`.

The conclusion `S.commSq.HasLift` says that there is a morphism
`l : Spec R ⟶ (dualScheme A hA).left` with
`Spec.map (algebraMap R K) ≫ l = i₁` and `l ≫ (dualScheme A hA).hom = i₂`.
The lift is over the given `R` and `K`. No extension of `K`, no
replacement of `R` by another valuation ring and no base alteration is
allowed. Only existence is asserted. Uniqueness of the lift
(`ValuativeCriterion.Uniqueness`) is a different property and is not part
of this statement. The squares are not restricted to discrete valuation
rings or to noetherian rings. Every universe level is `u`, as in Mathlib's
`ValuativeCommSq`.

## Scope

The declaration is universe-polymorphic in `u`. The only base hypothesis is
`QuasiSeparatedSpace S`. No noetherian, reducedness, quasi-compactness,
projectivity, ample-line-bundle, polarization or coherence premise is
imposed on `S`, `A`, `hA`, the parameter scheme or its morphism. In
particular the statement does not assume that `(dualScheme A hA).hom` is
quasi-compact, separated or of finite type. `HasDualScheme`, `dualScheme`
and the Picard-zero predicate are the existing Library definitions in
`Langlands.AlgebraicGeometry.Picard.DualScheme`. They are imported
unchanged. The target is conditional on `hA` and makes no claim that a dual
exists.

## Original source and derived formulation

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
Harvard thesis, revised March 14, 2021, registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`. The
following passages were read:

- The conventions, printed p.xxvi (PDF p.26), say that schemes are almost
  always quasi-separated preschemes, unless otherwise specified. Geometric
  points are morphisms from algebraically closed fields. This is why the
  base hypothesis is kept.
- Definition 1.3.1.1, printed p.67 (PDF p.95), defines an abelian scheme as
  a group scheme `A → S` that is proper, smooth, and has geometrically
  connected fibres.
- Definition 1.3.2.1, printed p.73 (PDF p.101), defines the relative Picard
  functor and its subfunctor `Pic⁰(A/S)`. This subfunctor is cut out by
  fibrewise algebraic equivalence to zero. Line bundles of the form
  `pr₂^*(M)` are quotiented out. Lemma 1.3.2.2, printed pp.73–74 (PDF
  pp.101–102), identifies these functors with the rigidified functors
  `Pic_e(A/S)` and `Pic⁰_e(A/S)`.
- Theorem 1.3.2.3, printed p.74 (PDF p.102), states that for every abelian
  scheme `A → S`, `Pic⁰_e(A/S)` is representable by an abelian scheme
  `A^∨` over `S`. For the proof it refers to Faltings–Chai, *Degeneration of
  abelian varieties*, Ch. I, §1. Remark 1.3.2.4 notes that the functors are
  also representable when `A` is locally projective over `S`. This is an
  alternative route, not an extra premise of the theorem, so no local
  projectivity hypothesis is added here. Definition 1.3.2.5 names the
  universal rigidified Poincaré sheaf on `A ×_S A^∨`.

The author's March 14, 2021 errata, registered as
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
were read at PDF pp.1 and 8–9. Page 1 recommends reading the revision. It
also replaces the convention that schemes are separated by the convention
that they are quasi-separated. Page 8 corrects Definition 1.3.2.1: the
quotiented line bundles are `pr₂^*(M)` for `M` on `T`, not on `S`. The
revision has this correction. Page 9 continues the list for Section 1.3.2.
Its first item supplies a missing "S" in the original thesis's
Rem. 1.3.2.5. None of its items changes the passages used here. The errata
use the numbering of the original thesis; the numbering above is the
revision's.

This proposition is a derived formulation about the Library's chosen
parameter scheme, not a verbatim source theorem. The source representer
`A^∨` is an abelian scheme, so it is proper over `S`. By Mathlib's
`UniversallyClosed.eq_valuativeCriterion`
(`@UniversallyClosed = ValuativeCriterion.Existence ⊓ @QuasiCompact`), a
proper morphism satisfies `ValuativeCriterion.Existence`. To transfer this
conclusion to `dualScheme A hA`, a proof that uses the source must
identify the chosen parameter scheme with the source representer over `S`.

In the Library, `HasDualScheme A` asserts that some parameter scheme
carries an actual rigidified family satisfying `IsUniversalPicardZero A`.
That predicate's Picard-zero condition is translation invariance on every
geometric fibre. Its universal property classifies actual rigidified
classes over every test scheme `T : Over S`, including nonreduced ones. A
comparison with the source must identify the actual rigidified functors on
these tests. It must compare the source's fibrewise algebraic equivalence
to zero with the Library's geometric-fibre translation-invariance
condition, and it must also compare line bundles, rigidifications and
pullbacks. Agreement on geometric points does not suffice. Lan's test
schemes are quasi-separated, whereas the Library's universal property
quantifies over all test schemes. One may first restrict the Library
property to quasi-separated tests. An isomorphism of the actual parameter
schemes must then still be recovered, for example by affine tests and
gluing, without assuming that the chosen parameter scheme is already
quasi-separated. The valuative existence property must finally be
transported along that isomorphism over `S`. The paired Markdown of
`RelativeDualSchemeGeometryStatement` describes the same comparison
boundary. None of these steps is carried out in this unit.

A direct proof is another possible route. The given `i₂` makes `Spec R` a
test scheme `Over.mk i₂` over `S`. By the universal property of the chosen
family, every Picard-zero rigidified class over that test is classified by a
unique morphism `Over.mk i₂ ⟶ dualScheme A hA`, whose underlying morphism `l`
satisfies `l ≫ (dualScheme A hA).hom = i₂`. To obtain the required lift, one
would extend the rigidified pullback of the chosen Poincaré family along
`i₁` from `Spec K` to all of `Spec R`, keeping the Picard-zero condition on
every geometric fibre. The equation `Spec.map (algebraMap R K) ≫ l = i₁`
must then be derived from compatibility of classification with actual
pullback. The Library lemma `dualClassify_pullback` gives this
compatibility, but only under its explicit coherence and stability inputs. Extending rigidified Picard-zero line
bundles over an arbitrary valuation domain is a substantial proof
obligation. Writing this proposition, or citing the source representer,
does not prove it. This route description is guidance, not proof evidence.

## Role

Mathlib's `UniversallyClosed.of_valuativeCriterion` derives
`UniversallyClosed f` from `[QuasiCompact f]` and
`ValuativeCriterion.Existence f`. This proposition is therefore one
prerequisite for the properness target
`RelativeDualSchemeProperStatement` (in
`Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeProperStatement`).
Quasi-compactness of `(dualScheme A hA).hom` is a separate prerequisite and
is deliberately not assumed here. Conversely, the properness target implies
this proposition through `UniversallyClosed.eq_valuativeCriterion`.
A proof of this proposition must therefore not assume the properness target
or the parent geometry target `RelativeDualSchemeGeometryStatement`.
Valuative existence is not a fibrewise property, so the field statement
`FieldDualSchemeGeometryStatement` does not imply it. A separate
exact-target proof obligation is required.

The exact Lean statement was specified by Worker 529 in the objective of
task `7e87e0e1-48f0-4f60-bcb7-ba864efdc0b6`. Worker 302 wrote the module
and this Markdown after reading the cited passages and errata.
