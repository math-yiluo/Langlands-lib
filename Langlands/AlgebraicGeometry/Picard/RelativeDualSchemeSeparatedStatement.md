# Separatedness of the chosen dual over a quasi-separated base

`Langlands.AbelianScheme.RelativeDualSchemeSeparatedStatement` is a
proposition definition. For every `S : Scheme.{u}` with
`[QuasiSeparatedSpace S]`, every `A : AbelianScheme S` and every proof
`hA : HasDualScheme A`, it asserts

```text
IsSeparated (dualScheme A hA).hom
```

that is, the structural morphism of the actual chosen parameter scheme
`dualScheme A hA : Over S` to `S` is separated. Mathlib's
`AlgebraicGeometry.IsSeparated` means that the diagonal
`pullback.diagonal (dualScheme A hA).hom` is a closed immersion.

The declaration is universe-polymorphic in `u`. The only hypothesis on the
base is quasi-separatedness of its underlying space. No noetherian,
reducedness, quasi-compactness, projectivity, ample line bundle,
polarization or coherence hypothesis is imposed on `S`, `A`, `hA`, the
parameter scheme or its structural morphism. In particular the chosen
parameter scheme, and its structural morphism, are not assumed to be
quasi-separated. `HasDualScheme`, `dualScheme` and the geometric Picard-zero
predicate used by `IsUniversalPicardZero` are the existing Library
definitions in `Langlands.AlgebraicGeometry.Picard.DualScheme`.

This unit provides a proposition definition only. It does not prove the
proposition, and no axiom is introduced.

## Original source and derived formulation

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
Harvard thesis, revised March 14, 2021, registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
The following passages were read:

- The conventions, printed p.xxvi (PDF p.26), take schemes to be
  quasi-separated preschemes unless otherwise specified. This is why the
  base hypothesis `[QuasiSeparatedSpace S]` is kept.
- Definition 1.3.1.1, printed p.67 (PDF p.95), defines an abelian scheme
  as a group scheme `A → S` that is proper, smooth and has geometrically
  connected fibres.
- Definition 1.3.2.1, printed p.73 (PDF p.101), defines the relative Picard
  functor as invertible sheaves on `X ×_S T` modulo those of the form
  `pr₂^* M` for `M` over `T`. Its part 2(b) defines the subfunctor
  `Pic⁰(A/S)` by the condition that every fibre `L_t` is algebraically
  equivalent to zero over `A_t`.
- Lemma 1.3.2.2, printed pp.73–74 (PDF pp.101–102), identifies these
  functors with the rigidified functors `Pic_e(A/S)` and `Pic⁰_e(A/S)` of
  invertible sheaves rigidified along `e_T`, up to isomorphism.
- Theorem 1.3.2.3, printed p.74 (PDF p.102), states that for every
  abelian scheme `A → S` the functor `Pic⁰_e(A/S)` is representable by an
  abelian scheme `A^∨` over `S`, referring to Faltings–Chai, Ch. I, §1 for
  the proof.
- Remark 1.3.2.4 on the same page notes that representability also follows
  from Hilbert schemes when `A` is locally projective over `S`, and
  that one may add local projectivity if one does not want to use
  Theorem 1.3.2.3. It imposes no premise on Theorem 1.3.2.3, so no local
  projectivity hypothesis is added here.
- Definition 1.3.2.5 on the same page names the tautological rigidified
  invertible sheaf on `A ×_S A^∨` the Poincaré invertible sheaf.

The author's March 14, 2021 errata, registered as
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
were checked at pp.1 and 8–9. Page 1 replaces the former convention that
schemes are separated by the convention that they are quasi-separated, and
recommends reading the revision. Page 8 corrects Definition 1.3.2.1 so that
the line bundles quotiented out are pulled back from `M` on the test scheme
`T`, not on `S`; the revision already incorporates this correction. No
entry on these pages corrects the representability theorem. The errata use
the original thesis numbering; this Markdown cites the revision's
numbering.

By Definition 1.3.1.1 the abelian scheme `A^∨` of Theorem 1.3.2.3 is proper
over `S`. Properness in the standard sense includes separatedness, and
Mathlib's `IsProper` likewise extends `IsSeparated`. Thus the source gives
separatedness of its representing object. The present proposition is a
derived formulation about the Library's chosen parameter scheme, not a
verbatim source theorem.

In the Library, `HasDualScheme A` asserts the existence of a parameter
scheme `P : Over S` with an actual rigidified family satisfying
`IsUniversalPicardZero A`, and `dualScheme A hA` is chosen from this
existence proof. The fibre condition of that predicate is translation
invariance on every algebraically closed geometric fibre, and the universal
property classifies families over every test scheme, including nonreduced
ones. A proof by comparison with the source's representing object must
therefore compare actual rigidified functors and pullbacks, including over
nonreduced test schemes, and must justify the equivalence between the
source's fibrewise algebraic equivalence to zero and the Library's
geometric-fibre translation-invariance condition. Agreement only on
geometric points does not suffice.

The source's test schemes are quasi-separated, whereas the Library's
universal property ranges over all test schemes. An isomorphism of the
actual parameter schemes must then be recovered, for example by affine
tests and gluing, without assuming that the chosen dual or its structural
morphism is already quasi-separated. Separatedness would then be
transported along that isomorphism over `S`. A direct proof of
separatedness, for example by studying the closed locus on which two
rigidified Picard-zero families agree via a seesaw argument, is another
possible route. Mathlib's `IsSeparated.of_valuativeCriterion` additionally
requires `QuasiSeparated` of the morphism; that hypothesis is not part of
this statement and would have to be proved. These remarks are route
guidance only; none of these steps is proved in this unit.

## Role

Mathlib's `IsProper` is the conjunction of `IsSeparated`,
`UniversallyClosed` and `LocallyOfFiniteType`. This proposition is the
separatedness component of the Library target
`RelativeDualSchemeProperStatement`, which asserts
`IsProper (dualScheme A hA).hom` under the same quantifiers and base
hypothesis. No Lean lemma relating the two statements is provided here.

Separatedness is not a fibrewise property. The field statement
`FieldDualSchemeSeparatedStatement`, over `Spec k` for a field `k`, is a
separate target and does not imply this arbitrary-base proposition.
