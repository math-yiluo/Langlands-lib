# Extension of Picard-zero classes across a dominating valuation ring

`Langlands.AbelianScheme.PicardZeroValuativeExtensionStatement` is a
proposition definition. Take a rigidified Picard-zero class on an abelian
scheme over the fraction field of a valuation ring. The proposition says that
the class extends over a valuation ring, after passing to an extension field
and a valuation ring of it that dominates the original one. This unit only
defines the proposition. It does not prove it, and it introduces no axiom.

## Exact Lean assertion

The statement quantifies over:

- a scheme `S : Scheme.{u}` with `[QuasiSeparatedSpace S]` and an abelian
  scheme `A : AbelianScheme S`;
- a valuation domain `R : Type u` (`CommRing`, `IsDomain`, `ValuationRing`),
  of arbitrary rank;
- a field `K : Type u` with `Algebra R K` and `IsFractionRing R K`;
- a morphism `i₂ : Spec R ⟶ S`;
- a class `q : PicardZeroClasses A TK`, where `TK` is the test scheme
  `Over.mk (Spec.map (algebraMap R K) ≫ i₂)`, that is, `Spec K` over `S`.

Here `Spec R` stands for `Spec (CommRingCat.of R)` and `Spec.map g` for
`Spec.map (CommRingCat.ofHom g)`. `PicardZeroClasses A T` is the Library
subtype of rigidified isomorphism classes on `A ×_S T` that satisfy
`IsPicardZeroClass` (`Langlands.AlgebraicGeometry.Picard.RelativePicardZero`).
The rigidification is along the unit section `unitSection A`. A class
satisfies `IsPicardZeroClass` when its underlying line bundle on `A ×_S T`
satisfies `IsGeometricallyPicardZero`. That predicate says: for every
algebraically closed field `k : Type u` and every morphism
`Spec k ⟶ T.left`, the restriction of the bundle to the geometric fibre is
isomorphic to its pullback under translation by every `k`-point of that
fibre.

The conclusion asserts that there exist:

- a valuation domain `R' : Type u` and a field `K' : Type u` with
  `Algebra R' K'` and `IsFractionRing R' K'`;
- a ring homomorphism `φ : R →+* R'` with `IsLocalHom φ`;
- a ring homomorphism `ψ : K →+* K'`;
- a proof `hφψ` of the ring-level square
  `(algebraMap R' K').comp φ = ψ.comp (algebraMap R K)`;
- a class `q' : PicardZeroClasses A TR'`, where `TR'` is
  `Over.mk (Spec.map φ ≫ i₂)`, that is, `Spec R'` over `S` through `Spec R`;

such that the two pullbacks of rigidified classes to the test scheme
`TK' = Over.mk (Spec.map ψ ≫ Spec.map (algebraMap R K) ≫ i₂)`, that is,
`Spec K'` over `S`, agree:

```text
classesPullback (Over.homMk (Spec.map (algebraMap R' K')) _ : TK' ⟶ TR') q'.val
  = classesPullback (Over.homMk (Spec.map ψ) rfl : TK' ⟶ TK) q.val
```

`classesPullback` is `RigidifiedLineBundle.classesPullback A.X.hom
(unitSection A) (unitSection_comp A)`, the Library pullback of rigidified
classes along a morphism of test schemes. The proof term `_` of the first
`Over.homMk` is the commutativity `Spec.map (algebraMap R' K') ≫ Spec.map φ ≫
i₂ = Spec.map ψ ≫ Spec.map (algebraMap R K) ≫ i₂`, which follows from `hφψ`.
Only equality of the pulled-back classes over `Spec K'` is asserted. No
statement about `Spec K` itself, and no uniqueness of `q'`, is made.

Since `ψ` is a homomorphism of fields and both `algebraMap`s are injective,
`hφψ` forces `φ` to be injective. `IsLocalHom φ` says that `φ` maps the
maximal ideal of `R` into that of `R'`. Viewing `R` in `K'` through `ψ` and
`R'` in `K'` through `algebraMap R' K'`, the two conditions together say that
`R'` dominates the image of `R`. Because `q'` lies in `PicardZeroClasses`, the
extended class must satisfy the Picard-zero predicate on every geometric
fibre of `A ×_S Spec R'`, including the fibres over the closed point.

## Scope

The declaration is universe-polymorphic in `u`, and `R'` and `K'` live in the
same universe as `R` and `K`. The only base hypothesis is
`QuasiSeparatedSpace S`. This matches Lan's conventions and the base
hypothesis of the target described below. No noetherian, discrete-valuation,
finite-rank, completeness, henselian or algebraic-closedness condition is
imposed on `R`, `K`, `R'` or `K'`. The field extension `K'` of `K` is not
required to be algebraic or finite. No ample line bundle, polarization,
projectivity hypothesis or representability hypothesis (`HasDualScheme`) is
imposed on `A`. The statement does not assume that a dual exists.

Taking `R' = R`, `K' = K`, `φ = id` and `ψ = id` shows that the statement is
implied by the version without a change of valuation ring. It is formally
weaker: a proof may pass to a larger field, for instance an algebraic
closure of `K`, and to a valuation ring of it dominating `R`.

## Original source

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
thesis revised March 14, 2021, registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`. The
following passages were read:

- The conventions, printed p.xxvi (PDF p.26), say that schemes almost
  always mean quasi-separated preschemes, unless otherwise specified.
  A geometric point is a morphism from an algebraically closed field.
- Definition 1.3.1.1, printed p.67 (PDF p.95): an abelian scheme is a group
  scheme `A → S` that is proper, smooth and has geometrically connected
  fibres. The Library's `AbelianScheme` bundles these three properties with
  a commutative group scheme, so commutativity is explicit there.
- Definition 1.3.2.1, printed p.73 (PDF p.101), defines the relative Picard
  functor and its subfunctor `Pic⁰(A/S)`. That subfunctor is cut out by the
  condition that for every point `t` of the test scheme the fibre `L_t` is
  algebraically equivalent to zero on `A_t`. Line bundles `pr₂^*(M)` are
  quotiented out. Lemma 1.3.2.2, printed pp.73–74 (PDF pp.101–102),
  identifies these functors with the rigidified functors `Pic_e(A/S)` and
  `Pic⁰_e(A/S)` of line bundles on `A ×_S T` with a rigidification along
  `e_T`, up to isomorphism.
- Theorem 1.3.2.3, printed p.74 (PDF p.102), states that for every abelian
  scheme `A → S`, `Pic⁰_e(A/S)` is representable by an abelian scheme `A^∨`
  over `S`. For the proof it refers to Faltings–Chai, *Degeneration of
  abelian varieties*, Ch. I, §1. Remark 1.3.2.4 gives representability for
  locally projective `A` as an alternative route; it is not a premise of
  the theorem, so no projectivity hypothesis is added here. Definition
  1.3.2.5 names the universal rigidified Poincaré sheaf on `A ×_S A^∨`.

The author's errata of March 14, 2021, registered as
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`, were
read at PDF pp.1 and 8–9. Page 1 recommends reading the revision. It also
replaces the convention that schemes are separated by the convention that
they are quasi-separated. Page 8 corrects Definition 1.3.2.1: the quotiented
line bundles are `pr₂^*(M)` for `M` on `T`, not on `S`. Page 9 fixes a
missing "S" in the original thesis's Rem. 1.3.2.5. The revision incorporates
these corrections, and none of them changes the passages used here. The
errata use the numbering of the original thesis; the numbering above is the
revision's.

## Derived formulation

This is a derived, internal prerequisite, not a verbatim source theorem.
Worker 302 formulated it for the exact-target proof task
`54d4a7cc-7607-4c5a-82e7-25bafba9e3e9`, whose target is
`Langlands.AbelianScheme.RelativeDualSchemeValuativeExistenceStatement`.
That target asserts Mathlib's `ValuativeCriterion.Existence` for the
structural morphism of the Library's chosen dual parameter scheme
`dualScheme A hA`.

Source justification, stated in Lan's terms. Let `S` be quasi-separated and
let `R`, `K` and `i₂` be as above. By Theorem 1.3.2.3, an element of
`Pic⁰_e(A/S)(Spec K)` is a point of `A^∨(K)` over `S`. Since `A^∨` is an
abelian scheme, `A^∨ → S` is proper. By the existence part of the valuative
criterion, which holds for arbitrary valuation rings, that point extends to
a point of `A^∨(R)` over `i₂`. This is an element of `Pic⁰_e(A/S)(Spec R)`
restricting to the given one over `Spec K`. This gives the source analogue
of the statement with `R' = R`.

The Library statement differs from this in its functor. `PicardZeroClasses`
uses the geometric-fibre translation-invariance predicate described above,
not Lan's fibrewise algebraic equivalence to zero. To apply Lan's theorem
to the Library predicate, one must compare the two rigidified functors. The
paired Markdown of `RelativeDualSchemeValuativeExistenceStatement` describes
that comparison: line bundles, rigidifications, pullbacks and the
Picard-zero conditions over arbitrary test schemes. This unit does not
carry out the comparison.

Role. Worker 302 reports a private Lean draft, unpublished and not reviewed,
in which this statement implies the target. It is not part of this unit and
is not evidence for anything here. The argument has two steps. First, pull
the Poincaré class back along `i₁ : Spec K ⟶ dualScheme` and extend it over
a dominating `R'` by this statement. The Library lemma
`dualClassify_pullback` then places its classifying morphism
`Spec R' ⟶ dualScheme` in the square over `Spec K'`. Second, descend that
lift to a lift over `Spec R`. This is the argument of Mathlib's
`ValuativeCriterion.Existence.of_specializingMap`. It uses the image of the
closed point of `Spec R'` in the base change of the dual along `i₂`. It also
uses that a valuation ring is maximal for domination among local subrings
of its fraction field (Mathlib's
`bijective_rangeRestrict_comp_of_valuationRing`). The ring-level square
`hφψ` and `IsLocalHom φ` are the data this descent uses. This is why the
statement allows a change of valuation ring.

The statement introduces no new definition. It uses the existing Library
declarations `AbelianScheme`, `PicardZeroClasses`, `unitSection`,
`unitSection_comp` and `RigidifiedLineBundle.classesPullback`, and Mathlib's
`Spec`, `Over`, `ValuationRing`, `IsFractionRing` and `IsLocalHom`.

Worker 302 specified the exact Lean statement in the objective of task
`0e323b86-9ca2-41a3-bbe2-af3fdad90034` and wrote the first draft of this
module and Markdown. Worker 967 checked the draft against the Library
definitions, the cited passages and errata, and revised the docstring and
this Markdown.
