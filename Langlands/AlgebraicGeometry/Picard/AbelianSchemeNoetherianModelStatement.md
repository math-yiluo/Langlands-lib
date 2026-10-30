# Noetherian models of an abelian scheme with two rigidified line bundles

`Langlands.AbelianScheme.AbelianSchemeNoetherianModelStatement.{u}` is the proposition

```lean
∀ (R : CommRingCat.{u}) (A : AbelianScheme (Spec R))
  (M₁ M₂ : RigidifiedLineBundle (unitSection A)),
  ∃ (R₀ : CommRingCat.{u}) (_ : IsNoetherianRing R₀) (φ : R₀ ⟶ R)
    (A₀ : AbelianScheme (Spec R₀)) (a : A.X.left ⟶ A₀.X.left)
    (M₁₀ M₂₀ : RigidifiedLineBundle (unitSection A₀)),
    IsPullback a A.X.hom A₀.X.hom (Spec.map φ) ∧
      unitSection A ≫ a = Spec.map φ ≫ unitSection A₀ ∧
      Nonempty ((LineBundle.pullback a).obj ((RigidifiedLineBundle.forget _).obj M₁₀) ≅
        (RigidifiedLineBundle.forget _).obj M₁) ∧
      Nonempty ((LineBundle.pullback a).obj ((RigidifiedLineBundle.forget _).obj M₂₀) ≅
        (RigidifiedLineBundle.forget _).obj M₂)
```

It lives in module `Langlands.AlgebraicGeometry.Picard.AbelianSchemeNoetherianModelStatement`,
which imports only `Langlands.AlgebraicGeometry.Picard.RelativePicardZero`. This unit only
defines the proposition. It proves nothing.

## Meaning

Let `R` be an arbitrary commutative ring and `A` an abelian scheme over `Spec R`, with total
space `A.X.left` and structure morphism `A.X.hom : A.X.left ⟶ Spec R`. Let `M₁` and `M₂` be two
line bundles on `A.X.left`, each rigidified along the unit section
`unitSection A : Spec R ⟶ A.X.left`. The proposition provides:

- a noetherian commutative ring `R₀` in the same universe `u` and a ring map `φ : R₀ ⟶ R`;
- an abelian scheme `A₀` over `Spec R₀`;
- a morphism of schemes `a : A.X.left ⟶ A₀.X.left` such that the square

  ```text
  A.X.left  --a-->  A₀.X.left
     |                 |
  A.X.hom           A₀.X.hom
     v                 v
   Spec R --Spec.map φ--> Spec R₀
  ```

  is a pullback square (`IsPullback a A.X.hom A₀.X.hom (Spec.map φ)`). So `A.X.left` is the
  base change `Spec R ×_{Spec R₀} A₀.X.left`, with `a` the projection;
- the compatibility `unitSection A ≫ a = Spec.map φ ≫ unitSection A₀`: `a` carries the unit
  section of `A` to the unit section of `A₀`;
- two line bundles `M₁₀`, `M₂₀` on `A₀.X.left`, each rigidified along `unitSection A₀`, such
  that for `i = 1, 2` the pullback along `a` of the underlying line bundle of `Mᵢ₀` is
  isomorphic to the underlying line bundle of `Mᵢ`.

## What is deliberately not asked

- No compatibility of `a` with the group laws of `A` and `A₀` is required. Only the pullback
  square and the unit sections are needed by the downstream use.
- The isomorphisms are between the underlying line bundles only
  (`RigidifiedLineBundle.forget`), not between rigidified line bundles. The rigidifications
  of `M₁` and `M₂` are not compared with those of `M₁₀` and `M₂₀`.
- There is no claim that `R₀` is a subring of `R`, or finitely generated. The expected proof
  takes a finitely generated `ℤ`-subalgebra of `R`, but the proposition only needs a
  noetherian `R₀` and some ring map `φ`.

## Exact interface

All names are published ones or Mathlib's; nothing is redefined.

- `AbelianScheme (Spec R)`, `unitSection A` and `unitSection_comp A` (used implicitly by the
  `RigidifiedLineBundle` type) are from `Langlands.AlgebraicGeometry.Picard.RelativePicardZero`.
- `RigidifiedLineBundle ε` for `ε : S ⟶ X` is the published category of line bundles on `X`
  rigidified along `ε`; `RigidifiedLineBundle.forget ε` is its forgetful functor to
  `LineBundle X`.
- `LineBundle.pullback a : LineBundle A₀.X.left ⥤ LineBundle A.X.left` is the published
  pullback of line bundles along `a`.
- `IsPullback`, `Spec.map`, `IsNoetherianRing` are Mathlib's.

## Use

This proposition is the hypothesis of
`Langlands.AbelianScheme.RigidifiedClassesNoetherianApproximationReductionStatement.{u}`,
which says that it implies
`Langlands.AbelianScheme.RigidifiedClassesNoetherianApproximationStatement.{u}`. The
rigidifications forgotten here are recovered there from the published lemma
`RigidifiedLineBundle.nonempty_iso_of_forget_iso`, since `A.X.hom` has a section and
two rigidifications of one line bundle differ by a unit of the base.

## Provenance

Derived. It is the standard absolute noetherian approximation of an abelian scheme over an
affine base together with finitely many line bundles, from the Stacks Project, Chapter 32
"Limits of Schemes", registered as `stacks-limits-of-schemes-a04446e5` (file `limits.tex`,
commit `a04446e57ec1fbc252a871afcec7752fb2807b14`). Write `R` as the directed union of its
finitely generated `ℤ`-subalgebras, which are noetherian (Section 32.5, tag 01Z1). Then:

- the finitely presented scheme `A.X.left` over `Spec R`, its unit section and its group-law
  morphisms with the identities between them descend to some stage `R₀`
  (Lemma 32.10.1, tag 01ZM; Proposition 32.6.1, tag 01ZC); the descended scheme `A₀.X.left`
  gives the pullback square and the unit compatibility;
- smoothness and properness descend (Lemma 32.8.9, tag 0C0C; Lemma 32.13.1, tag 081F);
- the line bundles underlying `M₁` and `M₂` descend, and so do rigidifications along the
  descended unit section, after enlarging the stage (Lemma 32.10.2, tag 01ZR;
  Lemma 32.10.3, tag 0B8W);
- geometric connectedness of the fibres holds after replacing the stage by an open and
  closed part, since the number of geometric connected components of the fibres of a proper,
  flat, finitely presented morphism with geometrically reduced fibres is locally constant
  (Stacks Project, *More on Morphisms*, tag 0E0N, label `lemma-proper-flat-geom-red` in
  `more-morphisms.tex`, registered `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`).

These are the same references as the provenance of the published
`RigidifiedClassesNoetherianApproximationStatement`. The present proposition isolates the
geometric content of that approximation: it was introduced in proof task
`a825ba6f-ac5b-43b7-8794-52b2039388f7` as the interface between the descent half of the proof
and the formal reduction to the agreement equivalence.
