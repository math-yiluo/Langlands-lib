# Comparison of universal smooth-family parameters

`Langlands.AbelianScheme.SmoothFamilyUniversalComparisonStatement.{u}` is a
proposition definition. It is not a proof, and no axiom is introduced.

## Exact statement

The definition is

```lean
∀ (S : Scheme.{u}) (A : AbelianScheme S) (P Q : Over S) [QuasiSeparatedSpace P.left]
  (L : RigidifiedFamily A P) (M : RigidifiedFamily A Q),
  IsUniversalSmoothFamilyOnQuasiSeparatedTests A L →
  IsUniversalSmoothFamilyOnQuasiSeparatedTests A M →
  ∃! e : P ≅ Q,
    Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) e.hom).obj M ≅ L)
```

- `S` is an arbitrary scheme in universe `u`; it is not assumed
  quasi-separated. `A : AbelianScheme S` is the Library's actual abelian
  scheme, with `unitSection A : S ⟶ A.X.left` and
  `unitSection_comp A : unitSection A ≫ A.X.hom = 𝟙 S`.
- `P` and `Q` are objects of Mathlib's category `Over S`. The only
  hypothesis on them is `QuasiSeparatedSpace P.left`: the underlying space
  of the first parameter is quasi-separated. `Q.left` is unrestricted.
- `L : RigidifiedFamily A P` and `M : RigidifiedFamily A Q` are actual
  rigidified line bundles on the relative family over `P` and over `Q`, as
  defined in `Langlands.AlgebraicGeometry.Picard.RelativePicardZero`.
- Both hypotheses use the existing predicate
  `IsUniversalSmoothFamilyOnQuasiSeparatedTests` from
  `Langlands.AlgebraicGeometry.Picard.SmoothFamilyQuasiSeparatedRepresentabilityStatement`,
  imported by its Lean name and neither redefined nor replaced. For `L` it is
  the conjunction of `IsAlgebraicallyTrivialFamilyViaSmoothFamily A L` and the
  requirement that for every `T : Over S` with `[QuasiSeparatedSpace T.left]`
  and every `q : AlgebraicallyTrivialClassesViaSmoothFamily A T` there is
  exactly one `h : T ⟶ P` with
  `RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
  (unitSection_comp A) L T h = q.val`; likewise for `M` with `Q`.
- The conclusion asserts that there is exactly one isomorphism `e : P ≅ Q`
  in `Over S` such that the actual rigidified pullback of `M` along
  `e.hom : P ⟶ Q`, namely
  `(RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
  (unitSection_comp A) e.hom).obj M`, is isomorphic to `L` in the category
  `RigidifiedFamily A P` of rigidified line bundles. `Nonempty` records only
  the existence of such a bundle isomorphism; no particular isomorphism is
  chosen, and uniqueness concerns `e` only.

The statement does not assert that a universal pair exists; existence is the
separate proposition `SmoothFamilyQuasiSeparatedRepresentabilityStatement`,
and the abelian-scheme representer is
`SmoothFamilyAbelianRepresentabilityStatement`. Neither is assumed here.
There is no further hypothesis: in particular no quasi-separatedness of `S`
or `Q.left`, no separatedness, quasi-compactness, finiteness or noetherian
condition, and no assumption that the smooth-family condition is stable under
pullback. The declaration is universe-polymorphic in `u`.

## Derived provenance and role

This is a derived internal formalization target, not a theorem quoted from
the literature, and no original source is cited for it. It is the familiar
uniqueness of representing objects up to unique compatible isomorphism,
specialized to the Library's smooth-family classification on quasi-separated
tests.

Its purpose is the final assembly of the geometry targets
`SmoothFamilyFinitePresentationStatement` and `SmoothFamilyFlatStatement`.
Those quantify over an arbitrary universal pair `(P, L)` with `P.left`
unrestricted. Once an abelian-scheme representer `(B, N)` is available, with
`B.X.left` quasi-separated because `B.X.hom` is proper (hence separated) over
a quasi-separated base, this statement applied with the first parameter
`B.X` and the second parameter the given `P` yields `B.X ≅ P` over `S`, and
geometric properties of `B.X.hom` transport to `P.hom`. This is why the
quasi-separatedness assumption is placed on the first parameter only.

## Expected proof route

A future proof is expected to proceed as follows; none of these steps is
implemented in this module, and none is a hypothesis.

1. Classify `L` by `M`: since `P.left` is quasi-separated, `P` is a permitted
   test, so the universality of `M` gives a unique `k : P ⟶ Q` whose
   classifying map sends the identity to the class of `L`.
2. Show that `g ↦ g ≫ k` is bijective on morphisms from every
   quasi-separated test `T`. This uses
   `RigidifiedLineBundle.classifyingMap_comp` (with the module pullback
   coherence) and requires that the smooth-family condition is preserved by
   actual rigidified pullback, so that pullbacks of `L` and `M` define
   classes in `AlgebraicallyTrivialClassesViaSmoothFamily`. That pullback
   stability is not yet in the Library and is a separate obligation.
3. Conclude `IsIso k` by the published criterion
   `Langlands.AlgebraicGeometry.quasiSeparatedTestIsoDetection`, which tests
   only quasi-separated schemes and needs no hypothesis on `Q.left`.
4. Uniqueness of `e` follows from uniqueness of `k` via
   `RigidifiedLineBundle.classifyingMap_eq_iff`.
