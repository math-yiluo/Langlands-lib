# Proof of the reduced fibre theorem for schemes over a Nagata Dedekind domain

`Langlands.AlgebraicGeometry.DvrAffineReducedFibre.schemeReducedFibre.{u,v}` proves the Library
proposition `Langlands.AlgebraicGeometry.DvrAffineReducedFibre.SchemeReducedFibreStatement.{u,v}`,
imported from `Langlands.AlgebraicGeometry.DvrAffineReducedFibre.SchemeReducedFibreStatement`.
Its type is exactly that closed proposition, with independent universe levels `u` (for the
Dedekind domain, the schemes and the extension field) and `v` (for the fraction field). The
statement module is unchanged.

```lean
theorem schemeReducedFibre : SchemeReducedFibreStatement.{u, v}
```

## Statement proved

Let \(A\) be a Dedekind domain with fraction field \(K\), Nagata in the sense that \(A\) is
Noetherian and, for every prime \(\mathfrak p\), the integral closure of \(A/\mathfrak p\) in
every finite extension of its fraction field is a finite \(A/\mathfrak p\)-module. Let
\(f\colon X\to\operatorname{Spec}A\) be flat, locally of finite type and quasi-compact. Then there
is a finite extension \(L/K\) such that, with \(B\) the integral closure of \(A\) in \(L\) and
\(W = X\times_{\operatorname{Spec}A}\operatorname{Spec}B\), every quasi-compact open of \(W\) has
finitely many irreducible components, and the composite \(h\) of the normalization of \(W\) with
\(W\to\operatorname{Spec}B\) is smooth on an open neighbourhood of every generic point of every
fibre. In Lean the proposition is

```lean
def SchemeReducedFibreStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDedekindDomain A] (K : Type v) [Field K]
    [Algebra A K] [IsFractionRing A K],
    (IsNoetherianRing A ∧ ∀ (p : Ideal A) [p.IsPrime]
      (L : Type u) [Field L] [Algebra (FractionRing (A ⧸ p)) L] [Algebra (A ⧸ p) L]
      [IsScalarTower (A ⧸ p) (FractionRing (A ⧸ p)) L]
      [FiniteDimensional (FractionRing (A ⧸ p)) L],
      Module.Finite (A ⧸ p) (integralClosure (A ⧸ p) L)) →
    ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f] [LocallyOfFiniteType f] [QuasiCompact f],
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
        (_ : Algebra A L) (_ : IsScalarTower A K L),
      let g := Spec.algebraMap A (integralClosure A L)
      let W := pullback f g
      ∃ hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite,
        let h := schemeNormalizationHom W hW ≫ pullback.snd f g
        ∀ (b : Spec (.of ↥(integralClosure A L))) (y : h.fiber b),
          y ∈ genericPoints (h.fiber b) →
          ∃ U : (schemeNormalization W hW).Opens, h.fiberι b y ∈ U ∧
            Smooth (h.resLE ⊤ U le_top)
```

## Proof

The theorem is the Stacks copy's theorem for Tag 09IL,

```lean
theorem AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_pullback
    {A : Type u} [CommRing A] [IsDedekindDomain A] (K : Type v) [Field K]
    [Algebra A K] [IsFractionRing A K] (hA : StacksIsNagataRing A) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [Flat f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra A L) (_ : IsScalarTower A K L),
      ∃ hW : ∀ U : (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L)))) : Scheme.{u}).Opens,
        IsCompact (U : Set (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L)))) : Scheme.{u})) →
        (irreducibleComponents U).Finite,
      ∀ b : Spec (.of ↥(integralClosure A L)),
      ∀ y : (Scheme.stacksNormalization _ hW ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
        (algebraMap A ↥(integralClosure A L))))).fiber b,
      y ∈ genericPoints ↥((Scheme.stacksNormalization _ hW ≫ pullback.snd f (Spec.map
        (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L))))).fiber b) →
      InfinitesimalLifting.SmoothAt (Scheme.stacksNormalization _ hW ≫ pullback.snd f
          (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L)))))
        ((Scheme.stacksNormalization _ hW ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L))))).fiberι b y)
```

applied to the hypotheses of the statement.

1. **The Nagata hypothesis.** The copy's class `StacksIsNagataRing A` has the fields
   `isNoetherianRing : IsNoetherianRing A` and
   `isJapaneseRing_quotient (p : Ideal A) [p.IsPrime] : IsJapaneseRing (A ⧸ p)`, and the class
   `IsJapaneseRing (A ⧸ p)` has the single field `finite`, whose type is the finiteness clause
   of the statement for `A ⧸ p`, with the same binders in the same order. The instance is built by
   anonymous constructors from the two components of the statement's conjunction.
2. **The conclusion.** The copy's conclusion is the statement's conclusion up to unfolding, and
   the proof passes the witnesses `L`, its structures, the finiteness witness `hW` and the
   pointwise smoothness on unchanged. The base change `Spec.algebraMap A (integralClosure A L)` is
   Mathlib's abbreviation for `Spec.map (CommRingCat.ofHom (algebraMap A _))`. The copy's
   `Scheme.stacksNormalization W hW` is
   `(Scheme.fromGenericPointResidueFields W).fromNormalization`, Mathlib's relative
   normalization of `Sigma.desc fun η : genericPoints W ↦ W.fromSpecResidueField η.1` out of
   `∐ fun η ↦ Spec (.of (W.residueField η.1))`; the Library's `schemeNormalizationHom W hW` is
   `(genericPointResidueMorphism W).fromNormalization` for the same `Sigma.desc` out of
   `∐ fun x ↦ Spec (W.residueField x.1)`. The two families agree definitionally
   (`CommRingCat.of` of the carrier of a commutative ring object is that object, by structure
   eta), and the quasi-compactness and quasi-separatedness instances that the normalization takes
   are propositions. The copy's `InfinitesimalLifting.SmoothAt h x` is defined as
   `∃ U : X.Opens, x ∈ U ∧ Smooth (h.resLE ⊤ U le_top)`, which is the statement's last clause.
   Lean checks all of this by definitional unfolding; no transport is needed.

The theorem depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Declarations used

From the extract of the Stacks copy (`StacksFrontier/`, module system files):

- `AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_pullback`
  (`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreTheorem`), Tag 09IL;
- `StacksIsNagataRing`, `IsJapaneseRing` (`StacksFrontier.RingTheory.Nagata.Defs`), the copy's
  Nagata and Japanese (N-2) rings, Tags 032R and 032F;
- through the theorem's type: `AlgebraicGeometry.Scheme.stacksNormalization`,
  `AlgebraicGeometry.Scheme.normalizationScheme`
  (`StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme`),
  `AlgebraicGeometry.Scheme.fromGenericPointResidueFields`,
  `AlgebraicGeometry.Scheme.genericPointResidueSpectrum`
  (`StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.GenericPoints`), Tags 035M and
  035N, and `InfinitesimalLifting.SmoothAt` (`StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting`).

From the Library: `SchemeReducedFibreStatement`, `schemeNormalization`, `schemeNormalizationHom`
and `genericPointResidueMorphism` (`Langlands.AlgebraicGeometry.DvrAffineReducedFibre.SchemeReducedFibreStatement`).

The module imports the statement module and the two modules of the extract named above.

## Sources

- Stacks Project, Theorem 37.65.1, [Tag 09IL](https://stacks.math.columbia.edu/tag/09IL): the
  reduced fibre theorem over a Nagata Dedekind domain.
- [Tag 032R](https://stacks.math.columbia.edu/tag/032R) (Nagata rings) and
  [Tag 032F](https://stacks.math.columbia.edu/tag/032F) (N-1 and N-2 domains).
- [Tag 035M](https://stacks.math.columbia.edu/tag/035M) and
  [Tag 035N](https://stacks.math.columbia.edu/tag/035N): the normalization of a scheme as the
  normalization in the residue fields of its generic points.
- The proof of Tag 09IL in Lean is that of the Stacks copy (AxiomMath/Stacks, commit
  `c496df0d9beea9deaeabcea8492605f9a0a2313b`, Apache-2.0), file
  `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreTheorem.lean`, which reaches this
  module through the extract of that library kept in `StacksCore/` and `StacksFrontier/`. In the
  extract the copy's class `IsNagataRing` is named `StacksIsNagataRing` and its
  `Scheme.normalization` is named `Scheme.stacksNormalization`.
