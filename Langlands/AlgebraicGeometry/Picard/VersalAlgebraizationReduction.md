# Algebraization of formally versal Picard families from etale approximation

This module proves the conditional reduction

```text
versalAlgebraization_of_etaleApproximation :
  FiniteTypeIntEtaleCompletionApproximationStatement.{u} →
    VersalAlgebraizationStatement.{u}
```

in namespace `Langlands.AlgebraicGeometry.Picard`. This is Stacks Project Lemma
98.12.7 (Tag 07XH, `artin.pdf` printed pp. 20–21) for the Picard stack of a proper
flat scheme over a finite-type `ℤ`-algebra. The G-ring and approximation input of
Lemma 98.10.1 (Tag 07XB) is replaced by the étale approximation statement, which is
assumed. The hypothesis is not proved here. The reduction keeps every
finite-type `ℤ`-algebra `R`, every proper flat `X`, every field `K` of finite type
over `R`, every complete Noetherian local `A` with surjective `ε : A → K`, every
line bundle `L` and every point `p` of `VersalAlgebraizationStatement`, and the
universe `u`.

## Helper lemmas

In namespace `VersalAlgebraizationReduction`:

- `baseMap_eq_affineBaseMap` and `reduction_eq_affineBaseMap` identify the base map
  of a test arrow and the residue point of a test with affine-base arrows.
- `augmentation_comp_of_reduction`: a map `affineBaseMap ψ` from a test with residue
  map `affineBaseMap εT` has `A.augmentation ∘ ψ = εT`.
- `exists_pow_le_ker`: for every test `A` there is `N` such that every
  augmentation-compatible `ψ : T →ₐ[k] A` kills `(ker εT) ^ n` for all `n ≥ N`. The
  maximal ideal of a test is nilpotent.
- `affineBaseMap_comp_eq`: a composite of affine-base arrows is the affine-base
  arrow of the composite algebra map.

## Proof of the reduction

1. **Spreading.** `PicardGroupoid.exists_affineFamily_subalgebra` gives a finitely
   generated `R`-subalgebra `B ⊆ A`, a line bundle `LB` on `Spec B ×_R X` and an
   isomorphism `eB` from its pullback to `L`. `X → Spec R` is proper, hence
   quasi-compact and quasi-separated.
2. **Algebraic chart.** `CompleteLocalAlgebraicChart.exists_algebraicChart` applied
   to `ε` and the inclusion `B → A` gives `T`, `εT`, `βT` and `φ₂`. The chart is
   `U = affineBase R T`, and `L'` is the pullback of `LB` along `affineBaseMap βT`.
3. **Truncations.** The tests `Tt n = T / (ker εT) ^ (n + 2)` with their transitions
   and levels `c n` come from `AffineQuotientTests`. The point
   `p' = affineBaseMap εT` satisfies `reduction (Tt n) ≫ c n = p'`.
4. **Initial fibre point.** `a₀ = affineBaseMap φ₂ : base (Tt 0) ⟶ Spec A`. Property
   (1) of the chart gives `a₀ ≫ ι_B = c 0 ≫ aβ`. The bundle isomorphism `e₀` is
   `eB⁻¹` pulled back along `a₀`, followed by the composition comparisons
   `PseudofunctorPointFiberAtlasRestriction.atlasComparison` along this square. By
   property (2) of the chart, `reduction ≫ a₀ = p`.
5. **Lifting.** `exists_tower_points` lifts `⟨a₀, e₀⟩` to fibre points `xs n` over
   every level, compatible with `a₀`. Their chart maps are `affineBaseMap (φs n)`.
   The compatibility and `towerDown` show that `φs n` reduces to `φ₂` modulo
   `(ker εT) ^ 2`. Property (3) of the chart then makes every `φs n` surjective with
   kernel `m_A ^ (n + 2)`.
6. **Versality.** `isFormallyVersalAt_of_levels` applies. Each `(xs n).1` is a
   monomorphism because `φs n` is surjective. Each `c n` is a monomorphism, so the
   only pointed `K`-point of a level is its residue point. Pointed maps from a test
   into `U` kill `(ker εT) ^ (n + 2)` for large `n`, so they factor through `c n`.
   Pointed maps from a test into `Spec A` kill `m_A ^ (n + 2) = ker (φs n)` for large
   `n`, so they factor through `(xs n).1` by `Ideal.quotientKerAlgEquivOfSurjective`.
7. **Packaging.** `exists_residueField_iso` gives `u₀` and `e : κ(u₀) ≅ K` with
   `p'.left = Spec.map e.hom ≫ fromSpecResidueField u₀`. `U → Spec R` is locally of
   finite type because `T` is of finite type over `R`
   (`HasRingHomProperty.Spec_iff`, `RingHom.finiteType_algebraMap`). The isomorphism
   of residue bundles is `e₀` pulled back along `reduction (Tt 0)`
   (`PseudofunctorPointFiber.pullIso`). Its two composites are `p` and `p'`.

`versalAlgebraizationOfEtaleApproximation` is the same implication as a definition
of type
`FiniteTypeIntEtaleCompletionApproximationStatement.{u} → VersalAlgebraizationStatement.{u}`.
Its body is the theorem `versalAlgebraization_of_etaleApproximation`.
