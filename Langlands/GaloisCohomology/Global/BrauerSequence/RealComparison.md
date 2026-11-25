# Local invariants of inflated Brauer classes at the infinite places

`Langlands/GaloisCohomology/Global/BrauerSequence/RealComparison.lean`, namespace
`Langlands.GaloisCohomology`.

**Groups of order two.** For a discrete group `G` and a smooth module `A`:
`cochainOf_one_left`, `cochainOf_one_right` give the normalized values `z(1, g)`, `z(g, 1)` of a
`2`-cocycle; `fixed_cochainOf_add`: for an involution `c`, `z(c, c) + z(1, 1)` is fixed by `c`;
`cohomologyπ_two_eq_zero_iff_of_orderTwo`: when `G = {1, c}` with `c ≠ 1`, the class of `z` is zero
exactly when `z(c, c) + z(1, 1)` is a norm `m + c·m`; `cohomologyπ_two_eq_zero_of_forall_eq_one`:
for the trivial group every `2`-cocycle is a coboundary.

**The closure of a completion at an infinite place.** For an infinite place `w`,
`closureToComplex w : K̄_w → ℂ` extends `extensionEmbedding` (`closureToComplex_algebraMap`), is onto
(`closureToComplex_surjective`) and hence a ring isomorphism `closureEquivComplex`; every
automorphism of `K̄_w` over `K_w` is the identity or, at a real place, the conjugation `closureConj`
(`eq_one_or_eq_closureConj`, `closureConj_ne_one`, `eq_one_of_isComplex`); the Galois group is finite
and discrete. `exists_mul_closureConj_iff`: at a real place, a unit fixed by the conjugation is a
norm `m · c(m)` exactly when its image in `ℂ` has positive real part.

**Real invariants.** `subsingleton_realBrauerGroup_of_isComplex`: at a complex place the local Brauer
group is zero. `realInvariant_cohomologyπ`: at a real place the invariant of the class of a cocycle
`z` is the Library's `signClass` of the image in `ℂ` of `z(c, c) · z(1, 1)`.

**Comparison with the Library.** For a finite Galois `E ⊆ Ω`, `realPlace ι E w` is the place of `E`
given by `ι.infinite w` (`realComplexEmbedding`), and `realLocalInvariant_unitsInflation`: the real
invariant at `w` of a class inflated from `a ∈ H²(Gal(E/K), Eˣ)` is the Library's
`Reciprocity.archimedeanInvariant (realPlace ι E w) a`.

## Complete types

```lean
@Langlands.GaloisCohomology.cochainOf_one_left : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] (A : Rep.{u_1, u_1, u_1} k G)
  [inst_4 : Langlands.IsSmoothRep A] (z : ↑(Langlands.ProfiniteCohomology.cocycles A 2)) (g : G),
  Langlands.ProfiniteCohomology.cochainOf A ((Langlands.ProfiniteCohomology.cocycleι A 2) z) ![1, g] =
    Langlands.ProfiniteCohomology.cochainOf A ((Langlands.ProfiniteCohomology.cocycleι A 2) z) ![1, 1]

@Langlands.GaloisCohomology.cochainOf_one_right : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] (A : Rep.{u_1, u_1, u_1} k G)
  [inst_4 : Langlands.IsSmoothRep A] (z : ↑(Langlands.ProfiniteCohomology.cocycles A 2)) (g : G),
  Langlands.ProfiniteCohomology.cochainOf A ((Langlands.ProfiniteCohomology.cocycleι A 2) z) ![g, 1] =
    (A.ρ g) (Langlands.ProfiniteCohomology.cochainOf A ((Langlands.ProfiniteCohomology.cocycleι A 2) z) ![1, 1])

@Langlands.GaloisCohomology.fixed_cochainOf_add : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] (A : Rep.{u_1, u_1, u_1} k G)
  [inst_4 : Langlands.IsSmoothRep A] {c : G},
  c * c = 1 →
    ∀ (z : ↑(Langlands.ProfiniteCohomology.cocycles A 2)),
      (A.ρ c)
          (Langlands.ProfiniteCohomology.cochainOf A ((Langlands.ProfiniteCohomology.cocycleι A 2) z) ![c, c] +
            Langlands.ProfiniteCohomology.cochainOf A ((Langlands.ProfiniteCohomology.cocycleι A 2) z) ![1, 1]) =
        Langlands.ProfiniteCohomology.cochainOf A ((Langlands.ProfiniteCohomology.cocycleι A 2) z) ![c, c] +
          Langlands.ProfiniteCohomology.cochainOf A ((Langlands.ProfiniteCohomology.cocycleι A 2) z) ![1, 1]

@Langlands.GaloisCohomology.cohomologyπ_two_eq_zero_iff_of_orderTwo : ∀ {k G : Type u_1} [inst : CommRing k]
  [inst_1 : Group G] [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] [DiscreteTopology G]
  (A : Rep.{u_1, u_1, u_1} k G) [inst_5 : Langlands.IsSmoothRep A] {c : G},
  (∀ (g : G), g = 1 ∨ g = c) →
    c ≠ 1 →
      ∀ (z : ↑(Langlands.ProfiniteCohomology.cocycles A 2)),
        (CategoryTheory.ConcreteCategory.hom (Langlands.ProfiniteCohomology.cohomologyπ A 2)) z = 0 ↔
          ∃ (m : ↑A),
            Langlands.ProfiniteCohomology.cochainOf A ((Langlands.ProfiniteCohomology.cocycleι A 2) z) ![c, c] +
                Langlands.ProfiniteCohomology.cochainOf A ((Langlands.ProfiniteCohomology.cocycleι A 2) z) ![1, 1] =
              m + (A.ρ c) m

@Langlands.GaloisCohomology.cohomologyπ_two_eq_zero_of_forall_eq_one : ∀ {k G : Type u_1} [inst : CommRing k]
  [inst_1 : Group G] [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] [DiscreteTopology G]
  (A : Rep.{u_1, u_1, u_1} k G) [inst_5 : Langlands.IsSmoothRep A],
  (∀ (g : G), g = 1) →
    ∀ (z : ↑(Langlands.ProfiniteCohomology.cocycles A 2)),
      (CategoryTheory.ConcreteCategory.hom (Langlands.ProfiniteCohomology.cohomologyπ A 2)) z = 0

@Langlands.GaloisCohomology.complexAlgebra : {K : Type u_1} →
  [inst : Field K] → (w : NumberField.InfinitePlace K) → Algebra w.Completion ℂ

@Langlands.GaloisCohomology.closureToComplex : {K : Type u_1} →
  [inst : Field K] → (w : NumberField.InfinitePlace K) → AlgebraicClosure w.Completion →+* ℂ

@Langlands.GaloisCohomology.closureToComplex_algebraMap : ∀ {K : Type u_1} [inst : Field K]
  (w : NumberField.InfinitePlace K) (x : w.Completion),
  (Langlands.GaloisCohomology.closureToComplex w) ((algebraMap w.Completion (AlgebraicClosure w.Completion)) x) =
    (NumberField.InfinitePlace.Completion.extensionEmbedding w) x

@Langlands.GaloisCohomology.extensionEmbedding_im_eq_zero : ∀ {K : Type u_1} [inst : Field K]
  {w : NumberField.InfinitePlace K},
  w.IsReal → ∀ (x : w.Completion), ((NumberField.InfinitePlace.Completion.extensionEmbedding w) x).im = 0

@Langlands.GaloisCohomology.closureToComplex_surjective : ∀ {K : Type u_1} [inst : Field K] [NumberField K]
  (w : NumberField.InfinitePlace K), Function.Surjective ⇑(Langlands.GaloisCohomology.closureToComplex w)

@Langlands.GaloisCohomology.closureEquivComplex : {K : Type u_1} →
  [inst : Field K] → [NumberField K] → (w : NumberField.InfinitePlace K) → AlgebraicClosure w.Completion ≃+* ℂ

@Langlands.GaloisCohomology.closureEquivComplex_apply : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (w : NumberField.InfinitePlace K) (x : AlgebraicClosure w.Completion),
  (Langlands.GaloisCohomology.closureEquivComplex w) x = (Langlands.GaloisCohomology.closureToComplex w) x

@Langlands.GaloisCohomology.closureToComplex_comp_eq : ∀ {K : Type u_1} [inst : Field K] [NumberField K]
  (w : NumberField.InfinitePlace K) (σ : Gal(AlgebraicClosure w.Completion/w.Completion)),
  (∀ (x : AlgebraicClosure w.Completion),
      (Langlands.GaloisCohomology.closureToComplex w) (σ x) = (Langlands.GaloisCohomology.closureToComplex w) x) ∨
    w.IsReal ∧
      ∀ (x : AlgebraicClosure w.Completion),
        (Langlands.GaloisCohomology.closureToComplex w) (σ x) =
          (starRingEnd ℂ) ((Langlands.GaloisCohomology.closureToComplex w) x)

@Langlands.GaloisCohomology.closureConj : {K : Type u_1} →
  [inst : Field K] →
    [NumberField K] → (w : NumberField.InfinitePlace K) → w.IsReal → Gal(AlgebraicClosure w.Completion/w.Completion)

@Langlands.GaloisCohomology.closureToComplex_closureConj : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (w : NumberField.InfinitePlace K) (hw : w.IsReal) (x : AlgebraicClosure w.Completion),
  (Langlands.GaloisCohomology.closureToComplex w) ((Langlands.GaloisCohomology.closureConj w hw) x) =
    (starRingEnd ℂ) ((Langlands.GaloisCohomology.closureToComplex w) x)

@Langlands.GaloisCohomology.closureConj_ne_one : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (w : NumberField.InfinitePlace K) (hw : w.IsReal), Langlands.GaloisCohomology.closureConj w hw ≠ 1

@Langlands.GaloisCohomology.eq_one_or_eq_closureConj : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (w : NumberField.InfinitePlace K) (hw : w.IsReal) (σ : Gal(AlgebraicClosure w.Completion/w.Completion)),
  σ = 1 ∨ σ = Langlands.GaloisCohomology.closureConj w hw

@Langlands.GaloisCohomology.eq_one_of_isComplex : ∀ {K : Type u_1} [inst : Field K] [NumberField K]
  (w : NumberField.InfinitePlace K), w.IsComplex → ∀ (σ : Gal(AlgebraicClosure w.Completion/w.Completion)), σ = 1

@Langlands.GaloisCohomology.finite_closureGalois : ∀ {K : Type u_1} [inst : Field K] [NumberField K]
  (w : NumberField.InfinitePlace K), Finite Gal(AlgebraicClosure w.Completion/w.Completion)

@Langlands.GaloisCohomology.discreteTopology_closureGalois : ∀ {K : Type u_1} [inst : Field K] [NumberField K]
  (w : NumberField.InfinitePlace K), DiscreteTopology Gal(AlgebraicClosure w.Completion/w.Completion)

@Langlands.GaloisCohomology.exists_mul_closureConj_iff : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (w : NumberField.InfinitePlace K) (hw : w.IsReal) (x : (AlgebraicClosure w.Completion)ˣ),
  (Langlands.GaloisCohomology.closureConj w hw) ↑x = ↑x →
    ((∃ (m : (AlgebraicClosure w.Completion)ˣ), ↑x = ↑m * (Langlands.GaloisCohomology.closureConj w hw) ↑m) ↔
      0 < ((Langlands.GaloisCohomology.closureToComplex w) ↑x).re)

@Langlands.GaloisCohomology.subsingleton_realBrauerGroup_of_isComplex : ∀ {K : Type u_1} [inst : Field K]
  [NumberField K] (w : NumberField.InfinitePlace K),
  w.IsComplex → Subsingleton (Langlands.GaloisCohomology.RealBrauerGroup w)

@Langlands.GaloisCohomology.realInvariant_cohomologyπ : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (w : NumberField.InfinitePlace K) (hw : w.IsReal)
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)) 2)),
  Langlands.GaloisCohomology.realInvariant w
      ((CategoryTheory.ConcreteCategory.hom
          (Langlands.ProfiniteCohomology.cohomologyπ
            (Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)) 2))
        z) =
    Langlands.ClassFieldTheory.Global.Reciprocity.signClass
      ((Langlands.GaloisCohomology.closureToComplex w)
        ↑(Additive.toMul
            (Langlands.ProfiniteCohomology.cochainOf
                (Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion))
                ((Langlands.ProfiniteCohomology.cocycleι
                    (Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)) 2)
                  z)
                ![Langlands.GaloisCohomology.closureConj w hw, Langlands.GaloisCohomology.closureConj w hw] +
              Langlands.ProfiniteCohomology.cochainOf
                (Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion))
                ((Langlands.ProfiniteCohomology.cocycleι
                    (Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)) 2)
                  z)
                ![1, 1])))

@Langlands.GaloisCohomology.realPlaceEmbedding : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          Langlands.Galois.PlaceEmbeddings K Ω →
            (E : IntermediateField K Ω) → (w : NumberField.InfinitePlace K) → ↥E →ₐ[K] AlgebraicClosure w.Completion

@Langlands.GaloisCohomology.realComplexEmbedding : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          Langlands.Galois.PlaceEmbeddings K Ω → (E : IntermediateField K Ω) → NumberField.InfinitePlace K → ↥E →+* ℂ

@Langlands.GaloisCohomology.realPlace : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          Langlands.Galois.PlaceEmbeddings K Ω →
            (E : IntermediateField K Ω) → NumberField.InfinitePlace K → NumberField.InfinitePlace ↥E

@Langlands.GaloisCohomology.realPlaceEmbedding_restrictNormal : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω) [inst_5 : IsGalois K ↥E]
  (w : NumberField.InfinitePlace K) (σ : Gal(AlgebraicClosure w.Completion/w.Completion)) (x : ↥E),
  (Langlands.GaloisCohomology.realPlaceEmbedding ι E w)
      (((AlgEquiv.restrictNormalHom ↥E) ((Langlands.Galois.decompositionHom w.Completion (ι.infinite w)) σ)) x) =
    σ ((Langlands.GaloisCohomology.realPlaceEmbedding ι E w) x)

@Langlands.GaloisCohomology.realRestrict : {K Ω : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : Field Ω] →
        [inst_3 : Algebra K Ω] →
          [IsSepClosure K Ω] →
            Langlands.Galois.PlaceEmbeddings K Ω →
              (E : IntermediateField K Ω) →
                [IsGalois K ↥E] →
                  (w : NumberField.InfinitePlace K) → Gal(AlgebraicClosure w.Completion/w.Completion) → Gal(↥E/K)

@Langlands.GaloisCohomology.realComplexEmbedding_realRestrict : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω) [inst_5 : IsGalois K ↥E]
  (w : NumberField.InfinitePlace K) (σ : Gal(AlgebraicClosure w.Completion/w.Completion)) (x : ↥E),
  (Langlands.GaloisCohomology.realComplexEmbedding ι E w) ((Langlands.GaloisCohomology.realRestrict ι E w σ) x) =
    (Langlands.GaloisCohomology.closureToComplex w) (σ ((Langlands.GaloisCohomology.realPlaceEmbedding ι E w) x))

@Langlands.GaloisCohomology.realComplexEmbedding_realRestrict_closureConj : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω) [inst_5 : IsGalois K ↥E]
  (w : NumberField.InfinitePlace K) (hw : w.IsReal) (x : ↥E),
  (Langlands.GaloisCohomology.realComplexEmbedding ι E w)
      ((Langlands.GaloisCohomology.realRestrict ι E w (Langlands.GaloisCohomology.closureConj w hw)) x) =
    (starRingEnd ℂ) ((Langlands.GaloisCohomology.realComplexEmbedding ι E w) x)

@Langlands.GaloisCohomology.realComplexEmbedding_comp_algebraMap : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (E : IntermediateField K Ω) (w : NumberField.InfinitePlace K),
  (Langlands.GaloisCohomology.realComplexEmbedding ι E w).comp (algebraMap K ↥E) = w.embedding

@Langlands.GaloisCohomology.realRestrict_one : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (E : IntermediateField K Ω) [inst_5 : IsGalois K ↥E] (w : NumberField.InfinitePlace K),
  Langlands.GaloisCohomology.realRestrict ι E w 1 = 1

@Langlands.GaloisCohomology.realLocalInvariant_unitsInflation : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (E : IntermediateField K Ω) [inst_5 : FiniteDimensional K ↥E]
  [inst_6 : IsGalois K ↥E] (w : NumberField.InfinitePlace K)
  (a : ↑(Langlands.ClassFieldTheory.Local.relativeCohomology K (↥E) 2)),
  Langlands.GaloisCohomology.realLocalInvariant ι w
      ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.unitsInflation E 2)) a) =
    (Langlands.ClassFieldTheory.Global.Reciprocity.archimedeanInvariant (Langlands.GaloisCohomology.realPlace ι E w)) a
```

## Outline of the proofs

The order-two criterion is the computation of `Ĥ⁰ = A^G/N_G A` for a cyclic group of order two,
done on cochains (`OrderTwo.cohomologyπ_two_eq_zero_iff` of
`Langlands.GaloisCohomology.CompactSupport.TateModified.OrderTwo`). `closureToComplex` is
`IsAlgClosed.lift`; it is onto because its image is an algebraically closed field containing `ℝ`
(real place) or equal to `ℂ` (complex place, `bijective_extensionEmbedding_of_isComplex`). Every
automorphism becomes, in `ℂ`, a continuous automorphism over `ℝ` or `ℂ`, hence the identity or the
conjugation (`Complex.real_algHom_eq_id_or_conj`). `realInvariant_cohomologyπ` combines the
criterion with `exists_mul_closureConj_iff` (positive reals are norms `|m|²`).
`realLocalInvariant_unitsInflation`: the localization of the inflated class is the class of
`(σ, τ) ↦ a(σ|_E, τ|_E)` restricted to `Gal(K̄_w/K_w)`; its value at `(c, c)` and `(1, 1)` is
`a(c', c') a(1, 1)` for the conjugation `c'` of `realPlace ι E w` (or `1`), so the sign classes agree
with the Library's `archimedeanCocycleHom` (`archimedeanCocycleHom_apply_of_mem`,
`archimedeanCocycleHom_apply_of_not_exists`, `signClass_conjugate`).

## Declarations

`cochainOf_one_left`, `cochainOf_one_right`, `fixed_cochainOf_add`,
`cohomologyπ_two_eq_zero_iff_of_orderTwo`, `cohomologyπ_two_eq_zero_of_forall_eq_one`,
`complexAlgebra`, `closureToComplex`, `closureToComplex_algebraMap`, `extensionEmbedding_im_eq_zero`,
`closureToComplex_surjective`, `closureEquivComplex`, `closureEquivComplex_apply`,
`closureToComplex_comp_eq`, `closureConj`, `closureToComplex_closureConj`, `closureConj_ne_one`,
`eq_one_or_eq_closureConj`, `eq_one_of_isComplex`, `finite_closureGalois`,
`discreteTopology_closureGalois`, `exists_mul_closureConj_iff`,
`subsingleton_realBrauerGroup_of_isComplex`, `realInvariant_cohomologyπ`, `realPlaceEmbedding`,
`realComplexEmbedding`, `realPlace`, `realPlaceEmbedding_restrictNormal`, `realRestrict`,
`realComplexEmbedding_realRestrict`, `realComplexEmbedding_realRestrict_closureConj`,
`realComplexEmbedding_comp_algebraMap`, `realRestrict_one`, `realLocalInvariant_unitsInflation`.

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013): Proposition (1.7.1), p. 74 (`Ĥ^{2n}(G, A) ≅ A^G/N_G A` for a cyclic
  group `G`).
