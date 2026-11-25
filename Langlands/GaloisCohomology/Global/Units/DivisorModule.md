# Divisor modules of a family of homomorphisms

`Langlands/GaloisCohomology/Global/Units/DivisorModule.lean`, namespace `Langlands.GaloisCohomology`.

Let `G` be a topological group and `φ_i : H_i →ₜ* G` (`i ∈ I`) a family of continuous homomorphisms,
`A` an abelian group. `divisorFunctions φ A` is the group of functions `f : I → G → A` with finite
support in `i`, each `f i` locally constant and invariant under left translation by the image of
`φ i`; `G` acts by right translation, and for compact `G` this is a smooth `G`-module
`divisorModule φ A` (`isSmoothRep_divisorModule`). Evaluation at `(i, 1)` is a morphism
`divisorEval φ A i : Res_{φ i}(divisorModule φ A) ⟶ A` (trivial action, `trivialModule`).

For `G = G_S`, `H_v = Gal(K̄_v/K_v)` and `φ_v` the localization at the places `v ∉ S`, the module
`divisorModule φ ℤ` is the module of divisors prime to `S` of `K_S`: a divisor is determined by its
multiplicities at the places `g⁻¹ w_v`, `g ∈ G_S`, above each `v`
(`Langlands.GaloisCohomology.Global.Units.DivisorMap`).

Results (for compact totally disconnected `G` and `H_i`):

- `divisorSequence_shortExact`: `0 → D(ℤ) → D(ℚ) → D(ℚ/ℤ) → 0` is exact;
- `isZero_cohomology_divisorModule_rat`: `Hⁿ(G, D(ℚ)) = 0` for `n ≥ 1` (multiplication by `n ≠ 0` is
  bijective; `isZero_cohomology_of_bijective_nsmul` of
  `Langlands.Cohomology.Profinite.Characters`);
- `isZero_cohomology_one_divisorModule_int`: `H¹(G, D(ℤ)) = 0` (the `G`-invariants of `D(ℚ)` map onto
  those of `D(ℚ/ℤ)`);
- `eq_zero_of_divisorEval_eq_zero`: a class of `H²(G, D(ℤ))` whose images in all `H²(H_i, ℤ)` vanish is
  zero; `finite_divisorEval_ne_zero`: only finitely many of these images are nonzero (both through
  `H²(G, D(ℤ)) ≅ H¹(G, D(ℚ/ℤ))` and `H²(H_i, ℤ) ≅ H¹(H_i, ℚ/ℤ)`, by the connecting maps of
  `divisorSequence` and `trivialSequence`, compatible through `divisorEvalSequence`);
- `exists_coprime_nsmul_cohomology_eq_zero`, `eq_zero_of_pow_nsmul_eq_zero_of_coprime`: if every element
  of a smooth module of a compact group is killed by an integer prime to `ℓ`, so is every cohomology
  class, and a class killed by a power of `ℓ` is zero.

The first three are the module-theoretic part of the computation of `H^*(G_S, D)` (Shapiro's lemma
for the induced modules `D(ℚ/ℤ) = ⊕'_v Ind_{H_v}^{G} ℚ/ℤ` is not needed in degrees `≤ 2`).

## Complete types

As printed by `#check` with `pp.fullNames`:

```lean
Langlands.GaloisCohomology.trivialModule : (G : Type u_1) →
  [inst : Group G] → (A : Type u_1) → [AddCommGroup A] → Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G
Langlands.GaloisCohomology.trivialModule_ρ_apply : ∀ (G : Type u_1) [inst : Group G] (A : Type u_1)
  [inst_1 : AddCommGroup A] (g : G) (a : A), ((Langlands.GaloisCohomology.trivialModule G A).ρ g) a = a
Langlands.GaloisCohomology.isTrivial_trivialModule : ∀ (G : Type u_1) [inst : Group G] (A : Type u_1)
  [inst_1 : AddCommGroup A], (Langlands.GaloisCohomology.trivialModule G A).ρ.IsTrivial
Langlands.GaloisCohomology.isSmoothRep_trivialModule : ∀ (G : Type u_1) [inst : Group G] (A : Type u_1)
  [inst_1 : AddCommGroup A] [inst_2 : TopologicalSpace G],
  Langlands.IsSmoothRep (Langlands.GaloisCohomology.trivialModule G A)
Langlands.GaloisCohomology.trivialMap : (G : Type u_1) →
  [inst : Group G] →
    {A B : Type u_1} →
      [inst_1 : AddCommGroup A] →
        [inst_2 : AddCommGroup B] →
          (A →+ B) → (Langlands.GaloisCohomology.trivialModule G A ⟶ Langlands.GaloisCohomology.trivialModule G B)
Langlands.GaloisCohomology.ratToQZ : ℚ →+ Langlands.ProfiniteCohomology.QZ
Langlands.GaloisCohomology.ratToQZ_eq_zero_iff : ∀ (q : ℚ), Langlands.GaloisCohomology.ratToQZ q = 0 ↔ ∃ (n : ℤ), ↑n = q
Langlands.GaloisCohomology.ratToQZ_surjective : Function.Surjective ⇑Langlands.GaloisCohomology.ratToQZ
Langlands.GaloisCohomology.uliftIntToRat : ULift.{u_1, 0} ℤ →+ ULift.{u_1, 0} ℚ
Langlands.GaloisCohomology.uliftRatToQZ : ULift.{u_1, 0} ℚ →+ ULift.{u_1, 0} Langlands.ProfiniteCohomology.QZ
Langlands.GaloisCohomology.uliftIntToRat_apply : ∀ (n : ULift.{u_1, 0} ℤ),
  Langlands.GaloisCohomology.uliftIntToRat n = { down := ↑n.down }
Langlands.GaloisCohomology.uliftRatToQZ_apply : ∀ (q : ULift.{u_1, 0} ℚ),
  Langlands.GaloisCohomology.uliftRatToQZ q = { down := Langlands.GaloisCohomology.ratToQZ q.down }
@Langlands.GaloisCohomology.bijective_nsmul_uliftRat : ∀ {n : ℕ},
  n ≠ 0 → Function.Bijective fun (q : ULift.{u_1, 0} ℚ) => n • q
@Langlands.GaloisCohomology.exists_coprime_nsmul_cohomology_eq_zero : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [CompactSpace G] {k : Type u_1} [inst_4 : CommRing k]
  (M : Rep.{u_1, u_1, u_1} k G) [inst_5 : Langlands.IsSmoothRep M] (ℓ : ℕ),
  (∀ (m : ↑M), ∃ (N : ℕ), N.Coprime ℓ ∧ N • m = 0) →
    ∀ (n : ℕ) (x : ↑(Langlands.ProfiniteCohomology.cohomology M n)), ∃ (N : ℕ), N.Coprime ℓ ∧ N • x = 0
@Langlands.GaloisCohomology.eq_zero_of_pow_nsmul_eq_zero_of_coprime : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [CompactSpace G] {k : Type u_1} [inst_4 : CommRing k]
  (M : Rep.{u_1, u_1, u_1} k G) [inst_5 : Langlands.IsSmoothRep M] (ℓ : ℕ),
  (∀ (m : ↑M), ∃ (N : ℕ), N.Coprime ℓ ∧ N • m = 0) →
    ∀ (n : ℕ) (x : ↑(Langlands.ProfiniteCohomology.cohomology M n)) (j : ℕ), ℓ ^ j • x = 0 → x = 0
@Langlands.GaloisCohomology.divisorFunctions : {G : Type u_1} →
  [inst : Group G] →
    [inst_1 : TopologicalSpace G] →
      {I : Type u_1} →
        {H : I → Type u_1} →
          [inst_2 : (i : I) → Group (H i)] →
            [inst_3 : (i : I) → TopologicalSpace (H i)] →
              ((i : I) → H i →ₜ* G) → (A : Type u_1) → [inst : AddCommGroup A] → AddSubgroup (I → G → A)
@Langlands.GaloisCohomology.mem_divisorFunctions : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  {I : Type u_1} {H : I → Type u_1} [inst_2 : (i : I) → Group (H i)] [inst_3 : (i : I) → TopologicalSpace (H i)]
  (φ : (i : I) → H i →ₜ* G) (A : Type u_1) [inst_4 : AddCommGroup A] {f : I → G → A},
  f ∈ Langlands.GaloisCohomology.divisorFunctions φ A ↔
    {i : I | f i ≠ 0}.Finite ∧ ∀ (i : I), IsLocallyConstant (f i) ∧ ∀ (h : H i) (x : G), f i ((φ i) h * x) = f i x
@Langlands.GaloisCohomology.divisorAction : {G : Type u_1} →
  [inst : Group G] →
    [inst_1 : TopologicalSpace G] →
      {I : Type u_1} →
        {H : I → Type u_1} →
          [inst_2 : (i : I) → Group (H i)] →
            [inst_3 : (i : I) → TopologicalSpace (H i)] →
              (φ : (i : I) → H i →ₜ* G) →
                (A : Type u_1) →
                  [inst_4 : AddCommGroup A] →
                    [IsTopologicalGroup G] → G →* AddMonoid.End ↥(Langlands.GaloisCohomology.divisorFunctions φ A)
@Langlands.GaloisCohomology.coe_divisorAction_apply : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  {I : Type u_1} {H : I → Type u_1} [inst_2 : (i : I) → Group (H i)] [inst_3 : (i : I) → TopologicalSpace (H i)]
  (φ : (i : I) → H i →ₜ* G) (A : Type u_1) [inst_4 : AddCommGroup A] [inst_5 : IsTopologicalGroup G] (g : G)
  (f : ↥(Langlands.GaloisCohomology.divisorFunctions φ A)) (i : I) (x : G),
  ↑(((Langlands.GaloisCohomology.divisorAction φ A) g) f) i x = ↑f i (x * g)
@Langlands.GaloisCohomology.exists_mem_nhds_one_forall_mul_eq : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {X : Type u_2} {f : G → X},
  IsLocallyConstant f → ∃ V ∈ nhds 1, ∀ (x v : G), v ∈ V → f (x * v) = f x
@Langlands.GaloisCohomology.divisorModule : {G : Type u_1} →
  [inst : Group G] →
    [inst_1 : TopologicalSpace G] →
      {I : Type u_1} →
        {H : I → Type u_1} →
          [inst_2 : (i : I) → Group (H i)] →
            [inst_3 : (i : I) → TopologicalSpace (H i)] →
              ((i : I) → H i →ₜ* G) →
                (A : Type u_1) → [AddCommGroup A] → [IsTopologicalGroup G] → Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G
@Langlands.GaloisCohomology.isSmoothRep_divisorModule : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  {I : Type u_1} {H : I → Type u_1} [inst_2 : (i : I) → Group (H i)] [inst_3 : (i : I) → TopologicalSpace (H i)]
  (φ : (i : I) → H i →ₜ* G) (A : Type u_1) [inst_4 : AddCommGroup A] [inst_5 : IsTopologicalGroup G] [CompactSpace G],
  Langlands.IsSmoothRep (Langlands.GaloisCohomology.divisorModule φ A)
@Langlands.GaloisCohomology.divisorEval : {G : Type u_1} →
  [inst : Group G] →
    [inst_1 : TopologicalSpace G] →
      {I : Type u_1} →
        {H : I → Type u_1} →
          [inst_2 : (i : I) → Group (H i)] →
            [inst_3 : (i : I) → TopologicalSpace (H i)] →
              (φ : (i : I) → H i →ₜ* G) →
                (A : Type u_1) →
                  [inst_4 : AddCommGroup A] →
                    [inst_5 : IsTopologicalGroup G] →
                      (i : I) →
                        Rep.res (↑(φ i)) (Langlands.GaloisCohomology.divisorModule φ A) ⟶
                          Langlands.GaloisCohomology.trivialModule (H i) A
@Langlands.GaloisCohomology.divisorEval_hom_apply : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  {I : Type u_1} {H : I → Type u_1} [inst_2 : (i : I) → Group (H i)] [inst_3 : (i : I) → TopologicalSpace (H i)]
  (φ : (i : I) → H i →ₜ* G) (A : Type u_1) [inst_4 : AddCommGroup A] [inst_5 : IsTopologicalGroup G] (i : I)
  (f : ↥(Langlands.GaloisCohomology.divisorFunctions φ A)),
  (Rep.Hom.hom (Langlands.GaloisCohomology.divisorEval φ A i)) f = ↑f i 1
@Langlands.GaloisCohomology.divisorMap : {G : Type u_1} →
  [inst : Group G] →
    [inst_1 : TopologicalSpace G] →
      {I : Type u_1} →
        {H : I → Type u_1} →
          [inst_2 : (i : I) → Group (H i)] →
            [inst_3 : (i : I) → TopologicalSpace (H i)] →
              (φ : (i : I) → H i →ₜ* G) →
                (A : Type u_1) →
                  [inst_4 : AddCommGroup A] →
                    [inst_5 : IsTopologicalGroup G] →
                      {B : Type u_1} →
                        [inst_6 : AddCommGroup B] →
                          (A →+ B) →
                            (Langlands.GaloisCohomology.divisorModule φ A ⟶
                              Langlands.GaloisCohomology.divisorModule φ B)
@Langlands.GaloisCohomology.coe_divisorMap_hom_apply : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  {I : Type u_1} {H : I → Type u_1} [inst_2 : (i : I) → Group (H i)] [inst_3 : (i : I) → TopologicalSpace (H i)]
  (φ : (i : I) → H i →ₜ* G) (A : Type u_1) [inst_4 : AddCommGroup A] [inst_5 : IsTopologicalGroup G] {B : Type u_1}
  [inst_6 : AddCommGroup B] (g : A →+ B) (f : ↥(Langlands.GaloisCohomology.divisorFunctions φ A)),
  ↑((Rep.Hom.hom (Langlands.GaloisCohomology.divisorMap φ A g)) f) = fun (i : I) (x : G) => g (↑f i x)
@Langlands.GaloisCohomology.divisorSequence : {G : Type u_1} →
  [inst : Group G] →
    [inst_1 : TopologicalSpace G] →
      {I : Type u_1} →
        {H : I → Type u_1} →
          [inst_2 : (i : I) → Group (H i)] →
            [inst_3 : (i : I) → TopologicalSpace (H i)] →
              ((i : I) → H i →ₜ* G) →
                [IsTopologicalGroup G] → CategoryTheory.ShortComplex (Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G)
@Langlands.GaloisCohomology.isSmoothRep_divisorSequence_X₁ : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] {I : Type u_1} {H : I → Type u_1} [inst_2 : (i : I) → Group (H i)]
  [inst_3 : (i : I) → TopologicalSpace (H i)] (φ : (i : I) → H i →ₜ* G) [inst_4 : IsTopologicalGroup G]
  [CompactSpace G], Langlands.IsSmoothRep (Langlands.GaloisCohomology.divisorSequence φ).X₁
@Langlands.GaloisCohomology.isSmoothRep_divisorSequence_X₂ : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] {I : Type u_1} {H : I → Type u_1} [inst_2 : (i : I) → Group (H i)]
  [inst_3 : (i : I) → TopologicalSpace (H i)] (φ : (i : I) → H i →ₜ* G) [inst_4 : IsTopologicalGroup G]
  [CompactSpace G], Langlands.IsSmoothRep (Langlands.GaloisCohomology.divisorSequence φ).X₂
@Langlands.GaloisCohomology.isSmoothRep_divisorSequence_X₃ : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] {I : Type u_1} {H : I → Type u_1} [inst_2 : (i : I) → Group (H i)]
  [inst_3 : (i : I) → TopologicalSpace (H i)] (φ : (i : I) → H i →ₜ* G) [inst_4 : IsTopologicalGroup G]
  [CompactSpace G], Langlands.IsSmoothRep (Langlands.GaloisCohomology.divisorSequence φ).X₃
@Langlands.GaloisCohomology.divisorSequence_shortExact : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  {I : Type u_1} {H : I → Type u_1} [inst_2 : (i : I) → Group (H i)] [inst_3 : (i : I) → TopologicalSpace (H i)]
  (φ : (i : I) → H i →ₜ* G) [inst_4 : IsTopologicalGroup G], (Langlands.GaloisCohomology.divisorSequence φ).ShortExact
Langlands.GaloisCohomology.trivialSequence : (H : Type u_1) →
  [inst : Group H] → CategoryTheory.ShortComplex (Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) H)
Langlands.GaloisCohomology.trivialSequence_shortExact : ∀ (H : Type u_1) [inst : Group H],
  (Langlands.GaloisCohomology.trivialSequence H).ShortExact
Langlands.GaloisCohomology.isSmoothRep_trivialSequence_X₁ : ∀ (H : Type u_1) [inst : Group H]
  [inst_1 : TopologicalSpace H], Langlands.IsSmoothRep (Langlands.GaloisCohomology.trivialSequence H).X₁
Langlands.GaloisCohomology.isSmoothRep_trivialSequence_X₂ : ∀ (H : Type u_1) [inst : Group H]
  [inst_1 : TopologicalSpace H], Langlands.IsSmoothRep (Langlands.GaloisCohomology.trivialSequence H).X₂
Langlands.GaloisCohomology.isSmoothRep_trivialSequence_X₃ : ∀ (H : Type u_1) [inst : Group H]
  [inst_1 : TopologicalSpace H], Langlands.IsSmoothRep (Langlands.GaloisCohomology.trivialSequence H).X₃
@Langlands.GaloisCohomology.bijective_nsmul_divisorFunctions_rat : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] {I : Type u_1} {H : I → Type u_1}
  [inst_3 : (i : I) → Group (H i)] [inst_4 : (i : I) → TopologicalSpace (H i)] (φ : (i : I) → H i →ₜ* G) {n : ℕ},
  n ≠ 0 → Function.Bijective fun (f : ↑(Langlands.GaloisCohomology.divisorModule φ (ULift.{u_1, 0} ℚ))) => n • f
@Langlands.GaloisCohomology.isZero_cohomology_divisorModule_rat : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [inst_3 : CompactSpace G] [TotallyDisconnectedSpace G]
  {I : Type u_1} {H : I → Type u_1} [inst_5 : (i : I) → Group (H i)] [inst_6 : (i : I) → TopologicalSpace (H i)]
  [∀ (i : I), IsTopologicalGroup (H i)] (φ : (i : I) → H i →ₜ* G) {q : ℕ},
  1 ≤ q →
    CategoryTheory.Limits.IsZero
      (Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.divisorModule φ (ULift.{u_1, 0} ℚ)) q)
Langlands.GaloisCohomology.isZero_cohomology_trivialModule_rat : ∀ (K : Type u_1) [inst : Group K]
  [inst_1 : TopologicalSpace K] [inst_2 : IsTopologicalGroup K] [CompactSpace K] [TotallyDisconnectedSpace K] {q : ℕ},
  1 ≤ q →
    CategoryTheory.Limits.IsZero
      (Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.trivialModule K (ULift.{u_1, 0} ℚ)) q)
@Langlands.GaloisCohomology.isZero_cohomology_one_divisorModule_int : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [inst_3 : CompactSpace G] [TotallyDisconnectedSpace G]
  {I : Type u_1} {H : I → Type u_1} [inst_5 : (i : I) → Group (H i)] [inst_6 : (i : I) → TopologicalSpace (H i)]
  [∀ (i : I), IsTopologicalGroup (H i)] (φ : (i : I) → H i →ₜ* G),
  CategoryTheory.Limits.IsZero
    (Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.divisorModule φ (ULift.{u_1, 0} ℤ)) 1)
@Langlands.GaloisCohomology.divisorEvalSequence : {G : Type u_1} →
  [inst : Group G] →
    [inst_1 : TopologicalSpace G] →
      [inst_2 : IsTopologicalGroup G] →
        {I : Type u_1} →
          {H : I → Type u_1} →
            [inst_3 : (i : I) → Group (H i)] →
              [inst_4 : (i : I) → TopologicalSpace (H i)] →
                (φ : (i : I) → H i →ₜ* G) →
                  (i : I) →
                    (Langlands.GaloisCohomology.divisorSequence φ).map (Rep.resFunctor ↑(φ i)) ⟶
                      Langlands.GaloisCohomology.trivialSequence (H i)
@Langlands.GaloisCohomology.eq_zero_of_divisorEval_eq_zero : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [inst_3 : CompactSpace G] [TotallyDisconnectedSpace G]
  {I : Type u_1} {H : I → Type u_1} [inst_5 : (i : I) → Group (H i)] [inst_6 : (i : I) → TopologicalSpace (H i)]
  [inst_7 : ∀ (i : I), IsTopologicalGroup (H i)] (φ : (i : I) → H i →ₜ* G) [∀ (i : I), CompactSpace (H i)]
  [∀ (i : I), TotallyDisconnectedSpace (H i)]
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.divisorModule φ (ULift.{u_1, 0} ℤ)) 2)),
  (∀ (i : I),
      (ModuleCat.Hom.hom
            (Langlands.ProfiniteCohomology.map (φ i) (Langlands.GaloisCohomology.divisorEval φ (ULift.{u_1, 0} ℤ) i) 2))
          x =
        0) →
    x = 0
@Langlands.GaloisCohomology.finite_divisorEval_ne_zero : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] [inst_3 : CompactSpace G] {I : Type u_1} {H : I → Type u_1}
  [inst_4 : (i : I) → Group (H i)] [inst_5 : (i : I) → TopologicalSpace (H i)]
  [inst_6 : ∀ (i : I), IsTopologicalGroup (H i)] (φ : (i : I) → H i →ₜ* G) (A : Type u_1) [inst_7 : AddCommGroup A]
  (n : ℕ) (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.divisorModule φ A) n)),
  {i : I |
      (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.map (φ i) (Langlands.GaloisCohomology.divisorEval φ A i) n)) x ≠
        0}.Finite
```

## Literature

- page reference to be added.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/DivisorModule.lean` and `DivisorModuleSupport.lean` (same directory). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: one universe `u` instead of `Type`; `ULift ℤ`, `ULift ℚ`, `ULift (ℚ/ℤ)` coefficients;
the source's `divFun`, `divFunRep`, `divFunEval` are `divisorFunctions`, `divisorModule`, `divisorEval`.
