# Counting components of divisor classes

`Langlands/GaloisCohomology/Global/Units/DivisorCount.lean`, namespace `Langlands.GaloisCohomology`.

Let `G` be a profinite group, `φ_i : H_i →ₜ* G` continuous homomorphisms from profinite groups and
`D = divisorModule φ ℤ` (`Langlands.GaloisCohomology.Global.Units.DivisorModule`). The component at `i`
of a class `d ∈ H²(G, D)` is its image in `H²(H_i, ℤ)` under `divisorEval`.

**Theorem** (`card_le_of_topologicallyCyclic`). Suppose the image of `H_i` is topologically cyclic up
to every neighbourhood of `1`: for every neighbourhood `V` of `1` in `G` there is `h₀ ∈ H_i` such that
every `φ_i(h)` lies in `φ_i(h₀)^k V` for some `k ∈ ℤ`. Then for `m ≠ 0` every finite set of classes of
`H²(H_i, ℤ)` killed by `m` which are components at `i` of classes of `H²(G, D)` has at most `m`
elements.

Proof. `H²(G, D) ≅ H¹(G, D ⊗ ℚ/ℤ)` and `H²(H_i, ℤ) ≅ H¹(H_i, ℚ/ℤ)` through the sequences
`0 → ℤ → ℚ → ℚ/ℤ → 0` (the middle terms have no cohomology in positive degrees), so a component is the
connecting image of a homomorphism `χ : H_i → ℚ/ℤ` which is constant on the cosets of the pull-back of
a neighbourhood `V` of `1` (`exists_cocycle_of_divisorEval`). For finitely many components take the
intersection of their neighbourhoods and an `h₀` for it: each `χ` is determined by `χ(h₀)`
(`cocycleFun_mul_trivial`), an element of `ℚ/ℤ` killed by `m`, and there are at most `m` of those
(`exists_finset_nsmul_eq_zero`).

The theorem is used at a finite place `v ∉ S` for `G_S` with the localization at `v`
(`Langlands.GaloisCohomology.Global.Units.HighDegree`, `card_le_sDivisor_component`): the image of the
local Galois group in every finite quotient of `G_S` is the decomposition group of an unramified
place, which is cyclic.

Declarations, in order: `exists_fin_eq_of_nsmul_eq_zero`, `exists_finset_nsmul_eq_zero`,
`exists_cocycle_of_divisorEval`, `cocycleFun_mul_trivial`, `card_le_of_topologicallyCyclic`.

## Complete types

```lean
@Langlands.GaloisCohomology.exists_fin_eq_of_nsmul_eq_zero : ∀ {m : ℕ},
  m ≠ 0 →
    ∀ {a : ULift.{u_1, 0} Langlands.ProfiniteCohomology.QZ},
      m • a = 0 → ∃ (k : Fin m), a = { down := Langlands.GaloisCohomology.ratToQZ (↑↑k / ↑m) }
@Langlands.GaloisCohomology.exists_finset_nsmul_eq_zero : ∀ {m : ℕ},
  m ≠ 0 →
    ∃ (T : Finset (ULift.{u_1, 0} Langlands.ProfiniteCohomology.QZ)),
      T.card ≤ m ∧ ∀ (a : ULift.{u_1, 0} Langlands.ProfiniteCohomology.QZ), m • a = 0 → a ∈ T
@Langlands.GaloisCohomology.exists_cocycle_of_divisorEval : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [inst_3 : CompactSpace G] [TotallyDisconnectedSpace G]
  {I : Type u_1} {H : I → Type u_1} [inst_5 : (i : I) → Group (H i)] [inst_6 : (i : I) → TopologicalSpace (H i)]
  [inst_7 : ∀ (i : I), IsTopologicalGroup (H i)] (φ : (i : I) → H i →ₜ* G) (i : I)
  (d : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.divisorModule φ (ULift.{u_1, 0} ℤ)) 2)),
  ∃ (w : ↑(Langlands.ProfiniteCohomology.cocycles (Langlands.GaloisCohomology.trivialSequence (H i)).X₃ 1)),
    ∃ V ∈ nhds 1,
      (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.δ ⋯ 1 2 ⋯))
            ((ModuleCat.Hom.hom
                (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.GaloisCohomology.trivialSequence (H i)).X₃ 1))
              w) =
          (ModuleCat.Hom.hom
              (Langlands.ProfiniteCohomology.map (φ i) (Langlands.GaloisCohomology.divisorEval φ (ULift.{u_1, 0} ℤ) i)
                2))
            d ∧
        ∀ (h h' : H i),
          ((φ i) h)⁻¹ * (φ i) h' ∈ V →
            (Langlands.ProfiniteCohomology.cocycleFun (Langlands.GaloisCohomology.trivialSequence (H i)).X₃ w
                fun (x : Fin 1) => h) =
              Langlands.ProfiniteCohomology.cocycleFun (Langlands.GaloisCohomology.trivialSequence (H i)).X₃ w
                fun (x : Fin 1) => h'
@Langlands.GaloisCohomology.cocycleFun_mul_trivial : ∀ {K : Type u_1} [inst : Group K] [inst_1 : TopologicalSpace K]
  [inst_2 : IsTopologicalGroup K]
  (w : ↑(Langlands.ProfiniteCohomology.cocycles (Langlands.GaloisCohomology.trivialSequence K).X₃ 1)) (g h : K),
  (Langlands.ProfiniteCohomology.cocycleFun (Langlands.GaloisCohomology.trivialSequence K).X₃ w fun (x : Fin 1) =>
      g * h) =
    (Langlands.ProfiniteCohomology.cocycleFun (Langlands.GaloisCohomology.trivialSequence K).X₃ w fun (x : Fin 1) =>
        g) +
      Langlands.ProfiniteCohomology.cocycleFun (Langlands.GaloisCohomology.trivialSequence K).X₃ w fun (x : Fin 1) => h
@Langlands.GaloisCohomology.card_le_of_topologicallyCyclic : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [inst_3 : CompactSpace G] [TotallyDisconnectedSpace G]
  {I : Type u_1} {H : I → Type u_1} [inst_5 : (i : I) → Group (H i)] [inst_6 : (i : I) → TopologicalSpace (H i)]
  [inst_7 : ∀ (i : I), IsTopologicalGroup (H i)] [∀ (i : I), CompactSpace (H i)]
  [∀ (i : I), TotallyDisconnectedSpace (H i)] (φ : (i : I) → H i →ₜ* G) (i : I) {m : ℕ},
  m ≠ 0 →
    (∀ V ∈ nhds 1, ∃ (h₀ : H i), ∀ (h : H i), ∃ (k : ℤ), ((φ i) (h₀ ^ k))⁻¹ * (φ i) h ∈ V) →
      ∀
        (s :
          Finset
            ↑(Langlands.ProfiniteCohomology.cohomology
                (Langlands.GaloisCohomology.trivialModule (H i) (ULift.{u_1, 0} ℤ)) 2)),
        (∀ c ∈ s,
            m • c = 0 ∧
              ∃ (d :
                ↑(Langlands.ProfiniteCohomology.cohomology
                    (Langlands.GaloisCohomology.divisorModule φ (ULift.{u_1, 0} ℤ)) 2)),
                (ModuleCat.Hom.hom
                      (Langlands.ProfiniteCohomology.map (φ i)
                        (Langlands.GaloisCohomology.divisorEval φ (ULift.{u_1, 0} ℤ) i) 2))
                    d =
                  c) →
          s.card ≤ m
```

## Literature

The file is elementary group cohomology (the connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0` and characters
of cyclic groups); no source is cited.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/FiniteSetOfNsmulEqZeroQZ.lean` (lines
14–44: the finiteness of the elements of `ℚ/ℤ` killed by `m`, here `exists_finset_nsmul_eq_zero` with an
explicit bound). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: the source counts
through a Frobenius element of the local Galois group and the injection of characters into `ℚ/ℤ`
(`SurjectiveOfInjectiveOfInjective.lean`, `FrobData`, `exists_val_eq_of_counting`, lines 54–146);
here the count is the bound `card_le_of_topologicallyCyclic` for topologically cyclic images, proved
from cocycles.
