# Finiteness of cohomology by dévissage

`Langlands/Cohomology/Profinite/Finiteness.lean`, namespace `Langlands.ProfiniteCohomology`.

For a topological group `G` and continuous cohomology `Hʳ(G, M)` of smooth modules:

* `finite_cohomology_X₁_succ hS r`: for a short exact sequence `0 → A → B → C → 0` of smooth modules,
  `Hʳ⁺¹(G, A)` is finite when `Hʳ(G, C)` and `Hʳ⁺¹(G, B)` are (`Hʳ(C) → Hʳ⁺¹(A) → Hʳ⁺¹(B)` is exact;
  `finite_of_exact_of_finite` of `Langlands.Cohomology.Profinite.Duality.DualModule`).
* `cokerShortComplex i`: the short complex `A → B → B / i(A)` of a morphism `i : A ⟶ B` of
  representations (`range_hom_le_comap`: the range of `i` is stable), short exact when `i` is
  injective (`cokerShortComplex_shortExact`).
* For subgroups `V ≤ U`: `subgroupOfTransport h B`, a module of `V.subgroupOf U` as a module of `V`
  (`subgroupOfTransportHom`, instance `isSmoothRep_subgroupOfTransport`), with the same cohomology
  (`cohomologySubgroupOfIso`).
* `finite_cohomology_zero M`: `H⁰(G, M)` is finite for a finite smooth `M`;
  `exists_openSubgroup_le_fixing U W₀ M`: an open subgroup `U` acting on a finite smooth module `M` has
  an open subgroup `V ≤ U ∩ W₀` acting trivially.
* **Dévissage** (`finite_cohomology_of_forall_trivial n R W₀ h U M hM`): let `G` be compact and `W₀` an
  open subgroup. If for every open subgroup `V ≤ W₀` the cohomology of `V` with coefficients in finite
  smooth modules killed by `n` with trivial action is finite in degrees `≤ R`, then for every open
  subgroup `U` and every finite smooth `U`-module `M` killed by `n`, `Hʳ(U, M)` is finite for `r ≤ R`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.ProfiniteCohomology.finite_cohomology_X₁_succ.{u} {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {S : CategoryTheory.ShortComplex (Rep.{u, u, u} k G)} [Langlands.IsSmoothRep S.X₁]
  [Langlands.IsSmoothRep S.X₂] [Langlands.IsSmoothRep S.X₃] (hS : S.ShortExact) (r : ℕ)
  [Finite ↑(Langlands.ProfiniteCohomology.cohomology S.X₃ r)]
  [Finite ↑(Langlands.ProfiniteCohomology.cohomology S.X₂ (r + 1))] :
  Finite ↑(Langlands.ProfiniteCohomology.cohomology S.X₁ (r + 1))
Langlands.ProfiniteCohomology.range_hom_le_comap.{u} {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u, u, u} k G}
  (i : A ⟶ B) (g : G) : (Rep.Hom.hom i).range ≤ Submodule.comap (B.ρ g) (Rep.Hom.hom i).range
Langlands.ProfiniteCohomology.cokerShortComplex.{u} {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u, u, u} k G}
  (i : A ⟶ B) : CategoryTheory.ShortComplex (Rep.{u, u, u} k G)
Langlands.ProfiniteCohomology.cokerShortComplex_shortExact.{u} {k G : Type u} [CommRing k] [Group G]
  {A B : Rep.{u, u, u} k G} (i : A ⟶ B) (hi : Function.Injective ⇑(Rep.Hom.hom i)) :
  (Langlands.ProfiniteCohomology.cokerShortComplex i).ShortExact
Langlands.ProfiniteCohomology.subgroupOfTransport.{u} {k G : Type u} [CommRing k] [Group G] {U V : Subgroup G}
  (h : V ≤ U) (B : Rep.{u, u, u} k ↥(V.subgroupOf U)) : Rep.{u, u, u} k ↥V
Langlands.ProfiniteCohomology.subgroupOfTransportHom.{u} {k G : Type u} [CommRing k] [Group G] {U V : Subgroup G}
  (h : V ≤ U) (B : Rep.{u, u, u} k ↥(V.subgroupOf U)) :
  Rep.res (Subgroup.subgroupOfEquivOfLe h).toMonoidHom (Langlands.ProfiniteCohomology.subgroupOfTransport h B) ⟶ B
Langlands.ProfiniteCohomology.isSmoothRep_subgroupOfTransport.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] {U V : Subgroup G} (h : V ≤ U) (B : Rep.{u, u, u} k ↥(V.subgroupOf U))
  [Langlands.IsSmoothRep B] : Langlands.IsSmoothRep (Langlands.ProfiniteCohomology.subgroupOfTransport h B)
Langlands.ProfiniteCohomology.cohomologySubgroupOfIso.{u} {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {U V : Subgroup G} (h : V ≤ U) (B : Rep.{u, u, u} k ↥(V.subgroupOf U))
  [Langlands.IsSmoothRep B] (r : ℕ) :
  Langlands.ProfiniteCohomology.cohomology (Langlands.ProfiniteCohomology.subgroupOfTransport h B) r ≅
    Langlands.ProfiniteCohomology.cohomology B r
Langlands.ProfiniteCohomology.finite_cohomology_zero.{u} {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (M : Rep.{u, u, u} k G) [Langlands.IsSmoothRep M] [Finite ↑M] :
  Finite ↑(Langlands.ProfiniteCohomology.cohomology M 0)
Langlands.ProfiniteCohomology.exists_openSubgroup_le_fixing.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] (U W₀ : OpenSubgroup G) (M : Rep.{u, u, u} k ↥↑U)
  [Langlands.IsSmoothRep M] [Finite ↑M] :
  ∃ V, ∃ (_ : ↑V ≤ ↑U), V ≤ W₀ ∧ ∀ (g : ↥((↑V).subgroupOf ↑U)) (m : ↑M), (M.ρ ↑g) m = m
Langlands.ProfiniteCohomology.finite_cohomology_of_forall_trivial.{u} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] (n R : ℕ) (W₀ : OpenSubgroup G)
  (h :
    ∀ V ≤ W₀,
      ∀ (A : Rep.{u, u, u} (ULift.{u, 0} ℤ) ↥↑V) [inst : Langlands.IsSmoothRep A] [Finite ↑A],
        (∀ (g : ↥↑V) (a : ↑A), (A.ρ g) a = a) →
          (∀ (a : ↑A), n • a = 0) → ∀ r ≤ R, Finite ↑(Langlands.ProfiniteCohomology.cohomology A r))
  (U : OpenSubgroup G) (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) ↥↑U) [Langlands.IsSmoothRep M] [Finite ↑M]
  (hM : ∀ (m : ↑M), n • m = 0) (r : ℕ) : r ≤ R → Finite ↑(Langlands.ProfiniteCohomology.cohomology M r)
```

## Outline of the proofs

Dévissage by induction on the degree `r`, for all modules at once. Degree `0` is
`finite_cohomology_zero`. For `r + 1`: choose an open subgroup `V ≤ U ∩ W₀` acting trivially on `M`
(the intersection of the stabilizers of the finitely many elements), and embed `M` into the module
`Coind_V^U Res_V M` coinduced from `V` by the unit map; the cokernel is again finite, smooth and
killed by `n` (`cokerShortComplex_shortExact`). By Shapiro's lemma (`shapiroIso`) and
`cohomologySubgroupOfIso`, `Hʳ⁺¹(U, Coind_V^U Res_V M) = Hʳ⁺¹(V, M)`, finite by the hypothesis since `V`
acts trivially; the cokernel has finite `Hʳ` by induction; so `Hʳ⁺¹(U, M)` is finite
(`finite_cohomology_X₁_succ`). This is the method of dimension shifting through induced modules,
with the coinduced module of an open subgroup acting trivially in place of the module induced from
the trivial group.

## Declarations

`finite_cohomology_X₁_succ`, `range_hom_le_comap`, `cokerShortComplex`, `cokerShortComplex_shortExact`,
`subgroupOfTransport`, `subgroupOfTransportHom`, `isSmoothRep_subgroupOfTransport`,
`cohomologySubgroupOfIso`, `finite_cohomology_zero`, `exists_openSubgroup_le_fixing`,
`finite_cohomology_of_forall_trivial`.

Used for the finiteness of the cohomology of local fields
(`Langlands.GaloisCohomology.Local.Finiteness`) and of `G_S`
(`Langlands.GaloisCohomology.Global.Finiteness`); `cokerShortComplex` also in the dévissages of
`Langlands.GaloisCohomology.Global.RealPlaces` and of the local Euler characteristic.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`: the dévissage
lemmas of `src/GroundTheory/ProfiniteCohomology/LocalClassFormation/FiniteVanishing/` (files
`Devissage.lean`, `KummerOpen.lean`, `Trivial.lean`), with the source's names (`isDiscreteRep_subgroupOfTransport` → `isSmoothRep_subgroupOfTransport`). The
repository has no licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). The Library's `IsSmoothRep` and `vectorStabilizer` replace
the source's `IsDiscreteRep` and stabilizer; `finite_cohomology_X₁_succ` uses
`finite_of_exact_of_finite` (exactness in the form `ker ⊆ range`).

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008,
  corrected printing 2013), Chapter I, §3, p. 32 (dimension shifting through `0 → A → Ind_G(A) → A₁ → 0`,
  after Proposition (1.3.7)), and §6, Proposition (1.6.4), p. 62 (Shapiro's lemma).
