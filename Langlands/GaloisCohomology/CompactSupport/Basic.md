# Cohomology with compact support relative to a family of homomorphisms

`Langlands/GaloisCohomology/CompactSupport/Basic.lean`, namespace `Langlands.GaloisCohomology`.

Let `k` be a commutative ring, `G` a topological group, `(H_v)_{v ∈ ι}` a family of topological
groups with continuous homomorphisms `φ_v : H_v →ₜ* G`, `A` a smooth `G`-module, `A_v` smooth
`H_v`-modules and `a_v : Res_{φ_v} A ⟶ A_v` (all in one universe `u`). Restriction of locally
constant cochains along `φ_v` followed by `a_v` is a morphism of complexes
`localRes : C•(G, A) ⟶ ∏_v C•(H_v, A_v)`. Cohomology with compact support is the cohomology of its
mapping cocone, and it sits in a long exact sequence with the global and local cohomology.

```lean
variable (φ : ∀ v, H v →ₜ* G) (A : Rep.{u} k G) [IsSmoothRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsSmoothRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v)
noncomputable def localRes : cochains A ⟶ piComplex fun v => cochains (Aᵥ v)
noncomputable def compactSupportCochains : CochainComplex (ModuleCat.{u} k) ℕ
noncomputable def compactSupportCohomology (n : ℕ) : ModuleCat.{u} k
noncomputable def compactToGlobal (n : ℕ) : compactSupportCohomology φ A Aᵥ a n ⟶ cohomology A n
noncomputable def globalToLocal (n : ℕ) : cohomology A n ⟶ ModuleCat.of k (∀ v, cohomology (Aᵥ v) n)
noncomputable def localToCompact (n : ℕ) :
    ModuleCat.of k (∀ v, cohomology (Aᵥ v) n) ⟶ compactSupportCohomology φ A Aᵥ a (n + 1)
theorem compactSupportCohomology_exact_global (n : ℕ) :
    (ShortComplex.mk _ _ (compactToGlobal_globalToLocal φ A Aᵥ a n)).Exact
theorem compactSupportCohomology_exact_local (n : ℕ) :
    (ShortComplex.mk _ _ (globalToLocal_localToCompact φ A Aᵥ a n)).Exact
theorem compactSupportCohomology_exact_compact (n : ℕ) :
    (ShortComplex.mk _ _ (localToCompact_compactToGlobal φ A Aᵥ a n)).Exact
theorem mono_compactToGlobal_zero : Mono (compactToGlobal φ A Aᵥ a 0)
```

So `⋯ → H_c^n(G, A) → Hⁿ(G, A) → ∏_v Hⁿ(H_v, A_v) → H_c^{n+1}(G, A) → ⋯` is exact, beginning
with `0 → H_c^0(G, A) → H^0(G, A)`.

## Complete types

As printed by `#check` (all variables and instance arguments explicit; `↑(φ v)` is the coercion `(φ v : H v →* G)`):

```lean
@compactSupportCohomology_exact_global : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] {ι : Type u_1} {H : ι → Type u_1}
  [inst_4 : (v : ι) → Group (H v)] [inst_5 : (v : ι) → TopologicalSpace (H v)]
  [inst_6 : ∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G) (A : Rep.{u_1, u_1, u_1} k G)
  [inst_7 : Langlands.IsSmoothRep A] (Aᵥ : (v : ι) → Rep.{u_1, u_1, u_1} k (H v))
  [inst_8 : ∀ (v : ι), Langlands.IsSmoothRep (Aᵥ v)] (a : (v : ι) → Rep.res (↑(φ v)) A ⟶ Aᵥ v) (n : ℕ),
  { X₁ := compactSupportCohomology φ A Aᵥ a n, X₂ := Langlands.ProfiniteCohomology.cohomology A n,
      X₃ := ↧((v : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Aᵥ v) n)), f := compactToGlobal φ A Aᵥ a n,
      g := globalToLocal φ A Aᵥ a n, zero := ⋯ }.Exact

@compactSupportCohomology_exact_local : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] {ι : Type u_1} {H : ι → Type u_1}
  [inst_4 : (v : ι) → Group (H v)] [inst_5 : (v : ι) → TopologicalSpace (H v)]
  [inst_6 : ∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G) (A : Rep.{u_1, u_1, u_1} k G)
  [inst_7 : Langlands.IsSmoothRep A] (Aᵥ : (v : ι) → Rep.{u_1, u_1, u_1} k (H v))
  [inst_8 : ∀ (v : ι), Langlands.IsSmoothRep (Aᵥ v)] (a : (v : ι) → Rep.res (↑(φ v)) A ⟶ Aᵥ v) (n : ℕ),
  { X₁ := Langlands.ProfiniteCohomology.cohomology A n,
      X₂ := ↧((v : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Aᵥ v) n)),
      X₃ := compactSupportCohomology φ A Aᵥ a (n + 1), f := globalToLocal φ A Aᵥ a n, g := localToCompact φ A Aᵥ a n,
      zero := ⋯ }.Exact

@compactSupportCohomology_exact_compact : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] {ι : Type u_1} {H : ι → Type u_1}
  [inst_4 : (v : ι) → Group (H v)] [inst_5 : (v : ι) → TopologicalSpace (H v)]
  [inst_6 : ∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G) (A : Rep.{u_1, u_1, u_1} k G)
  [inst_7 : Langlands.IsSmoothRep A] (Aᵥ : (v : ι) → Rep.{u_1, u_1, u_1} k (H v))
  [inst_8 : ∀ (v : ι), Langlands.IsSmoothRep (Aᵥ v)] (a : (v : ι) → Rep.res (↑(φ v)) A ⟶ Aᵥ v) (n : ℕ),
  { X₁ := ↧((v : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Aᵥ v) n)),
      X₂ := compactSupportCohomology φ A Aᵥ a (n + 1), X₃ := Langlands.ProfiniteCohomology.cohomology A (n + 1),
      f := localToCompact φ A Aᵥ a n, g := compactToGlobal φ A Aᵥ a (n + 1), zero := ⋯ }.Exact

@mono_compactToGlobal_zero : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G] [inst_2 : TopologicalSpace G]
  [inst_3 : IsTopologicalGroup G] {ι : Type u_1} {H : ι → Type u_1} [inst_4 : (v : ι) → Group (H v)]
  [inst_5 : (v : ι) → TopologicalSpace (H v)] [inst_6 : ∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  (A : Rep.{u_1, u_1, u_1} k G) [inst_7 : Langlands.IsSmoothRep A] (Aᵥ : (v : ι) → Rep.{u_1, u_1, u_1} k (H v))
  [inst_8 : ∀ (v : ι), Langlands.IsSmoothRep (Aᵥ v)] (a : (v : ι) → Rep.res (↑(φ v)) A ⟶ Aᵥ v),
  CategoryTheory.Mono (compactToGlobal φ A Aᵥ a 0)
```

## Outline of the proofs

The three exactness theorems are the long exact sequence of the mapping cocone
(`mappingCoconeNat.homology_exact₁₂₃`, `Internal/MappingCocone.lean`) transported along the
isomorphism `piHomologyIso` between the homology of the product of the local complexes and the
product of the local cohomology groups, under which `Hⁿ(localRes)` becomes `globalToLocal`
(`homologyMap_localRes_localCohomologyIso_hom`).

## Declarations

`localRes`, `compactSupportCochains`, `compactSupportCohomology`, `compactSupportCohomologyRes`
(local modules the restrictions of `A`), `compactToGlobal`, `globalToLocal`, `localCohomologyIso`,
`homologyMap_localRes_localCohomologyIso_hom`, `localToCompact`, `compactToGlobal_globalToLocal`,
`globalToLocal_localToCompact`, `localToCompact_compactToGlobal`,
`compactSupportCohomology_exact_global`, `compactSupportCohomology_exact_local`,
`compactSupportCohomology_exact_compact`, `mono_compactToGlobal_zero`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/CompactSupportCohomology/HomApplyHomApplyEqOfCompEq.lean`
(section `CompactSupport`, lines 162–195) and `CompactSupportCohomology.lean` (section
`LongExactSequence`, lines 89–159). The repository has no licence file; its text is used with
attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes:
the Library's cochains and smooth coefficients (`cochains`, `cochainsMap φ`, `map φ`, `IsSmoothRep`)
replace the source's (`cochainsComplex`, `cochainsMapAlong`, `cohomologyMapAlong`, `IsDiscreteRep`);
restriction is along the coercion `(φ v : H v →* G)` (the foundations' convention) in place of
`(φ v).toMonoidHom`; `compactCochains`, `compactCohomology`, `compactCohomologyRes` are
`compactSupportCochains`, `compactSupportCohomology`, `compactSupportCohomologyRes`, and
`compactCohomology_exact_{global,local,compact}` are `compactSupportCohomology_exact_*`; the
auxiliary `continuous_toMonoidHom` and `isDiscreteRep_res_toMonoidHom` are not needed.

## References

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter II, §2,
  pp. 165–166 (definition through the mapping cone and Proposition 2.3 (a), the exact sequence
  `⋯ → H_c^r(U, F) → H^r(U, F) → ⊕_{v ∉ U} H^r(K_v, F_v) → H_c^{r+1}(U, F) → ⋯`). Milne uses
  complete resolutions at the real places; here all local complexes are ordinary cochains (the
  variant with Tate's modified groups is in `TateModified/`).
