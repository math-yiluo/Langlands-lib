# Functoriality of cohomology with compact support and the connecting map

`Langlands/GaloisCohomology/CompactSupport/Functoriality.lean`, namespace `Langlands.GaloisCohomology`.

Notation of `Basic.lean`. A morphism `g : A ⟶ B` of `G`-modules with morphisms `g_v : A_v ⟶ B_v`
such that `a_v ≫ g_v = Res(g) ≫ b_v` induces maps of cochains with compact support and of
`H_c^n`, functorially; they commute with `globalToLocal` and `localToCompact`. A short exact
sequence of `G`-modules `S` with compatible short exact sequences of `H_v`-modules `S_v` gives a
short exact sequence of cochains with compact support, hence a connecting map and a long exact
sequence in cohomology with compact support.

```lean
noncomputable def compactSupportMap (g : A ⟶ B) (gᵥ : ∀ v, Aᵥ v ⟶ Bᵥ v)
    (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v : H v →* G)).map g ≫ b v) (n : ℕ) :
    compactSupportCohomology φ A Aᵥ a n ⟶ compactSupportCohomology φ B Bᵥ b n
theorem localToCompact_compactSupportMap (n : ℕ) :
    localToCompact φ A Aᵥ a n ≫ compactSupportMap φ g gᵥ hg (n + 1) =
      ModuleCat.ofHom (LinearMap.pi fun v => (coeffMap (gᵥ v) n).hom.comp (LinearMap.proj v)) ≫
        localToCompact φ B Bᵥ b n
noncomputable def compactSupportδ (hS : S.ShortExact) (hSᵥ : ∀ v, (Sᵥ v).ShortExact) (n : ℕ) :
    compactSupportCohomology φ S.X₃ (fun v => (Sᵥ v).X₃) (fun v => (s v).τ₃) n ⟶
      compactSupportCohomology φ S.X₁ (fun v => (Sᵥ v).X₁) (fun v => (s v).τ₁) (n + 1)
theorem compactSupportCohomology_exact₁ / _exact₂ / _exact₃ (n : ℕ) : (ShortComplex.mk …).Exact
```

(`S : ShortComplex (Rep.{u} k G)`, `Sᵥ : ∀ v, ShortComplex (Rep.{u} k (H v))`,
`s : ∀ v, S.map (Rep.resFunctor (φ v : H v →* G)) ⟶ Sᵥ v`, all terms smooth.)

## Complete types

As printed by `#check` (all variables and instance arguments explicit; `↑(φ v)` is the coercion `(φ v : H v →* G)`):

```lean
@compactSupportCohomology_exact₁ : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] {ι : Type u_1} {H : ι → Type u_1}
  [inst_4 : (v : ι) → Group (H v)] [inst_5 : (v : ι) → TopologicalSpace (H v)]
  [inst_6 : ∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {S : CategoryTheory.ShortComplex (Rep.{u_1, u_1, u_1} k G)} [inst_7 : Langlands.IsSmoothRep S.X₁]
  [inst_8 : Langlands.IsSmoothRep S.X₂] [inst_9 : Langlands.IsSmoothRep S.X₃]
  {Sᵥ : (v : ι) → CategoryTheory.ShortComplex (Rep.{u_1, u_1, u_1} k (H v))}
  [inst_10 : ∀ (v : ι), Langlands.IsSmoothRep (Sᵥ v).X₁] [inst_11 : ∀ (v : ι), Langlands.IsSmoothRep (Sᵥ v).X₂]
  [inst_12 : ∀ (v : ι), Langlands.IsSmoothRep (Sᵥ v).X₃] (s : (v : ι) → S.map (Rep.resFunctor ↑(φ v)) ⟶ Sᵥ v)
  (hS : S.ShortExact) (hSᵥ : ∀ (v : ι), (Sᵥ v).ShortExact) (n : ℕ),
  { X₁ := compactSupportCohomology φ S.X₃ (fun v => (Sᵥ v).X₃) (fun v => (s v).τ₃) n,
      X₂ := compactSupportCohomology φ S.X₁ (fun v => (Sᵥ v).X₁) (fun v => (s v).τ₁) (n + 1),
      X₃ := compactSupportCohomology φ S.X₂ (fun v => (Sᵥ v).X₂) (fun v => (s v).τ₂) (n + 1),
      f := compactSupportδ φ s hS hSᵥ n, g := compactSupportMap φ S.f (fun v => (Sᵥ v).f) ⋯ (n + 1), zero := ⋯ }.Exact

@compactSupportCohomology_exact₂ : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] {ι : Type u_1} {H : ι → Type u_1}
  [inst_4 : (v : ι) → Group (H v)] [inst_5 : (v : ι) → TopologicalSpace (H v)]
  [inst_6 : ∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {S : CategoryTheory.ShortComplex (Rep.{u_1, u_1, u_1} k G)} [inst_7 : Langlands.IsSmoothRep S.X₁]
  [inst_8 : Langlands.IsSmoothRep S.X₂] [inst_9 : Langlands.IsSmoothRep S.X₃]
  {Sᵥ : (v : ι) → CategoryTheory.ShortComplex (Rep.{u_1, u_1, u_1} k (H v))}
  [inst_10 : ∀ (v : ι), Langlands.IsSmoothRep (Sᵥ v).X₁] [inst_11 : ∀ (v : ι), Langlands.IsSmoothRep (Sᵥ v).X₂]
  [inst_12 : ∀ (v : ι), Langlands.IsSmoothRep (Sᵥ v).X₃] (s : (v : ι) → S.map (Rep.resFunctor ↑(φ v)) ⟶ Sᵥ v),
  S.ShortExact →
    (∀ (v : ι), (Sᵥ v).ShortExact) →
      ∀ (n : ℕ),
        { X₁ := compactSupportCohomology φ S.X₁ (fun v => (Sᵥ v).X₁) (fun v => (s v).τ₁) n,
            X₂ := compactSupportCohomology φ S.X₂ (fun v => (Sᵥ v).X₂) (fun v => (s v).τ₂) n,
            X₃ := compactSupportCohomology φ S.X₃ (fun v => (Sᵥ v).X₃) (fun v => (s v).τ₃) n,
            f := compactSupportMap φ S.f (fun v => (Sᵥ v).f) ⋯ n, g := compactSupportMap φ S.g (fun v => (Sᵥ v).g) ⋯ n,
            zero := ⋯ }.Exact

@compactSupportCohomology_exact₃ : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] {ι : Type u_1} {H : ι → Type u_1}
  [inst_4 : (v : ι) → Group (H v)] [inst_5 : (v : ι) → TopologicalSpace (H v)]
  [inst_6 : ∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {S : CategoryTheory.ShortComplex (Rep.{u_1, u_1, u_1} k G)} [inst_7 : Langlands.IsSmoothRep S.X₁]
  [inst_8 : Langlands.IsSmoothRep S.X₂] [inst_9 : Langlands.IsSmoothRep S.X₃]
  {Sᵥ : (v : ι) → CategoryTheory.ShortComplex (Rep.{u_1, u_1, u_1} k (H v))}
  [inst_10 : ∀ (v : ι), Langlands.IsSmoothRep (Sᵥ v).X₁] [inst_11 : ∀ (v : ι), Langlands.IsSmoothRep (Sᵥ v).X₂]
  [inst_12 : ∀ (v : ι), Langlands.IsSmoothRep (Sᵥ v).X₃] (s : (v : ι) → S.map (Rep.resFunctor ↑(φ v)) ⟶ Sᵥ v)
  (hS : S.ShortExact) (hSᵥ : ∀ (v : ι), (Sᵥ v).ShortExact) (n : ℕ),
  { X₁ := compactSupportCohomology φ S.X₂ (fun v => (Sᵥ v).X₂) (fun v => (s v).τ₂) n,
      X₂ := compactSupportCohomology φ S.X₃ (fun v => (Sᵥ v).X₃) (fun v => (s v).τ₃) n,
      X₃ := compactSupportCohomology φ S.X₁ (fun v => (Sᵥ v).X₁) (fun v => (s v).τ₁) (n + 1),
      f := compactSupportMap φ S.g (fun v => (Sᵥ v).g) ⋯ n, g := compactSupportδ φ s hS hSᵥ n, zero := ⋯ }.Exact

@localToCompact_compactSupportMap : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] {ι : Type u_1} {H : ι → Type u_1}
  [inst_4 : (v : ι) → Group (H v)] [inst_5 : (v : ι) → TopologicalSpace (H v)]
  [inst_6 : ∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G) {A B : Rep.{u_1, u_1, u_1} k G}
  [inst_7 : Langlands.IsSmoothRep A] [inst_8 : Langlands.IsSmoothRep B] {Aᵥ Bᵥ : (v : ι) → Rep.{u_1, u_1, u_1} k (H v)}
  [inst_9 : ∀ (v : ι), Langlands.IsSmoothRep (Aᵥ v)] [inst_10 : ∀ (v : ι), Langlands.IsSmoothRep (Bᵥ v)]
  {a : (v : ι) → Rep.res (↑(φ v)) A ⟶ Aᵥ v} {b : (v : ι) → Rep.res (↑(φ v)) B ⟶ Bᵥ v} (g : A ⟶ B)
  (gᵥ : (v : ι) → Aᵥ v ⟶ Bᵥ v)
  (hg :
    ∀ (v : ι),
      CategoryTheory.CategoryStruct.comp (a v) (gᵥ v) =
        CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑(φ v)).map g) (b v))
  (n : ℕ),
  CategoryTheory.CategoryStruct.comp (localToCompact φ A Aᵥ a n) (compactSupportMap φ g gᵥ hg (n + 1)) =
    CategoryTheory.CategoryStruct.comp
      (ModuleCat.ofHom
        (LinearMap.pi fun v => ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.coeffMap (gᵥ v) n) ∘ₗ LinearMap.proj v))
      (localToCompact φ B Bᵥ b n)
```

`resMorphism φ g v : Res_{φ_v} A ⟶ Res_{φ_v} B`, a morphism `g : A ⟶ B` as a morphism of the
restrictions to `H_v`, equal to `(Rep.resFunctor (φ v)).map g` (`resMorphism_eq`).

Complete types, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.resMorphism.{u} {G : Type u} [Group G] [TopologicalSpace G] {ι : Type u} {Hv : ι → Type u}
  [(v : ι) → Group (Hv v)] [(v : ι) → TopologicalSpace (Hv v)] (φ : (v : ι) → Hv v →ₜ* G)
  {A B : Rep.{u, u, u} (ULift.{u, 0} ℤ) G} (g : A ⟶ B) (v : ι) : Rep.res (↑(φ v)) A ⟶ Rep.res (↑(φ v)) B
Langlands.GaloisCohomology.resMorphism_eq.{u} {G : Type u} [Group G] [TopologicalSpace G] {ι : Type u} {Hv : ι → Type u}
  [(v : ι) → Group (Hv v)] [(v : ι) → TopologicalSpace (Hv v)] (φ : (v : ι) → Hv v →ₜ* G)
  {A B : Rep.{u, u, u} (ULift.{u, 0} ℤ) G} (g : A ⟶ B) (v : ι) :
  Langlands.GaloisCohomology.resMorphism φ g v = (Rep.resFunctor ↑(φ v)).map g
```

## Outline of the proofs

`localRes` is natural (`localRes_naturality`, from `cochainsMap_comp_coeffCochainsMap`), so a
compatible pair `(g, g_v)` gives a commutative square of complexes and hence a map of mapping
cocones (`mappingCoconeNat.map`). Identities and composites are checked on pairs. The map of
cocones commutes with the connecting map of the cocone (`homologyδ_naturality`) and the
identification of the local homology, which gives `localToCompact_compactSupportMap`. For short
exact sequences, the cochain functor is exact (`cochainsShortComplex_shortExact` of the
foundations), products of short exact sequences are short exact, and the cocones of a morphism of
short exact sequences of complexes form a short exact sequence (`shortExact_mapShortComplex`);
Mathlib's long exact sequence of a short exact sequence of complexes gives the rest.

## Declarations

`cochainsMap_comp_coeffCochainsMap`, `localRes_naturality`, `compactSupportCochainsMap`,
`compactSupportMap`, `compactSupportMap_id`, `compactSupportMap_comp`, `cohomologyMap_globalToLocal`,
`localToCompact_compactSupportMap`, `localResShortComplex`, `compactSupportMap_f_g`,
`compactSupportCochains_shortExact`, `compactSupportδ`, `compactSupportCohomology_exact₂`,
`compactSupportCohomology_exact₃`, `compactSupportCohomology_exact₁`, `resMorphism`, `resMorphism_eq`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file
`src/GroundTheory/ProfiniteCohomology/CompactSupportCohomology.lean`, sections `Functoriality` and
`CoefficientSequence` (lines 161–334). The repository has no licence file; its text is used with
attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes:
the foundations' cochains and maps (`cochainsMap`, `coeffCochainsMap`, `coeffMap`) replace the
source's; `cochainsMapAlong_comp_cochainsMap` (for `ψ : H' →* G` with a continuity proof) is
`cochainsMap_comp_coeffCochainsMap` (for `ψ : H' →ₜ* G`); `compact*` names become
`compactSupport*`; the lemma names keep `cohomologyMap` where the map is now `coeffMap`, as in the
foundations.

## References

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter II, §2,
  Proposition 2.3 (b), p. 166 (a short exact sequence of sheaves gives a long exact sequence of
  cohomology groups with compact support).
