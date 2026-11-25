# Cup products on cohomology with compact support

`Langlands/GaloisCohomology/CompactSupport/CupProduct.lean`, namespace `Langlands.GaloisCohomology`.

Notation of `Basic.lean`. A morphism `μ : A ⊗ B ⟶ C` of `G`-modules together with local pairings
`μ_v : A_v ⊗ Res_{φ_v} B ⟶ C_v` compatible with `a` and `c` gives the cup product of a class with
compact support and an ordinary class; symmetrically with compact support in the right factor.

```lean
noncomputable def compactCup (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v : H v →* G) B ⟶ Cᵥ v)
    (hμ : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ ≫ c v =
      resTensorHom (φ v : H v →* G) (a v) (𝟙 _) ≫ μᵥ v) {r s n : ℕ} (h : r + s = n) :
    compactSupportCohomology φ A Aᵥ a r →ₗ[k] cohomology B s →ₗ[k] compactSupportCohomology φ C Cᵥ c n
theorem compactCup_localToCompact {r s n : ℕ} (h : r + s = n) (h' : r + 1 + s = n + 1)
    (ξ : ∀ v, cohomology (Aᵥ v) r) (z : cohomology B s) :
    compactCup φ μ μᵥ hμ h' ((localToCompact φ A Aᵥ a r).hom ξ) z =
      (localToCompact φ C Cᵥ c n).hom (fun v => cupPairing (μᵥ v) h (ξ v) ((map (φ v) (𝟙 _) s).hom z))
theorem compactCup_eq_compactCupRight (hL : ∀ v, μᵥ v = (𝟙 _ ⊗ₘ b v) ≫ μᵥ'' v)
    (hR : ∀ v, μᵥ' v = (a v ⊗ₘ 𝟙 _) ≫ μᵥ'' v) {r s n : ℕ} (h : r + s = n)
    (x : compactSupportCohomology φ A Aᵥ a r) (y : compactSupportCohomology φ B Bᵥ b s) :
    compactCup φ μ μᵥ hμ h x ((compactToGlobal φ B Bᵥ b s).hom y) =
      compactCupRight φ μ μᵥ' hμ' h ((compactToGlobal φ A Aᵥ a r).hom x) y
theorem compactCup_compactSupportδ_add_compactCup_δ … :
    compactCup φ μ₁ μ₁ᵥ hμ₁ h₁ ((compactSupportδ φ sA hSA hSAᵥ r).hom x) y +
      (-1 : k) ^ r • compactCup φ μ₃ μ₃ᵥ hμ₃ h₃ x ((δ hSB s (s + 1) rfl).hom y) = 0
```

## Complete types

As printed by `#check` (all variables and instance arguments explicit; `↑(φ v)` is the coercion `(φ v : H v →* G)`):

```lean
@compactCup_localToCompact : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G] [inst_2 : TopologicalSpace G]
  [inst_3 : IsTopologicalGroup G] {ι : Type u_1} {H : ι → Type u_1} [inst_4 : (v : ι) → Group (H v)]
  [inst_5 : (v : ι) → TopologicalSpace (H v)] [inst_6 : ∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {A B C : Rep.{u_1, u_1, u_1} k G} [inst_7 : Langlands.IsSmoothRep A] [inst_8 : Langlands.IsSmoothRep B]
  [inst_9 : Langlands.IsSmoothRep C] {Aᵥ Cᵥ : (v : ι) → Rep.{u_1, u_1, u_1} k (H v)}
  [inst_10 : ∀ (v : ι), Langlands.IsSmoothRep (Aᵥ v)] [inst_11 : ∀ (v : ι), Langlands.IsSmoothRep (Cᵥ v)]
  {a : (v : ι) → Rep.res (↑(φ v)) A ⟶ Aᵥ v} {c : (v : ι) → Rep.res (↑(φ v)) C ⟶ Cᵥ v}
  (μ : CategoryTheory.MonoidalCategoryStruct.tensorObj A B ⟶ C)
  (μᵥ : (v : ι) → CategoryTheory.MonoidalCategoryStruct.tensorObj (Aᵥ v) (Rep.res (↑(φ v)) B) ⟶ Cᵥ v)
  (hμ :
    ∀ (v : ι),
      CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑(φ v)).map μ) (c v) =
        CategoryTheory.CategoryStruct.comp
          (Langlands.ProfiniteCohomology.resTensorHom (↑(φ v)) (a v)
            (CategoryTheory.CategoryStruct.id (Rep.res (↑(φ v)) B)))
          (μᵥ v))
  {r s n : ℕ} (h : r + s = n) (h' : r + 1 + s = n + 1)
  (ξ : (v : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Aᵥ v) r))
  (z : ↑(Langlands.ProfiniteCohomology.cohomology B s)),
  ((compactCup φ μ μᵥ hμ h') ((ModuleCat.Hom.hom (localToCompact φ A Aᵥ a r)) ξ)) z =
    (ModuleCat.Hom.hom (localToCompact φ C Cᵥ c n)) fun v =>
      ((Langlands.ProfiniteCohomology.cupPairing (μᵥ v) h) (ξ v))
        ((ModuleCat.Hom.hom
            (Langlands.ProfiniteCohomology.map (φ v) (CategoryTheory.CategoryStruct.id (Rep.res (↑(φ v)) B)) s))
          z)

@compactCup_eq_compactCupRight : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G] [inst_2 : TopologicalSpace G]
  [inst_3 : IsTopologicalGroup G] {ι : Type u_1} {H : ι → Type u_1} [inst_4 : (v : ι) → Group (H v)]
  [inst_5 : (v : ι) → TopologicalSpace (H v)] [inst_6 : ∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {A B C : Rep.{u_1, u_1, u_1} k G} [inst_7 : Langlands.IsSmoothRep A] [inst_8 : Langlands.IsSmoothRep B]
  [inst_9 : Langlands.IsSmoothRep C] {Aᵥ Bᵥ Cᵥ : (v : ι) → Rep.{u_1, u_1, u_1} k (H v)}
  [inst_10 : ∀ (v : ι), Langlands.IsSmoothRep (Aᵥ v)] [inst_11 : ∀ (v : ι), Langlands.IsSmoothRep (Bᵥ v)]
  [inst_12 : ∀ (v : ι), Langlands.IsSmoothRep (Cᵥ v)] {a : (v : ι) → Rep.res (↑(φ v)) A ⟶ Aᵥ v}
  {b : (v : ι) → Rep.res (↑(φ v)) B ⟶ Bᵥ v} {c : (v : ι) → Rep.res (↑(φ v)) C ⟶ Cᵥ v}
  (μ : CategoryTheory.MonoidalCategoryStruct.tensorObj A B ⟶ C)
  (μᵥ : (v : ι) → CategoryTheory.MonoidalCategoryStruct.tensorObj (Aᵥ v) (Rep.res (↑(φ v)) B) ⟶ Cᵥ v)
  (μᵥ' : (v : ι) → CategoryTheory.MonoidalCategoryStruct.tensorObj (Rep.res (↑(φ v)) A) (Bᵥ v) ⟶ Cᵥ v)
  (μᵥ'' : (v : ι) → CategoryTheory.MonoidalCategoryStruct.tensorObj (Aᵥ v) (Bᵥ v) ⟶ Cᵥ v)
  (hμ :
    ∀ (v : ι),
      CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑(φ v)).map μ) (c v) =
        CategoryTheory.CategoryStruct.comp
          (Langlands.ProfiniteCohomology.resTensorHom (↑(φ v)) (a v)
            (CategoryTheory.CategoryStruct.id (Rep.res (↑(φ v)) B)))
          (μᵥ v))
  (hμ' :
    ∀ (v : ι),
      CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑(φ v)).map μ) (c v) =
        CategoryTheory.CategoryStruct.comp
          (Langlands.ProfiniteCohomology.resTensorHom (↑(φ v)) (CategoryTheory.CategoryStruct.id (Rep.res (↑(φ v)) A))
            (b v))
          (μᵥ' v)),
  (∀ (v : ι),
      μᵥ v =
        CategoryTheory.CategoryStruct.comp
          (CategoryTheory.MonoidalCategoryStruct.tensorHom (CategoryTheory.CategoryStruct.id (Aᵥ v)) (b v)) (μᵥ'' v)) →
    (∀ (v : ι),
        μᵥ' v =
          CategoryTheory.CategoryStruct.comp
            (CategoryTheory.MonoidalCategoryStruct.tensorHom (a v) (CategoryTheory.CategoryStruct.id (Bᵥ v)))
            (μᵥ'' v)) →
      ∀ {r s n : ℕ} (h : r + s = n) (x : ↑(compactSupportCohomology φ A Aᵥ a r))
        (y : ↑(compactSupportCohomology φ B Bᵥ b s)),
        ((compactCup φ μ μᵥ hμ h) x) ((ModuleCat.Hom.hom (compactToGlobal φ B Bᵥ b s)) y) =
          ((compactCupRight φ μ μᵥ' hμ' h) ((ModuleCat.Hom.hom (compactToGlobal φ A Aᵥ a r)) x)) y

@compactCup_compactSupportδ_add_compactCup_δ : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] {ι : Type u_1} {H : ι → Type u_1}
  [inst_4 : (v : ι) → Group (H v)] [inst_5 : (v : ι) → TopologicalSpace (H v)]
  [inst_6 : ∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G)
  {SA : CategoryTheory.ShortComplex (Rep.{u_1, u_1, u_1} k G)} [inst_7 : Langlands.IsSmoothRep SA.X₁]
  [inst_8 : Langlands.IsSmoothRep SA.X₂] [inst_9 : Langlands.IsSmoothRep SA.X₃]
  {SAᵥ : (v : ι) → CategoryTheory.ShortComplex (Rep.{u_1, u_1, u_1} k (H v))}
  [inst_10 : ∀ (v : ι), Langlands.IsSmoothRep (SAᵥ v).X₁] [inst_11 : ∀ (v : ι), Langlands.IsSmoothRep (SAᵥ v).X₂]
  [inst_12 : ∀ (v : ι), Langlands.IsSmoothRep (SAᵥ v).X₃] (sA : (v : ι) → SA.map (Rep.resFunctor ↑(φ v)) ⟶ SAᵥ v)
  {SB : CategoryTheory.ShortComplex (Rep.{u_1, u_1, u_1} k G)} [inst_13 : Langlands.IsSmoothRep SB.X₁]
  [inst_14 : Langlands.IsSmoothRep SB.X₂] [inst_15 : Langlands.IsSmoothRep SB.X₃] {C : Rep.{u_1, u_1, u_1} k G}
  [inst_16 : Langlands.IsSmoothRep C] {Cᵥ : (v : ι) → Rep.{u_1, u_1, u_1} k (H v)}
  [inst_17 : ∀ (v : ι), Langlands.IsSmoothRep (Cᵥ v)] {c : (v : ι) → Rep.res (↑(φ v)) C ⟶ Cᵥ v}
  (μ₁ : CategoryTheory.MonoidalCategoryStruct.tensorObj SA.X₁ SB.X₃ ⟶ C)
  (μ₂ : CategoryTheory.MonoidalCategoryStruct.tensorObj SA.X₂ SB.X₂ ⟶ C)
  (μ₃ : CategoryTheory.MonoidalCategoryStruct.tensorObj SA.X₃ SB.X₁ ⟶ C)
  (μ₁ᵥ : (v : ι) → CategoryTheory.MonoidalCategoryStruct.tensorObj (SAᵥ v).X₁ (Rep.res (↑(φ v)) SB.X₃) ⟶ Cᵥ v)
  (μ₂ᵥ : (v : ι) → CategoryTheory.MonoidalCategoryStruct.tensorObj (SAᵥ v).X₂ (Rep.res (↑(φ v)) SB.X₂) ⟶ Cᵥ v)
  (μ₃ᵥ : (v : ι) → CategoryTheory.MonoidalCategoryStruct.tensorObj (SAᵥ v).X₃ (Rep.res (↑(φ v)) SB.X₁) ⟶ Cᵥ v)
  (hμ₁ :
    ∀ (v : ι),
      CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑(φ v)).map μ₁) (c v) =
        CategoryTheory.CategoryStruct.comp
          (Langlands.ProfiniteCohomology.resTensorHom (↑(φ v)) (sA v).τ₁
            (CategoryTheory.CategoryStruct.id (Rep.res (↑(φ v)) SB.X₃)))
          (μ₁ᵥ v)),
  (∀ (v : ι),
      CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑(φ v)).map μ₂) (c v) =
        CategoryTheory.CategoryStruct.comp
          (Langlands.ProfiniteCohomology.resTensorHom (↑(φ v)) (sA v).τ₂
            (CategoryTheory.CategoryStruct.id (Rep.res (↑(φ v)) SB.X₂)))
          (μ₂ᵥ v)) →
    ∀
      (hμ₃ :
        ∀ (v : ι),
          CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑(φ v)).map μ₃) (c v) =
            CategoryTheory.CategoryStruct.comp
              (Langlands.ProfiniteCohomology.resTensorHom (↑(φ v)) (sA v).τ₃
                (CategoryTheory.CategoryStruct.id (Rep.res (↑(φ v)) SB.X₁)))
              (μ₃ᵥ v)),
      CategoryTheory.CategoryStruct.comp
            (CategoryTheory.MonoidalCategoryStruct.tensorHom SA.f (CategoryTheory.CategoryStruct.id SB.X₂)) μ₂ =
          CategoryTheory.CategoryStruct.comp
            (CategoryTheory.MonoidalCategoryStruct.tensorHom (CategoryTheory.CategoryStruct.id SA.X₁) SB.g) μ₁ →
        CategoryTheory.CategoryStruct.comp
              (CategoryTheory.MonoidalCategoryStruct.tensorHom (CategoryTheory.CategoryStruct.id SA.X₂) SB.f) μ₂ =
            CategoryTheory.CategoryStruct.comp
              (CategoryTheory.MonoidalCategoryStruct.tensorHom SA.g (CategoryTheory.CategoryStruct.id SB.X₁)) μ₃ →
          (∀ (v : ι),
              CategoryTheory.CategoryStruct.comp
                  (CategoryTheory.MonoidalCategoryStruct.tensorHom (SAᵥ v).f
                    (CategoryTheory.CategoryStruct.id (Rep.res (↑(φ v)) SB.X₂)))
                  (μ₂ᵥ v) =
                CategoryTheory.CategoryStruct.comp
                  (CategoryTheory.MonoidalCategoryStruct.tensorHom (CategoryTheory.CategoryStruct.id (SAᵥ v).X₁)
                    ((Rep.resFunctor ↑(φ v)).map SB.g))
                  (μ₁ᵥ v)) →
            (∀ (v : ι),
                CategoryTheory.CategoryStruct.comp
                    (CategoryTheory.MonoidalCategoryStruct.tensorHom (CategoryTheory.CategoryStruct.id (SAᵥ v).X₂)
                      ((Rep.resFunctor ↑(φ v)).map SB.f))
                    (μ₂ᵥ v) =
                  CategoryTheory.CategoryStruct.comp
                    (CategoryTheory.MonoidalCategoryStruct.tensorHom (SAᵥ v).g
                      (CategoryTheory.CategoryStruct.id (Rep.res (↑(φ v)) SB.X₁)))
                    (μ₃ᵥ v)) →
              ∀ (hSA : SA.ShortExact) (hSAᵥ : ∀ (v : ι), (SAᵥ v).ShortExact) (hSB : SB.ShortExact) {r s n : ℕ}
                (h₁ : r + 1 + s = n + 1) (h₃ : r + (s + 1) = n + 1)
                (x : ↑(compactSupportCohomology φ SA.X₃ (fun v => (SAᵥ v).X₃) ⋯ r)) (y : ↑⋯), ⋯ = ⋯
```

## Outline of the proofs

`compactCup` is the homology pairing of the cone pairing (`Internal/ConeSigns.lean`) built from the
product of the local cup products and the global cup product (`Internal/LeibnizPairing.lean`),
which are compatible with `localRes`. The compatibility with `localToCompact` is
`coconeLeft_homology_homologyδ` followed by the factorwise computation of the product pairing; the
comparison of the left and right versions is `coconeLeft_homology_eq_coconeRight_homology`; the
compatibility with connecting maps is `LeibnizPairing.homology_δ_add_homology_δ` for the cone
pairings of the two short exact sequences.

## Declarations

`compactCupLeibniz`, `compactCup`, `compactCup_localToCompact`, `compactCupRightLeibniz`,
`compactCupRight`, `cupCochain_tensorHom_eq`, `cupCochain_tensorHom_eq'`,
`compactCup_eq_compactCupRight`, `compactCup_compactSupportδ_add_compactCup_δ`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file
`src/GroundTheory/ProfiniteCohomology/CompactSupportCohomology/CompactCupEqCompactCupRight.lean`.
The repository has no licence file; its text is used with
attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's; the file, named after one of its lemmas, is named for its content; the
foundations' cup products and restriction (`cupPairing`, `resTensorHom`, `map (φ v)`) replace the
source's.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §4, Proposition (1.4.3), pp. 38–39 (cup products commute with
  connecting maps up to the sign `(−1)^p`), for ordinary cohomology.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter II, §2,
  pp. 165–166 (cohomology with compact support as a mapping cone).
