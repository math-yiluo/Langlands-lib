import Langlands.GaloisCohomology.CompactSupport.Internal.MappingCocone
import Langlands.Cohomology.Profinite.LongExactSequence

/-!
# Cohomology with compact support of a profinite group relative to a family of homomorphisms

Let `G` be a topological group, `(H_v)_{v ∈ ι}` a family of topological groups with continuous
homomorphisms `φ_v : H_v → G`, `A` a smooth `G`-module, `A_v` smooth `H_v`-modules and
`a_v : Res_{φ_v} A ⟶ A_v`. Restriction followed by the `a_v` is a map of cochain complexes
`localRes : C•(G, A) ⟶ ∏_v C•(H_v, A_v)`; the cochains with compact support are its mapping
cocone, and `H_c^n(G, A)` (`compactSupportCohomology φ A Aᵥ a n`) is its cohomology. There is a
long exact sequence

`⋯ ⟶ H_c^n(G, A) ⟶ Hⁿ(G, A) ⟶ ∏_v Hⁿ(H_v, A_v) ⟶ H_c^{n+1}(G, A) ⟶ ⋯`

(`compactToGlobal`, `globalToLocal`, `localToCompact` and the three exactness theorems), and
`H_c^0(G, A) ⟶ H^0(G, A)` is injective. For `G = G_S` and the local Galois groups at the places
in `S` and the real places this is the cohomology with compact support of arithmetic duality.
-/

namespace Langlands.GaloisCohomology

open Langlands Langlands.ProfiniteCohomology CategoryTheory Limits

universe u

section CompactSupport

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)

section Definitions

variable (A : Rep.{u} k G) [IsSmoothRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsSmoothRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v)

/-- Restriction of cochains to the local groups, followed by the local coefficient maps:
`C•(G, A) → ∏_v C•(H_v, A_v)`. -/
noncomputable def localRes : cochains A ⟶ piComplex fun v => cochains (Aᵥ v) :=
  piLift fun v => cochainsMap (φ v) (a v)

/-- The complex of cochains with compact support: the mapping cocone of `localRes`. -/
noncomputable def compactSupportCochains : CochainComplex (ModuleCat.{u} k) ℕ :=
  mappingCoconeNat (localRes φ A Aᵥ a)

/-- Cohomology with compact support `H_c^n(G, A)`. -/
noncomputable def compactSupportCohomology (n : ℕ) : ModuleCat.{u} k :=
  (compactSupportCochains φ A Aᵥ a).homology n

/-- Cohomology with compact support when the local modules are the restrictions of `A`. -/
noncomputable abbrev compactSupportCohomologyRes (n : ℕ) : ModuleCat.{u} k :=
  compactSupportCohomology φ A (fun v => Rep.res (φ v : H v →* G) A) (fun _ => 𝟙 _) n

end Definitions

section LongExactSequence

variable (A : Rep.{u} k G) [IsSmoothRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsSmoothRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v)

/-- The map `H_c^n(G, A) ⟶ Hⁿ(G, A)` (projection of the mapping cocone). -/
noncomputable def compactToGlobal (n : ℕ) : compactSupportCohomology φ A Aᵥ a n ⟶ cohomology A n :=
  HomologicalComplex.homologyMap (mappingCoconeNat.fst (localRes φ A Aᵥ a)) n

/-- The localization `Hⁿ(G, A) ⟶ ∏_v Hⁿ(H_v, A_v)`: restriction along `φ_v` followed by `a_v`. -/
noncomputable def globalToLocal (n : ℕ) :
    cohomology A n ⟶ ModuleCat.of k (∀ v, cohomology (Aᵥ v) n) :=
  ModuleCat.ofHom (LinearMap.pi fun v =>
    (map (φ v) (a v) n).hom)

/-- The homology of the product of the local cochain complexes is the product of the local
cohomology groups. -/
noncomputable abbrev localCohomologyIso (n : ℕ) :
    (piComplex fun v => cochains (Aᵥ v)).homology n ≅
      ModuleCat.of k (∀ v, cohomology (Aᵥ v) n) :=
  piHomologyIso _ n

theorem homologyMap_localRes_localCohomologyIso_hom (n : ℕ) :
    HomologicalComplex.homologyMap (localRes φ A Aᵥ a) n ≫ (localCohomologyIso Aᵥ n).hom =
      globalToLocal φ A Aᵥ a n :=
  homologyMap_piLift_piHomologyIso_hom _ _ n

/-- The connecting map `∏_v Hⁿ(H_v, A_v) ⟶ H_c^{n+1}(G, A)` of the mapping cocone. -/
noncomputable def localToCompact (n : ℕ) :
    ModuleCat.of k (∀ v, cohomology (Aᵥ v) n) ⟶ compactSupportCohomology φ A Aᵥ a (n + 1) :=
  (localCohomologyIso Aᵥ n).inv ≫ mappingCoconeNat.homologyδ (localRes φ A Aᵥ a) n

@[reassoc (attr := simp)]
theorem compactToGlobal_globalToLocal (n : ℕ) :
    compactToGlobal φ A Aᵥ a n ≫ globalToLocal φ A Aᵥ a n = 0 := by
  have h := mappingCoconeNat.homologyMap_fst_homologyMap_assoc (localRes φ A Aᵥ a) n
    (localCohomologyIso Aᵥ n).hom
  rw [homologyMap_localRes_localCohomologyIso_hom, zero_comp] at h
  exact h

@[reassoc (attr := simp)]
theorem globalToLocal_localToCompact (n : ℕ) :
    globalToLocal φ A Aᵥ a n ≫ localToCompact φ A Aᵥ a n = 0 := by
  have h := mappingCoconeNat.homologyMap_homologyδ (localRes φ A Aᵥ a) n
  rw [← Iso.hom_inv_id_assoc (localCohomologyIso Aᵥ n) (mappingCoconeNat.homologyδ _ n),
    ← Category.assoc, homologyMap_localRes_localCohomologyIso_hom] at h
  exact h

@[reassoc (attr := simp)]
theorem localToCompact_compactToGlobal (n : ℕ) :
    localToCompact φ A Aᵥ a n ≫ compactToGlobal φ A Aᵥ a (n + 1) = 0 := by
  have h := congrArg ((localCohomologyIso Aᵥ n).inv ≫ ·)
    (mappingCoconeNat.homologyδ_homologyMap_fst (localRes φ A Aᵥ a) n)
  simp only [comp_zero, ← Category.assoc] at h
  exact h

/-- Exactness at `Hⁿ(G, A)`: `H_c^n(G, A) ⟶ Hⁿ(G, A) ⟶ ∏_v Hⁿ(H_v, A_v)`. -/
theorem compactSupportCohomology_exact_global (n : ℕ) :
    (ShortComplex.mk _ _ (compactToGlobal_globalToLocal φ A Aᵥ a n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (mappingCoconeNat.homology_exact₃ (localRes φ A Aᵥ a) n)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (localCohomologyIso Aᵥ n)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (homologyMap_localRes_localCohomologyIso_hom φ A Aᵥ a n).symm)

/-- Exactness at `∏_v Hⁿ(H_v, A_v)`: `Hⁿ(G, A) ⟶ ∏_v Hⁿ(H_v, A_v) ⟶ H_c^{n+1}(G, A)`. -/
theorem compactSupportCohomology_exact_local (n : ℕ) :
    (ShortComplex.mk _ _ (globalToLocal_localToCompact φ A Aᵥ a n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (mappingCoconeNat.homology_exact₁ (localRes φ A Aᵥ a) n)
  exact ShortComplex.isoMk (Iso.refl _) (localCohomologyIso Aᵥ n) (Iso.refl _)
    ((Category.id_comp _).trans (homologyMap_localRes_localCohomologyIso_hom φ A Aᵥ a n).symm)
    ((Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm)

/-- Exactness at `H_c^{n+1}(G, A)`: `∏_v Hⁿ(H_v, A_v) ⟶ H_c^{n+1}(G, A) ⟶ H^{n+1}(G, A)`. -/
theorem compactSupportCohomology_exact_compact (n : ℕ) :
    (ShortComplex.mk _ _ (localToCompact_compactToGlobal φ A Aᵥ a n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (mappingCoconeNat.homology_exact₂ (localRes φ A Aᵥ a) n)
  exact ShortComplex.isoMk (localCohomologyIso Aᵥ n) (Iso.refl _) (Iso.refl _)
    ((Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- `H_c^0(G, A) ⟶ H^0(G, A)` is injective. -/
theorem mono_compactToGlobal_zero : Mono (compactToGlobal φ A Aᵥ a 0) :=
  mappingCoconeNat.mono_homologyMap_fst_zero _

end LongExactSequence


end CompactSupport

end Langlands.GaloisCohomology
