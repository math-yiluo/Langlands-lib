import Langlands.LocalFactor.Ramification.Herbrand.LocalRelativePsiIndependenceProof
import Langlands.LocalFactor.Ramification.Herbrand.LocalFiniteSubgroupProof

/-!
# Herbrand's subgroup formula for the absolute Galois group of a finite subextension

For a finite intermediate field `E` of a separable closure `Ω/K`, the upper filtration
of `K` on `Aut_E(Ω)` is the upper filtration of `E` reindexed by `ψ_{E/K}`
(Serre, *Local Fields*, IV §3, Remarks 1–3). Both absolute groups are tested on finite
Galois fields. Herbrand's quotient theorem for arbitrary realizations
(`upperRestrictionCompatibility`) passes from larger to smaller finite Galois fields, and,
applied to the identity of carriers between `M` over `K` and `M` viewed over `E`,
compares the two canonical realizations of `M`. In one realization the finite subgroup
formula gives the index `φ_{M/E}(ψ_{M/K}(u))`, which is `ψ_{E/K}(u)` by
`relativeHerbrandPsiIndependence`.
-/

noncomputable section

namespace Langlands.Ramification.Local

universe u₀ uK uE uL uΩ

section Restriction

variable {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
  (K : Type uK) [Field K] [Algebra K₀ K]
  (L : Type uL) [Field L] [Algebra K₀ L] [FiniteDimensional K₀ L]
  [Algebra K L] [IsScalarTower K₀ K L]
  (E : Type uE) [Field E] [Algebra K₀ E] [FiniteDimensional K₀ E]
  [Algebra K E] [Algebra E L] [IsScalarTower K₀ K E]
  [IsScalarTower K E L] [IsGalois K L] [IsGalois K E] [IsGalois E L]

omit [IsGalois K L] [IsGalois E L] in
/-- An automorphism `ρ'` of `E` compatible with `ρ` along `E → L` is the normal
restriction of `ρ`. -/
theorem restrictNormalHom_eq_of_commutes (ρ : L ≃ₐ[K] L) (ρ' : E ≃ₐ[K] E)
    (h : ∀ x : E, algebraMap E L (ρ' x) = ρ (algebraMap E L x)) :
    AlgEquiv.restrictNormalHom E ρ = ρ' :=
  AlgEquiv.ext fun x => (algebraMap E L).injective
    ((AlgEquiv.restrictNormal_commutes ρ E x).trans (h x).symm)

/-- Restriction along `E → L` preserves the upper groups at indices `v ≥ -1`, for any
realizations `T` of `L` and `S` of `E`. -/
theorem mem_upperRamificationGroup_of_commutes (T : LocalField.TopologicalData K₀ L)
    (S : LocalField.TopologicalData K₀ E) {v : ℝ} (hv : -1 ≤ v)
    (ρ : L ≃ₐ[K] L) (ρ' : E ≃ₐ[K] E)
    (h : ∀ x : E, algebraMap E L (ρ' x) = ρ (algebraMap E L x))
    (hρ : ρ ∈ upperRamificationGroup T K v) :
    ρ' ∈ upperRamificationGroup S K v := by
  rw [← upperRestrictionCompatibility K L E T S v hv,
    ← restrictNormalHom_eq_of_commutes K L E ρ ρ' h]
  exact Subgroup.mem_map_of_mem _ hρ

/-- When `E → L` is surjective, restriction identifies the upper groups. -/
theorem mem_upperRamificationGroup_iff_of_surjective
    (hsurj : Function.Surjective (algebraMap E L))
    (T : LocalField.TopologicalData K₀ L)
    (S : LocalField.TopologicalData K₀ E) {v : ℝ} (hv : -1 ≤ v)
    (ρ : L ≃ₐ[K] L) (ρ' : E ≃ₐ[K] E)
    (h : ∀ x : E, algebraMap E L (ρ' x) = ρ (algebraMap E L x)) :
    ρ' ∈ upperRamificationGroup S K v ↔ ρ ∈ upperRamificationGroup T K v := by
  refine ⟨fun hρ' => ?_, mem_upperRamificationGroup_of_commutes K L E T S hv ρ ρ' h⟩
  rw [← upperRestrictionCompatibility K L E T S v hv] at hρ'
  obtain ⟨ρ₁, hρ₁, heq⟩ := hρ'
  have hρ₁ρ : ρ₁ = ρ := by
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    rw [← AlgEquiv.restrictNormal_commutes ρ₁ E x, ← h x]
    exact congrArg (algebraMap E L) (congrArg (fun σ : E ≃ₐ[K] E => σ x) heq)
  exact hρ₁ρ ▸ hρ₁

end Restriction

section Ambient

variable (K₀ : Type u₀) [NontriviallyNormedField K₀] [IsUltrametricDist K₀]
  [CompleteSpace K₀] [ValuativeRel K₀] [LocallyCompactSpace K₀]
  (F : Type uK) [Field F] [Algebra K₀ F] [FiniteDimensional K₀ F]
  {Ω : Type uΩ} [Field Ω] [Algebra F Ω] [Algebra K₀ Ω] [IsScalarTower K₀ F Ω]
  (hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b)

/-- Restriction from a larger finite Galois subfield of `Ω/F` to a smaller one preserves
the canonical upper groups at indices `v ≥ -1`. -/
theorem restrictNormalHom_mem_canonicalUpperRamificationGroup_of_le
    {N M : FiniteGaloisIntermediateField F Ω} (hNM : N ≤ M) {v : ℝ} (hv : -1 ≤ v)
    (τ : Ω ≃ₐ[F] Ω)
    (hτ : AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) M τ ∈
      canonicalUpperRamificationGroup K₀ M hbase F v) :
    haveI : FiniteDimensional K₀ N := FiniteDimensional.trans K₀ F N
    AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) N τ ∈
      canonicalUpperRamificationGroup K₀ N hbase F v := by
  have : FiniteDimensional K₀ N := FiniteDimensional.trans K₀ F N
  have : FiniteDimensional K₀ M := FiniteDimensional.trans K₀ F M
  let : Algebra N M := (IntermediateField.inclusion
    ((FiniteGaloisIntermediateField.le_iff N M).mp hNM)).toRingHom.toAlgebra
  let : IsScalarTower F N M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsGalois N M := IsGalois.tower_top_of_isGalois F N M
  refine mem_upperRamificationGroup_of_commutes F M N
    (LocalField.canonicalTopologicalData K₀ M hbase)
    (LocalField.canonicalTopologicalData K₀ N hbase) hv
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) M τ)
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) N τ) (fun x => ?_) hτ
  apply Subtype.ext
  change (AlgEquiv.restrictNormalHom N.toIntermediateField τ x : Ω) =
    (AlgEquiv.restrictNormalHom M.toIntermediateField τ (algebraMap N M x) : Ω)
  rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
  rfl

end Ambient

section Subextension

variable (K₀ : Type u₀) [NontriviallyNormedField K₀] [IsUltrametricDist K₀]
  [CompleteSpace K₀] [ValuativeRel K₀] [LocallyCompactSpace K₀]
  (K : Type uK) [Field K] [Algebra K₀ K] [FiniteDimensional K₀ K]
  {Ω : Type uΩ} [Field Ω] [Algebra K Ω] [Algebra K₀ Ω] [IsScalarTower K₀ K Ω]
  (hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b)
  (E : IntermediateField K Ω)

/-- The relative index fixes the endpoint `-1` and is monotone, so it maps `[-1, ∞)`
into itself. -/
theorem neg_one_le_relativeIndex (M : FiniteGaloisIntermediateField K Ω)
    (h : ∀ x : E, algebraMap E Ω x ∈ M.toIntermediateField) {u : ℝ} (hu : -1 ≤ u) :
    haveI : IsScalarTower K₀ E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    (-1 : ℝ) ≤ relativeIndex K₀ K hbase M h u := by
  let : IsScalarTower K₀ E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let N := extendFiniteGalois h
  have : FiniteDimensional K N := M.finiteDimensional
  let : IsScalarTower K₀ K N := IsScalarTower.of_algebraMap_eq fun a => Subtype.ext
    (IsScalarTower.algebraMap_apply K₀ K Ω a)
  have : FiniteDimensional K₀ N := FiniteDimensional.trans K₀ K N
  let T := LocalField.canonicalTopologicalData K₀ N hbase
  change -1 ≤ herbrandPhi T E (herbrandPsi T K u)
  have h1 := (herbrandPsi_strictMono T K).monotone hu
  have h2 := (herbrandPhi_strictMono T E).monotone h1
  rwa [herbrandPsi_neg_one, herbrandPhi_neg_one] at h2

/-- Herbrand's subgroup formula at one finite Galois field `M ⊇ E` of `Ω/K`: the
restriction of `τ` to `M` is in the upper group of `M/K` at `u` exactly when its
restriction to `M`, viewed over `E`, is in the upper group of `M/E` at the relative
index `φ_{M/E}(ψ_{M/K}(u))`. The two canonical realizations of `M` live on the
carriers of `M` and of `extendFiniteGalois h`; they are compared by the quotient
theorem for the trivial extension between these carriers. -/
theorem restrictNormalHom_restrictScalars_mem_iff [FiniteDimensional K E]
    (M : FiniteGaloisIntermediateField K Ω)
    (h : ∀ x : E, algebraMap E Ω x ∈ M.toIntermediateField) {u : ℝ} (hu : -1 ≤ u)
    (τ : Ω ≃ₐ[E] Ω) :
    haveI : FiniteDimensional K₀ E := FiniteDimensional.trans K₀ K E
    haveI : IsScalarTower K₀ E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M (τ.restrictScalars K) ∈
        canonicalUpperRamificationGroup K₀ M hbase K u ↔
      AlgEquiv.restrictNormalHom (F := E) (K₁ := Ω) (extendFiniteGalois h) τ ∈
        canonicalUpperRamificationGroup K₀ (extendFiniteGalois h) hbase E
          (relativeIndex K₀ K hbase M h u) := by
  have : FiniteDimensional K₀ E := FiniteDimensional.trans K₀ K E
  let : IsScalarTower K₀ E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let N := extendFiniteGalois h
  have : FiniteDimensional K N := M.finiteDimensional
  have : IsGalois K N := M.isGalois
  let : IsScalarTower K₀ K N := IsScalarTower.of_algebraMap_eq fun a => Subtype.ext
    (IsScalarTower.algebraMap_apply K₀ K Ω a)
  have : FiniteDimensional K₀ N := FiniteDimensional.trans K₀ K N
  have : FiniteDimensional K₀ M := FiniteDimensional.trans K₀ K M
  let : Algebra M N := (extendFiniteGaloisEquiv h).toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower K M N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsGalois M N := IsGalois.tower_top_of_isGalois K M N
  let T := LocalField.canonicalTopologicalData K₀ N hbase
  have hsurj : Function.Surjective (algebraMap M N) := (extendFiniteGaloisEquiv h).surjective
  refine (mem_upperRamificationGroup_iff_of_surjective K N M hsurj T
    (LocalField.canonicalTopologicalData K₀ M hbase) hu
    ((AlgEquiv.restrictNormalHom (F := E) (K₁ := Ω) N τ).restrictScalars K)
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M (τ.restrictScalars K))
    (fun x => ?_)).trans ?_
  · apply Subtype.ext
    change (AlgEquiv.restrictNormalHom M.toIntermediateField (τ.restrictScalars K) x : Ω) =
      (AlgEquiv.restrictNormalHom N.toIntermediateField τ (algebraMap M N x) : Ω)
    rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
    rfl
  · exact finiteHerbrandSubgroupFormula K₀ K E N T u
      (AlgEquiv.restrictNormalHom (F := E) (K₁ := Ω) N τ)

end Subextension

/-- Herbrand's subgroup formula `G_K^u ∩ G_E = G_E^{ψ_{E/K}(u)}` for `u ≥ -1` and a
finite subextension `E/K` of a separable closure, over any complete, locally compact,
nontrivially and ultrametrically normed base, in either characteristic. -/
theorem absoluteHerbrandSubgroupFormula : AbsoluteHerbrandSubgroupFormula.{u₀, uK, uΩ} := by
  intro K₀ _ _ _ _ _ K _ _ _ Ω _ _ _ _ _ hbase E _ u hu τ
  have : FiniteDimensional K₀ E := FiniteDimensional.trans K₀ K E
  let : IsScalarTower K₀ E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsSepClosure E Ω :=
    ⟨IsSepClosure.sep_closed K, (IsGalois.tower_top_of_isGalois K E Ω).to_isSeparable⟩
  have hψ : -1 ≤ relativeHerbrandPsi K₀ K Ω hbase E u :=
    neg_one_le_relativeIndex K₀ K hbase E (galoisClosure E) (algebraMap_mem_galoisClosure E) hu
  rw [mem_absoluteUpperRamificationGroup_iff, mem_absoluteUpperRamificationGroup_iff]
  constructor
  · intro H N
    have : FiniteDimensional K N := FiniteDimensional.trans K E N
    let : IsScalarTower K N Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let M : FiniteGaloisIntermediateField K Ω :=
      { toIntermediateField := IntermediateField.normalClosure K N Ω
        finiteDimensional := normalClosure.is_finiteDimensional K N Ω
        isGalois := IsGalois.normalClosure K N Ω }
    have hNM : ∀ x ∈ N.toIntermediateField, x ∈ M.toIntermediateField := fun x hx =>
      (IsScalarTower.toAlgHom K N Ω).fieldRange_le_normalClosure ⟨⟨x, hx⟩, rfl⟩
    have h : ∀ x : E, algebraMap E Ω x ∈ M.toIntermediateField := fun x =>
      hNM _ (N.toIntermediateField.algebraMap_mem x)
    have h1 := (restrictNormalHom_restrictScalars_mem_iff K₀ K hbase E M h hu τ).mp (H M)
    rw [← relativeHerbrandPsiIndependence K₀ K Ω hbase E M h u] at h1
    exact restrictNormalHom_mem_canonicalUpperRamificationGroup_of_le K₀ E hbase
      ((FiniteGaloisIntermediateField.le_iff N (extendFiniteGalois h)).mpr
        fun x hx => hNM x hx) hψ τ h1
  · intro H L
    let M := L ⊔ galoisClosure E
    have h : ∀ x : E, algebraMap E Ω x ∈ M.toIntermediateField := fun x =>
      (FiniteGaloisIntermediateField.le_iff _ _).mp le_sup_right
        (algebraMap_mem_galoisClosure E x)
    have h1 := H (extendFiniteGalois h)
    rw [relativeHerbrandPsiIndependence K₀ K Ω hbase E M h u] at h1
    exact restrictNormalHom_mem_canonicalUpperRamificationGroup_of_le K₀ K hbase
      (le_sup_left : L ≤ M) hu (τ.restrictScalars K)
      ((restrictNormalHom_restrictScalars_mem_iff K₀ K hbase E M h hu τ).mpr h1)

end Langlands.Ramification.Local
