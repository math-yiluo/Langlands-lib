import Langlands.Representation.CompactCoefficient.AdmissibleLifting
import Langlands.Representation.CompactCoefficient.SemisimplicityProof
import Langlands.Representation.Smooth.Contragredient.HomDualityProof
import Langlands.Representation.Smooth.Contragredient.ExactProof
import Langlands.Representation.Smooth.Contragredient.LawsProof

/-!
# Retractions of embeddings of compact irreducible admissible representations

The smooth contragredient of an irreducible admissible representation with
compact smooth-dual coefficients is again irreducible, admissible and has
compact smooth-dual coefficients. Dualizing the lifting property of
`AdmissibleLifting` for the contragredient gives a retraction of every
embedding into a smooth representation.
-/

noncomputable section

namespace Langlands.CompactSplitting

open MeasureTheory

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

section Averaging

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A linear map that is constant on a finite orbit takes that constant value
at the orbit mean. -/
theorem map_orbitMean_of_constant (ρ : Representation ℂ G V) (v : V)
    [Finite (Compact.orbit ρ v)] (f : V →ₗ[ℂ] ℂ) (c : ℂ)
    (hf : ∀ g, f (ρ g v) = c) : f (Compact.orbitMean ρ v) = c := by
  classical
  let := Fintype.ofFinite (Compact.orbit ρ v)
  have hx (x : Compact.orbit ρ v) : f x.val = c := by
    obtain ⟨g, hg⟩ := x.property
    exact (congrArg f hg).symm.trans (hf g)
  have hcard : (Fintype.card (Compact.orbit ρ v) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [Compact.orbitMean_eq_finiteMean]
  change f ((Fintype.card (Compact.orbit ρ v) : ℂ)⁻¹ • ∑ x : Compact.orbit ρ v, x.val) = c
  rw [map_smul, map_sum]
  simp only [hx, Finset.sum_const, Finset.card_univ, smul_eq_mul, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- Averaging a smooth functional over a compact open subgroup `K` does not
change its values on `K`-fixed vectors. -/
theorem averageMap_smoothDual_apply (ρ : Representation ℂ G V) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (u : SmoothDual ρ) {x : V}
    (hx : x ∈ fixedVectors ρ K.toSubgroup) :
    (Compact.averageMap (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K hK
      u).val x = u.val x := by
  let := Compact.finite_orbit_of_smooth (smoothContragredient ρ)
    (isSmooth_smoothContragredient ρ) K hK u
  exact map_orbitMean_of_constant ((smoothContragredient ρ).comp K.toSubgroup.subtype) u
    ((smoothDualPairing ρ).flip x) (u.val x) (fun k => by
      change smoothDualPairing ρ (smoothContragredient ρ k.val u) x = u.val x
      rw [smoothDualPairing_action]
      have hk : ρ (k⁻¹ : K).val x = x := hx k⁻¹
      exact congrArg u.val hk)

end Averaging

section Contragredient

variable (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
include hcof

/-- The smooth contragredient of an irreducible admissible representation is
irreducible. -/
theorem isIrreducible_smoothContragredient (ρ : Representation ℂ G V)
    (hρ : IsAdmissible ρ) (hirr : ρ.IsIrreducible) :
    (smoothContragredient ρ).IsIrreducible := by
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨ℓ₀, hℓ₀, hℓ₀v⟩ := exists_smooth_functional_ne_zero hcof ρ hρ.1 hv₀
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    have hmem : (⟨ℓ₀, hℓ₀⟩ : SmoothDual ρ) ∈ (⊤ : Subrepresentation (smoothContragredient ρ)) :=
      Submodule.mem_top (R := ℂ) (M := SmoothDual ρ)
    rw [← h] at hmem
    have h0 : (⟨ℓ₀, hℓ₀⟩ : SmoothDual ρ) = 0 := (Submodule.mem_bot ℂ).1 hmem
    apply hℓ₀v
    have h1 := congrArg (fun ℓ : SmoothDual ρ => ℓ.val v₀) h0
    simpa using h1
  intro U
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  -- The common kernel of `U` is a subrepresentation of `ρ`.
  let U' : Subrepresentation ρ :=
    { toSubmodule := ⨅ u : U.toSubmodule, LinearMap.ker u.val.val
      apply_mem_toSubmodule := fun g v hv => by
        rw [Submodule.mem_iInf] at hv ⊢
        intro u
        have hu : smoothContragredient ρ g⁻¹ u.val ∈ U.toSubmodule :=
          U.apply_mem_toSubmodule g⁻¹ u.property
        have h := hv ⟨_, hu⟩
        rw [LinearMap.mem_ker] at h ⊢
        change smoothDualPairing ρ (smoothContragredient ρ g⁻¹ u.val) v = 0 at h
        rw [smoothDualPairing_action, inv_inv] at h
        exact h }
  have hmemU' (v : V) : v ∈ U' ↔ ∀ u ∈ U, u.val v = 0 := by
    change v ∈ (⨅ u : U.toSubmodule, LinearMap.ker u.val.val) ↔ _
    rw [Submodule.mem_iInf]
    exact ⟨fun h u hu => h ⟨u, hu⟩, fun h u => h u.val u.property⟩
  have hU'bot : U' = ⊥ := by
    rcases (hirr.eq_bot_or_eq_top U') with h | h
    · exact h
    · exfalso
      apply hU
      rw [eq_bot_iff]
      intro u hu
      have hzero : u = 0 := by
        apply Subtype.ext
        apply LinearMap.ext
        intro v
        have hv : v ∈ U' := by
          rw [h]
          exact Submodule.mem_top (R := ℂ) (M := V)
        exact (hmemU' v).1 hv u hu
      rw [hzero]
      exact Submodule.zero_mem (R := ℂ) (M := SmoothDual ρ) _
  rw [eq_top_iff]
  intro η _
  obtain ⟨J, hJ⟩ := η.property
  obtain ⟨K, hK, hKJ⟩ := hcof J
  have hηK : η ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup :=
    fun k => Subtype.ext (hJ ⟨k.val, hKJ k.property⟩)
  let X := fixedVectors ρ K.toSubgroup
  let : Module.Finite ℂ X := hρ.2 K
  let r := smoothDualFixedRestriction ρ K.toSubgroup
  let S : Submodule ℂ (Module.Dual ℂ X) :=
    Submodule.map r (U.toSubmodule.comap
      (fixedVectors (smoothContragredient ρ) K.toSubgroup).subtype)
  have hScoann : S.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    rw [Submodule.mem_bot]
    apply Subtype.ext
    have hxU' : x.val ∈ U' := by
      rw [hmemU']
      intro u hu
      let a := Compact.averageMap (smoothContragredient ρ)
        (isSmooth_smoothContragredient ρ) K hK u
      have haU : a ∈ U := CompactCoefficientSemisimplicity.averageMap_mem _ _ K hK U hu
      have haK : a ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup :=
        Compact.averageMap_mem_fixedVectors _ _ K hK u
      have h := hx (r ⟨a, haK⟩) ⟨⟨a, haK⟩, haU, rfl⟩
      rw [← averageMap_smoothDual_apply ρ K hK u x.property]
      exact h
    rw [hU'bot] at hxU'
    exact (Submodule.mem_bot ℂ).1 hxU'
  have hS : S = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := S), hScoann,
      Submodule.dualAnnihilator_bot]
  have hmem : r ⟨η, hηK⟩ ∈ S := by
    rw [hS]
    exact Submodule.mem_top
  obtain ⟨u, hu, hru⟩ := hmem
  have heq : u = ⟨η, hηK⟩ :=
    (smoothDualFixedRestriction_bijective ρ hρ.1 K hK).1 hru
  have h' : u.val = η := congrArg Subtype.val heq
  rw [← h']
  exact hu

/-- The smooth contragredient of an admissible representation with compact
smooth-dual coefficients has compact smooth-dual coefficients. -/
theorem hasCompactSmoothDualCoefficients_smoothContragredient
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (hc : HasCompactSmoothDualCoefficients ρ) :
    HasCompactSmoothDualCoefficients (smoothContragredient ρ) := by
  intro ξ Ξ hΞ
  obtain ⟨v, hv⟩ := smoothBidual_surjective_of_compact_cofinal hcof ρ hρ ⟨Ξ, hΞ⟩
  have hcoeff : matrixCoefficient (smoothContragredient ρ) Ξ ξ =
      (matrixCoefficient ρ ξ.val v) ∘ (Homeomorph.inv G) := by
    funext g
    have h := congrArg (fun ψ : SmoothDual (smoothContragredient ρ) =>
      ψ.val (smoothContragredient ρ g ξ)) hv
    change smoothDualPairing (smoothContragredient ρ) (smoothBidual hρ.1 v)
      (smoothContragredient ρ g ξ) = Ξ (smoothContragredient ρ g ξ) at h
    rw [smoothBidual_apply, smoothDualPairing_action] at h
    exact h.symm
  rw [hcoeff]
  exact (hc v ξ.val ξ.property).comp_homeomorph (Homeomorph.inv G)

theorem smoothBidual_bijective_of_compact_cofinal (ρ : Representation ℂ G V)
    (hρ : IsAdmissible ρ) : Function.Bijective (smoothBidual hρ.1) :=
  ⟨smoothBidual_injective_of_compact_cofinal hcof ρ hρ.1,
    smoothBidual_surjective_of_compact_cofinal hcof ρ hρ⟩

variable [MeasurableSpace G] [BorelSpace G]

/-- Every embedding of an irreducible admissible representation with compact
smooth-dual coefficients into a smooth representation has an equivariant
retraction. -/
theorem exists_retraction (μ : Measure G) [μ.IsHaarMeasure]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (hirr : ρ.IsIrreducible)
    (hc : HasCompactSmoothDualCoefficients ρ)
    {σ : Representation ℂ G W} (hσ : IsSmooth σ) (j : ρ.IntertwiningMap σ)
    (hj : Function.Injective j) :
    ∃ r : σ.IntertwiningMap ρ, r.comp j = Representation.IntertwiningMap.id ρ := by
  have hsurj : Function.Surjective (contragredientMap j) :=
    contragredientMap_surjective_of_injective_of_compact_cofinal hcof hρ.1 hσ j hj
  obtain ⟨t, ht⟩ := exists_section μ hcof (smoothContragredient ρ)
    (isAdmissible_smoothContragredient_of_compact_cofinal hcof ρ hρ)
    (isIrreducible_smoothContragredient hcof ρ hρ hirr)
    (hasCompactSmoothDualCoefficients_smoothContragredient hcof ρ hρ hc)
    (isSmooth_smoothContragredient σ) (contragredientMap j) hsurj
  have hb := smoothBidual_bijective_of_compact_cofinal hcof ρ hρ
  obtain ⟨r, hr⟩ := (contragredientMap_bijective_of_bidual hσ hρ.1 hb).2 t
  replace hr : contragredientMap r = t := hr
  refine ⟨r, ?_⟩
  apply (contragredientMap_bijective_of_bidual hρ.1 hρ.1 hb).1
  change contragredientMap (r.comp j) =
    contragredientMap (Representation.IntertwiningMap.id ρ)
  rw [contragredientMap_comp, contragredientMap_id, hr, ht]

end Contragredient

end Langlands.CompactSplitting
