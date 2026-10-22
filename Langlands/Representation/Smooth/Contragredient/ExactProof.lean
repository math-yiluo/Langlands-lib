import Langlands.Representation.Smooth.Contragredient.ExactStatement
import Langlands.Representation.Smooth.Contragredient.CompactDualityProof
import Langlands.Representation.Smooth.FixedVectors.Definitions
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Reversal of short exact sequences by smooth contragredients -/

noncomputable section

namespace Langlands

universe uR uG uV uW uX

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable {W : Type uW} [AddCommGroup W] [Module R W]
variable {X : Type uX} [AddCommGroup X] [Module R X]
variable {ρ : Representation R G V} {σ : Representation R G W}
variable {τ : Representation R G X}

/-- Pullback along a surjection is injective on smooth functionals. -/
theorem contragredientMap_injective_of_surjective (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) : Function.Injective (contragredientMap f) := by
  intro ℓ m h
  apply Subtype.ext
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := hf w
  exact congrArg (fun a : SmoothDual ρ => a.val v) h

/-- Smooth functionals that vanish on the first image descend through the
surjective second map. No smoothness or compactness assumption is needed. -/
theorem contragredientMap_exact_of_surjective (f : ρ.IntertwiningMap σ)
    (g : σ.IntertwiningMap τ) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Exact (contragredientMap g) (contragredientMap f) := by
  intro ℓ
  constructor
  · intro hℓ
    have hker : ℓ.val ∈ (LinearMap.ker g.toLinearMap).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro w hw
      obtain ⟨v, rfl⟩ := (hfg w).mp hw
      exact congrArg (fun a : SmoothDual ρ => a.val v) hℓ
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective
      g.toLinearMap hg] at hker
    obtain ⟨m, hm⟩ := hker
    obtain ⟨K, hK⟩ := ℓ.property
    have hmK (k : K) : τ.dual k.val m = m := by
      apply LinearMap.ext
      intro x
      obtain ⟨w, rfl⟩ := hg x
      change m (τ k.val⁻¹ (g w)) = m (g w)
      rw [← g.isIntertwining]
      have hkw := congrArg (fun a : Module.Dual R W => a w) (hK k)
      change ℓ.val (σ k.val⁻¹ w) = ℓ.val w at hkw
      have hmval (y : W) : m (g y) = ℓ.val y :=
        congrArg (fun a : Module.Dual R W => a y) hm
      simpa only [hmval] using hkw
    refine ⟨⟨m, K, hmK⟩, ?_⟩
    exact Subtype.ext hm
  · rintro ⟨m, rfl⟩
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change m.val (g (f v)) = 0
    rw [hfg.apply_apply_eq_zero, map_zero]

section Complex

variable [Module ℂ V] [Module ℂ W] [Module ℂ X]
variable {ρc : Representation ℂ G V} {σc : Representation ℂ G W}

/-- A smooth functional extends across an injective map of smooth complex
representations when compact open subgroups are cofinal. -/
theorem contragredientMap_surjective_of_injective_of_compact_cofinal
    (hcof : ∀ K : OpenSubgroup G,
      ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsSmooth ρc) (hσ : IsSmooth σc)
    (f : ρc.IntertwiningMap σc) (hf : Function.Injective f) :
    Function.Surjective (contragredientMap f) := by
  intro ℓ
  obtain ⟨J, hJ⟩ := ℓ.property
  obtain ⟨K, hK, hKJ⟩ := hcof J
  have hℓK (k : K) : smoothContragredient ρc k.val ℓ = ℓ :=
    Subtype.ext (hJ ⟨k.val, hKJ k.property⟩)
  let ℓK : fixedVectors (smoothContragredient ρc) K.toSubgroup := ⟨ℓ, hℓK⟩
  have hfK : Function.Injective (fixedVectorsMap f K.toSubgroup) := by
    intro v w h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  obtain ⟨φ, hφ⟩ := LinearMap.dualMap_surjective_of_injective hfK
    (smoothDualFixedRestriction ρc K.toSubgroup ℓK)
  obtain ⟨mK, hmK⟩ :=
    (smoothDualFixedRestriction_bijective σc hσ K hK).2 φ
  let nK : fixedVectors (smoothContragredient ρc) K.toSubgroup :=
    fixedVectorsMap (contragredientMap f) K.toSubgroup mK
  have hnK : nK = ℓK := by
    apply (smoothDualFixedRestriction_bijective ρc hρ K hK).1
    ext v
    have hm := congrArg (fun a => a (fixedVectorsMap f K.toSubgroup v)) hmK
    have hφv := congrArg (fun a => a v) hφ
    exact hm.trans hφv
  exact ⟨mK.val, congrArg Subtype.val hnK⟩

theorem smoothContragredientShortExact
    {G : Type uG} [Group G] [TopologicalSpace G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {X : Type uX} [AddCommGroup X] [Module ℂ X] :
    SmoothContragredientShortExactStatement (G := G) (V := V) (W := W) (X := X) := by
  intro _ hcof ρc σc τc hρ hσ f g hf hfg hg
  exact ⟨contragredientMap_injective_of_surjective g hg,
    contragredientMap_exact_of_surjective f g hfg hg,
    contragredientMap_surjective_of_injective_of_compact_cofinal hcof hρ hσ f hf⟩

end Complex

end Langlands
