import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityStatement
import Langlands.Representation.Smooth.Contragredient.CompactDualityProof
import Langlands.Representation.Smooth.Admissibility.CofinalProof
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Smooth separation, admissibility and bidual reflexivity -/

noncomputable section

namespace Langlands

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

private theorem dual_smooth (ρ : Representation ℂ G V) :
    IsSmooth (smoothContragredient ρ) := by
  intro ℓ
  obtain ⟨K, hK⟩ := ℓ.property
  exact ⟨K, fun k => Subtype.ext (hK k)⟩

/-- A cofinal supply of compact open subgroups makes the smooth dual separating. -/
theorem smoothBidual_injective_of_compact_cofinal
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) :
    Function.Injective (smoothBidual hρ) := by
  have hzero (v : V) (hv : smoothBidual hρ v = 0) : v = 0 := by
    obtain ⟨K, hKv⟩ := hρ v
    obtain ⟨L, hL, hLK⟩ := hcofinal K
    have hLv : v ∈ fixedVectors ρ L.toSubgroup :=
      fun l => hKv ⟨l, hLK l.property⟩
    let u : fixedVectors ρ L.toSubgroup := ⟨v, hLv⟩
    have hu : u = 0 := by
      apply Module.eval_apply_injective ℂ
      apply LinearMap.ext
      intro φ
      change φ u = φ 0
      obtain ⟨ℓ, hℓ⟩ := (smoothDualFixedRestriction_bijective ρ hρ L hL).2 φ
      have heval := congrArg
        (fun ψ : SmoothDual (smoothContragredient ρ) => ψ.val ℓ.val) hv
      change ℓ.val.val v = 0 at heval
      calc
        φ u = ℓ.val.val v := (congrArg (fun f => f u) hℓ).symm
        _ = 0 := heval
        _ = φ 0 := (map_zero φ).symm
    exact congrArg Subtype.val hu
  intro v w hvw
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hvw, sub_self]

/-- The cofinal fixed-vector criterion transfers admissibility to the smooth dual. -/
theorem isAdmissible_smoothContragredient_of_compact_cofinal
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) :
    IsAdmissible (smoothContragredient ρ) := by
  apply (isAdmissible_iff_of_cofinal {K | IsCompact (K : Set G)} hcofinal).2
  refine ⟨dual_smooth ρ, ?_⟩
  intro K hK
  let : Module.Finite ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
  exact Module.Finite.of_injective (smoothDualFixedRestriction ρ K.toSubgroup)
    (smoothDualFixedRestriction_bijective ρ hρ.1 K hK).1

/-- Finite-dimensional reflexivity on each compact-open fixed space gives
surjectivity of the canonical smooth bidual map. -/
theorem smoothBidual_surjective_of_compact_cofinal
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) :
    Function.Surjective (smoothBidual hρ.1) := by
  intro ψ
  obtain ⟨H, hH⟩ := ψ.property
  obtain ⟨K, hK, hKH⟩ := hcofinal H
  have hψ : ψ ∈ fixedVectors (smoothContragredient (smoothContragredient ρ))
      K.toSubgroup := fun k => Subtype.ext (hH ⟨k, hKH k.property⟩)
  let ψK : fixedVectors (smoothContragredient (smoothContragredient ρ))
      K.toSubgroup := ⟨ψ, hψ⟩
  let U := fixedVectors ρ K.toSubgroup
  let : Module.Finite ℂ U := hρ.2 K
  let e : fixedVectors (smoothContragredient ρ) K.toSubgroup ≃ₗ[ℂ]
      Module.Dual ℂ U :=
    LinearEquiv.ofBijective (smoothDualFixedRestriction ρ K.toSubgroup)
      (smoothDualFixedRestriction_bijective ρ hρ.1 K hK)
  let η : Module.Dual ℂ (Module.Dual ℂ U) :=
    (smoothDualFixedRestriction (smoothContragredient ρ) K.toSubgroup ψK).comp
      e.symm.toLinearMap
  let u : U := (Module.evalEquiv ℂ U).symm η
  have hu (ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup) :
      ℓ.val.val u.val = ψ.val ℓ.val := by
    calc
      ℓ.val.val u.val = (e ℓ) u := rfl
      _ = η (e ℓ) := Module.apply_evalEquiv_symm_apply ℂ U (e ℓ) η
      _ = ψ.val ℓ.val := by
        simp only [η, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply]
        rfl
  have hz : smoothBidual hρ.1 u.val ∈
      fixedVectors (smoothContragredient (smoothContragredient ρ)) K.toSubgroup := by
    intro k
    change smoothContragredient (smoothContragredient ρ) k.val
      (smoothBidual hρ.1 u.val) = smoothBidual hρ.1 u.val
    exact ((smoothBidual hρ.1).isIntertwining _ _ k.val u.val).symm.trans
      (congrArg (smoothBidual hρ.1) (u.property k))
  let z : fixedVectors (smoothContragredient (smoothContragredient ρ))
      K.toSubgroup := ⟨smoothBidual hρ.1 u.val, hz⟩
  have heq : z = ψK := by
    apply (smoothDualFixedRestriction_bijective
      (smoothContragredient ρ) (dual_smooth ρ) K hK).1
    apply LinearMap.ext
    intro ℓ
    exact hu ℓ
  exact ⟨u.val, congrArg Subtype.val heq⟩

omit [IsTopologicalGroup G] in
theorem smoothAdmissibleDuality :
    SmoothAdmissibleDualityStatement (G := G) (V := V) := by
  intro _ hcofinal
  exact ⟨fun ρ hρ => smoothBidual_injective_of_compact_cofinal hcofinal ρ hρ,
    fun ρ hρ => ⟨isAdmissible_smoothContragredient_of_compact_cofinal hcofinal ρ hρ,
      smoothBidual_injective_of_compact_cofinal hcofinal ρ hρ.1,
      smoothBidual_surjective_of_compact_cofinal hcofinal ρ hρ⟩⟩

end Langlands
