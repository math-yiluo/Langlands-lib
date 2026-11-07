import Langlands.Representation.Smooth.Contragredient.InvariantPairingProof

/-! # Perfectness of an invariant pairing from surjectivity at every compact open level

`smoothInvariantPairingDuality` needs one admissible side. Here admissibility is
replaced by a condition at each compact open level `L`: every linear functional
on `V^L` is the pairing with a vector of `W^L`.
-/

noncomputable section

namespace Langlands

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- An invariant pairing `b : W × V → ℂ` that is nondegenerate on `W` identifies
`σ` with the smooth contragredient of `ρ` when, at every compact open level `L`,
every linear functional on `V^L` is `b w` restricted to `V^L` for some `w ∈ W^L`.
The equivalence is characterized by `b`. No admissibility is assumed. -/
theorem exists_smoothDualEquiv_of_fixedSurjective
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (hρ : IsSmooth ρ)
    (hσ : IsSmooth σ) (b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hinv : ∀ (g : G) (w : W) (v : V), b (σ g w) (ρ g v) = b w v)
    (hleft : ∀ w : W, (∀ v : V, b w v = 0) → w = 0)
    (hsurj : ∀ L : OpenSubgroup G, IsCompact (L : Set G) →
      ∀ φ : Module.Dual ℂ (fixedVectors ρ L.toSubgroup),
        ∃ w ∈ fixedVectors σ L.toSubgroup,
          ∀ v : fixedVectors ρ L.toSubgroup, b w v = φ v) :
    ∃ E : Representation.Equiv σ (smoothContragredient ρ),
      ∀ (w : W) (v : V), smoothDualPairing ρ (E w) v = b w v := by
  let F₀ : σ.IntertwiningMap ρ.dual :=
    { toLinearMap := b
      isIntertwining' := by
        intro g
        ext w v
        change b (σ g w) v = b w (ρ g⁻¹ v)
        simpa only [ρ.self_inv_apply] using hinv g w (ρ g⁻¹ v) }
  let F : σ.IntertwiningMap (smoothContragredient ρ) := smoothLift hσ F₀
  have hFzero (w : W) (hw : F w = 0) : w = 0 := by
    apply hleft w
    intro v
    exact congrArg (fun ℓ : SmoothDual ρ => ℓ.val v) hw
  have hF : Function.Injective F := by
    intro w w' h
    apply sub_eq_zero.mp
    apply hFzero
    rw [map_sub, h, sub_self]
  have hFsurjective : Function.Surjective F := by
    intro ℓ
    obtain ⟨K, hK⟩ := ℓ.property
    obtain ⟨L, hL, hLK⟩ := hcofinal K
    have hℓL : ℓ ∈ fixedVectors (smoothContragredient ρ) L.toSubgroup :=
      fun l => Subtype.ext (hK ⟨l, hLK l.2⟩)
    obtain ⟨w, hw, hwφ⟩ :=
      hsurj L hL (smoothDualFixedRestriction ρ L.toSubgroup ⟨ℓ, hℓL⟩)
    have hFw : F w ∈ fixedVectors (smoothContragredient ρ) L.toSubgroup := by
      intro l
      change smoothContragredient ρ (l : G) (F w) = F w
      rw [← F.isIntertwining]
      exact congrArg F (hw l)
    refine ⟨w, ?_⟩
    have heq := (smoothDualFixedRestriction_bijective ρ hρ L hL).1
      (a₁ := ⟨F w, hFw⟩) (a₂ := ⟨ℓ, hℓL⟩) (by
        ext v
        exact hwφ v)
    exact congrArg Subtype.val heq
  exact ⟨F.ofBijective ⟨hF, hFsurjective⟩, fun w v => rfl⟩

end Langlands
