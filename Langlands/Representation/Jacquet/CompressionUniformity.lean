import Langlands.Representation.Jacquet.StableCompressionPower
import Langlands.Representation.Category.SmoothCoproducts

/-! # Uniform compression from qualitative stability on all smooth objects

A diagonal countable direct sum upgrades eventual stability on every smooth
representation to a common stationary threshold. All hypotheses remain explicit.
-/

noncomputable section

namespace Langlands.LinearAlgebra.StableEndomorphism

universe uV uW

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Stability descends to an endomorphism retract. -/
theorem stable_of_retract (t : Module.End ℂ V) (s : Module.End ℂ W)
    (i : V →ₗ[ℂ] W) (p : W →ₗ[ℂ] V)
    (hpi : p.comp i = LinearMap.id)
    (hi : i.comp t = s.comp i) (hp : p.comp s = t.comp p)
    (hs : Stable s) : Stable t := by
  have hpi' (x : V) : p (i x) = x := LinearMap.congr_fun hpi x
  have hi' (x : V) : i (t x) = s (i x) := LinearMap.congr_fun hi x
  have hp' (x : W) : p (s x) = t (p x) := LinearMap.congr_fun hp x
  apply (stable_iff_le t).mpr
  constructor
  · intro x hx
    rw [LinearMap.mem_ker, pow_two, Module.End.mul_apply] at hx
    have hsx : s (s (i x)) = 0 := by rw [← hi', ← hi', hx, map_zero]
    have hix : i (t x) = 0 := by rw [hi']; exact hs.apply_eq_zero hsx
    rw [LinearMap.mem_ker]
    have := congrArg p hix
    simpa only [hpi', map_zero] using this
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hs.exists_apply_sq (i x)
    refine ⟨p y, ?_⟩
    have := congrArg p hy
    simpa only [hp', hpi', pow_two, Module.End.mul_apply] using this

end Langlands.LinearAlgebra.StableEndomorphism

namespace Langlands.Jacquet

open Langlands.LinearAlgebra.StableEndomorphism

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- An actual equivariant retract inherits the same stable compressed power. -/
theorem compactCompressionStablePower_of_retract
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (i : ρ.IntertwiningMap σ) (p : σ.IntertwiningMap ρ)
    (hpi : p.toLinearMap.comp i.toLinearMap = LinearMap.id)
    (b : ℕ) (h : CompactCompressionStablePower σ hσ K hK g b) :
    CompactCompressionStablePower ρ hρ K hK g b := by
  let iK := fixedVectorsMap i K.toSubgroup
  let pK := fixedVectorsMap p K.toSubgroup
  have hretract : pK.comp iK = LinearMap.id := by
    ext x
    exact LinearMap.congr_fun hpi x.val
  apply stable_of_retract _ _ iK pK hretract _ _ h
  · exact (Module.End.commute_pow_left_of_commute
      (compressedAction_natural ρ σ hρ hσ K hK g i).symm b).symm
  · exact (Module.End.commute_pow_left_of_commute
      (compressedAction_natural σ ρ hσ hρ K hK g p).symm b).symm

/-- Qualitative compression stability for every smooth representation in the
specified carrier universe. It is a hypothesis, not an existence theorem. -/
def PointwiseCompressionEventuallyStable
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) : Prop :=
  ∀ A : SmoothRep.{0, uG, uV} ℂ G,
    EventuallyStable (compressedAction A.representation A.isSmooth K hK g)

/-- A single stationary threshold chosen before all smooth objects of the
specified carrier universe. -/
def UniformCompressionStationary
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) : Prop :=
  ∃ b : ℕ, ∀ A : SmoothRep.{0, uG, uV} ℂ G,
    CompactCompressionStationaryFrom A.representation A.isSmooth K hK g b

/-- The diagonal argument uses the actual countable direct sum and its
inclusion/projection retracts, and preserves the carrier universe. -/
theorem uniformCompressionStationary_of_pointwise
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (h : PointwiseCompressionEventuallyStable.{uG, uV} K hK g) :
    UniformCompressionStationary.{uG, uV} K hK g := by
  classical
  by_contra hn
  have hbad : ∀ b : ℕ, ∃ A : SmoothRep.{0, uG, uV} ℂ G,
      ¬ CompactCompressionStationaryFrom A.representation A.isSmooth K hK g b := by
    simpa only [UniformCompressionStationary, not_exists, not_forall] using hn
  choose A hA using hbad
  let S := SmoothRep.directSum A
  obtain ⟨b, hb, hS⟩ := h S
  apply hA b
  apply compactCompressionStationaryFrom_of_stablePower _ _ K hK g hb
  apply compactCompressionStablePower_of_retract _ S.representation _ S.isSmooth
    K hK g (SmoothRep.hom (SmoothRep.directSumι A b))
      (SmoothRep.hom (SmoothRep.directSumπ A b)) _ b hS
  ext x
  change DirectSum.component ℂ ℕ (fun i => A i) b
    (DirectSum.lof ℂ ℕ (fun i => A i) b x) = x
  exact DirectSum.component.lof_self ℂ (M := fun i => A i) b x

/-- Qualitative stability for all smooth objects is equivalent to the uniform
stationary-chain conclusion in the same carrier universe. -/
theorem pointwiseCompressionEventuallyStable_iff_uniform
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) :
    PointwiseCompressionEventuallyStable.{uG, uV} K hK g ↔
      UniformCompressionStationary.{uG, uV} K hK g := by
  constructor
  · exact uniformCompressionStationary_of_pointwise K hK g
  · rintro ⟨b, hb⟩ A
    exact (compactCompression_eventuallyStable_iff_exists_stationaryFrom
      A.representation A.isSmooth K hK g).mpr ⟨b, hb A⟩

end Langlands.Jacquet
