import Langlands.ClassField.Global.AbsoluteWeilGroup
import Langlands.ClassField.Global.LocalRelativeWeilMapReduction

/-! # Local Weil groups mapped into the absolute global Weil group

A property of a continuous homomorphism `W_{F_v} → W_F` from the actual local Weil group of
a finite completion into the projective limit of a supplied system of Weil maps: at every
finite Galois layer `K`, its composite with `W_F → W_{K/F}` is, up to an inner automorphism
of `W_{K/F}`, a local-to-relative Weil map at some place of `K` above `v` (Tate 1979, (1.6.1)).
No such map is constructed and none is asserted to exist.
-/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

universe u

namespace WeilMapSystem

variable {c : FundamentalClass.ClassFamily.{u}} {F : Type u} [Field F] [NumberField F]
  {Ω : Type u} [Field Ω] [Algebra F Ω] {h : FundamentalClass.Restriction c}
  (S : WeilMapSystem c F Ω h)

section Conjugation

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- A continuous homomorphism into the global Weil group followed by conjugation by `y`. -/
def conjMap (y : S.WeilGroup) (θ : G →ₜ* S.WeilGroup) : G →ₜ* S.WeilGroup where
  toMonoidHom := (MulAut.conj y).toMonoidHom.comp θ.toMonoidHom
  continuous_toFun := (continuous_const.mul θ.continuous).mul continuous_const

@[simp]
theorem conjMap_apply (y : S.WeilGroup) (θ : G →ₜ* S.WeilGroup) (g : G) :
    S.conjMap y θ g = y * θ g * y⁻¹ :=
  rfl

section Level

attribute [local instance] FiniteGaloisLayer.galoisTopology

/-- The homomorphism underlying the projection `S.toLevel K`, without its topology. -/
abbrev levelHom (K : FiniteGaloisIntermediateField F Ω) :
    S.WeilGroup →* RelativeWeilGroup c F K :=
  (S.toLevel K).toMonoidHom

theorem levelHom_apply (K : FiniteGaloisIntermediateField F Ω) (x : S.WeilGroup) :
    S.levelHom K x = S.toLevel K x :=
  rfl

/-- The projection is continuous for the discrete topology `relativeGaloisTopology` on
`Gal(K/F)`. -/
theorem continuous_levelHom (K : FiniteGaloisIntermediateField F Ω) :
    letI := relativeGaloisTopology F K
    Continuous (S.levelHom K) :=
  (S.toLevel K).continuous

end Level

/-- The composite `G → W_F → W_{K/F}` followed by conjugation by `x`, as a continuous
homomorphism for the Krull topology on `Gal(K/F)`, the topology for which
`RelativeWeilGroup.IsLocalRelativeWeilMap` is stated. The Krull topology on the finite group
`Gal(K/F)` is discrete, so it is the same topology as the one used by `S.toLevel K`. -/
def conjLevelMap (K : FiniteGaloisIntermediateField F Ω) (x : RelativeWeilGroup c F K)
    (θ : G →ₜ* S.WeilGroup) : G →ₜ* RelativeWeilGroup c F K where
  toMonoidHom := (MulAut.conj x).toMonoidHom.comp ((S.levelHom K).comp θ.toMonoidHom)
  continuous_toFun := by
    refine RelativeWeilGroup.continuous_krull_of_relativeGalois c _ ?_
    let := relativeGaloisTopology F K
    exact (continuous_const.mul ((S.continuous_levelHom K).comp θ.continuous)).mul
      continuous_const

@[simp]
theorem conjLevelMap_apply (K : FiniteGaloisIntermediateField F Ω) (x : RelativeWeilGroup c F K)
    (θ : G →ₜ* S.WeilGroup) (g : G) :
    S.conjLevelMap K x θ g = x * S.toLevel K (θ g) * x⁻¹ :=
  rfl

/-- Conjugating `θ` by `y` amounts to conjugating at each level by the projection of `y`. -/
theorem conjLevelMap_conjMap (K : FiniteGaloisIntermediateField F Ω)
    (x : RelativeWeilGroup c F K) (y : S.WeilGroup) (θ : G →ₜ* S.WeilGroup) :
    S.conjLevelMap K x (S.conjMap y θ) = S.conjLevelMap K (x * S.toLevel K y) θ := by
  refine ContinuousMonoidHom.ext fun g => ?_
  simp only [conjLevelMap_apply, conjMap_apply, map_mul, map_inv, mul_inv_rev]
  group

end Conjugation

/-- `θ : W_{F_v} → W_F` is a local-to-global Weil map at the finite place `v` of `F`: for
every finite Galois layer `K` of `Ω / F` there are a place `w` of `K` above `v`, a
reciprocity candidate `e` of `K_w` and an element `x` of `W_{K/F}` such that the composite
`W_{F_v} → W_F → W_{K/F}` followed by conjugation by `x` is a local-to-relative Weil map for
`w` and `e` in the sense of `RelativeWeilGroup.IsLocalRelativeWeilMap`. -/
def IsLocalWeilMap (v : Langlands.Global.FinitePlace F)
    (θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup) : Prop :=
  ∀ K : FiniteGaloisIntermediateField F Ω,
    ∃ (w : FinitePlacesAbove K v)
      (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
      (x : RelativeWeilGroup c F K),
      RelativeWeilGroup.IsLocalRelativeWeilMap v w.1 e (S.conjLevelMap K x θ)

variable {S}

/-- The property is invariant under conjugation by elements of the global Weil group. -/
theorem IsLocalWeilMap.conjMap {v : Langlands.Global.FinitePlace F}
    {θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup}
    (hθ : S.IsLocalWeilMap v θ) (y : S.WeilGroup) : S.IsLocalWeilMap v (S.conjMap y θ) := by
  intro K
  obtain ⟨w, e, x, hx⟩ := hθ K
  refine ⟨w, e, x * (S.toLevel K y)⁻¹, ?_⟩
  rw [conjLevelMap_conjMap, inv_mul_cancel_right]
  exact hx

/-- At each layer, a local-to-global Weil map is conjugate to a local-to-relative Weil map:
`S.toLevel K (θ g) = x⁻¹ * ι g * x`. -/
theorem IsLocalWeilMap.exists_level {v : Langlands.Global.FinitePlace F}
    {θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup}
    (hθ : S.IsLocalWeilMap v θ) (K : FiniteGaloisIntermediateField F Ω) :
    ∃ (w : FinitePlacesAbove K v)
      (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
      (x : RelativeWeilGroup c F K)
      (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F K),
      RelativeWeilGroup.IsLocalRelativeWeilMap v w.1 e ι ∧
        ∀ g, S.toLevel K (θ g) = x⁻¹ * ι g * x := by
  obtain ⟨w, e, x, hx⟩ := hθ K
  refine ⟨w, e, x, _, hx, fun g => ?_⟩
  rw [conjLevelMap_apply]
  group

end WeilMapSystem

end Langlands.ClassField.Global
