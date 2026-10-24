import Langlands.Representation.Hecke.CornerAction
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RepresentationTheory.Irreducible

/-! # Corner annihilators of fixed vectors determine irreducible smooth representations -/

noncomputable section

namespace Langlands.Hecke

open MeasureTheory MeasureTheory.Measure

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- The corner projection of the left translate by `g` of the normalized indicator of `K`. -/
def translateCornerElement (g : G) : HeckeAlgebra.Corner μ K hK :=
  HeckeAlgebra.Corner.project μ K hK ((HeckeAlgebra.toTestFunction μ).symm
    (TestFunction.leftTranslate g
      (HeckeAlgebra.toTestFunction μ (HeckeAlgebra.normalizedIndicator μ K hK))))

/-- On `K`-fixed vectors, the translate element acts as `ρ g` followed by the projection
to `K`-fixed vectors, for every smooth representation at once. -/
theorem cornerAction_translateCornerElement (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (v : fixedVectors ρ K.toSubgroup) (g : G) :
    cornerAction μ ρ hρ K hK (translateCornerElement μ K hK g) v =
      fixedProjection μ ρ hρ K hK (ρ g v) := by
  rw [translateCornerElement, cornerAction_project, heckeAction_apply,
    LinearEquiv.apply_symm_apply, integratedAction_leftTranslate, ← heckeAction_apply,
    heckeAction_normalizedIndicator_of_fixed μ ρ hρ K hK v.property]

/-- Formal finite combinations of group elements, sent to the corresponding combinations
of translate elements of the corner. -/
def translateCombination : (G →₀ ℂ) →ₗ[ℂ] HeckeAlgebra.Corner μ K hK :=
  Finsupp.linearCombination ℂ (translateCornerElement μ K hK)

/-- Formal finite combinations of group elements, sent to the corresponding combinations
of translates of a fixed vector. -/
def orbitCombination (ρ : Representation ℂ G V) (v : V) : (G →₀ ℂ) →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ fun g => ρ g v

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
/-- Left translation of the formal combination corresponds to the group action. -/
theorem orbitCombination_mapDomain (ρ : Representation ℂ G V) (v : V) (h : G)
    (c : G →₀ ℂ) :
    orbitCombination ρ v (Finsupp.mapDomain (h * ·) c) = ρ h (orbitCombination ρ v c) := by
  rw [orbitCombination, Finsupp.linearCombination_mapDomain,
    Finsupp.apply_linearCombination]
  congr 2
  funext g
  simp [map_mul, Module.End.mul_apply]

/-- The corner element of a formal combination acts on a fixed vector as the projection
of the same combination of its translates. -/
theorem cornerAction_translateCombination (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (v : fixedVectors ρ K.toSubgroup) (c : G →₀ ℂ) :
    cornerAction μ ρ hρ K hK (translateCombination μ K hK c) v =
      fixedProjection μ ρ hρ K hK (orbitCombination ρ (v : V) c) := by
  have key : LinearMap.applyₗ v ∘ₗ (cornerAction μ ρ hρ K hK).toLinearMap ∘ₗ
      translateCombination μ K hK =
      fixedProjection μ ρ hρ K hK ∘ₗ orbitCombination ρ (v : V) := by
    apply Finsupp.lhom_ext
    intro g t
    simp [translateCombination, orbitCombination, cornerAction_translateCornerElement]
  exact LinearMap.congr_fun key c

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
/-- A submodule stable under an irreducible representation is zero or everything. -/
theorem submodule_eq_bot_or_eq_top_of_isIrreducible {σ : Representation ℂ G W}
    (hσ : σ.IsIrreducible) (N : Submodule ℂ W) (hN : ∀ g : G, ∀ w ∈ N, σ g w ∈ N) :
    N = ⊥ ∨ N = ⊤ := by
  rcases hσ.eq_bot_or_eq_top ⟨N, fun g w hw => hN g w hw⟩ with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
/-- In an irreducible representation the translates of a nonzero vector span. -/
theorem orbitCombination_surjective {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible)
    {v : V} (hv : v ≠ 0) : Function.Surjective (orbitCombination ρ v) := by
  rw [← LinearMap.range_eq_top]
  rcases submodule_eq_bot_or_eq_top_of_isIrreducible hρ
      (LinearMap.range (orbitCombination ρ v)) (by
        rintro g _ ⟨c, rfl⟩
        exact ⟨Finsupp.mapDomain (g * ·) c, orbitCombination_mapDomain ρ v g c⟩) with h | h
  · exfalso
    apply hv
    have hmem : v ∈ LinearMap.range (orbitCombination ρ v) :=
      ⟨Finsupp.single 1 1, by simp [orbitCombination]⟩
    rw [h] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  · exact h

/-- If every corner element killing `a` also kills `b`, then every formal relation among
the translates of `a` is also a relation among the translates of `b`. -/
theorem ker_orbitCombination_le {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    {σ : Representation ℂ G W} (hσ : IsSmooth σ) (hσirr : σ.IsIrreducible)
    (a : fixedVectors ρ K.toSubgroup) (b : fixedVectors σ K.toSubgroup) (hb : (b : W) ≠ 0)
    (h : ∀ e : HeckeAlgebra.Corner μ K hK,
      cornerAction μ ρ hρ K hK e a = 0 → cornerAction μ σ hσ K hK e b = 0) :
    LinearMap.ker (orbitCombination ρ (a : V)) ≤
      LinearMap.ker (orbitCombination σ (b : W)) := by
  have hN : ∀ g : G, ∀ w ∈ (LinearMap.ker (orbitCombination ρ (a : V))).map
      (orbitCombination σ (b : W)), σ g w ∈ (LinearMap.ker (orbitCombination ρ (a : V))).map
      (orbitCombination σ (b : W)) := by
    intro g w hw
    obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hw
    refine Submodule.mem_map.mpr ⟨Finsupp.mapDomain (g * ·) c, ?_,
      orbitCombination_mapDomain σ _ g c⟩
    rw [LinearMap.mem_ker] at hc ⊢
    rw [orbitCombination_mapDomain, hc, map_zero]
  rcases submodule_eq_bot_or_eq_top_of_isIrreducible hσirr _ hN with hbot | htop
  · intro c hc
    have hmem : orbitCombination σ (b : W) c ∈
        (LinearMap.ker (orbitCombination ρ (a : V))).map (orbitCombination σ (b : W)) :=
      Submodule.mem_map.mpr ⟨c, hc, rfl⟩
    rw [hbot] at hmem
    exact LinearMap.mem_ker.mpr ((Submodule.mem_bot ℂ).mp hmem)
  · exfalso
    have hbN : (b : W) ∈
        (LinearMap.ker (orbitCombination ρ (a : V))).map (orbitCombination σ (b : W)) := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨c, hc, hcb⟩ := Submodule.mem_map.mp hbN
    have h0 : cornerAction μ ρ hρ K hK (translateCombination μ K hK c) a = 0 := by
      apply Subtype.ext
      rw [cornerAction_translateCombination, LinearMap.mem_ker.mp hc, map_zero]
    have h1 := h _ h0
    rw [Subtype.ext_iff, cornerAction_translateCombination, hcb, fixedProjection_fixed] at h1
    exact hb h1

/-- Bernstein--Zelevinsky (1976), 2.10(b), in annihilator form: two irreducible smooth
complex representations with nonzero `K`-fixed vectors `a` and `b` that are killed by
exactly the same elements of the corner `H_K` are equivalent. -/
theorem nonempty_equiv_of_cornerAction_eq_zero_iff
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (hρirr : ρ.IsIrreducible)
    {σ : Representation ℂ G W} (hσ : IsSmooth σ) (hσirr : σ.IsIrreducible)
    (a : fixedVectors ρ K.toSubgroup) (b : fixedVectors σ K.toSubgroup)
    (ha : (a : V) ≠ 0) (hb : (b : W) ≠ 0)
    (h : ∀ e : HeckeAlgebra.Corner μ K hK,
      cornerAction μ ρ hρ K hK e a = 0 ↔ cornerAction μ σ hσ K hK e b = 0) :
    Nonempty (ρ.Equiv σ) := by
  have hker : LinearMap.ker (orbitCombination ρ (a : V)) =
      LinearMap.ker (orbitCombination σ (b : W)) :=
    le_antisymm (ker_orbitCombination_le μ K hK hρ hσ hσirr a b hb fun e => (h e).mp)
      (ker_orbitCombination_le μ K hK hσ hρ hρirr b a ha fun e => (h e).mpr)
  have hΦ := orbitCombination_surjective hρirr ha
  have hΨ := orbitCombination_surjective hσirr hb
  let φ : V ≃ₗ[ℂ] W :=
    ((orbitCombination ρ (a : V)).quotKerEquivOfSurjective hΦ).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker).trans
        ((orbitCombination σ (b : W)).quotKerEquivOfSurjective hΨ))
  have hφ : ∀ c, φ (orbitCombination ρ (a : V) c) = orbitCombination σ (b : W) c := by
    intro c
    simp [φ, Submodule.quotEquivOfEq_mk]
  refine ⟨Representation.Equiv.mk φ fun g => ?_⟩
  apply LinearMap.ext
  intro v
  obtain ⟨c, rfl⟩ := hΦ v
  change φ (ρ g (orbitCombination ρ (a : V) c)) = σ g (φ (orbitCombination ρ (a : V) c))
  rw [← orbitCombination_mapDomain, hφ, hφ, orbitCombination_mapDomain]

end Langlands.Hecke
