import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Smooth.IntertwinerFiniteness
import Langlands.Representation.SubrepresentationLattice
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RepresentationTheory.Irreducible

/-!
# Isotypic projectors from a nondegenerate test pairing

Let `σ` be an admissible irreducible representation and `ρ` a representation
with finite-dimensional `Hom(σ, ρ)`. If a functional `m` on `σ` and a vector
`u` with `m u ≠ 0` detect every nonzero `f : σ → ρ` through some `r : ρ → σ`,
in the sense that `m (r (f u)) ≠ 0`, then a dual basis of `Hom(σ, ρ)` built
from such maps `r` gives an idempotent self-intertwiner of `ρ` whose range is
the `σ`-isotypic subrepresentation, the supremum of the ranges of all
intertwiners `σ → ρ`.
-/

noncomputable section

namespace Langlands

open Representation

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

omit [TopologicalSpace G] in
/-- The simple module of an irreducible representation is finitely generated. -/
theorem moduleFinite_asModule_of_isIrreducible (σ : Representation ℂ G W)
    (hirr : σ.IsIrreducible) : Module.Finite (MonoidAlgebra ℂ G) σ.asModule := by
  have := hirr
  have : Nontrivial σ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) σ.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : σ.asModule)
  exact ⟨⟨{x}, by
    rw [Finset.coe_singleton]
    exact IsSimpleModule.span_singleton_eq_top (MonoidAlgebra ℂ G) hx⟩⟩

omit [TopologicalSpace G] in
/-- An idempotent is obtained from a self-intertwiner that fixes the range of every
intertwiner `σ → ρ` and takes values in their supremum. -/
theorem isotypicProjector_of_fixes {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (P : ρ.IntertwiningMap ρ) (hfix : ∀ f : σ.IntertwiningMap ρ, P.comp f = f)
    (hmem : ∀ v, P v ∈ (⨆ f : σ.IntertwiningMap ρ, f.range)) :
    P.comp P = P ∧ P.range = ⨆ f : σ.IntertwiningMap ρ, f.range := by
  have hsup : ∀ y ∈ (⨆ f : σ.IntertwiningMap ρ, f.range), P y = y := by
    intro y hy
    have hle : (⨆ f : σ.IntertwiningMap ρ, f.range).toSubmodule ≤
        LinearMap.ker (P.toLinearMap - LinearMap.id) := by
      rw [Subrepresentation.toSubmodule_iSup]
      refine iSup_le fun f => ?_
      rintro _ ⟨w, rfl⟩
      have h := congrArg (fun φ : σ.IntertwiningMap ρ => φ w) (hfix f)
      simp only [IntertwiningMap.comp_apply] at h
      simp [h]
    have h := hle hy
    simpa [sub_eq_zero] using h
  refine ⟨DFunLike.ext _ _ fun v => hsup (P v) (hmem v), ?_⟩
  apply _root_.Subrepresentation.toSubmodule_injective
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact hmem v
  · intro y hy
    exact ⟨y, hsup y hy⟩

/-- A dual basis of `Hom(σ, ρ)` for the nondegenerate pairing
`(r, f) ↦ m (r (f u))` gives a self-intertwiner of `ρ` that fixes every
intertwiner `σ → ρ` and takes values in the `σ`-isotypic subrepresentation. -/
theorem exists_isotypicProjector_of_nondegenerate
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hσ : IsAdmissible σ) (hirr : σ.IsIrreducible)
    [Module.Finite ℂ (σ.IntertwiningMap ρ)]
    (m : Module.Dual ℂ W) {u : W} (hu : m u ≠ 0)
    (hnd : ∀ f : σ.IntertwiningMap ρ, f ≠ 0 →
      ∃ r : ρ.IntertwiningMap σ, m (r (f u)) ≠ 0) :
    ∃ P : ρ.IntertwiningMap ρ, (∀ f : σ.IntertwiningMap ρ, P.comp f = f) ∧
      ∀ v, P v ∈ (⨆ f : σ.IntertwiningMap ρ, f.range) := by
  classical
  let β : ρ.IntertwiningMap σ →ₗ[ℂ] σ.IntertwiningMap ρ →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun r f => m (r (f u)))
      (fun r₁ r₂ f => by simp)
      (fun a r f => by simp)
      (fun r f₁ f₂ => by simp)
      (fun a r f => by simp)
  have hβ : ∀ r f, β r f = m (r (f u)) := fun _ _ => rfl
  have hinj : Function.Injective β.flip := by
    refine (injective_iff_map_eq_zero β.flip).mpr fun f hf => ?_
    by_contra hne
    obtain ⟨r, hr⟩ := hnd f hne
    apply hr
    have h := LinearMap.congr_fun hf r
    rwa [LinearMap.flip_apply, hβ, LinearMap.zero_apply] at h
  have hsurj : Function.Surjective β := LinearMap.flip_injective_iff₂.mp hinj
  let b := Module.finBasis ℂ (σ.IntertwiningMap ρ)
  choose r hr using fun i => hsurj (m u • b.coord i)
  have hcomp : ∀ i (f : σ.IntertwiningMap ρ),
      (r i).comp f = b.coord i f • IntertwiningMap.id σ := by
    intro i f
    obtain ⟨c, hc, -⟩ := admissibleSchur_scalarEndomorphism σ hσ hirr ((r i).comp f)
    have h1 : m (r i (f u)) = m u * b.coord i f := by
      have h := LinearMap.congr_fun (hr i) f
      rw [hβ, LinearMap.smul_apply, smul_eq_mul] at h
      exact h
    have h2 : m (r i (f u)) = c * m u := by
      have h := congrArg (fun φ : σ.IntertwiningMap σ => m (φ u)) hc
      simpa [IntertwiningMap.smul_apply] using h
    have hcf : c = b.coord i f := by
      apply mul_right_cancel₀ hu
      rw [← h2, h1, mul_comm]
    rw [hc, hcf]
  refine ⟨∑ i, (b i).comp (r i), fun f => ?_, fun v => ?_⟩
  · refine DFunLike.ext _ _ fun v => ?_
    have hri : ∀ i, r i (f v) = b.coord i f • v := by
      intro i
      have h := congrArg (fun φ : σ.IntertwiningMap σ => φ v) (hcomp i f)
      simpa [IntertwiningMap.smul_apply] using h
    calc ((∑ i, (b i).comp (r i)).comp f) v
        = ∑ i, b.repr f i • (b i) v := by
          simp only [IntertwiningMap.comp_apply, IntertwiningMap.sum_apply, hri, map_smul,
            Module.Basis.coord_apply]
      _ = f v := by
          conv_rhs => rw [← b.sum_repr f]
          rw [IntertwiningMap.sum_apply]
          exact Finset.sum_congr rfl fun i _ => rfl
  · rw [IntertwiningMap.sum_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    change (b i) (r i v) ∈ (⨆ f : σ.IntertwiningMap ρ, f.range).toSubmodule
    rw [Subrepresentation.toSubmodule_iSup]
    exact Submodule.mem_iSup_of_mem (b i) ⟨r i v, rfl⟩

end Langlands
