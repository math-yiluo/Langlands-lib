import Langlands.Global.AdelicBlockCompactProduct
import Langlands.Global.ArchimedeanIwasawaChart
import Langlands.Representation.Archimedean.CompactPolynomialSections
import Langlands.Representation.FiniteVectors

/-! # Polynomial compact sections for the actual infinite block parabolic -/

noncomputable section

open MeasureTheory NumberField
open scoped Classical Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000

universe u v

namespace Langlands.Global.AdelicBlockParabolic

open Langlands.GeneralLinear (BlockShape)
open Langlands.Archimedean ArchimedeanGL PrimitiveAdelicHeight

set_option backward.isDefEq.respectTransparency true in
private theorem exists_polynomialSection_of_locallyFinite
    {A₀ H₀ V : Type*} [NormedRing A₀] [NormedAlgebra ℝ A₀] [FiniteDimensional ℝ A₀]
    [Group H₀] [TopologicalSpace H₀] [IsTopologicalGroup H₀] [CompactSpace H₀] [T2Space H₀]
    [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (ι : H₀ →* A₀ˣ) (hι : Continuous fun h => (ι h).val) (hι' : Function.Injective ι)
    (ρ : Representation ℂ H₀ V) (hf : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hc : ∀ (v : V) (l : V →ₗ[ℂ] ℂ), Continuous fun h => l (ρ h v)) :
    ∃ (d : ℕ) (j : (Fin d → ℂ) →ₗ[ℂ] V) (f : A₀ → (Fin d → ℂ)),
      Function.Injective j ∧ f ∈ vectorCoordinatePolynomials A₀ (Fin d → ℂ) ∧ j (f 1) ≠ 0 ∧
        ∀ h a, j (f ((ι h).val * a)) = ρ h (j (f a)) := by
  let : MeasurableSpace H₀ := borel H₀
  let : BorelSpace H₀ := ⟨rfl⟩
  let C : TopologicalSpace.PositiveCompacts H₀ := ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  let μ := Measure.haarMeasure C
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  let O := FiniteVectors.orbitSubrepresentation ρ x
  let : FiniteDimensional ℂ O.toSubmodule := hf x
  let d := Module.finrank ℂ O.toSubmodule
  let e : O.toSubmodule ≃ₗ[ℂ] (Fin d → ℂ) := (Module.finBasis ℂ O.toSubmodule).equivFun
  let xO : O.toSubmodule := ⟨x, FiniteVectors.self_mem_orbitSpan ρ x⟩
  let τ : Representation ℂ H₀ (Fin d → ℂ) :=
    (e.conjAlgEquiv ℂ).toRingEquiv.toMonoidHom.comp O.toRepresentation
  let j : (Fin d → ℂ) →ₗ[ℂ] V := O.toSubmodule.subtype.comp e.symm.toLinearMap
  have hxO : xO ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have hτ (s : Fin d → ℂ) : Continuous fun h : H₀ => τ h s := by
    apply continuous_pi
    intro i
    let p : O.toSubmodule →ₗ[ℂ] ℂ := (LinearMap.proj i).comp e.toLinearMap
    obtain ⟨l, hl⟩ := LinearMap.exists_extend p
    have he (h : H₀) : τ h s i = l (ρ h (e.symm s).val) := by
      change p (O.toRepresentation h (e.symm s)) = _
      rw [← hl]
      rfl
    simp only [he]
    exact hc (e.symm s).val l
  have hE : e xO ≠ 0 := fun h => hxO (e.injective (h.trans (map_zero e).symm))
  obtain ⟨f, hf, hn, hcov⟩ := exists_covariantPolynomialSection ι
    μ τ hι hτ hι' (e xO) hE
  have hj : Function.Injective j := O.toSubmodule.subtype_injective.comp e.symm.injective
  have hJ : j (f 1) ≠ 0 := fun h => hn (hj (h.trans (map_zero j).symm))
  have hAct (h : H₀) (s : Fin d → ℂ) :
      e.symm (τ h s) = O.toRepresentation h (e.symm s) := by
    change e.symm (e (O.toRepresentation h (e.symm s))) = _
    exact e.symm_apply_apply _
  refine ⟨d, j, f, hj, hf, hJ, fun h a => ?_⟩
  calc
    j (f ((ι h).val * a)) = j (τ h (f a)) := congrArg j (hcov h a)
    _ = (O.toRepresentation h (e.symm (f a))).val :=
      congrArg (fun s : O.toSubmodule => s.val) (hAct h (f a))
    _ = ρ h (j (f a)) := rfl

variable (F : Type u) [Field F] {n : ℕ} (B : BlockShape n)

local notation "K" => standardInfiniteCompact F n
local notation "P" => B.parabolic (InfiniteAdeles F)
local notation "H" => infiniteCompactIntersection F B
local notation "A" => ArchimedeanMatrix F n

private def intersectionInCompactEquiv : H ≃ₜ* (P).comap (K).subtype where
  toFun p := ⟨⟨p.val.val, p.property⟩, p.val.property⟩
  invFun p := ⟨⟨p.val.val, p.property⟩, p.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

/-- The actual parabolic intersection inside the infinite standard compact is compact. -/
theorem compactSpace_infiniteCompactIntersection : CompactSpace H := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_standardInfiniteCompact F n)
  have hc : IsClosed ((P).comap (K).subtype : Set K) :=
    (B.isClosed_parabolic (InfiniteAdeles F)).preimage continuous_subtype_val
  let : CompactSpace ((P).comap (K).subtype) := isCompact_iff_compactSpace.mp hc.isCompact
  exact (intersectionInCompactEquiv F B).symm.toHomeomorph.compactSpace

/-- The continuous Levi projection on the actual infinite compact intersection. -/
def infiniteCompactLeviProjection : H →ₜ*
    (∀ i : Fin B.length, standardInfiniteCompact F (B.size i)) where
  toFun p i := ⟨B.leviProjection (InfiniteAdeles F) p.val i,
    leviProjection_mem_standardInfiniteCompact B F p.val p.property i⟩
  map_one' := funext fun i => Subtype.ext (congrFun ((B.leviProjection (InfiniteAdeles F)).map_one) i)
  map_mul' p q := funext fun i => Subtype.ext (congrFun ((B.leviProjection (InfiniteAdeles F)).map_mul p.val q.val) i)
  continuous_toFun := continuous_pi fun i =>
    ((continuous_apply i).comp ((B.leviProjectionContinuous (InfiniteAdeles F)).continuous.comp
      continuous_subtype_val)).subtype_mk _

@[simp]
theorem infiniteCompactLeviProjection_val (p : H) (i : Fin B.length) :
    (infiniteCompactLeviProjection F B p i).val = B.leviProjection (InfiniteAdeles F) p.val i := rfl

/-- Embed the compact parabolic subgroup into the units of the real matrix algebra. -/
def infiniteCompactMatrixInclusion : H →* Aˣ :=
  (archimedeanGLCoordinates F n).toMonoidHom.comp ((P).subtype.comp (H).subtype)

theorem infiniteCompactMatrixInclusion_injective : Function.Injective (infiniteCompactMatrixInclusion F B) :=
  (archimedeanGLCoordinates F n).injective.comp (Subtype.val_injective.comp Subtype.val_injective)

theorem continuous_infiniteCompactMatrixInclusion_val :
    Continuous fun p => (infiniteCompactMatrixInclusion F B p).val :=
  Units.continuous_val.comp ((archimedeanGLCoordinates F n).continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val))

variable [NumberField F] {V : Type v} [AddCommGroup V] [Module ℂ V] [Nontrivial V]

/-- A weakly continuous locally finite coefficient action gives a nonzero
polynomial section on the actual matrix algebra, valued in one compact orbit span. -/
theorem exists_polynomialSection_infiniteCompactIntersection
    (ρ : Representation ℂ H V) (hf : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hc : ∀ (v : V) (l : V →ₗ[ℂ] ℂ), Continuous fun h => l (ρ h v)) :
    ∃ (d : ℕ) (j : (Fin d → ℂ) →ₗ[ℂ] V) (f : A → (Fin d → ℂ)),
      Function.Injective j ∧ f ∈ vectorCoordinatePolynomials A (Fin d → ℂ) ∧ j (f 1) ≠ 0 ∧
        ∀ h a, j (f ((infiniteCompactMatrixInclusion F B h).val * a)) = ρ h (j (f a)) := by
  let : CompactSpace H := compactSpace_infiniteCompactIntersection F B
  exact exists_polynomialSection_of_locallyFinite (infiniteCompactMatrixInclusion F B)
    (continuous_infiniteCompactMatrixInclusion_val F B) (infiniteCompactMatrixInclusion_injective F B)
    ρ hf hc

end Langlands.Global.AdelicBlockParabolic
