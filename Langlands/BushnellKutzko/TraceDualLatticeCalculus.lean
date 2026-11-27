import Langlands.BushnellKutzko.CorestrictionLatticeDual
import Langlands.BushnellKutzko.TranslatedFiltrationCentralizer
import Langlands.BushnellKutzko.SimpleCharacters

/-! # Trace duality on sums, intersections, and conjugates -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "O" => 𝒪[F]
local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "tr" => LinearMap.trace F V

private def endomorphismTracePairing : LinearMap.BilinForm F A :=
  (LinearMap.mul F A).compr₂ tr

omit [ValuativeRel F] in
private theorem endomorphismTracePairing_nondegenerate [FiniteDimensional F V] :
    (endomorphismTracePairing (F := F) (V := V)).Nondegenerate := by
  have hleft : (endomorphismTracePairing (F := F) (V := V)).SeparatingLeft := by
    intro x hx
    ext v
    change x v = 0
    refine (Module.forall_dual_apply_eq_zero_iff F (x v)).mp fun f => ?_
    have he : x * f.smulRight v = f.smulRight (x v) := by
      ext w
      simp only [Module.End.mul_apply, LinearMap.smulRight_apply, map_smul]
    have ht := hx (f.smulRight v)
    change tr (x * f.smulRight v) = 0 at ht
    rwa [he, LinearMap.trace_smulRight] at ht
  refine ⟨hleft, fun y hy => hleft y fun x => ?_⟩
  change tr (y * x) = 0
  rw [LinearMap.trace_mul_comm]
  exact hy x

/-- Trace annihilation turns a sum into an intersection. -/
theorem traceDualLattice_sup_aux (ψF : AddChar F ℂ) (D : Submodule O A → Submodule O A)
    (hD : ∀ (M : Submodule O A) (x : A), x ∈ D M ↔
      ∀ y : A, y ∈ M → traceCharacter ψF (x * y) = 1)
    (M N : Submodule O A) : D (M ⊔ N) = D M ⊓ D N := by
  ext x
  rw [Submodule.mem_inf, hD, hD M, hD N]
  refine ⟨fun hx => ⟨fun y hy => hx y (Submodule.mem_sup_left hy),
    fun y hy => hx y (Submodule.mem_sup_right hy)⟩, ?_⟩
  rintro ⟨hxM, hxN⟩ y hy
  obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.mp hy
  rw [mul_add, AddChar.map_add_eq_mul, hxM m hm, hxN n hn, mul_one]

private theorem trace_mul_conj (g : G) (x y : A) :
    tr (x * endUnitConjugation g y) = tr ((endUnitConjugation g).symm x * y) := by
  simp only [endUnitConjugation_apply, endUnitConjugation_symm, inv_inv]
  calc
    tr (x * ((g : A) * y * (↑g⁻¹ : A))) = tr ((x * (g : A)) * y * (↑g⁻¹ : A)) := by
      simp only [mul_assoc]
    _ = _ := by
      rw [LinearMap.trace_mul_cycle]
      simp only [mul_assoc]

/-- The trace dual commutes with conjugation. -/
theorem traceDualLattice_map_conj_aux (ψF : AddChar F ℂ) (D : Submodule O A → Submodule O A)
    (hD : ∀ (M : Submodule O A) (x : A), x ∈ D M ↔
      ∀ y : A, y ∈ M → traceCharacter ψF (x * y) = 1)
    (g : G) (M : Submodule O A) :
    D (M.map (endUnitConjugation g).toLinearMap) = (D M).map (endUnitConjugation g).toLinearMap := by
  ext x
  rw [Submodule.mem_map_equiv, hD, hD M]
  constructor
  · intro hx y hy
    have h := hx (endUnitConjugation g y) (Submodule.mem_map_of_mem hy)
    simpa only [traceCharacter_apply, trace_mul_conj] using h
  · intro hx y hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    change ψF (tr (x * endUnitConjugation g z)) = 1
    rw [trace_mul_conj]
    exact hx z hz

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V]

/-- Double trace duality for finitely generated integral submodules. -/
theorem traceDualLattice_traceDualLattice_aux (D : Submodule O A → Submodule O A)
    (htrace : ∀ (M : Submodule O A) (x : A), x ∈ D M ↔
      ∀ y : A, y ∈ M → tr (x * y) ∈ maximalIdealInField O F)
    {M : Submodule O A} (hM : M.FG) : D (D M) = M := by
  ext x
  constructor
  · intro hx
    by_contra hxM
    obtain ⟨f, hf, hfx⟩ := separates_fg_submodule (K := F) M hM hxM
    let e := (endomorphismTracePairing (F := F) (V := V)).toDual endomorphismTracePairing_nondegenerate
    obtain ⟨y, hy⟩ := e.surjective f
    have hyf (z : A) : tr (y * z) = f z := LinearMap.congr_fun hy z
    have hyD : y ∈ D M := (htrace M y).mpr fun z hz => (hyf z).symm ▸ hf z hz
    have h := (htrace (D M) x).mp hx y hyD
    rw [LinearMap.trace_mul_comm F x y, hyf] at h
    exact hfx h
  · intro hx
    apply (htrace (D M) x).mpr
    intro y hy
    rw [LinearMap.trace_mul_comm F x y]
    exact (htrace M y).mp hy x hx

/-- Trace duality turns an intersection into a sum when the given submodules
and their duals are finitely generated. -/
theorem traceDualLattice_inf_aux (ψF : AddChar F ℂ) (D : Submodule O A → Submodule O A)
    (hD : ∀ (M : Submodule O A) (x : A), x ∈ D M ↔
      ∀ y : A, y ∈ M → traceCharacter ψF (x * y) = 1)
    (htrace : ∀ (M : Submodule O A) (x : A), x ∈ D M ↔
      ∀ y : A, y ∈ M → tr (x * y) ∈ maximalIdealInField O F)
    {M N : Submodule O A}
    (hM : M.FG) (hN : N.FG) (hDM : (D M).FG) (hDN : (D N).FG) :
    D (M ⊓ N) = D M ⊔ D N := by
  have hdual : D (D M ⊔ D N) = M ⊓ N := by
    rw [traceDualLattice_sup_aux ψF D hD, traceDualLattice_traceDualLattice_aux D htrace hM,
      traceDualLattice_traceDualLattice_aux D htrace hN]
  rw [← hdual, traceDualLattice_traceDualLattice_aux D htrace (hDM.sup hDN)]

end Langlands.BushnellKutzko
