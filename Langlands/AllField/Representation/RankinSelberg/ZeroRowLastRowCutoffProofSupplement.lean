import Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.HarmonicAnalysis.ConductorSupplement
import Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
import Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement
/-!
# Proof of the compact last-row cutoff for zero-row Whittaker coefficients

An open stabilizer of a preimage vector contains small upper columns. Conjugating
them by `diag(g, I)` makes the Whittaker character read the last row of `g`, and
the additive conductor bounds that row. See the paired Markdown for the route.
-/

noncomputable section

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe u
variable {F : Type u} [Field F] (T : LocalFieldData F)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F _ T.topology

end Langlands.LocalFieldData

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding LastRowCompactOrbitStatement ZeroRowLastRowCutoffStatement lastRowCompactOrbit zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.Topology
open Langlands.GeneralLinear
open Langlands.Whittaker
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open scoped Matrix

universe uF uV

section Column

variable {F : Type uF} [Field F]

section Topology



end Topology

end Column

/-- Every smooth zero-row Whittaker coefficient admits a zero-or-one compact
open last-row cutoff, for every supplied p-adic field realization. -/
theorem zeroRowLastRowCutoff : ZeroRowLastRowCutoffStatement.{uF,uV} := by
  intro F _ T n k
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ π hπ ℓ f
  have : T2Space F := T.fieldT2
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
  obtain ⟨K, hK⟩ := hπ v
  have hfix : ∀ u ∈ K, π u v = v := fun u hu =>
    (Representation.mem_invariants _ v).mp hK ⟨u, hu⟩
  -- A lattice of single-coordinate columns fixing `v`.
  let s : Set F := ⋂ i : Fin (n + 1),
    (fun x => zeroRowColumnUnipotent n (0 + k) (Pi.single i x)) ⁻¹'
      (K : Set (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F))
  have hs : IsOpen s := isOpen_iInter_of_finite fun i =>
    K.isOpen.preimage ((continuous_zeroRowColumnUnipotent n (0 + k)).comp
      (continuous_single i))
  have h0 : (0 : F) ∈ s := by
    simp only [s, Set.mem_iInter, Set.mem_preimage, Pi.single_zero,
      zeroRowColumnUnipotent_zero]
    exact fun _ => K.one_mem
  obtain ⟨m, hm⟩ := T.exists_additiveLattice_subset (hs.mem_nhds h0)
  -- The compact open box of last rows.
  let M : ℤ := T.additiveConductor ψ - m
  let B : Set (Fin (n + 1) → F) :=
    Set.univ.pi fun _ => (T.additiveLattice M : Set F)
  have hBc : IsCompact B := isCompact_univ_pi fun _ => T.isCompact_additiveLattice M
  have hBo : IsOpen B :=
    isOpen_set_pi Set.finite_univ fun _ _ => T.isOpen_additiveLattice M
  refine ⟨compactOpenIndicator B hBc hBo, fun y => ?_, fun g => ?_⟩
  · rw [coe_compactOpenIndicator]
    by_cases hy : y ∈ B
    · exact Or.inr (Set.indicator_of_mem hy _)
    · exact Or.inl (Set.indicator_of_notMem hy _)
  · let h := appendIdentity n (0 + k + 1) g
    change ℓ.val (π h v) * _ = ℓ.val (π h v)
    by_cases hz : ℓ.val (π h v) = 0
    · rw [hz, zero_mul]
    · have hrow : lastRow g ∈ B := by
        intro i _
        apply T.mem_additiveLattice_of_forall_mul_eq_one ψ m
        intro x hx
        let z : Fin (n + 1) → F := g.val *ᵥ Pi.single i x
        have hU : zeroRowColumnUnipotent n (0 + k) (Pi.single i x) ∈ K :=
          Set.mem_iInter.mp (hm hx) i
        have hkey := appendIdentity_mul_zeroRowColumnUnipotent n (0 + k) g (Pi.single i x)
        have hact : π (zeroRowColumnUnipotent n (0 + k) z) (π h v) = π h v := by
          calc
            π (zeroRowColumnUnipotent n (0 + k) z) (π h v) =
                π (zeroRowColumnUnipotent n (0 + k) z * h) v := by
              rw [map_mul, Module.End.mul_apply]
            _ = π (appendIdentity n (0 + k + 1) g *
                zeroRowColumnUnipotent n (0 + k) (Pi.single i x)) v := by
              rw [hkey]
            _ = π h v := by
              rw [map_mul, Module.End.mul_apply, hfix _ hU]
        have heq := ℓ.property
          ⟨zeroRowColumnUnipotent n (0 + k) z,
            zeroRowColumnUnipotent_mem_upperUnipotent n (0 + k) z⟩ (π h v)
        change ℓ.val (π (zeroRowColumnUnipotent n (0 + k) z) (π h v)) = _ at heq
        rw [hact, standardCharacter_zeroRowColumnUnipotent] at heq
        have hone : ψ.complex (z (Fin.last n)) = 1 :=
          mul_right_cancel₀ hz (heq.symm.trans (one_mul _).symm)
        have hzlast : z (Fin.last n) = lastRow g i * x := by
          simp [z, Matrix.mulVec_single, lastRow, mul_comm]
        rw [hzlast] at hone
        apply Subtype.ext
        simpa using hone
      rw [coe_compactOpenIndicator, Set.indicator_of_mem hrow, mul_one]

end Langlands.AllField.RankinSelberg
