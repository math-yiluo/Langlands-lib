import Langlands.Global.Factors.CuspidalIsobaricFiniteFamilyStatement
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Representation.Classification.IsobaricSumExistence
import Langlands.Representation.Classification.IsobaricSumSubquotient
import Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof
import Langlands.Representation.Unramified.SphericalIsobaricSum

/-! Construction of the finite-place family of cuspidal isobaric sums. -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open CompletionPadic (padicField)
open Correspondence (AutomorphicObject)

local instance {F : Type u} [Field F] [NumberField F] (v : FinitePlace F) (n : ℕ) :
    TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

/-- The local isobaric sums form a family of induced constituents that is
spherical outside the union of the presentations' exceptional sets. -/
theorem cuspidalIsobaricFiniteFamily : CuspidalIsobaricFiniteFamilyStatement.{u, uQ} := by
  classical
  intro F _ _ _ r k m hm T P h
  let σ (v : FinitePlace F) (i : Fin k) : AutomorphicObject.{u, u} (padicField v) (m i).succPNat :=
    ((P i).localComponent v).padicObject (h i v).1 (h i v).2
  have hexists (v : FinitePlace F) :
      ∃ A : AutomorphicObject.{u, u} (padicField v) r.succPNat,
        (padicField v).canonicalTopologicalData.IsIsobaricSum.{u, u}
          (fun i => (σ v i).obj) A.obj := by
    let D := (padicField v).canonicalTopologicalData
    obtain ⟨X, hX⟩ := D.exists_isIsobaricSum.{u, u} hm (fun i => (σ v i).obj)
      (fun i => (σ v i).property.1)
    have hI := hX.isIrreducible
    have hA := Classification.TwoFactorCommutativity.isAdmissible_of_isIrreducible
      (padicField v) D X.representation X.isSmooth hI
    exact ⟨⟨X, hI, hA⟩, hX⟩
  choose A hA using hexists
  let S := Finset.univ.biUnion fun i : Fin k => (P i).exceptional
  refine ⟨A, S, hA, ?_, ?_⟩
  · intro v
    let B : GeneralLinear.BlockShape (r + 1) := ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
    exact PadicField.TopologicalData.IsIsobaricSum.isSubquotient_normalizedProduct
      (padicField v).canonicalTopologicalData (Nat.succ_pos r) B (hA v)
  · intro v hv
    apply Unramified.isSpherical_of_isIsobaricSum (padicField v) hm (hA v)
    intro i
    have hi : v ∉ (P i).exceptional := fun hvi =>
      hv (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hvi⟩)
    obtain ⟨_, _, hz⟩ :=
      CuspidalPairFunctionalEquation.hasSphericalSpectrum_padicObject (P i) (h i) v hi
    exact hz.1

end Langlands.Global
