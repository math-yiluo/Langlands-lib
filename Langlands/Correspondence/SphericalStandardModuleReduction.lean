import Langlands.Correspondence.SphericalStandardModulePrerequisites
import Langlands.Representation.Unramified.SphericalConstituentChoice
import Langlands.Representation.Unramified.SphericalConstituentUniquenessProof
import Mathlib.Data.Fin.Tuple.Sort

/-! # Reduction of spherical standard modules to ordered principal-series facts -/

noncomputable section

namespace Langlands.Correspondence

universe uF uA uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance reductionFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance reductionFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance reductionFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance reductionGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n
local instance reductionGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n
local instance reductionGeneralLinearT2 (n : ℕ) :
    T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearT2Space n
local instance reductionGeneralLinearMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance reductionGeneralLinearBorel (n : ℕ) :
    BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩

/-- Sorting the spectrum preserves the spherical constituent, by constituent
existence and uniqueness, without claiming the two induced modules equivalent. -/
theorem exists_ordered_sphericalConstituent {r : ℕ}
    (A : AutomorphicObject.{uF, uA} F r.succPNat)
    (s : Unramified.Eigenvalues (r + 1))
    (hs : Unramified.HasSphericalSpectrum F A s) :
    ∃ z : Fin (r + 1) → ℂˣ,
      Unramified.Eigenvalues.ofTuple z = s ∧
      Monotone (fun i => ‖(z i : ℂ)‖) ∧
      Unramified.IsSphericalConstituent F z A := by
  obtain ⟨w, hw, hA⟩ := hs
  let e := Tuple.sort (fun i => ‖(w i : ℂ)‖)
  let z : Fin (r + 1) → ℂˣ := w ∘ e
  have hz : Unramified.Eigenvalues.ofTuple z =
      Unramified.Eigenvalues.ofTuple w :=
    Unramified.Eigenvalues.ofTuple_reindex w e
  obtain ⟨B, hB⟩ := Unramified.exists_sphericalConstituentOfTuple.{uF, uA} F z
  obtain ⟨a⟩ := Unramified.sphericalConstituentUniqueness
    p F r z w hz B A hB hA
  refine ⟨z, hz.trans hw, Tuple.monotone_sort (fun i => ‖(w i : ℂ)‖), ?_⟩
  exact (Unramified.isSphericalConstituent_iff_of_equiv F z a).mp hB

/-- Ordered spherical generation upgrades a smooth spherical subquotient to an
actual quotient of the full principal series, in any target carrier universe. -/
theorem exists_principalSeries_quotient_of_generation
    (hgen : OrderedUnramifiedSphericalGenerationStatement F)
    {r : ℕ} (z : Fin (r + 1) → ℂˣ)
    (horder : Monotone (fun i => ‖(z i : ℂ)‖))
    {W : Type uV} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W)
    (hπ : IsSmooth π)
    (hfixed : fixedVectors π (sphericalSubgroup F r) ≠ ⊥)
    (hsub : IsSubquotientOf (Unramified.principalSeriesOfTuple F z) π) :
    ∃ q : (Unramified.principalSeriesOfTuple F z).IntertwiningMap π,
      Function.Surjective q := by
  obtain ⟨S, f, hf⟩ := hsub
  have hS : IsSmooth S.toRepresentation :=
    isSmooth_of_injective
      (Unramified.subrepresentationSubtype (Unramified.principalSeriesOfTuple F z) S)
      (Unramified.subrepresentationSubtype_injective
        (Unramified.principalSeriesOfTuple F z) S)
      (Unramified.isSmooth_principalSeriesOfTuple F z)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfixed
  obtain ⟨v, hv⟩ := Unramified.exists_fixed_lift
    (Unramified.sphericalHaar F r) S.toRepresentation hS π hπ
    (Unramified.sphericalOpenSubgroup F r)
    (Unramified.sphericalOpenSubgroup_isCompact F r)
    f hf ⟨w, hw⟩
  have hv0 : v.1 ≠ 0 := by
    intro h0
    apply hw0
    calc
      w = f v.1 := hv.symm
      _ = 0 := by rw [h0, map_zero]
  have hSfixed : fixedVectors S.toRepresentation (sphericalSubgroup F r) ≠ ⊥ :=
    (fixedVectors S.toRepresentation (sphericalSubgroup F r)).ne_bot_iff.mpr
      ⟨v.1, v.2, hv0⟩
  have htop : S = ⊤ := hgen r z horder S hSfixed
  subst S
  let e : (⊤ : Subrepresentation (Unramified.principalSeriesOfTuple F z)).toRepresentation.Equiv
      (Unramified.principalSeriesOfTuple F z) :=
    Representation.Equiv.mk Submodule.topEquiv (fun g => by ext v; rfl)
  exact ⟨f.comp e.symm.toIntertwiningMap, hf.comp e.symm.surjective⟩

/-- The two ordered principal-series obligations imply the unchanged spherical
tempered standard-module target. -/
theorem sphericalTemperedStandardModule_of_prerequisites
    (hgen : OrderedUnramifiedSphericalGenerationStatement F)
    (hrealize : OrderedUnramifiedTemperedRealizationStatement.{uF, uA} F) :
    SphericalTemperedStandardModuleStatement.{uF, uA} F := by
  intro r A J s ⟨a⟩ hs
  obtain ⟨z, hz, horder, hA⟩ := exists_ordered_sphericalConstituent F A s hs
  obtain ⟨d, ⟨e⟩⟩ := hrealize r z horder
  obtain ⟨q, hq⟩ := exists_principalSeries_quotient_of_generation F hgen
    z horder A.obj.representation A.obj.isSmooth hA.1 hA.2
  refine ⟨d, z, ?_, hz, horder, ⟨e⟩⟩
  exact ⟨(isIrreducible_iff_of_equiv a).mpr A.property.1,
    a.symm.toIntertwiningMap.comp (q.comp e.toIntertwiningMap),
    a.symm.surjective.comp (hq.comp e.surjective)⟩

end Langlands.Correspondence
