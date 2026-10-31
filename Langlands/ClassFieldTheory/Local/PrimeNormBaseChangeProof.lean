import Langlands.ClassFieldTheory.Local.PrimeNormBaseChangeStatement
import Langlands.ClassFieldTheory.Local.TotalUnramifiedCompositumProof
import Langlands.ClassFieldTheory.Local.PrimeCriticalNormBaseChangeProof
import Langlands.ClassFieldTheory.Local.PrimeRamifiedNormReductionProof

/-! Exact prime-degree norms by critical approximation and higher-unit correction. -/

noncomputable section

namespace Langlands.LocalClassField

open IntermediateField

universe u

private theorem compositum_unitsNorm_inclusion
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (E K M : FiniteIntermediateExtension F.Carrier) [IsGalois F.Carrier E.field]
    (hM : M.field = E.field ⊔ K.field)
    (hE : E.field ≤ M.field) (hK : K.field ≤ M.field)
    (hEram : (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier E.field * F.canonicalTopologicalData.ramificationIndex)
    (hKram : (K.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex)
    (y : E.fieldˣ) :
    K.unitsNorm M hK (E.unitsInclusion M hE y) =
      Units.map (algebraMap F.Carrier K.field).toMonoidHom
        (normUnits F.Carrier E.field y) := by
  obtain ⟨_, M', hM', hE', hK', _, _, _, _, _, hn⟩ :=
    totalUnramifiedCompositum p F E K hEram hKram
  have heq : M' = M := Subtype.ext (hM'.trans hM.symm)
  subst M'
  apply Units.ext
  exact hn (y : E.field)

private theorem compositum_unitsNorm_corrected_witness
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (E K M : FiniteIntermediateExtension F.Carrier) [IsGalois F.Carrier E.field]
    (hM : M.field = E.field ⊔ K.field)
    (hE : E.field ≤ M.field) (hK : K.field ≤ M.field)
    (hEram : (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier E.field * F.canonicalTopologicalData.ramificationIndex)
    (hKram : (K.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex)
    (x z : F.Carrierˣ) (yE : E.fieldˣ)
    (hx : x = normUnits F.Carrier E.field yE * z)
    (yC yH : M.fieldˣ)
    (herr : K.unitsNorm M hK yH =
      Units.map (algebraMap F.Carrier K.field).toMonoidHom z /
        K.unitsNorm M hK yC) :
    K.unitsNorm M hK (E.unitsInclusion M hE yE * (yC * yH)) =
      Units.map (algebraMap F.Carrier K.field).toMonoidHom x := by
  rw [map_mul, map_mul, compositum_unitsNorm_inclusion F E K M hM hE hK hEram hKram,
    herr, hx, map_mul]
  simp [div_eq_mul_inv, mul_left_comm, mul_comm]

/-- Every field unit becomes an exact norm after a bounded unramified Galois
base change, using the actual compositum and determinant norm. -/
theorem primeNormAfterUnramifiedBaseChange :
    PrimeNormAfterUnramifiedBaseChange.{u} := by
  classical
  intro p _ F E _
  let := (E.asPadicField (p := p)).algebra
  let : IsScalarTower (Padic p) F.Carrier E.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  dsimp only
  intro hell htot x
  obtain ⟨t, hpat, _, hcrit⟩ :=
    primeCriticalNormAfterUnramifiedBaseChange p F E hell htot
  obtain ⟨_, _, hred⟩ :=
    primeRamifiedNormReduction p F (E.asPadicField (p := p)) hell htot t hpat
  obtain ⟨yE, z, hx⟩ := hred x
  obtain ⟨K, hgK, heK, hdK, M, hM, hE, hK, hdata⟩ := hcrit z
  let := (K.asPadicField (p := p)).algebra
  let := (M.asPadicField (p := p)).algebra
  let : Algebra E.field M.field := (inclusion hE).toAlgebra
  let : Algebra K.field M.field := (inclusion hK).toAlgebra
  let : IsScalarTower F.Carrier E.field M.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F.Carrier K.field M.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (Padic p) F.Carrier K.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (Padic p) E.field M.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (Padic p) K.field M.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional K.field M.field :=
    FiniteDimensional.right F.Carrier K.field M.field
  obtain ⟨hn, htotM, hgM, hpatM, yC, herr⟩ := hdata
  let : IsGalois K.field M.field := hgM
  let TK := (K.asPadicField (p := p)).canonicalTopologicalData
  let TM := (M.asPadicField (p := p)).canonicalTopologicalData
  have hellM : Nat.Prime (Module.finrank K.field M.field) := hn ▸ hell
  have htotM' : TM.ramificationIndex =
      Module.finrank K.field M.field * TK.ramificationIndex := by
    rw [hn]
    exact htotM
  obtain ⟨_, hhigh, _⟩ :=
    primeRamifiedNormReduction p (K.asPadicField (p := p))
      (M.asPadicField (p := p)) hellM htotM' t hpatM
  have heq : (TM.unitFiltration (t + 1)).map (normUnits K.field M.field) =
      TK.unitFiltration (t + 1) := by
    simpa only [le_refl, ite_true] using hhigh t (le_refl t)
  have hpre :
      Units.map (algebraMap F.Carrier K.field).toMonoidHom (z : F.Carrierˣ) /
          K.unitsNorm M hK (yC : M.fieldˣ) ∈
        (TM.unitFiltration (t + 1)).map (normUnits K.field M.field) := by
    rw [heq]
    exact herr
  obtain ⟨yH, _, hyH⟩ := hpre
  refine ⟨K, hgK, heK, hdK, M, hM, hK,
    E.unitsInclusion M hE yE * ((yC : M.fieldˣ) * yH), ?_⟩
  exact compositum_unitsNorm_corrected_witness F E K M hM hE hK htot heK
    x z yE hx yC yH hyH

end Langlands.LocalClassField
