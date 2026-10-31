import Langlands.ClassFieldTheory.Local.PrimeCriticalNormBaseChangeStatement
import Langlands.ClassFieldTheory.Local.NormTraceCoefficientBaseChange
import Langlands.ClassFieldTheory.Local.PrimeRamificationBreakProof
import Langlands.ClassFieldTheory.Local.PrimeRamifiedGradedNormProof
import Langlands.ClassFieldTheory.Local.PrimeBreakUnramifiedBaseChangeProof
import Langlands.ClassFieldTheory.Local.ResiduePolynomialUnramifiedLiftProof

/-! Critical norm approximation using literal coefficients and bounded residue roots. -/

noncomputable section

namespace Langlands.LocalClassField

open IntermediateField PadicField.TopologicalData

universe u v

private theorem positiveCoordinate_div_mem
    {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
    (T : F.TopologicalData) (π : F.Carrier) (hπ : T.ord π = 1)
    (n : ℕ) (hn : 0 < n) (x y : T.unitFiltration n)
    (h : T.residue (T.unitCoefficient π hπ n x) =
      T.residue (T.unitCoefficient π hπ n y)) :
    (x : F.Carrierˣ) / (y : F.Carrierˣ) ∈ T.unitFiltration (n + 1) := by
  have he : T.positiveUnitCoordinate π hπ n hn x =
      T.positiveUnitCoordinate π hπ n hn y :=
    congrArg Multiplicative.ofAdd h
  have hk : x / y ∈ (T.positiveUnitCoordinate π hπ n hn).ker := by
    change T.positiveUnitCoordinate π hπ n hn (x / y) = 1
    rw [map_div, he, div_self']
  rw [T.positiveUnitCoordinate_ker π hπ n hn] at hk
  exact hk

private theorem zeroCoordinate_div_mem
    {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
    (T : F.TopologicalData) (x y : T.unitFiltration 0)
    (h : T.zeroUnitCoordinate x = T.zeroUnitCoordinate y) :
    (x : F.Carrierˣ) / (y : F.Carrierˣ) ∈ T.unitFiltration 1 := by
  have hk : x / y ∈ T.zeroUnitCoordinate.ker := by
    change T.zeroUnitCoordinate (x / y) = 1
    rw [map_div, h, div_self']
  rw [T.zeroUnitCoordinate_ker] at hk
  exact hk

/-- A bounded residue root removes the critical norm obstruction in the actual
unramified compositum, with the original lower break preserved. -/
theorem primeCriticalNormAfterUnramifiedBaseChange :
    PrimeCriticalNormAfterUnramifiedBaseChange.{u} := by
  classical
  intro p _ F E _
  let := (E.asPadicField (p := p)).algebra
  let : IsScalarTower (Padic p) F.Carrier E.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  dsimp only
  intro hell htot
  let ell := Module.finrank F.Carrier E.field
  let TF := F.canonicalTopologicalData
  let TE := (E.asPadicField (p := p)).canonicalTopologicalData
  obtain ⟨t, hpat, hpos, _⟩ :=
    primeTotallyRamifiedBreak p F (E.asPadicField (p := p)) hell htot
  refine ⟨t, hpat, hpos, ?_⟩
  intro z
  have hab : ∃ a b : TF.Integers,
      TF.residue a ≠ 0 ∧
      (0 < t →
        (a : F.Carrier) = Algebra.norm F.Carrier TE.uniformizer ^ t / TF.uniformizer ^ t ∧
        (b : F.Carrier) =
          Algebra.trace F.Carrier E.field (TE.uniformizer ^ t) / TF.uniformizer ^ t) ∧
      (t = 0 → a = 1 ∧ b = 0) := by
    by_cases ht : 0 < t
    · obtain ⟨_, _, _, _, hc⟩ :=
        primeRamifiedGradedNorm p F (E.asPadicField (p := p)) hell htot t hpat
      obtain ⟨a, b, ha, hb, ha0, _, _⟩ :=
        (hc TF.uniformizer TF.ord_uniformizer TE.uniformizer TE.ord_uniformizer).2.1 ht
      exact ⟨a, b, ha0, fun _ => ⟨ha, hb⟩, fun h => (by omega)⟩
    · refine ⟨1, 0, by simp, ?_, fun _ => ⟨rfl, rfl⟩⟩
      intro h
      exact (ht h).elim
  obtain ⟨a, b, ha0, habpos, habzero⟩ := hab
  let c : TF.ResidueField :=
    if ht : t = 0 then
      (TF.zeroUnitCoordinate (ht ▸ z) : TF.ResidueField)
    else TF.residue (TF.unitCoefficient TF.uniformizer TF.ord_uniformizer t z)
  let P := TF.normTraceResiduePolynomial ell a b c
  have hdeg : P.natDegree = ell :=
    TF.normTraceResiduePolynomial_natDegree ell hell.one_lt a b ha0 c
  obtain ⟨K, hgK, heK, hdK, hroot⟩ :=
    residuePolynomialUnramifiedLift p F P (by rw [hdeg]; exact hell.pos)
  let := (K.asPadicField (p := p)).algebra
  let : IsScalarTower (Padic p) F.Carrier K.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  let TK := (K.asPadicField (p := p)).canonicalTopologicalData
  let rFK := relativeResidueMap TF TK
  obtain ⟨w, hw⟩ := hroot
  have hw' : rFK (TF.residue a) * w ^ ell + rFK (TF.residue b) * w = rFK c := by
    change ((TF.normTraceResiduePolynomial ell a b c).map rFK).eval w = 0 at hw
    rw [TF.normTraceResiduePolynomial_map TK] at hw
    rw [TK.normTraceResiduePolynomial_eval] at hw
    simpa only [← relativeResidueMap_residue TF TK a,
      ← relativeResidueMap_residue TF TK b] using sub_eq_zero.mp hw
  obtain ⟨_, M, hM, hE, hK, hn, he, hgM, hrM, hoE, hoF, hnorm, htrace, hna, htb⟩ :=
    totalUnramifiedCompositum_coefficientTransport F E K htot heK
  let := (M.asPadicField (p := p)).algebra
  let : Algebra E.field M.field := (inclusion hE).toAlgebra
  let : Algebra K.field M.field := (inclusion hK).toAlgebra
  let : IsScalarTower F.Carrier E.field M.field := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F.Carrier K.field M.field := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (Padic p) E.field M.field := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (Padic p) K.field M.field := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional K.field M.field :=
    FiniteDimensional.right F.Carrier K.field M.field
  let TM := (M.asPadicField (p := p)).canonicalTopologicalData
  let rKM := relativeResidueMap TK TM
  let : IsGalois K.field M.field := hgM
  have hellM : Nat.Prime (Module.finrank K.field M.field) := hn ▸ hell
  have htotM : TM.ramificationIndex =
      Module.finrank K.field M.field * TK.ramificationIndex := by
    rw [hn, he, htot, heK]
  have hpatM := primeBreakUnramifiedBaseChange p F E K hell htot heK M hM hE hK t hpat
  refine ⟨K, hgK, heK, ?_, M, hM, hE, hK, hn, ?_, hgM, hpatM, ?_⟩
  · simpa only [hdeg] using hdK
  · simpa only [hn] using htotM
  obtain ⟨hr, hcontain, _, hzero, hc⟩ :=
    primeRamifiedGradedNorm p (K.asPadicField (p := p)) (M.asPadicField (p := p))
      hellM htotM t hpatM
  let zK := relativeUnitFiltrationMap TF TK t z
  have hπK : TK.ord (algebraMap F.Carrier K.field TF.uniformizer) = 1 :=
    (hoF TF.uniformizer).trans TF.ord_uniformizer
  have hπM : TM.ord (inclusion hE TE.uniformizer) = 1 :=
    (hoE TE.uniformizer).trans TE.ord_uniformizer
  by_cases ht : 0 < t
  · obtain ⟨aK, bK, haK, hbK, _, _, hform⟩ :=
      (hc (algebraMap F.Carrier K.field TF.uniformizer) hπK
        (inclusion hE TE.uniformizer) hπM).2.1 ht
    have hka : aK = relativeIntegerMap TF TK a := by
      apply Subtype.ext
      exact haK.trans (hna t TF.uniformizer TE.uniformizer a (habpos ht).1).symm
    have hkb : bK = relativeIntegerMap TF TK b := by
      apply Subtype.ext
      exact hbK.trans (htb t t TF.uniformizer TE.uniformizer b (habpos ht).2).symm
    obtain ⟨y, hy⟩ := TM.positiveUnitCoordinate_surjective
      (inclusion hE TE.uniformizer) hπM t ht (Multiplicative.ofAdd (rKM w))
    have hyres : TM.residue
        (TM.unitCoefficient (inclusion hE TE.uniformizer) hπM t y) = rKM w :=
      congrArg Multiplicative.toAdd hy
    have hNy : normUnits K.field M.field (y : M.fieldˣ) ∈ TK.unitFiltration t := by
      simpa only [ite_true, le_refl] using
        hcontain t ⟨y, by simpa only [ite_true, le_refl] using y.property⟩
    let yN : TK.unitFiltration t := ⟨normUnits K.field M.field y, hNy⟩
    have heqN : TK.residue
        (TK.unitCoefficient (algebraMap F.Carrier K.field TF.uniformizer) hπK t yN) =
          rFK c := by
      apply hr.1
      rw [hform y yN rfl, hka, hkb, ← relativeResidueMap_residue TF TK a,
        ← relativeResidueMap_residue TF TK b, hyres]
      rw [show (rKM w) ^ p = (rKM w) ^ ell from
        congrArg (fun n : ℕ => (rKM w) ^ n) (hpos.mp ht).symm]
      simpa only [map_add, map_mul, map_pow] using congrArg rKM hw'
    refine ⟨y, ?_⟩
    apply positiveCoordinate_div_mem TK
      (algebraMap F.Carrier K.field TF.uniformizer) hπK t ht zK yN
    rw [residue_unitCoefficient_relativeUnitFiltrationMap TF TK
      TF.uniformizer TF.ord_uniformizer hπK]
    simpa only [c, dite_eq_right (Nat.ne_of_gt ht)] using heqN.symm
  · have ht0 : t = 0 := Nat.eq_zero_of_not_pos ht
    subst t
    obtain ⟨ha, hb⟩ := habzero rfl
    have hw0 : w ^ ell = rFK (TF.zeroUnitCoordinate z : TF.ResidueField) := by
      simpa only [ha, hb, map_one, map_zero, one_mul, zero_mul, add_zero, c,
        dite_eq_left rfl]
        using hw'
    have hwne : w ≠ 0 := by
      intro hwz
      have hc0 := hw0
      rw [hwz, zero_pow hell.ne_zero] at hc0
      exact (map_ne_zero rFK).mpr (Units.ne_zero (TF.zeroUnitCoordinate z)) hc0.symm
    let wU : TK.ResidueFieldˣ := Units.mk0 w hwne
    have hwU : wU ^ ell = Units.map rFK.toMonoidHom (TF.zeroUnitCoordinate z) := by
      apply Units.ext
      exact hw0
    obtain ⟨y, hy⟩ := TM.zeroUnitCoordinate_surjective
      (Units.map rKM.toMonoidHom wU)
    have hNy : normUnits K.field M.field (y : M.fieldˣ) ∈ TK.unitFiltration 0 := by
      simpa only [ite_true, le_refl] using
        hcontain 0 ⟨y, by simpa only [ite_true, le_refl] using y.property⟩
    let yN : TK.unitFiltration 0 := ⟨normUnits K.field M.field y, hNy⟩
    have heqN : TK.zeroUnitCoordinate yN = TK.zeroUnitCoordinate zK := by
      apply Units.map_injective hr.1
      rw [hzero y yN rfl, hy, hn, ← map_pow, hwU]
      rw [zeroUnitCoordinate_relativeUnitFiltrationMap TF TK]
    refine ⟨y, ?_⟩
    exact zeroCoordinate_div_mem TK zK yN heqN.symm

end Langlands.LocalClassField
