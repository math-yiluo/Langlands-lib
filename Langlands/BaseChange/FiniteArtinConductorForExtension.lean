import Langlands.ClassFieldTheory.Local.FiniteConductorProof
import Langlands.ClassFieldTheory.Local.FiniteArtinSystemExistenceProof
import Langlands.ClassFieldTheory.Local.NormUnitImageCardinalityProof

/-! # Conductor transport for a finite abelian extension given as a field -/

noncomputable section

namespace Langlands.BaseChange

open LocalClassField LocalClassField.FiniteArtinSystemExistence Ramification.Padic
open scoped IsMulCommutative

universe u

variable {p : ℕ} [Fact p.Prime] (F M : PadicField.{u} p)
  [Algebra F.Carrier M.Carrier] [IsScalarTower (Padic p) F.Carrier M.Carrier]
  [IsAbelianGalois F.Carrier M.Carrier] (T : F.TopologicalData) (S : M.TopologicalData)

/-- The geometric Artin symbol as a continuous homomorphism on the supplied field. -/
def geometricArtinHom :
    letI := T.topology
    F.Carrierˣ →ₜ* (M.Carrier ≃ₐ[F.Carrier] M.Carrier) := by
  let := T.topology
  exact { toMonoidHom := geometricArtin F M S
          continuous_toFun := continuous_geometricArtin F T M S }

/-- The actual units at a real upper level map onto the corresponding
ramification group of the supplied finite abelian extension. -/
theorem geometricArtin_unitFiltration_map {s : ℝ} (hs : 0 ≤ s) :
    (T.unitFiltration ⌈s⌉₊).map (geometricArtin F M S) =
      upperRamificationGroup S F.Carrier s := by
  let : FiniteDimensional F.Carrier M.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) F.Carrier M.Carrier
  let H := upperRamificationGroup S F.Carrier s
  let E := fixedPadicField F M H
  let R := E.canonicalTopologicalData
  let : FiniteDimensional F.Carrier E.Carrier := inferInstanceAs
    (FiniteDimensional F.Carrier (IntermediateField.fixedField H))
  let : IsAbelianGalois F.Carrier E.Carrier := inferInstanceAs
    (IsAbelianGalois F.Carrier (IntermediateField.fixedField H))
  let q : (M.Carrier ≃ₐ[F.Carrier] M.Carrier) →* (E.Carrier ≃ₐ[F.Carrier] E.Carrier) :=
    AlgEquiv.restrictNormalHom (IntermediateField.fixedField H)
  have hk : q.ker = H :=
    ((IntermediateField.fixedField H).restrictNormalHom_ker).trans
      (IntermediateField.fixingSubgroup_fixedField H)
  have hmap : H.map q = upperRamificationGroup R F.Carrier s :=
    Ramification.HerbrandBridge.upperQuotientCompatibility F M S H R s (by linarith)
  have hbot : upperRamificationGroup R F.Carrier s = ⊥ := by
    rw [← hmap, Subgroup.map_eq_bot_iff, hk]
  have htab := NormUnitImage.finiteAbelianNormUnitImageCardinality p F E T R s hs
  rw [hbot, Subgroup.card_bot] at htab
  have hlev : T.unitFiltration ⌈s⌉₊ ≤ normSubgroup F.Carrier E.Carrier := by
    have h := Subgroup.eq_bot_of_card_eq _ htab
    rw [Subgroup.map_eq_bot_iff] at h
    exact h.trans (QuotientGroup.ker_mk' _).le
  change (T.unitFiltration ⌈s⌉₊).map (geometricSymbol F M.Carrier) = H
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨a, ha, rfl⟩
    rw [← hk, MonoidHom.mem_ker]
    have hr : q (geometricSymbol F M.Carrier a) = geometricSymbol F E.Carrier a :=
      restrictNormalHom_geometricSymbol F M.Carrier E.Carrier a
    rw [hr, ← MonoidHom.mem_ker, ker_geometricSymbol]
    exact hlev ha
  · let e := QuotientGroup.liftEquiv (normSubgroup F.Carrier M.Carrier)
      (geometricSymbol_surjective F M.Carrier) (ker_geometricSymbol F M.Carrier).symm
    have he : e.toMonoidHom.comp (normQuotientProjection F.Carrier M.Carrier) =
        geometricSymbol F M.Carrier := MonoidHom.ext fun a => rfl
    have hcard := NormUnitImage.finiteAbelianNormUnitImageCardinality p F M T S s hs
    rw [← hcard, ← he, ← Subgroup.map_map]
    exact (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).ge

/-- A character of the supplied finite Galois group transported by its geometric symbol. -/
def geometricArtinCharacter (χ : (M.Carrier ≃ₐ[F.Carrier] M.Carrier) →* ℂˣ) :
    letI := T.topology
    HarmonicAnalysis.Quasicharacter F.Carrier := by
  let := T.topology
  let : FiniteDimensional F.Carrier M.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) F.Carrier M.Carrier
  exact (⟨χ, continuous_of_discreteTopology⟩ : (_ ≃ₐ[F.Carrier] _) →ₜ* ℂˣ).comp
    (geometricArtinHom F M T S)

/-- The conductor transport theorem for a finite abelian extension on its
supplied carrier, using the actual one-dimensional Artin expression. -/
theorem geometricArtin_multiplicativeConductor (χ : (M.Carrier ≃ₐ[F.Carrier] M.Carrier) →* ℂˣ) :
    (T.multiplicativeConductor (geometricArtinCharacter F M T S χ) : ℚ) =
      artinConductor S F.Carrier (rankOneCharacterRepresentation χ) := by
  let := T.topology
  symm
  apply artinConductor_rankOne_eq_of_upper_levels
  intro s hs
  rw [T.multiplicativeConductor_le_iff_unitFiltration_le_ker,
    ← geometricArtin_unitFiltration_map F M T S hs]
  constructor
  · rintro h g ⟨a, ha, rfl⟩
    exact h ha
  · intro h a ha
    exact h _ ⟨a, ha, rfl⟩

end Langlands.BaseChange
