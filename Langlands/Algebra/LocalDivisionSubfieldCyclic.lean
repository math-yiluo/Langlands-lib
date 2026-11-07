import Langlands.Algebra.LocalDivisionSubfieldSplitting
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-! Original subfield automorphisms, actual reduction, and cyclicity. -/

noncomputable section

namespace Langlands.CentralDivision

open ValuativeRel

universe u uL

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

local instance : Field (DivisionValuation.Residue (localReducedNormValuation K D)) :=
  localDivisionResidueField K D
local instance : Algebra 𝓀[K] (DivisionValuation.Residue (localReducedNormValuation K D)) :=
  localDivisionResidueAlgebra K D
local instance : NontriviallyNormedField K := LocalGalois.localNormedField K
local instance : CompleteSpace K := LocalGalois.localNormedField_complete K
local instance : IsUltrametricDist K := LocalGalois.localNormedField_ultrametric K

section Embedded

variable {L : Type uL} [Field L] [Algebra K L] [FiniteDimensional K L]
  (ι : L →ₐ[K] D)

omit [Algebra.IsCentral K D] in
/-- Original subfield automorphisms preserve the pulled-back actual norm. -/
theorem localDivisionSubfield_norm_aut (σ : L ≃ₐ[K] L) (x : L) :
    letI := localDivisionSubfieldNormedField K D ι
    ‖σ x‖ = ‖x‖ := by
  let := localDivisionSubfieldNormedField K D ι
  let := localDivisionSubfieldNormedAlgebra K D ι
  rw [NormedAlgebra.norm_eq_spectralNorm K, NormedAlgebra.norm_eq_spectralNorm K]
  exact (spectralNorm_eq_of_equiv σ x).symm

/-- Original subfield automorphisms preserve the restricted division-algebra valuation. -/
theorem localDivisionSubfieldValuation_aut (σ : L ≃ₐ[K] L) (x : L) :
    localDivisionSubfieldValuation K D ι (σ x) =
      localDivisionSubfieldValuation K D ι x := by
  let := localDivisionSubfieldNormedField K D ι
  apply le_antisymm
  · apply (localDivisionSubfield_norm_le_iff K D ι _ _).mp
    exact (localDivisionSubfield_norm_aut K D ι σ x).le
  · apply (localDivisionSubfield_norm_le_iff K D ι _ _).mp
    exact (localDivisionSubfield_norm_aut K D ι σ x).ge

/-- Restrict an original subfield automorphism to its actual integer ring. -/
def localDivisionSubfieldIntegerAut (σ : L ≃ₐ[K] L) :
    (localDivisionSubfieldValuation K D ι).integer ≃+*
      (localDivisionSubfieldValuation K D ι).integer where
  toFun x := ⟨σ x.val, by
    change localDivisionSubfieldValuation K D ι (σ x.val) ≤ 1
    rw [localDivisionSubfieldValuation_aut]
    exact x.prop⟩
  invFun x := ⟨σ.symm x.val, by
    change localDivisionSubfieldValuation K D ι (σ.symm x.val) ≤ 1
    rw [localDivisionSubfieldValuation_aut]
    exact x.prop⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x.val)
  right_inv x := Subtype.ext (σ.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add σ x.val y.val)
  map_mul' x y := Subtype.ext (map_mul σ x.val y.val)

/-- The induced homomorphism on the actual strict-ideal residue quotient. -/
def localDivisionSubfieldResidueAutHom (σ : L ≃ₐ[K] L) :
    DivisionValuation.Residue (localDivisionSubfieldValuation K D ι) →+*
      DivisionValuation.Residue (localDivisionSubfieldValuation K D ι) :=
  Ideal.Quotient.lift (DivisionValuation.strictIdeal _)
    ((DivisionValuation.reduction _).comp (localDivisionSubfieldIntegerAut K D ι σ).toRingHom)
    (fun x hx => by
      apply (DivisionValuation.reduction_eq_zero_iff _ _).mpr
      change localDivisionSubfieldValuation K D ι (σ x.val) < 1
      rw [localDivisionSubfieldValuation_aut]
      exact hx)

/-- The original automorphism induces an actual residue automorphism. -/
def localDivisionSubfieldResidueAut (σ : L ≃ₐ[K] L) :
    DivisionValuation.Residue (localDivisionSubfieldValuation K D ι) ≃+*
      DivisionValuation.Residue (localDivisionSubfieldValuation K D ι) where
  __ := localDivisionSubfieldResidueAutHom K D ι σ
  invFun := localDivisionSubfieldResidueAutHom K D ι σ.symm
  left_inv z := by
    obtain ⟨x, rfl⟩ := DivisionValuation.reduction_surjective _ z
    change DivisionValuation.reduction _
      (localDivisionSubfieldIntegerAut K D ι σ.symm
        (localDivisionSubfieldIntegerAut K D ι σ x)) = DivisionValuation.reduction _ x
    congr 1
    exact Subtype.ext (σ.symm_apply_apply x.val)
  right_inv z := by
    obtain ⟨x, rfl⟩ := DivisionValuation.reduction_surjective _ z
    change DivisionValuation.reduction _
      (localDivisionSubfieldIntegerAut K D ι σ
        (localDivisionSubfieldIntegerAut K D ι σ.symm x)) = DivisionValuation.reduction _ x
    congr 1
    exact Subtype.ext (σ.apply_symm_apply x.val)

@[simp]
theorem localDivisionSubfieldResidueAut_reduction (σ : L ≃ₐ[K] L)
    (x : (localDivisionSubfieldValuation K D ι).integer) :
    localDivisionSubfieldResidueAut K D ι σ (DivisionValuation.reduction _ x) =
      DivisionValuation.reduction _ (localDivisionSubfieldIntegerAut K D ι σ x) := rfl

/-- Conjugate the original residue action onto the full actual division-algebra residue. -/
def localDivisionSubfieldFullResidueRingAut
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (σ : L ≃ₐ[K] L) :
    DivisionValuation.Residue (localReducedNormValuation K D) ≃+*
      DivisionValuation.Residue (localReducedNormValuation K D) :=
  let e := RingEquiv.ofBijective (localDivisionSubfieldResidueMap K D ι)
    ⟨(localDivisionSubfieldResidueMap K D ι).injective, hsurj⟩
  e.symm.trans ((localDivisionSubfieldResidueAut K D ι σ).trans e)

@[simp]
theorem localDivisionSubfieldFullResidueRingAut_reduction
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (σ : L ≃ₐ[K] L) (x : (localDivisionSubfieldValuation K D ι).integer) :
    localDivisionSubfieldFullResidueRingAut K D ι hsurj σ
        (localDivisionSubfieldResidueMap K D ι (DivisionValuation.reduction _ x)) =
      localDivisionSubfieldResidueMap K D ι (DivisionValuation.reduction _
        (localDivisionSubfieldIntegerAut K D ι σ x)) := by
  let e := RingEquiv.ofBijective (localDivisionSubfieldResidueMap K D ι)
    ⟨(localDivisionSubfieldResidueMap K D ι).injective, hsurj⟩
  change e (localDivisionSubfieldResidueAut K D ι σ
    (e.symm (e (DivisionValuation.reduction _ x)))) = _
  rw [e.symm_apply_apply]
  rfl

/-- Reduction of an original field automorphism fixes the actual base residue scalars. -/
def localDivisionSubfieldFullResidueAut
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (σ : L ≃ₐ[K] L) :
    DivisionValuation.Residue (localReducedNormValuation K D) ≃ₐ[𝓀[K]]
      DivisionValuation.Residue (localReducedNormValuation K D) where
  __ := localDivisionSubfieldFullResidueRingAut K D ι hsurj σ
  commutes' z := by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    change localDivisionSubfieldFullResidueRingAut K D ι hsurj σ
      (localDivisionBaseReduction K D a) = localDivisionBaseReduction K D a
    rw [← localDivisionSubfieldBaseIntegerMap_reduction K D ι a,
      localDivisionSubfieldFullResidueRingAut_reduction]
    apply congrArg (fun t => localDivisionSubfieldResidueMap K D ι
      (DivisionValuation.reduction _ t))
    apply Subtype.ext
    exact σ.commutes a.val

@[simp]
theorem localDivisionSubfieldFullResidueAut_reduction
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (σ : L ≃ₐ[K] L) (x : (localDivisionSubfieldValuation K D ι).integer) :
    localDivisionSubfieldFullResidueAut K D ι hsurj σ
        (localDivisionSubfieldResidueMap K D ι (DivisionValuation.reduction _ x)) =
      localDivisionSubfieldResidueMap K D ι (DivisionValuation.reduction _
        (localDivisionSubfieldIntegerAut K D ι σ x)) :=
  localDivisionSubfieldFullResidueRingAut_reduction K D ι hsurj σ x

/-- The original Galois group acts on the full actual residue over its original base residue. -/
def localDivisionSubfieldGaloisReduction
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι)) :
    (L ≃ₐ[K] L) →*
      (DivisionValuation.Residue (localReducedNormValuation K D) ≃ₐ[𝓀[K]]
        DivisionValuation.Residue (localReducedNormValuation K D)) where
  toFun := localDivisionSubfieldFullResidueAut K D ι hsurj
  map_one' := by
    ext z
    obtain ⟨z₀, rfl⟩ := hsurj z
    obtain ⟨x, rfl⟩ := DivisionValuation.reduction_surjective _ z₀
    rw [localDivisionSubfieldFullResidueAut_reduction]
    rfl
  map_mul' σ τ := by
    ext z
    obtain ⟨z₀, rfl⟩ := hsurj z
    obtain ⟨x, rfl⟩ := DivisionValuation.reduction_surjective _ z₀
    change localDivisionSubfieldFullResidueAut K D ι hsurj (σ * τ) _ =
      localDivisionSubfieldFullResidueAut K D ι hsurj σ
        (localDivisionSubfieldFullResidueAut K D ι hsurj τ _)
    simp only [localDivisionSubfieldFullResidueAut_reduction]
    rfl

omit [FiniteDimensional K L] in
/-- Original integral roots with simple reduction are determined by their actual residue. -/
theorem localDivisionSubfield_simpleRoot_unique
    (f : Polynomial 𝒪[K])
    (a b : (localDivisionSubfieldValuation K D ι).integer)
    (ha : f.eval₂ (localDivisionSubfieldBaseIntegerMap K D ι) a = 0)
    (hb : f.eval₂ (localDivisionSubfieldBaseIntegerMap K D ι) b = 0)
    (hred : localDivisionSubfieldResidueMap K D ι (DivisionValuation.reduction _ a) =
      localDivisionSubfieldResidueMap K D ι (DivisionValuation.reduction _ b))
    (hder : f.derivative.eval₂ (localDivisionBaseReduction K D)
      (localDivisionSubfieldResidueMap K D ι (DivisionValuation.reduction _ a)) ≠ 0) :
    a = b := by
  let φ := localDivisionSubfieldBaseIntegerMap K D ι
  let ρ := DivisionValuation.reduction (localDivisionSubfieldValuation K D ι)
  let τ := localDivisionSubfieldResidueMap K D ι
  have hcomp : (τ.comp ρ).comp φ = localDivisionBaseReduction K D := by
    ext c
    exact localDivisionSubfieldBaseIntegerMap_reduction K D ι c
  apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := f.map φ)
    (by simpa only [Polynomial.eval_map] using ha)
    (by simpa only [Polynomial.eval_map] using hb)
  · apply (DivisionValuation.mem_strictIdeal_iff_not_isUnit _ _).mp
    rw [DivisionValuation.mem_strictIdeal]
    apply (DivisionValuation.reduction_eq_zero_iff _ _).mp
    rw [map_sub, sub_eq_zero]
    exact τ.injective hred
  · apply (DivisionValuation.isUnit_iff_value_eq_one _ _).mpr
    apply (DivisionValuation.reduction_ne_zero_iff _ _).mp
    intro h
    apply hder
    have hh := congrArg τ h
    rw [map_zero] at hh
    change (τ.comp ρ) ((f.map φ).derivative.eval a) = 0 at hh
    simpa only [Polynomial.derivative_map, Polynomial.eval_map,
      Polynomial.hom_eval₂, hcomp, map_zero, RingHom.comp_apply, τ, ρ] using hh

/-- Original scalar polynomial evaluation commutes with the integer-ring automorphism. -/
theorem localDivisionSubfieldIntegerAut_eval₂
    (σ : L ≃ₐ[K] L) (f : Polynomial 𝒪[K])
    (a : (localDivisionSubfieldValuation K D ι).integer) :
    localDivisionSubfieldIntegerAut K D ι σ
        (f.eval₂ (localDivisionSubfieldBaseIntegerMap K D ι) a) =
      f.eval₂ (localDivisionSubfieldBaseIntegerMap K D ι)
        (localDivisionSubfieldIntegerAut K D ι σ a) := by
  change (localDivisionSubfieldIntegerAut K D ι σ).toRingHom
    (f.eval₂ (localDivisionSubfieldBaseIntegerMap K D ι) a) = _
  rw [Polynomial.hom_eval₂]
  congr 1
  ext c
  exact σ.commutes c.val

/-- A simple integral power-basis generator makes actual Galois reduction faithful. -/
theorem localDivisionSubfieldGaloisReduction_injective
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (pb : PowerBasis K L)
    (a : (localDivisionSubfieldValuation K D ι).integer) (hgen : pb.gen = (a : L))
    (f : Polynomial 𝒪[K])
    (hroot : f.eval₂ (localDivisionSubfieldBaseIntegerMap K D ι) a = 0)
    (hsep : (f.map (IsLocalRing.residue 𝒪[K])).Separable) :
    Function.Injective (localDivisionSubfieldGaloisReduction K D ι hsurj) := by
  let φ := localDivisionSubfieldBaseIntegerMap K D ι
  let ρ := DivisionValuation.reduction (localDivisionSubfieldValuation K D ι)
  let τ := localDivisionSubfieldResidueMap K D ι
  have hcomp : (τ.comp ρ).comp φ = localDivisionBaseReduction K D := by
    ext c
    exact localDivisionSubfieldBaseIntegerMap_reduction K D ι c
  have heval (g : Polynomial 𝒪[K])
      (z : DivisionValuation.Residue (localReducedNormValuation K D)) :
      Polynomial.aeval z (g.map (IsLocalRing.residue 𝒪[K])) =
        g.eval₂ (localDivisionBaseReduction K D) z := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rfl
  have hrootAut (σ : L ≃ₐ[K] L) :
      f.eval₂ φ (localDivisionSubfieldIntegerAut K D ι σ a) = 0 := by
    rw [← localDivisionSubfieldIntegerAut_eval₂, hroot, map_zero]
  intro σ υ h
  have hred : τ (ρ (localDivisionSubfieldIntegerAut K D ι σ a)) =
      τ (ρ (localDivisionSubfieldIntegerAut K D ι υ a)) := by
    have hh := congrArg (fun γ => γ (τ (ρ a))) h
    change localDivisionSubfieldFullResidueAut K D ι hsurj σ _ =
      localDivisionSubfieldFullResidueAut K D ι hsurj υ _ at hh
    dsimp only [τ, ρ] at hh ⊢
    simpa only [localDivisionSubfieldFullResidueAut_reduction] using hh
  have hrootR : Polynomial.aeval
      (τ (ρ (localDivisionSubfieldIntegerAut K D ι σ a)))
      (f.map (IsLocalRing.residue 𝒪[K])) = 0 := by
    rw [heval, ← hcomp]
    change f.eval₂ ((τ.comp ρ).comp φ)
      ((τ.comp ρ) (localDivisionSubfieldIntegerAut K D ι σ a)) = 0
    rw [← Polynomial.hom_eval₂, hrootAut, map_zero]
  have hder : f.derivative.eval₂ (localDivisionBaseReduction K D)
      (τ (ρ (localDivisionSubfieldIntegerAut K D ι σ a))) ≠ 0 := by
    rw [← heval, ← Polynomial.derivative_map]
    exact hsep.aeval_derivative_ne_zero hrootR
  have heq := localDivisionSubfield_simpleRoot_unique K D ι f _ _
    (hrootAut σ) (hrootAut υ) hred hder
  apply AlgEquiv.coe_toAlgHom_injective
  apply pb.algHom_ext
  rw [hgen]
  exact congrArg Subtype.val heq

/-- The faithful actual residue action makes the original field automorphism group cyclic. -/
theorem localDivisionSubfield_isCyclic
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (pb : PowerBasis K L)
    (a : (localDivisionSubfieldValuation K D ι).integer) (hgen : pb.gen = (a : L))
    (f : Polynomial 𝒪[K])
    (hroot : f.eval₂ (localDivisionSubfieldBaseIntegerMap K D ι) a = 0)
    (hsep : (f.map (IsLocalRing.residue 𝒪[K])).Separable) :
    IsCyclic (L ≃ₐ[K] L) :=
  isCyclic_of_injective (localDivisionSubfieldGaloisReduction K D ι hsurj)
    (localDivisionSubfieldGaloisReduction_injective K D ι hsurj pb a hgen f hroot hsep)

end Embedded

/-- An original cyclic Galois full-residue subfield exists with exactly the residue degree. -/
theorem exists_localDivision_fullResidue_cyclic_subfield :
    ∃ b : (localReducedNormValuation K D).integer,
      letI := residueGeneratorField K D (b : D)
      IsSeparable K (b : D) ∧
        Function.Surjective (localDivisionSubfieldResidueMap K D
          (residueGeneratorSubalgebra K D (b : D)).val) ∧
        Module.finrank K (residueGeneratorSubalgebra K D (b : D)) =
          Module.finrank 𝓀[K] (DivisionValuation.Residue (localReducedNormValuation K D)) ∧
        IsGalois K (residueGeneratorSubalgebra K D (b : D)) ∧
        IsCyclic (residueGeneratorSubalgebra K D (b : D) ≃ₐ[K]
          residueGeneratorSubalgebra K D (b : D)) := by
  obtain ⟨f, b, hmon, hres, hmin, hsep, hsurj, hdim⟩ :=
    exists_localDivision_fullResidue_polynomial_subfield K D
  let := residueGeneratorField K D (b : D)
  let E := residueGeneratorSubalgebra K D (b : D)
  let R := DivisionValuation.Residue (localReducedNormValuation K D)
  have hsepR : (f.map (IsLocalRing.residue 𝒪[K])).Separable := by
    rw [hres]
    exact PerfectField.separable_of_irreducible
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral _))
  have hsplitR :
      ((f.map (IsLocalRing.residue 𝒪[K])).map (algebraMap 𝓀[K] R)).Splits := by
    rw [hres]
    exact IsGalois.splits 𝓀[K] _
  have hsplit : ((minpoly K (b : D)).map (algebraMap K E)).Splits := by
    rw [← hmin]
    exact localDivisionSubfield_splits_base_polynomial K D E.val hsurj f hmon hsepR hsplitR
  let : Polynomial.IsSplittingField K E (minpoly K (b : D)) :=
    residueGenerator_isSplittingField K D (b : D) hsplit
  have hgal : IsGalois K E := IsGalois.of_separable_splitting_field hsep
  let a : (localDivisionSubfieldValuation K D E.val).integer :=
    ⟨⟨(b : D), residueGenerator_mem K D (b : D)⟩, b.prop⟩
  have hroot : f.eval₂ (localDivisionSubfieldBaseIntegerMap K D E.val) a = 0 := by
    let θ : (localDivisionSubfieldValuation K D E.val).integer →+* D :=
      E.val.toRingHom.comp (localDivisionSubfieldValuation K D E.val).integer.subtype
    have hθ : θ.comp (localDivisionSubfieldBaseIntegerMap K D E.val) =
        (algebraMap K D).comp (algebraMap 𝒪[K] K) := by
      ext c
      exact E.val.commutes c.val
    apply (E.val.injective.comp Subtype.val_injective)
    change θ (f.eval₂ (localDivisionSubfieldBaseIntegerMap K D E.val) a) = θ 0
    rw [map_zero, Polynomial.hom_eval₂, hθ, ← Polynomial.eval₂_map]
    change Polynomial.aeval (b : D) (f.map (algebraMap 𝒪[K] K)) = 0
    rw [hmin]
    exact minpoly.aeval K (b : D)
  refine ⟨b, hsep, hsurj, hdim, hgal, ?_⟩
  exact localDivisionSubfield_isCyclic K D E.val hsurj
    (residueGeneratorPowerBasis K D (b : D)) a rfl f hroot hsepR

end Langlands.CentralDivision
