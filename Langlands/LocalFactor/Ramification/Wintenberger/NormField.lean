import Langlands.LocalFactor.Ramification.Wintenberger.Absolute
import FontaineWintenberger.FieldOfNorms.Galois.Filtration
import FontaineWintenberger.FieldOfNorms.Relative.EssImage
import FontaineWintenberger.LocalField.Spectral.Uniqueness
import FontaineWintenberger.Ramification.Upper.Transport

/-!
# The filtration of the field of norms and the Library's filtration of a local field

Let `L/K` be an infinite arithmetically profinite extension, `Ω` a separable closure of `K`
containing `L`, `X = X_K(L)` the field of norms and `U = RelFieldOfNorms K L Ω`, which is a
separable closure of `X`. The FontaineWintenberger library puts on `Gal(U/X)` the upper filtration
`RelFieldOfNorms.normUpperRamificationGroup K L Ω`, computed from the finite norm fields `X_K(N)`,
`N/L` finite Galois in `Ω`. If a Mathlib local field `X'` is identified with `X` by an isomorphism
compatible with the valuations, this filtration is the Library's filtration of `X'` in the
separable closure `U`.
-/

noncomputable section

namespace Langlands.Ramification.Wintenberger

universe uK uL uΩ uX

section Setting

variable (K : Type uK) [NontriviallyNormedField K] [FontaineWintenberger.IsPerfectResidueLocalField K]
  (L : Type uL) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [FontaineWintenberger.IsAPF K L]
  [Fact (¬ Module.Finite K L)]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsSepClosure K Ω]
  [IsSepClosure L Ω]
  (X' : Type uX) [Field X'] [Algebra X' (FontaineWintenberger.FieldOfNorms K L)]
  [Algebra X' (FontaineWintenberger.RelFieldOfNorms K L Ω)]
  [IsScalarTower X' (FontaineWintenberger.FieldOfNorms K L)
    (FontaineWintenberger.RelFieldOfNorms K L Ω)]

/-- If the base `X'` is identified with the field of norms, the relative field of norms is a
separable closure of `X'`. -/
theorem relFieldOfNorms_isSepClosure
    (hbij : Function.Bijective (algebraMap X' (FontaineWintenberger.FieldOfNorms K L))) :
    IsSepClosure X' (FontaineWintenberger.RelFieldOfNorms K L Ω) := by
  have : Algebra.IsSeparable X' (FontaineWintenberger.FieldOfNorms K L) := by
    constructor
    intro x
    obtain ⟨y, rfl⟩ := hbij.2 x
    have h := (Algebra.IsSeparable.isSeparable X' y).map
      (f := Algebra.ofId X' (FontaineWintenberger.FieldOfNorms K L)) hbij.1
    simpa using h
  have : Algebra.IsSeparable (FontaineWintenberger.FieldOfNorms K L)
      (FontaineWintenberger.RelFieldOfNorms K L Ω) :=
    FontaineWintenberger.RelFieldOfNorms.isSeparable K L Ω
  have : Algebra.IsSeparable X' (FontaineWintenberger.RelFieldOfNorms K L Ω) :=
    Algebra.IsSeparable.trans X' (FontaineWintenberger.FieldOfNorms K L) _
  have : IsSepClosed (FontaineWintenberger.RelFieldOfNorms K L Ω) :=
    FontaineWintenberger.RelFieldOfNorms.isSepClosed K L Ω
  exact isSepClosure_iff.mpr ⟨inferInstance, inferInstance⟩

end Setting

section RestrictScalars

variable (R S A : Type*) [CommRing R] [CommRing S] [Ring A] [Algebra R S] [Algebra S A]
  [Algebra R A] [IsScalarTower R S A]

/-- Restriction of scalars along a surjective base map is an isomorphism of automorphism groups. -/
def restrictScalarsMulEquiv (h : Function.Surjective (algebraMap R S)) :
    (A ≃ₐ[S] A) ≃* (A ≃ₐ[R] A) :=
  MulEquiv.ofBijective (AlgEquiv.restrictScalarsHom R)
    ⟨AlgEquiv.restrictScalars_injective R, fun σ =>
      ⟨{ σ with
          commutes' := fun s => by
            obtain ⟨r, rfl⟩ := h s
            change σ (algebraMap S A (algebraMap R S r)) = algebraMap S A (algebraMap R S r)
            rw [← IsScalarTower.algebraMap_apply]
            exact σ.commutes r }, AlgEquiv.ext fun _ => rfl⟩⟩

@[simp]
theorem restrictScalarsMulEquiv_apply (h : Function.Surjective (algebraMap R S)) (σ : A ≃ₐ[S] A)
    (a : A) : restrictScalarsMulEquiv R S A h σ a = σ a := rfl

end RestrictScalars

section Stages

variable (K : Type uK) [NontriviallyNormedField K] [FontaineWintenberger.IsPerfectResidueLocalField K]
  (L : Type uL) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [FontaineWintenberger.IsAPF K L]
  [Fact (¬ Module.Finite K L)]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] 
  [IsSepClosure L Ω]
  (X' : Type uX) [Field X'] [Algebra X' (FontaineWintenberger.FieldOfNorms K L)]
  [Algebra X' (FontaineWintenberger.RelFieldOfNorms K L Ω)]
  [IsScalarTower X' (FontaineWintenberger.FieldOfNorms K L)
    (FontaineWintenberger.RelFieldOfNorms K L Ω)]

/-- A finite Galois subextension of `Ω/L`, as a finite intermediate field. -/
def galoisStage (N : FiniteGaloisIntermediateField L Ω) :
    FontaineWintenberger.FiniteIntermediateField L Ω :=
  ⟨N.toIntermediateField, inferInstance⟩

/-- The norm field of a finite Galois stage, inside the relative field of norms. -/
abbrev stageImage (N : FiniteGaloisIntermediateField L Ω) :
    IntermediateField (FontaineWintenberger.FieldOfNorms K L)
      (FontaineWintenberger.RelFieldOfNorms K L Ω) :=
  FontaineWintenberger.RelFieldOfNorms.finiteImage K L Ω (galoisStage L Ω N)

/-- The norm field of a finite stage is isomorphic to its image. -/
def stageEquiv (N : FiniteGaloisIntermediateField L Ω) :
    FontaineWintenberger.FieldOfNorms K (galoisStage L Ω N).val ≃ₐ[FontaineWintenberger.FieldOfNorms K L]
      stageImage K L Ω N :=
  AlgEquiv.ofInjectiveField (FontaineWintenberger.RelFieldOfNorms.ofAlgHom K L Ω (galoisStage L Ω N))

instance galoisStage_isGalois (N : FiniteGaloisIntermediateField L Ω) :
    IsGalois L (galoisStage L Ω N).val :=
  inferInstanceAs (IsGalois L N)

theorem stageImage_isGalois (N : FiniteGaloisIntermediateField L Ω) :
    IsGalois (FontaineWintenberger.FieldOfNorms K L) (stageImage K L Ω N) := by
  have : IsGalois (FontaineWintenberger.FieldOfNorms K L)
      (FontaineWintenberger.FieldOfNorms K (galoisStage L Ω N).val) :=
    FontaineWintenberger.FieldOfNorms.isGalois K L (galoisStage L Ω N).val
  exact IsGalois.of_algEquiv (stageEquiv K L Ω N)

end Stages

section GaloisBaseChange

variable (F' F E : Type*) [Field F'] [Field F] [Field E] [Algebra F' F] [Algebra F E] [Algebra F' E]
  [IsScalarTower F' F E]

theorem finiteDimensional_of_surjective (h : Function.Surjective (algebraMap F' F))
    [FiniteDimensional F E] : FiniteDimensional F' E := by
  have : Module.Finite F' F := Module.Finite.of_surjective (Algebra.linearMap F' F) h
  exact Module.Finite.trans F E

/-- A Galois extension of `F` is Galois over every field `F'` mapping onto `F`. -/
theorem isGalois_of_surjective (h : Function.Surjective (algebraMap F' F))
    [FiniteDimensional F E] [IsGalois F E] : IsGalois F' E := by
  have := finiteDimensional_of_surjective F' F E h
  apply IsGalois.of_fixedField_eq_bot
  rw [eq_bot_iff]
  intro x hx
  have hbot : x ∈ (⊥ : IntermediateField F E) := by
    rw [← IsGalois.fixedField_fixingSubgroup (⊥ : IntermediateField F E),
      IntermediateField.fixingSubgroup_bot]
    rintro ⟨σ, -⟩
    exact hx ⟨σ.restrictScalars F', Subgroup.mem_top _⟩
  obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.mp hbot
  obtain ⟨z, rfl⟩ := h y
  rw [← IsScalarTower.algebraMap_apply]
  exact IntermediateField.algebraMap_mem _ z

end GaloisBaseChange

section StagesOverX

variable (K : Type uK) [NontriviallyNormedField K] [FontaineWintenberger.IsPerfectResidueLocalField K]
  (L : Type uL) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [FontaineWintenberger.IsAPF K L]
  [Fact (¬ Module.Finite K L)]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] 
  [IsSepClosure L Ω]
  (X' : Type uX) [Field X'] [Algebra X' (FontaineWintenberger.FieldOfNorms K L)]
  [Algebra X' (FontaineWintenberger.RelFieldOfNorms K L Ω)]
  [IsScalarTower X' (FontaineWintenberger.FieldOfNorms K L)
    (FontaineWintenberger.RelFieldOfNorms K L Ω)]

/-- The identity of the elements of an intermediate field, after restriction of scalars. -/
def restrictScalarsAlgEquiv {A B C : Type*} [Field A] [Field B] [Field C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] (S : IntermediateField B C) :
    S ≃ₐ[A] S.restrictScalars A where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The norm field of a finite Galois stage, as a finite Galois subextension of the relative field
of norms over `X'`. -/
def stageGalois (hbij : Function.Bijective (algebraMap X' (FontaineWintenberger.FieldOfNorms K L)))
    (N : FiniteGaloisIntermediateField L Ω) :
    FiniteGaloisIntermediateField X' (FontaineWintenberger.RelFieldOfNorms K L Ω) :=
  have : FiniteDimensional (FontaineWintenberger.FieldOfNorms K L) (stageImage K L Ω N) :=
    FontaineWintenberger.RelFieldOfNorms.finiteImage_finite K L Ω (galoisStage L Ω N)
  have := stageImage_isGalois K L Ω N
  have : FiniteDimensional X' (stageImage K L Ω N) :=
    finiteDimensional_of_surjective X' (FontaineWintenberger.FieldOfNorms K L) _ hbij.2
  have : IsGalois X' (stageImage K L Ω N) :=
    isGalois_of_surjective X' (FontaineWintenberger.FieldOfNorms K L) _ hbij.2
  { toIntermediateField := (stageImage K L Ω N).restrictScalars X'
    finiteDimensional := (restrictScalarsAlgEquiv (stageImage K L Ω N)).toLinearEquiv.finiteDimensional
    isGalois := IsGalois.of_algEquiv (restrictScalarsAlgEquiv (stageImage K L Ω N)) }

end StagesOverX

section Integers

variable (K : Type uK) [NontriviallyNormedField K] [FontaineWintenberger.IsPerfectResidueLocalField K]
  (L : Type uL) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [FontaineWintenberger.IsAPF K L]
  [Fact (¬ Module.Finite K L)]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] 
  [IsSepClosure L Ω]
  (X' : Type uX) [Field X'] [Algebra X' (FontaineWintenberger.FieldOfNorms K L)]
  [Algebra X' (FontaineWintenberger.RelFieldOfNorms K L Ω)]
  [IsScalarTower X' (FontaineWintenberger.FieldOfNorms K L)
    (FontaineWintenberger.RelFieldOfNorms K L Ω)]
  (hbij : Function.Bijective (algebraMap X' (FontaineWintenberger.FieldOfNorms K L)))

/-- The norm field of a finite Galois stage, identified with its image over `X'`. -/
def stageRingEquiv (N : FiniteGaloisIntermediateField L Ω) :
    stageGalois K L Ω X' hbij N ≃+* FontaineWintenberger.FieldOfNorms K (galoisStage L Ω N).val :=
  (restrictScalarsAlgEquiv (A := X') (stageImage K L Ω N)).symm.toRingEquiv.trans
    (stageEquiv K L Ω N).symm.toRingEquiv

theorem stageRingEquiv_algebraMap (N : FiniteGaloisIntermediateField L Ω) (x : X') :
    stageRingEquiv K L Ω X' hbij N (algebraMap X' (stageGalois K L Ω X' hbij N) x) =
      algebraMap (FontaineWintenberger.FieldOfNorms K L)
        (FontaineWintenberger.FieldOfNorms K (galoisStage L Ω N).val)
        (algebraMap X' (FontaineWintenberger.FieldOfNorms K L) x) := by
  have h : (restrictScalarsAlgEquiv (A := X') (stageImage K L Ω N)).symm
      (algebraMap X' (stageGalois K L Ω X' hbij N) x) =
      algebraMap (FontaineWintenberger.FieldOfNorms K L) (stageImage K L Ω N)
        (algebraMap X' (FontaineWintenberger.FieldOfNorms K L) x) := by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply X' (FontaineWintenberger.FieldOfNorms K L)
      (FontaineWintenberger.RelFieldOfNorms K L Ω) x
  change (stageEquiv K L Ω N).symm ((restrictScalarsAlgEquiv (A := X') (stageImage K L Ω N)).symm
    (algebraMap X' (stageGalois K L Ω X' hbij N) x)) = _
  rw [h, AlgEquiv.commutes]

/-- The valuation of the norm field of a stage, on its image over `X'`. -/
def stageValuation (N : FiniteGaloisIntermediateField L Ω) :
    Valuation (stageGalois K L Ω X' hbij N) (WithZero (Multiplicative ℤ)) :=
  (FontaineWintenberger.FieldOfNorms.fieldValuation K (galoisStage L Ω N).val).comap
    (stageRingEquiv K L Ω X' hbij N).toRingHom

end Integers

section HasExtension

variable (K : Type uK) [NontriviallyNormedField K] [FontaineWintenberger.IsPerfectResidueLocalField K]
  (L : Type uL) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [FontaineWintenberger.IsAPF K L]
  [Fact (¬ Module.Finite K L)]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] 
  [IsSepClosure L Ω]
  (X' : Type uX) [Field X'] [ValuativeRel X'] [TopologicalSpace X'] [IsNonarchimedeanLocalField X']
  [Algebra X' (FontaineWintenberger.FieldOfNorms K L)]
  [Algebra X' (FontaineWintenberger.RelFieldOfNorms K L Ω)]
  [IsScalarTower X' (FontaineWintenberger.FieldOfNorms K L)
    (FontaineWintenberger.RelFieldOfNorms K L Ω)]
  (hbij : Function.Bijective (algebraMap X' (FontaineWintenberger.FieldOfNorms K L)))
  (hval : ∀ x y : X', ValuativeRel.vle x y ↔
    FontaineWintenberger.FieldOfNorms.fieldValuation K L (algebraMap X' _ x) ≤
      FontaineWintenberger.FieldOfNorms.fieldValuation K L (algebraMap X' _ y))

include hval in
/-- The valuation of a finite norm field extends the norm of `X'`. -/
theorem stageValuation_hasExtension (N : FiniteGaloisIntermediateField L Ω) :
    letI := LocalGalois.localNormedField X'
    letI := LocalGalois.localNormedField_ultrametric X'
    (NormedField.valuation (K := X')).HasExtension (stageValuation K L Ω X' hbij N) := by
  let := LocalGalois.localNormedField X'
  have := LocalGalois.localNormedField_ultrametric X'
  have hext := FontaineWintenberger.FieldOfNorms.fieldValuation_hasExtension_inclusion K L
    (galoisStage L Ω N).val
  constructor
  intro x y
  simp only [Valuation.comap_apply, stageValuation, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    stageRingEquiv_algebraMap]
  have h1 := hext.val_isEquiv_comap (algebraMap X' _ x) (algebraMap X' _ y)
  simp only [Valuation.comap_apply] at h1
  rw [NormedField.valuation_apply, NormedField.valuation_apply, ← NNReal.coe_le_coe,
    coe_nnnorm, coe_nnnorm, LocalGalois.localNormedField_le, ← Valuation.vle_iff_le]
  exact (hval x y).trans h1

end HasExtension

section StageComparison

variable (K : Type uK) [NontriviallyNormedField K] [FontaineWintenberger.IsPerfectResidueLocalField K]
  (L : Type uL) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [FontaineWintenberger.IsAPF K L]
  [Fact (¬ Module.Finite K L)]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] 
  [IsSepClosure L Ω]
  (X' : Type uX) [Field X'] [ValuativeRel X'] [TopologicalSpace X'] [IsNonarchimedeanLocalField X']
  [Algebra X' (FontaineWintenberger.FieldOfNorms K L)]
  [Algebra X' (FontaineWintenberger.RelFieldOfNorms K L Ω)]
  [IsScalarTower X' (FontaineWintenberger.FieldOfNorms K L)
    (FontaineWintenberger.RelFieldOfNorms K L Ω)]
  (hbij : Function.Bijective (algebraMap X' (FontaineWintenberger.FieldOfNorms K L)))
  (hval : ∀ x y : X', ValuativeRel.vle x y ↔
    FontaineWintenberger.FieldOfNorms.fieldValuation K L (algebraMap X' _ x) ≤
      FontaineWintenberger.FieldOfNorms.fieldValuation K L (algebraMap X' _ y))

local instance normFieldLocalNormedFieldX : NontriviallyNormedField X' := LocalGalois.localNormedField X'
local instance normFieldLocalUltrametricX : IsUltrametricDist X' := LocalGalois.localNormedField_ultrametric X'
local instance normFieldLocalFieldX : FontaineWintenberger.IsPerfectResidueLocalField X' :=
  localField_isPerfectResidueLocalField X'

include hval in
/-- The spectral integers of a stage over `X'` are the valuation ring of the norm field. -/
theorem spectralIntegerRing_stage_eq (N : FiniteGaloisIntermediateField L Ω) :
    FontaineWintenberger.spectralIntegerRing X' (stageGalois K L Ω X' hbij N) =
      (stageValuation K L Ω X' hbij N).valuationSubring := by
  have := stageValuation_hasExtension K L Ω X' hbij hval N
  exact FontaineWintenberger.spectralIntegerRing_eq_extension_valuationSubring X'
    (stageGalois K L Ω X' hbij N) (stageValuation K L Ω X' hbij N)

/-- The valuation ring of the norm field of a stage, identified with the spectral integers of its
image over `X'`. -/
def stageIntegerEquiv (N : FiniteGaloisIntermediateField L Ω) :
    (FontaineWintenberger.FieldOfNorms.fieldValuation K (galoisStage L Ω N).val).valuationSubring ≃+*
      FontaineWintenberger.spectralIntegerRing X' (stageGalois K L Ω X' hbij N) where
  toFun y := ⟨(stageRingEquiv K L Ω X' hbij N).symm y, by
    rw [spectralIntegerRing_stage_eq K L Ω X' hbij hval N, Valuation.mem_valuationSubring_iff]
    change FontaineWintenberger.FieldOfNorms.fieldValuation K (galoisStage L Ω N).val
      ((stageRingEquiv K L Ω X' hbij N) ((stageRingEquiv K L Ω X' hbij N).symm y)) ≤ 1
    rw [RingEquiv.apply_symm_apply]
    exact y.2⟩
  invFun z := ⟨stageRingEquiv K L Ω X' hbij N z, by
    have h : (z : stageGalois K L Ω X' hbij N) ∈ (stageValuation K L Ω X' hbij N).valuationSubring := by
      rw [← spectralIntegerRing_stage_eq K L Ω X' hbij hval N]
      exact z.2
    exact h⟩
  left_inv y := Subtype.ext ((stageRingEquiv K L Ω X' hbij N).apply_symm_apply y)
  right_inv z := Subtype.ext ((stageRingEquiv K L Ω X' hbij N).symm_apply_apply z)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_add' x y := Subtype.ext (map_add _ _ _)

/-- The Galois group of a finite stage, identified with the Galois group of its norm field over
`X'`. -/
def stageAutEquiv (N : FiniteGaloisIntermediateField L Ω) :
    ((galoisStage L Ω N).val ≃ₐ[L] (galoisStage L Ω N).val) ≃*
      (stageGalois K L Ω X' hbij N ≃ₐ[X'] stageGalois K L Ω X' hbij N) :=
  (FontaineWintenberger.FieldOfNorms.autEquiv K L (galoisStage L Ω N).val).trans
    ((stageEquiv K L Ω N).autCongr.trans
      ((restrictScalarsMulEquiv X' (FontaineWintenberger.FieldOfNorms K L) (stageImage K L Ω N)
        hbij.2).trans (restrictScalarsAlgEquiv (A := X') (stageImage K L Ω N)).autCongr))

theorem stageIntegerEquiv_smul (N : FiniteGaloisIntermediateField L Ω)
    (g : (galoisStage L Ω N).val ≃ₐ[L] (galoisStage L Ω N).val)
    (a : (FontaineWintenberger.FieldOfNorms.fieldValuation K (galoisStage L Ω N).val).valuationSubring) :
    letI := FontaineWintenberger.FieldOfNorms.integerGaloisAction K L (galoisStage L Ω N).val
    stageIntegerEquiv K L Ω X' hbij hval N (g • a) =
      stageAutEquiv K L Ω X' hbij N g • stageIntegerEquiv K L Ω X' hbij hval N a := by
  let := FontaineWintenberger.FieldOfNorms.integerGaloisAction K L (galoisStage L Ω N).val
  apply Subtype.ext
  change restrictScalarsAlgEquiv (A := X') (stageImage K L Ω N) (stageEquiv K L Ω N
      (FontaineWintenberger.FieldOfNorms.autEquiv K L (galoisStage L Ω N).val g a)) =
    restrictScalarsAlgEquiv (A := X') (stageImage K L Ω N) (stageEquiv K L Ω N
      (FontaineWintenberger.FieldOfNorms.autEquiv K L (galoisStage L Ω N).val g
        ((stageEquiv K L Ω N).symm ((restrictScalarsAlgEquiv (A := X') (stageImage K L Ω N)).symm
          (restrictScalarsAlgEquiv (A := X') (stageImage K L Ω N) (stageEquiv K L Ω N a))))))
  rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]

end StageComparison

section Comparison

variable (K : Type uK) [NontriviallyNormedField K] [FontaineWintenberger.IsPerfectResidueLocalField K]
  (L : Type uL) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [FontaineWintenberger.IsAPF K L]
  [Fact (¬ Module.Finite K L)]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] 
  [IsSepClosure L Ω]
  (X' : Type uX) [Field X'] [ValuativeRel X'] [TopologicalSpace X'] [IsNonarchimedeanLocalField X']
  [Algebra X' (FontaineWintenberger.FieldOfNorms K L)]
  [Algebra X' (FontaineWintenberger.RelFieldOfNorms K L Ω)]
  [IsScalarTower X' (FontaineWintenberger.FieldOfNorms K L)
    (FontaineWintenberger.RelFieldOfNorms K L Ω)]
  (hbij : Function.Bijective (algebraMap X' (FontaineWintenberger.FieldOfNorms K L)))
  (hval : ∀ x y : X', ValuativeRel.vle x y ↔
    FontaineWintenberger.FieldOfNorms.fieldValuation K L (algebraMap X' _ x) ≤
      FontaineWintenberger.FieldOfNorms.fieldValuation K L (algebraMap X' _ y))

local instance normFieldLocalNormedFieldX₂ : NontriviallyNormedField X' := LocalGalois.localNormedField X'
local instance normFieldLocalUltrametricX₂ : IsUltrametricDist X' :=
  LocalGalois.localNormedField_ultrametric X'
local instance normFieldLocalFieldX₂ : FontaineWintenberger.IsPerfectResidueLocalField X' :=
  localField_isPerfectResidueLocalField X'

include hval in
/-- The upper groups of a finite Galois stage, computed on its norm field, are the
FontaineWintenberger upper groups of its image over `X'`. -/
theorem stage_upperRamificationGroup_map (N : FiniteGaloisIntermediateField L Ω) {v : ℝ}
    (hv : -1 ≤ v) :
    (FontaineWintenberger.FieldOfNorms.upperRamificationGroup K L (galoisStage L Ω N).val v).map
        (stageAutEquiv K L Ω X' hbij N).toMonoidHom =
      FontaineWintenberger.upperRamificationGroup
        (R := FontaineWintenberger.spectralIntegerRing X' (stageGalois K L Ω X' hbij N))
        (stageGalois K L Ω X' hbij N ≃ₐ[X'] stageGalois K L Ω X' hbij N) v := by
  unfold FontaineWintenberger.FieldOfNorms.upperRamificationGroup
  let := FontaineWintenberger.FieldOfNorms.integerGaloisAction K L (galoisStage L Ω N).val
  exact FontaineWintenberger.upperRamificationGroup_map_equivariant
    (stageIntegerEquiv K L Ω X' hbij hval N) (stageAutEquiv K L Ω X' hbij N)
    (stageIntegerEquiv_smul K L Ω X' hbij hval N) hv

omit [ValuativeRel X'] [TopologicalSpace X'] [IsNonarchimedeanLocalField X'] in
/-- Restriction to a stage corresponds to restriction to its norm field. -/
theorem stageAutEquiv_restrictNormal (N : FiniteGaloisIntermediateField L Ω) (τ : Ω ≃ₐ[L] Ω) :
    stageAutEquiv K L Ω X' hbij N (τ.restrictNormal (galoisStage L Ω N).val) =
      ((FontaineWintenberger.RelFieldOfNorms.autEquiv K L Ω τ).restrictScalars X').restrictNormal
        (stageGalois K L Ω X' hbij N) := by
  apply AlgEquiv.ext
  intro z
  apply Subtype.ext
  rw [show ((((FontaineWintenberger.RelFieldOfNorms.autEquiv K L Ω τ).restrictScalars X').restrictNormal
      (stageGalois K L Ω X' hbij N) z : stageGalois K L Ω X' hbij N) :
        FontaineWintenberger.RelFieldOfNorms K L Ω) =
      FontaineWintenberger.RelFieldOfNorms.autEquiv K L Ω τ (z : _) from
    AlgEquiv.restrictNormal_commutes _ _ z]
  obtain ⟨x, rfl⟩ : ∃ x, z = restrictScalarsAlgEquiv (A := X') (stageImage K L Ω N)
      (stageEquiv K L Ω N x) :=
    ⟨(stageEquiv K L Ω N).symm ((restrictScalarsAlgEquiv (A := X') (stageImage K L Ω N)).symm z),
      by
        rw [AlgEquiv.apply_symm_apply]
        exact ((restrictScalarsAlgEquiv (A := X') (stageImage K L Ω N)).apply_symm_apply z).symm⟩
  change FontaineWintenberger.RelFieldOfNorms.of K L Ω (galoisStage L Ω N)
      (FontaineWintenberger.FieldOfNorms.autEquiv K L (galoisStage L Ω N).val
        (τ.restrictNormal (galoisStage L Ω N).val)
        ((stageEquiv K L Ω N).symm ((restrictScalarsAlgEquiv (A := X') (stageImage K L Ω N)).symm
          (restrictScalarsAlgEquiv (A := X') (stageImage K L Ω N) (stageEquiv K L Ω N x))))) =
    FontaineWintenberger.RelFieldOfNorms.autEquiv K L Ω τ
      (FontaineWintenberger.RelFieldOfNorms.of K L Ω (galoisStage L Ω N) x)
  rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply,
    FontaineWintenberger.RelFieldOfNorms.autEquiv_of,
    FontaineWintenberger.FieldOfNorms.autEquiv_apply, FontaineWintenberger.RelFieldOfNorms.stageMap_apply]
  symm
  apply FontaineWintenberger.RelFieldOfNorms.of_transport_congr K L Ω
  · apply Subtype.ext
    exact (IntermediateField.normal_iff_forall_map_eq'.mp inferInstance τ)
  · intro a
    exact (AlgEquiv.restrictNormal_commutes τ (galoisStage L Ω N).val a).symm

end Comparison

section Main

variable (K : Type uK) [NontriviallyNormedField K] [FontaineWintenberger.IsPerfectResidueLocalField K]
  (L : Type uL) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [FontaineWintenberger.IsAPF K L]
  [Fact (¬ Module.Finite K L)]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsSepClosure K Ω]
  [IsSepClosure L Ω]
  (X' : Type uX) [Field X'] [ValuativeRel X'] [TopologicalSpace X'] [IsNonarchimedeanLocalField X']
  [Algebra X' (FontaineWintenberger.FieldOfNorms K L)]
  [Algebra X' (FontaineWintenberger.RelFieldOfNorms K L Ω)]
  [IsScalarTower X' (FontaineWintenberger.FieldOfNorms K L)
    (FontaineWintenberger.RelFieldOfNorms K L Ω)]
  (hbij : Function.Bijective (algebraMap X' (FontaineWintenberger.FieldOfNorms K L)))
  (hval : ∀ x y : X', ValuativeRel.vle x y ↔
    FontaineWintenberger.FieldOfNorms.fieldValuation K L (algebraMap X' _ x) ≤
      FontaineWintenberger.FieldOfNorms.fieldValuation K L (algebraMap X' _ y))

local instance normFieldLocalNormedFieldX₃ : NontriviallyNormedField X' := LocalGalois.localNormedField X'
local instance normFieldLocalUltrametricX₃ : IsUltrametricDist X' :=
  LocalGalois.localNormedField_ultrametric X'
local instance normFieldLocalFieldX₃ : FontaineWintenberger.IsPerfectResidueLocalField X' :=
  localField_isPerfectResidueLocalField X'

omit [ValuativeRel X'] [TopologicalSpace X'] [IsNonarchimedeanLocalField X'] [IsSepClosure K Ω] in
/-- The norm fields of the finite Galois stages are cofinal among the finite Galois subextensions
of the relative field of norms over `X'`. -/
theorem stageGalois_cofinal
    (D : FiniteGaloisIntermediateField X' (FontaineWintenberger.RelFieldOfNorms K L Ω)) :
    ∃ N : FiniteGaloisIntermediateField L Ω, D ≤ stageGalois K L Ω X' hbij N := by
  let D' : IntermediateField (FontaineWintenberger.FieldOfNorms K L)
      (FontaineWintenberger.RelFieldOfNorms K L Ω) :=
    { D.toIntermediateField.toSubfield with
      algebraMap_mem' := fun y => by
        obtain ⟨y', rfl⟩ := hbij.2 y
        rw [← IsScalarTower.algebraMap_apply]
        exact D.toIntermediateField.algebraMap_mem y' }
  have hD : D'.restrictScalars X' = D.toIntermediateField := IntermediateField.ext fun _ => Iff.rfl
  have : FiniteDimensional (FontaineWintenberger.FieldOfNorms K L) D' := by
    have : FiniteDimensional X' (D'.restrictScalars X') := by
      rw [hD]
      infer_instance
    have : FiniteDimensional X' D' :=
      (restrictScalarsAlgEquiv (A := X') D').symm.toLinearEquiv.finiteDimensional
    exact Module.Finite.of_restrictScalars_finite X' (FontaineWintenberger.FieldOfNorms K L) D'
  obtain ⟨Q, hQ⟩ := FontaineWintenberger.RelFieldOfNorms.exists_finiteImage_ge K L Ω D'
  have : IsGalois L Ω := inferInstance
  let N : FiniteGaloisIntermediateField L Ω := { IntermediateField.normalClosure L Q.val Ω with }
  refine ⟨N, ?_⟩
  have hQN : Q ≤ galoisStage L Ω N := IntermediateField.le_normalClosure Q.val
  have h1 : D' ≤ stageImage K L Ω N :=
    hQ.trans ((FontaineWintenberger.RelFieldOfNorms.finiteImage_le_iff K L Ω Q _).mpr hQN)
  change D.toIntermediateField ≤ (stageImage K L Ω N).restrictScalars X'
  rw [← hD]
  exact fun x hx => h1 hx

include hval in
/-- **The filtration of the field of norms is the Library's filtration of `X'`.** For an
automorphism `σ` of the relative field of norms over the field of norms and `v ≥ -1`, `σ` lies in
the upper group of the FontaineWintenberger library at `v` exactly when, as an automorphism over
`X'`, it lies in the Library's absolute upper group of `X'` at `v`. -/
theorem mem_normUpperRamificationGroup_iff
    (σ : FontaineWintenberger.RelFieldOfNorms K L Ω ≃ₐ[FontaineWintenberger.FieldOfNorms K L]
      FontaineWintenberger.RelFieldOfNorms K L Ω) {v : ℝ} (hv : -1 ≤ v) :
    σ ∈ FontaineWintenberger.RelFieldOfNorms.normUpperRamificationGroup K L Ω v ↔
      haveI := relFieldOfNorms_isSepClosure K L Ω X' hbij
      σ.restrictScalars X' ∈
        Local.localAbsoluteUpperRamificationGroup X' (FontaineWintenberger.RelFieldOfNorms K L Ω) v := by
  have := relFieldOfNorms_isSepClosure K L Ω X' hbij
  obtain ⟨τ, rfl⟩ := (FontaineWintenberger.RelFieldOfNorms.autEquiv K L Ω).surjective σ
  rw [FontaineWintenberger.RelFieldOfNorms.autEquiv_mem_normUpperRamificationGroup_iff,
    FontaineWintenberger.RelFieldOfNorms.mem_upperRamificationGroup,
    ← upperRamificationGroupInfinite_eq_local X' _ v,
    FontaineWintenberger.mem_upperRamificationGroupInfinite_iff_cofinal X' _
      (stageGalois K L Ω X' hbij) (stageGalois_cofinal K L Ω X' hbij) hv]
  refine forall_congr' fun N => ?_
  rw [← stageAutEquiv_restrictNormal K L Ω X' hbij N τ,
    ← stage_upperRamificationGroup_map K L Ω X' hbij hval N hv]
  change τ.restrictNormal (galoisStage L Ω N).val ∈
    FontaineWintenberger.FieldOfNorms.upperRamificationGroup K L (galoisStage L Ω N).val v ↔ _
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

end Main

end Langlands.Ramification.Wintenberger
