import Langlands.HarmonicAnalysis.Basic
import Langlands.Representation.Conductor.Congruence
import Langlands.Group.GL.UpperUnipotent
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Concrete measures for representation-side local integrals

Multiplicative measures are normalized on actual compact-open integral groups.
Rectangular additive measures reuse the shared additive Haar input.
No measure on a nonnormal quotient is inferred from these constructions.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory TopologicalSpace HarmonicAnalysis

universe uG uF

section CompactOpen

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

/-- The positive compact set underlying a compact-open subgroup.
Its interior contains the identity. -/
def compactOpenPositive (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    PositiveCompacts G where
  carrier := K
  isCompact' := hK
  interior_nonempty' := by
    rw [K.isOpen.interior_eq]
    exact ⟨1, K.one_mem⟩

/-- Actual Haar measure with the explicitly chosen compact-open subgroup of mass one. -/
def normalizedCompactOpenHaar (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    Measure G :=
  Measure.haarMeasure (compactOpenPositive K hK)

instance normalizedCompactOpenHaar_isHaar (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) : (normalizedCompactOpenHaar K hK).IsHaarMeasure :=
  inferInstanceAs (Measure.haarMeasure (compactOpenPositive K hK)).IsHaarMeasure

instance normalizedCompactOpenHaar_regular (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) : (normalizedCompactOpenHaar K hK).Regular :=
  inferInstanceAs (Measure.haarMeasure (compactOpenPositive K hK)).Regular

@[simp] theorem normalizedCompactOpenHaar_self (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) :
    normalizedCompactOpenHaar K hK (K : Set G) = 1 :=
  Measure.haarMeasure_self

end CompactOpen

section Units

variable {F : Type uF} [Field F]

/-- The actual unit group of the integral subring, viewed in the field's units. -/
def integralUnits (O : Subring F) : Subgroup Fˣ :=
  (Units.map O.subtype.toMonoidHom).range

theorem mem_integralUnits (O : Subring F) (a : Fˣ) :
    a ∈ integralUnits O ↔ (a : F) ∈ O ∧ ((a⁻¹ : Fˣ) : F) ∈ O := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b.val.property, b.inv.property⟩
  · rintro ⟨ha, hi⟩
    let b : Oˣ :=
      { val := ⟨a.val, ha⟩
        inv := ⟨a.inv, hi⟩
        val_inv := Subtype.ext a.val_inv
        inv_val := Subtype.ext a.inv_val }
    exact ⟨b, Units.ext rfl⟩

variable [TopologicalSpace F] [IsTopologicalRing F]

omit [IsTopologicalRing F] in
theorem integralUnits_isOpen (O : Subring F) (hO : IsOpen (O : Set F)) :
    IsOpen (integralUnits O : Set Fˣ) := by
  have he : (integralUnits O : Set Fˣ) =
      {a : Fˣ | (a : F) ∈ O} ∩ {a : Fˣ | ((a⁻¹ : Fˣ) : F) ∈ O} := by
    ext a
    exact mem_integralUnits O a
  rw [he]
  exact (hO.preimage Units.continuous_val).inter
    (hO.preimage Units.continuous_coe_inv)

/-- The open subgroup of integral field units. -/
def integralUnitsOpen (O : Subring F) (hO : IsOpen (O : Set F)) : OpenSubgroup Fˣ where
  toSubgroup := integralUnits O
  isOpen' := integralUnits_isOpen O hO

theorem integralUnits_isCompact [T2Space F] (O : Subring F) [CompactSpace O] :
    IsCompact (integralUnits O : Set Fˣ) := by
  change IsCompact (Set.range (Units.map O.subtype.toMonoidHom))
  exact isCompact_range (Continuous.units_map _ continuous_subtype_val)

/-- Multiplicative Haar measure with the actual integral units having mass one. -/
def multiplicativeHaar [T2Space F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]
    (O : Subring F) [CompactSpace O] (hO : IsOpen (O : Set F)) : Measure Fˣ :=
  normalizedCompactOpenHaar (integralUnitsOpen O hO) (integralUnits_isCompact O)

instance multiplicativeHaar_isHaar [T2Space F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]
    (O : Subring F) [CompactSpace O] (hO : IsOpen (O : Set F)) :
    (multiplicativeHaar O hO).IsHaarMeasure := by
  unfold multiplicativeHaar
  exact normalizedCompactOpenHaar_isHaar _ _

instance multiplicativeHaar_regular [T2Space F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]
    (O : Subring F) [CompactSpace O] (hO : IsOpen (O : Set F)) :
    (multiplicativeHaar O hO).Regular := by
  unfold multiplicativeHaar
  exact normalizedCompactOpenHaar_regular _ _

@[simp] theorem multiplicativeHaar_integralUnits [T2Space F]
    [MeasurableSpace Fˣ] [BorelSpace Fˣ]
    (O : Subring F) [CompactSpace O] (hO : IsOpen (O : Set F)) :
    multiplicativeHaar O hO (integralUnits O : Set Fˣ) = 1 :=
  normalizedCompactOpenHaar_self (integralUnitsOpen O hO) (integralUnits_isCompact O)

end Units

section LocalField

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- A nonarchimedean local field is Hausdorff, via its uniform additive group. -/
theorem localField_t2 : T2Space F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

/-- The multiplicative Haar measure of a local field, normalized on its integer units. -/
def localMultiplicativeHaar [MeasurableSpace Fˣ] [BorelSpace Fˣ] : Measure Fˣ := by
  have := localField_t2 F
  exact multiplicativeHaar (ValuativeRel.valuation F).integer
    (Valuation.isOpen_integer (v := ValuativeRel.valuation F))

instance localMultiplicativeHaar_isHaar [MeasurableSpace Fˣ] [BorelSpace Fˣ] :
    (localMultiplicativeHaar F).IsHaarMeasure := by
  have := localField_t2 F
  unfold localMultiplicativeHaar
  infer_instance

instance localMultiplicativeHaar_regular [MeasurableSpace Fˣ] [BorelSpace Fˣ] :
    (localMultiplicativeHaar F).Regular := by
  have := localField_t2 F
  unfold localMultiplicativeHaar
  infer_instance

@[simp] theorem localMultiplicativeHaar_integerUnits [MeasurableSpace Fˣ]
    [BorelSpace Fˣ] :
    localMultiplicativeHaar F
      (integralUnits (ValuativeRel.valuation F).integer : Set Fˣ) = 1 := by
  have := localField_t2 F
  exact multiplicativeHaar_integralUnits _ _

/-- Actual Haar measure on `GL_(n+1)` with `GL_(n+1)(O_F)` of mass one.
It uses the conductor branch's proved compact-open level-zero subgroup. -/
def generalLinearHaar (n : ℕ)
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)]
    [BorelSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)] :
    Measure (Matrix.GeneralLinearGroup (Fin (n + 1)) F) :=
  normalizedCompactOpenHaar (Conductor.levelOpenSubgroup F n 0)
    (Conductor.isCompact_levelOpenSubgroup F n 0)

instance generalLinearHaar_isHaar (n : ℕ)
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)]
    [BorelSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)] :
    (generalLinearHaar F n).IsHaarMeasure := by
  unfold generalLinearHaar
  infer_instance

instance generalLinearHaar_regular (n : ℕ)
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)]
    [BorelSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)] :
    (generalLinearHaar F n).Regular := by
  unfold generalLinearHaar
  infer_instance

@[simp] theorem generalLinearHaar_integralSubgroup (n : ℕ)
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)]
    [BorelSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)] :
    generalLinearHaar F n
      (Conductor.integralSubgroup (ValuativeRel.valuation F).integer n :
        Set (Matrix.GeneralLinearGroup (Fin (n + 1)) F)) = 1 := by
  rw [← Conductor.levelSubgroup_zero F n]
  exact normalizedCompactOpenHaar_self _ _

/-- Integral points of the actual upper-unipotent group, as an open subgroup. -/
def unipotentIntegralOpen (n : ℕ) :
    OpenSubgroup (GeneralLinear.upperUnipotent (n + 1) F) :=
  OpenSubgroup.comap (GeneralLinear.upperUnipotent (n + 1) F).subtype
    continuous_subtype_val (Conductor.levelOpenSubgroup F n 0)

/-- The integral unipotent subgroup is compact: it is the inverse image of
the compact integral matrix subgroup under a closed embedding. -/
theorem unipotentIntegralOpen_isCompact (n : ℕ) :
    IsCompact (unipotentIntegralOpen F n : Set (GeneralLinear.upperUnipotent (n + 1) F)) := by
  have := localField_t2 F
  exact (GeneralLinear.UpperUnipotent.isClosed (R := F) (n := n + 1)).isClosedEmbedding_subtypeVal
    |>.isCompact_preimage (Conductor.isCompact_levelOpenSubgroup F n 0)

/-- Actual left Haar on the unipotent subgroup, normalized on its integral points.
Compatibility with product coordinates and with Fourier normalization is separate. -/
def unipotentHaar (n : ℕ)
    [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) F)]
    [BorelSpace (GeneralLinear.upperUnipotent (n + 1) F)] :
    Measure (GeneralLinear.upperUnipotent (n + 1) F) :=
  normalizedCompactOpenHaar (unipotentIntegralOpen F n) (unipotentIntegralOpen_isCompact F n)

instance unipotentHaar_isHaar (n : ℕ)
    [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) F)]
    [BorelSpace (GeneralLinear.upperUnipotent (n + 1) F)] :
    (unipotentHaar F n).IsHaarMeasure := by
  unfold unipotentHaar
  infer_instance

instance unipotentHaar_regular (n : ℕ)
    [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) F)]
    [BorelSpace (GeneralLinear.upperUnipotent (n + 1) F)] :
    (unipotentHaar F n).Regular := by
  unfold unipotentHaar
  infer_instance

@[simp] theorem unipotentHaar_integral (n : ℕ)
    [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) F)]
    [BorelSpace (GeneralLinear.upperUnipotent (n + 1) F)] :
    unipotentHaar F n (unipotentIntegralOpen F n :
      Set (GeneralLinear.upperUnipotent (n + 1) F)) = 1 :=
  normalizedCompactOpenHaar_self _ _

end LocalField

section Rectangular

variable {F : Type uF} [AddGroup F] [TopologicalSpace F] [MeasurableSpace F]

/-- The actual product measure on a rectangular matrix space, from the shared
additive Haar measure on the field. This does not choose another scalar normalization. -/
def rectangularMeasure (μ : AdditiveHaarMeasure F) (j t : ℕ) :
    Measure (Matrix (Fin j) (Fin t) F) :=
  Measure.pi (fun _ : Fin j => Measure.pi (fun _ : Fin t => μ.measure))

/-- The zero-row matrix variable has exactly unit point mass, as required by
the corank-one specialization of the general JPSS integral. -/
@[simp] theorem rectangularMeasure_zero_rows (μ : AdditiveHaarMeasure F) (t : ℕ) :
    rectangularMeasure μ 0 t = Measure.dirac 0 := by
  change (Measure.pi (fun _ : Fin 0 => Measure.pi (fun _ : Fin t => μ.measure)) :
    Measure (Fin 0 → Fin t → F)) = Measure.dirac 0
  exact Measure.pi_of_empty _ _

instance rectangularMeasure_sigmaFinite (μ : AdditiveHaarMeasure F)
    [SigmaFinite μ.measure] (j t : ℕ) : SigmaFinite (rectangularMeasure μ j t) := by
  exact inferInstanceAs (SigmaFinite
    (Measure.pi (fun _ : Fin j => Measure.pi (fun _ : Fin t => μ.measure)) :
      Measure (Fin j → Fin t → F)))

instance rectangularMeasure_isAddHaar [MeasurableAdd₂ F]
    (μ : AdditiveHaarMeasure F) [SigmaFinite μ.measure] (j t : ℕ) :
    (rectangularMeasure μ j t).IsAddHaarMeasure := by
  exact inferInstanceAs
    ((Measure.pi (fun _ : Fin j => Measure.pi (fun _ : Fin t => μ.measure)) :
      Measure (Fin j → Fin t → F)).IsAddHaarMeasure)

/-- If the scalar input gives a set mass one, the rectangular product gives all
matrices with entries in that set mass one as well. -/
theorem rectangularMeasure_entries_one (μ : AdditiveHaarMeasure F)
    [SigmaFinite μ.measure] (j t : ℕ) (S : Set F) (hS : μ.measure S = 1) :
    rectangularMeasure μ j t {x | ∀ a b, x a b ∈ S} = 1 := by
  have he : {x : Matrix (Fin j) (Fin t) F | ∀ a b, x a b ∈ S} =
      Set.univ.pi (fun _ : Fin j => Set.univ.pi (fun _ : Fin t => S)) := by
    ext x
    change (∀ a b, x a b ∈ S) ↔ (∀ a ∈ Set.univ, ∀ b ∈ Set.univ, x a b ∈ S)
    simp
  rw [he]
  change (Measure.pi (fun _ : Fin j => Measure.pi (fun _ : Fin t => μ.measure)) :
    Measure (Fin j → Fin t → F)) (Set.univ.pi (fun _ : Fin j =>
      Set.univ.pi (fun _ : Fin t => S))) = 1
  simp only [Measure.pi_pi, hS, Finset.prod_const_one]

end Rectangular

end Langlands.RankinSelberg
