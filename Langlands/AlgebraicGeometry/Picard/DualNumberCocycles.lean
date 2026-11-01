import Langlands.AlgebraicGeometry.Picard.DualNumberActualUnits
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleGauge
import Langlands.AlgebraicGeometry.Modules.CechDegreeOne

/-! # Additive cocycles and actual normalized dual-number unit cocycles -/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.DualNumberThickening

open Langlands.Scheme.Modules

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The actual unit with specified first-order coefficient. -/
def coefficientUnit (U : X.Opens) (a : Γ(X, U)) :
    Γ(thickening f, projection f ⁻¹ᵁ U)ˣ :=
  (unitKernelEquiv f U (Multiplicative.ofAdd a)).val

@[simp]
lemma coefficientUnit_val (U : X.Opens) (a : Γ(X, U)) :
    (coefficientUnit f U a : Γ(thickening f, projection f ⁻¹ᵁ U)) =
      1 + (projection f).app U a * epsilonSection f U :=
  unitKernelEquiv_val f U a

lemma coefficientUnit_injective (U : X.Opens) : Function.Injective (coefficientUnit f U) := by
  intro a b h
  exact congrArg Multiplicative.toAdd ((unitKernelEquiv f U).injective (Subtype.ext h))

@[simp]
lemma coefficientUnit_zero (U : X.Opens) : coefficientUnit f U 0 = 1 := by
  exact congrArg Subtype.val ((unitKernelEquiv f U).map_one)

lemma coefficientUnit_add (U : X.Opens) (a b : Γ(X, U)) :
    coefficientUnit f U (a + b) = coefficientUnit f U a * coefficientUnit f U b :=
  congrArg Subtype.val ((unitKernelEquiv f U).map_mul
    (Multiplicative.ofAdd a) (Multiplicative.ofAdd b))

@[simp]
lemma coefficientUnit_neg (U : X.Opens) (a : Γ(X, U)) :
    coefficientUnit f U (-a) = (coefficientUnit f U a)⁻¹ :=
  congrArg Subtype.val ((unitKernelEquiv f U).map_inv (Multiplicative.ofAdd a))

lemma coefficientUnit_sub (U : X.Opens) (a b : Γ(X, U)) :
    coefficientUnit f U (a - b) = coefficientUnit f U a * (coefficientUnit f U b)⁻¹ := by
  rw [sub_eq_add_neg, coefficientUnit_add, coefficientUnit_neg]

lemma coefficientUnit_restrict {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    Units.map ((thickening f).presheaf.map
        ((Opens.map (projection f).base).map (homOfLE h)).op).hom.toMonoidHom
      (coefficientUnit f U a) =
      coefficientUnit f V (X.presheaf.map (homOfLE h).op a) :=
  congrArg Subtype.val (unitKernelMap_equiv f h a)

lemma coefficientUnit_restrict_val {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (thickening f).presheaf.map
        ((Opens.map (projection f).base).map (homOfLE h)).op
      (coefficientUnit f U a : Γ(thickening f, projection f ⁻¹ᵁ U)) =
      (coefficientUnit f V (X.presheaf.map (homOfLE h).op a) :
        Γ(thickening f, projection f ⁻¹ᵁ V)) :=
  congrArg Units.val (coefficientUnit_restrict f h a)

@[simp]
lemma coefficientUnit_reduction (U : X.Opens) (a : Γ(X, U)) :
    unitReduction f U (coefficientUnit f U a) = 1 :=
  (unitKernelEquiv f U (Multiplicative.ofAdd a)).property

/-- Lift ordinary units by the actual first projection. -/
def liftUnit (U : X.Opens) : Γ(X, U)ˣ →* Γ(thickening f, projection f ⁻¹ᵁ U)ˣ :=
  Units.map ((projection f).app U).hom.toMonoidHom

@[simp]
lemma unitReduction_liftUnit (U : X.Opens) (a : Γ(X, U)ˣ) :
    unitReduction f U (liftUnit f U a) = a := by
  apply Units.ext
  exact reductionMap_projection_apply f U (a : Γ(X, U))

/-- Divide an actual unit by the canonical lift of its reduction. -/
def normalizeUnit (U : X.Opens) :
    Γ(thickening f, projection f ⁻¹ᵁ U)ˣ →* UnitKernel f U where
  toFun a := ⟨a * (liftUnit f U (unitReduction f U a))⁻¹, by
    change unitReduction f U (a * (liftUnit f U (unitReduction f U a))⁻¹) = 1
    rw [map_mul, map_inv, unitReduction_liftUnit, mul_inv_cancel]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    change (a * b) * (liftUnit f U (unitReduction f U (a * b)))⁻¹ =
      (a * (liftUnit f U (unitReduction f U a))⁻¹) *
        (b * (liftUnit f U (unitReduction f U b))⁻¹)
    simp only [map_mul, mul_inv_rev]
    ac_rfl

@[simp]
lemma normalizeUnit_coefficientUnit (U : X.Opens) (a : Γ(X, U)) :
    normalizeUnit f U (coefficientUnit f U a) =
      unitKernelEquiv f U (Multiplicative.ofAdd a) := by
  apply Subtype.ext
  change coefficientUnit f U a * (liftUnit f U (unitReduction f U (coefficientUnit f U a)))⁻¹ = _
  rw [coefficientUnit_reduction, map_one, inv_one, mul_one]
  rfl

/-- The first-order coefficient of any unit after dividing by its reduction. -/
def unitCoefficient (U : X.Opens) :
    Γ(thickening f, projection f ⁻¹ᵁ U)ˣ →* Multiplicative Γ(X, U) :=
  (unitKernelEquiv f U).symm.toMonoidHom.comp (normalizeUnit f U)

@[simp]
lemma unitCoefficient_coefficientUnit (U : X.Opens) (a : Γ(X, U)) :
    unitCoefficient f U (coefficientUnit f U a) = Multiplicative.ofAdd a := by
  change (unitKernelEquiv f U).symm (normalizeUnit f U (coefficientUnit f U a)) = _
  rw [normalizeUnit_coefficientUnit, MulEquiv.symm_apply_apply]

lemma unitReduction_naturality {U V : X.Opens} (h : V ≤ U)
    (a : Γ(thickening f, projection f ⁻¹ᵁ U)ˣ) :
    unitReduction f V (Units.map ((thickening f).presheaf.map
      ((Opens.map (projection f).base).map (homOfLE h)).op).hom.toMonoidHom a) =
      Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom (unitReduction f U a) := by
  apply Units.ext
  exact congrArg (fun r ↦ r.hom (a : Γ(thickening f, projection f ⁻¹ᵁ U)))
    (reductionMap_naturality f h)

lemma liftUnit_naturality {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) :
    Units.map ((thickening f).presheaf.map
      ((Opens.map (projection f).base).map (homOfLE h)).op).hom.toMonoidHom
      (liftUnit f U a) =
      liftUnit f V (Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom a) := by
  apply Units.ext
  exact (congrArg (fun r ↦ r.hom (a : Γ(X, U)))
    ((projection f).naturality (homOfLE h).op)).symm

lemma normalizeUnit_naturality {U V : X.Opens} (h : V ≤ U)
    (a : Γ(thickening f, projection f ⁻¹ᵁ U)ˣ) :
    unitKernelMap f h (normalizeUnit f U a) =
      normalizeUnit f V (Units.map ((thickening f).presheaf.map
        ((Opens.map (projection f).base).map (homOfLE h)).op).hom.toMonoidHom a) := by
  apply Subtype.ext
  change Units.map ((thickening f).presheaf.map
    ((Opens.map (projection f).base).map (homOfLE h)).op).hom.toMonoidHom
      (a * (liftUnit f U (unitReduction f U a))⁻¹) = _
  rw [map_mul, map_inv, liftUnit_naturality]
  change _ = _ * (liftUnit f V (unitReduction f V _))⁻¹
  rw [unitReduction_naturality]

lemma unitCoefficient_naturality {U V : X.Opens} (h : V ≤ U)
    (a : Γ(thickening f, projection f ⁻¹ᵁ U)ˣ) :
    unitCoefficient f V (Units.map ((thickening f).presheaf.map
      ((Opens.map (projection f).base).map (homOfLE h)).op).hom.toMonoidHom a) =
      Multiplicative.ofAdd (X.presheaf.map (homOfLE h).op (unitCoefficient f U a).toAdd) := by
  have he := unitKernelMap_equiv f h (unitCoefficient f U a).toAdd
  change unitKernelMap f h
    (unitKernelEquiv f U ((unitKernelEquiv f U).symm (normalizeUnit f U a))) = _ at he
  rw [MulEquiv.apply_symm_apply, normalizeUnit_naturality] at he
  apply (unitKernelEquiv f V).injective
  change unitKernelEquiv f V ((unitKernelEquiv f V).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  exact he

/-- The cover of the actual thickening induced by a family of opens of `X`. -/
abbrev thickenedOpens {ι : Type u} (T : ι → X.Opens) (i : ι) : (thickening f).Opens :=
  projection f ⁻¹ᵁ T i

/-- The actual unit cochain `1 + epsilon z`, on inverse-image intersections. -/
def unitCochain {ι : Type u} (T : ι → X.Opens)
    (z : ∀ i j, Γ(X, T i ⊓ T j)) (i j : ι) :
    Γ(thickening f, thickenedOpens f T i ⊓ thickenedOpens f T j)ˣ :=
  coefficientUnit f (T i ⊓ T j) (z i j)

set_option backward.isDefEq.respectTransparency false in
/-- The actual multiplicative cocycle condition is exactly the additive one. -/
lemma isCocycle_unitCochain_iff {ι : Type u} (T : ι → X.Opens)
    (z : ∀ i j, Γ(X, T i ⊓ T j)) :
    CocycleGluing.IsCocycle (unitCochain f T z) ↔
      Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCocycle
        (G := structureSheaf X) T z := by
  constructor
  · intro hz i j l O hij hjl hil
    have h := CocycleGluing.cocycle_res (unitCochain f T z) hz i j l
      (W := projection f ⁻¹ᵁ O)
      ((Opens.map (projection f).base).map (homOfLE hij)).le
      ((Opens.map (projection f).base).map (homOfLE hjl)).le
      ((Opens.map (projection f).base).map (homOfLE hil)).le
    change (thickening f).presheaf.map
        ((Opens.map (projection f).base).map (homOfLE hij)).op
          (coefficientUnit f (T i ⊓ T j) (z i j) : Γ(thickening f, projection f ⁻¹ᵁ (T i ⊓ T j))) *
      (thickening f).presheaf.map
        ((Opens.map (projection f).base).map (homOfLE hjl)).op
          (coefficientUnit f (T j ⊓ T l) (z j l) : Γ(thickening f, projection f ⁻¹ᵁ (T j ⊓ T l))) =
      (thickening f).presheaf.map
        ((Opens.map (projection f).base).map (homOfLE hil)).op
          (coefficientUnit f (T i ⊓ T l) (z i l) : Γ(thickening f, projection f ⁻¹ᵁ (T i ⊓ T l))) at h
    rw [coefficientUnit_restrict_val f hij (z i j),
      coefficientUnit_restrict_val f hjl (z j l),
      coefficientUnit_restrict_val f hil (z i l)] at h
    apply coefficientUnit_injective f O
    apply Units.ext
    rw [coefficientUnit_add, Units.val_mul]
    exact h
  · intro hz i j l
    have h := hz i j l (O := T i ⊓ T j ⊓ T l) inf_le_left
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    change (thickening f).presheaf.map
        ((Opens.map (projection f).base).map
          (homOfLE (inf_le_left : T i ⊓ T j ⊓ T l ≤ T i ⊓ T j))).op
          (coefficientUnit f (T i ⊓ T j) (z i j) : Γ(thickening f, projection f ⁻¹ᵁ (T i ⊓ T j))) *
      (thickening f).presheaf.map
        ((Opens.map (projection f).base).map
          (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            T i ⊓ T j ⊓ T l ≤ T j ⊓ T l))).op
          (coefficientUnit f (T j ⊓ T l) (z j l) : Γ(thickening f, projection f ⁻¹ᵁ (T j ⊓ T l))) =
      (thickening f).presheaf.map
        ((Opens.map (projection f).base).map
          (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            T i ⊓ T j ⊓ T l ≤ T i ⊓ T l))).op
          (coefficientUnit f (T i ⊓ T l) (z i l) : Γ(thickening f, projection f ⁻¹ᵁ (T i ⊓ T l)))
    rw [coefficientUnit_restrict_val f inf_le_left (z i j),
      coefficientUnit_restrict_val f
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (z j l),
      coefficientUnit_restrict_val f
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (z i l),
      ← Units.val_mul, ← coefficientUnit_add]
    exact congrArg (fun a ↦ (coefficientUnit f (T i ⊓ T j ⊓ T l) a :
      Γ(thickening f, projection f ⁻¹ᵁ (T i ⊓ T j ⊓ T l)))) h

set_option backward.isDefEq.respectTransparency false in
/-- Any actual gauge gives the additive coefficient gauge equation. -/
lemma coefficients_of_isGauge {ι : Type u} (T : ι → X.Opens)
    (z w : ∀ i j, Γ(X, T i ⊓ T j))
    (a : ∀ i, Γ(thickening f, thickenedOpens f T i)ˣ)
    (ha : CocycleGluing.IsGauge (unitCochain f T z) (unitCochain f T w) a) :
    ∀ i j, w i j =
      X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op
        (unitCoefficient f (T i) (a i)).toAdd + z i j -
      X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op
        (unitCoefficient f (T j) (a j)).toAdd := by
  intro i j
  have hh := (CocycleGluing.isGauge_iff _ _ a).mp ha i j
  have hu :
      Units.map ((thickening f).presheaf.map
          ((Opens.map (projection f).base).map
            (homOfLE (inf_le_left : T i ⊓ T j ≤ T i))).op).hom.toMonoidHom (a i) *
        coefficientUnit f (T i ⊓ T j) (z i j) =
      coefficientUnit f (T i ⊓ T j) (w i j) *
        Units.map ((thickening f).presheaf.map
          ((Opens.map (projection f).base).map
            (homOfLE (inf_le_right : T i ⊓ T j ≤ T j))).op).hom.toMonoidHom (a j) := by
    apply Units.ext
    exact hh
  have hc := congrArg (unitCoefficient f (T i ⊓ T j)) hu
  rw [map_mul, map_mul, unitCoefficient_naturality, unitCoefficient_naturality,
    unitCoefficient_coefficientUnit, unitCoefficient_coefficientUnit] at hc
  have he := congrArg Multiplicative.toAdd hc
  change X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op
      (unitCoefficient f (T i) (a i)).toAdd + z i j =
    w i j + X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op
      (unitCoefficient f (T j) (a j)).toAdd at he
  exact (eq_sub_iff_add_eq).mpr he.symm

set_option backward.isDefEq.respectTransparency false in
/-- A gauge of coefficient units is precisely the additive gauge equation. -/
lemma isGauge_unitCochain_iff {ι : Type u} (T : ι → X.Opens)
    (z w : ∀ i j, Γ(X, T i ⊓ T j)) (b : ∀ i, Γ(X, T i)) :
    CocycleGluing.IsGauge (unitCochain f T z) (unitCochain f T w)
      (fun i ↦ coefficientUnit f (T i) (b i)) ↔
    ∀ i j, w i j =
      X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (b i) + z i j -
      X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (b j) := by
  constructor
  · intro ha
    simpa only [unitCoefficient_coefficientUnit, toAdd_ofAdd] using
      coefficients_of_isGauge f T z w _ ha
  · intro hb
    apply (CocycleGluing.isGauge_iff _ _ _).mpr
    intro i j
    have he :
        X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (b i) + z i j =
        w i j + X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (b j) := by
      rw [hb i j]
      abel
    have hu := congrArg (fun c ↦ (coefficientUnit f (T i ⊓ T j) c :
      Γ(thickening f, projection f ⁻¹ᵁ (T i ⊓ T j)))) he
    rw [coefficientUnit_add, coefficientUnit_add, Units.val_mul, Units.val_mul] at hu
    change (thickening f).presheaf.map
        ((Opens.map (projection f).base).map
          (homOfLE (inf_le_left : T i ⊓ T j ≤ T i))).op
        (coefficientUnit f (T i) (b i) : Γ(thickening f, projection f ⁻¹ᵁ T i)) *
        (coefficientUnit f (T i ⊓ T j) (z i j) : Γ(thickening f, projection f ⁻¹ᵁ (T i ⊓ T j))) =
      (coefficientUnit f (T i ⊓ T j) (w i j) : Γ(thickening f, projection f ⁻¹ᵁ (T i ⊓ T j))) *
      (thickening f).presheaf.map
        ((Opens.map (projection f).base).map
          (homOfLE (inf_le_right : T i ⊓ T j ≤ T j))).op
        (coefficientUnit f (T j) (b j) : Γ(thickening f, projection f ⁻¹ᵁ T j))
    rw [coefficientUnit_restrict_val f inf_le_left, coefficientUnit_restrict_val f inf_le_right]
    exact hu

/-- Arbitrary actual gauges are equivalent to additive coboundaries of the difference. -/
lemma exists_isGauge_unitCochain_iff {ι : Type u} (T : ι → X.Opens)
    (z w : ∀ i j, Γ(X, T i ⊓ T j)) :
    (∃ a : ∀ i, Γ(thickening f, thickenedOpens f T i)ˣ,
      CocycleGluing.IsGauge (unitCochain f T z) (unitCochain f T w) a) ↔
    Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCoboundary
      (G := structureSheaf X) T (fun i j ↦ w i j - z i j) := by
  constructor
  · rintro ⟨a, ha⟩
    have hb := coefficients_of_isGauge f T z w a ha
    refine ⟨fun i ↦ -(unitCoefficient f (T i) (a i)).toAdd, ?_⟩
    intro i j
    change w i j - z i j =
      X.presheaf.map (homOfLE inf_le_right).op (-(unitCoefficient f (T j) (a j)).toAdd) -
      X.presheaf.map (homOfLE inf_le_left).op (-(unitCoefficient f (T i) (a i)).toAdd)
    rw [hb i j]
    simp only [map_neg]
    abel
  · rintro ⟨b, hb⟩
    let c : ∀ i, Γ(X, T i) := b
    refine ⟨fun i ↦ coefficientUnit f (T i) (-c i),
      (isGauge_unitCochain_iff f T z w (fun i ↦ -c i)).mpr ?_⟩
    intro i j
    have he := hb i j
    change w i j - z i j =
      X.presheaf.map (homOfLE inf_le_right).op (c j) -
      X.presheaf.map (homOfLE inf_le_left).op (c i) at he
    simp only [map_neg]
    calc
      w i j = (w i j - z i j) + z i j := by abel
      _ = _ := by rw [he]; abel

/-- An actual isomorphism of the glued modules associated to a coboundary difference. -/
def coboundaryIso {ι : Type u} (T : ι → X.Opens)
    (z w : ∀ i j, Γ(X, T i ⊓ T j))
    (h : Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCoboundary
      (G := structureSheaf X) T (fun i j ↦ w i j - z i j)) :
    CocycleGluing.glued (unitCochain f T z) ≅ CocycleGluing.glued (unitCochain f T w) :=
  CocycleGluing.gaugeIso ((exists_isGauge_unitCochain_iff f T z w).mpr h).choose
    ((exists_isGauge_unitCochain_iff f T z w).mpr h).choose_spec

/-- The actual glued modules are isomorphic exactly for coboundary differences. -/
lemma nonempty_iso_unitCochain_iff {ι : Type u} (T : ι → X.Opens)
    (z w : ∀ i j, Γ(X, T i ⊓ T j))
    (hz : Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCocycle
      (G := structureSheaf X) T z)
    (hw : Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCocycle
      (G := structureSheaf X) T w) :
    Nonempty (CocycleGluing.glued (unitCochain f T z) ≅
      CocycleGluing.glued (unitCochain f T w)) ↔
    Langlands.AlgebraicGeometry.Modules.CechDegreeOne.IsCoboundary
      (G := structureSheaf X) T (fun i j ↦ w i j - z i j) := by
  rw [CocycleGluing.nonempty_iso_glued_iff
    ((isCocycle_unitCochain_iff f T z).mpr hz)
    ((isCocycle_unitCochain_iff f T w).mpr hw)]
  exact exists_isGauge_unitCochain_iff f T z w

end Langlands.AlgebraicGeometry.Picard.DualNumberThickening
