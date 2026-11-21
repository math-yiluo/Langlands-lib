import Langlands.Geometry.FormalGroup.LubinTateStandardCoordinates

/-! # The one-coordinate standard Lubin–Tate formal module -/

noncomputable section

namespace Langlands.FormalGroup.LubinTateStandard

open MvPowerSeries IsLocalRing CoordinateMap
open scoped ENat

universe u

variable {A : Type u} [CommRing A] [IsLocalRing A] [Finite (ResidueField A)]
variable (π : A) (hπ : maximalIdeal A = Ideal.span {π})

local notation "q" => Nat.card (ResidueField A)

private def additionMap : CoordinateMap A (Unit ⊕ Unit) Unit := liftLinear π hπ (fun _ _ => 1)

/-- The scalar map is the actual standard intertwiner of linear coefficient `a`. -/
def scalarMap (a : A) : CoordinateMap A Unit Unit := liftLinear π hπ (fun _ _ => a)

private theorem intertwines_additionMap : Intertwines π (additionMap π hπ) :=
  intertwines_liftLinear π hπ _

@[simp]
theorem intertwines_scalarMap (a : A) : Intertwines π (scalarMap π hπ a) :=
  intertwines_liftLinear π hπ _

@[simp]
theorem scalarMap_linearCoeff (a : A) : (scalarMap π hπ a).linearCoeff () () = a :=
  linearCoeff_liftLinear π hπ _ () ()

@[simp]
private theorem additionMap_tangent (x : Unit ⊕ Unit → A) (i : Unit) :
    (additionMap π hπ).linearPart x i = x (Sum.inl ()) + x (Sum.inr ()) := by
  rw [linearPart_apply]
  have hc (j : Unit ⊕ Unit) : (additionMap π hπ).linearCoeff i j = 1 :=
    linearCoeff_liftLinear π hπ (fun _ _ => 1) i j
  simp only [hc, one_mul, Fintype.sum_sum_type, Fintype.sum_unique]

@[simp]
private theorem scalarMap_tangent (a : A) (x : Unit → A) (i : Unit) :
    (scalarMap π hπ a).linearPart x i = a * x () := by
  cases i
  rw [linearPart_apply, Fintype.sum_unique, scalarMap_linearCoeff]

omit [IsLocalRing A] [Finite (ResidueField A)] in
@[simp]
private theorem vars_tangent {σ τ : Type} [Fintype σ] (v : τ → σ) (x : σ → A) (i : τ) :
    (CoordinateMap.vars v).linearPart x i = x (v i) := by
  classical
  simp [linearPart_apply, linearCoeff, coeff_index_single_X, ite_mul]

variable [IsDomain A] (hπne : π ≠ 0)

local notation "B" => additionMap π hπ
local notation "S" => scalarMap π hπ

include hπne in
/-- Addition and inverse are the intertwiners of tangent addition and negation. -/
def commLaw : CommLaw A Unit where
  addition := B
  inverse := S (-1)
  zero_add := by
    apply ext_intertwines_tangent π hπ hπne
      ((intertwines_additionMap π hπ).comp (Intertwines.zero.pair Intertwines.id)) Intertwines.id
    intro x i
    cases i
    simp [linearPart_comp, linearPart_pair]
  add_zero := by
    apply ext_intertwines_tangent π hπ hπne
      ((intertwines_additionMap π hπ).comp (Intertwines.id.pair Intertwines.zero)) Intertwines.id
    intro x i
    cases i
    simp [linearPart_comp, linearPart_pair]
  add_assoc := by
    have h := intertwines_additionMap π hπ
    apply ext_intertwines_tangent π hπ hπne
      (h.comp ((h.comp Intertwines.fst).pair Intertwines.snd))
      (h.comp ((Intertwines.fst.comp Intertwines.fst).pair
        (h.comp ((Intertwines.snd.comp Intertwines.fst).pair Intertwines.snd))))
    intro x i
    simp [linearPart_comp, linearPart_pair, CoordinateMap.fst, CoordinateMap.snd, add_assoc]
  add_comm := by
    have h := intertwines_additionMap π hπ
    apply ext_intertwines_tangent π hπ hπne (h.comp (Intertwines.snd.pair Intertwines.fst)) h
    intro x i
    simp [linearPart_comp, linearPart_pair, CoordinateMap.fst, CoordinateMap.snd, add_comm]
  neg_add := by
    apply ext_intertwines_tangent π hπ hπne
      ((intertwines_additionMap π hπ).comp ((intertwines_scalarMap π hπ (-1)).pair Intertwines.id))
      Intertwines.zero
    intro x i
    simp [linearPart_comp, linearPart_pair]

local notation "G" => commLaw π hπ hπne

private def scalarEnd (a : A) : CommLaw.Hom G G where
  toCoordinateMap := S a
  map_add := by
    have hB := intertwines_additionMap π hπ
    have hS := intertwines_scalarMap π hπ a
    change (S a).comp B = (B).comp (((S a).comp fst).pair ((S a).comp snd))
    apply ext_intertwines_tangent π hπ hπne (hS.comp hB)
      (hB.comp ((hS.comp Intertwines.fst).pair (hS.comp Intertwines.snd)))
    intro x i
    simp [linearPart_comp, linearPart_pair, CoordinateMap.fst, CoordinateMap.snd, mul_add]

/-- The standard scalar intertwiners form a unital ring action by formal homomorphisms. -/
def scalarAction : A →+* CommLaw.Hom G G where
  toFun := scalarEnd π hπ hπne
  map_zero' := by
    apply CommLaw.Hom.ext
    change S 0 = CoordinateMap.zero
    apply ext_intertwines_tangent π hπ hπne (intertwines_scalarMap π hπ 0) Intertwines.zero
    intro x i
    simp
  map_one' := by
    apply CommLaw.Hom.ext
    change S 1 = CoordinateMap.id
    apply ext_intertwines_tangent π hπ hπne (intertwines_scalarMap π hπ 1) Intertwines.id
    intro x i
    cases i
    simp
  map_add' a b := by
    apply CommLaw.Hom.ext
    change S (a + b) = (B).comp ((S a).pair (S b))
    apply ext_intertwines_tangent π hπ hπne (intertwines_scalarMap π hπ (a + b))
      ((intertwines_additionMap π hπ).comp ((intertwines_scalarMap π hπ a).pair (intertwines_scalarMap π hπ b)))
    intro x i
    simp [linearPart_comp, linearPart_pair, add_mul]
  map_mul' a b := by
    apply CommLaw.Hom.ext
    change S (a * b) = (S a).comp (S b)
    apply ext_intertwines_tangent π hπ hπne (intertwines_scalarMap π hπ (a * b))
      ((intertwines_scalarMap π hπ a).comp (intertwines_scalarMap π hπ b))
    intro x i
    simp [linearPart_comp, mul_assoc]

/-- The standard one-coordinate Lubin–Tate law with its actual coefficient action. -/
def moduleLaw : ModuleLaw A A Unit where
  groupLaw := G
  action := scalarAction π hπ hπne
  linear_natural a i j := by
    cases i
    cases j
    change (S a).linearCoeff () () = _
    simp [CoordinateMap.scalarLinearCoeff]

@[simp]
theorem moduleLaw_action_coordinates (a : A) : ((moduleLaw π hπ hπne).action a).toCoordinateMap = S a := rfl

include hπne in
/-- The uniformizer acts by the original standard polynomial. -/
theorem scalarMap_uniformizer : S π = polynomialCoordinates π Unit := by
  apply ext_intertwines π hπ hπne (intertwines_scalarMap π hπ π) Intertwines.polynomial
  intro i j
  cases i
  cases j
  rw [scalarMap_linearCoeff]
  have hq : (1 : ℕ∞) < q := by exact_mod_cast Finite.one_lt_card (α := ResidueField A)
  have hzero : coeff (Finsupp.single () 1) ((X () : MvPowerSeries Unit A) ^ q) = 0 := by
    apply coeff_of_lt_order
    rw [Finsupp.degree_single]
    exact hq.trans_le (le_order_pow_of_constantCoeff_eq_zero q (constantCoeff_X ()))
  change π = coeff (Finsupp.single () 1) (π • X () + X () ^ q)
  rw [map_add, coeff_smul, hzero, add_zero, coeff_index_single_self_X, mul_one]

include hπne in
/-- A coefficient map fixing the uniformizer sends the scalar series for `a` to that for its image. -/
theorem scalarMap_map (φ : A →+* A) (hφ : φ π = π) (a : A) : (S a).map φ = S (φ a) :=
  map_liftLinear π hπ hπne φ hφ (fun _ _ => a)

include hπne in
/-- The commutative law is invariant under coefficient endomorphisms fixing the uniformizer. -/
theorem commLaw_map (φ : A →+* A) (hφ : φ π = π) : (G).map φ = G := by
  have hadd : (B).map φ = B := by
    simpa only [additionMap, map_one] using
      (map_liftLinear (σ := Unit ⊕ Unit) (τ := Unit) π hπ hπne φ hφ (fun _ _ => 1))
  have hinv : (S (-1)).map φ = S (-1) := by
    simpa only [map_neg, map_one] using scalarMap_map π hπ hπne φ hφ (-1)
  have extLaw {F H : CommLaw A Unit} (ha : F.addition = H.addition) (hi : F.inverse = H.inverse) : F = H := by
    cases F
    cases H
    cases ha
    cases hi
    rfl
  exact extLaw hadd hinv

end Langlands.FormalGroup.LubinTateStandard
