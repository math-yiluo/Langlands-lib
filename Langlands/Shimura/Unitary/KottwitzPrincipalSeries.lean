import Langlands.Shimura.Unitary.KottwitzChart
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Langlands.Representation.Induction.Definitions
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Intertwining
import Langlands.Representation.Smooth.IrreducibleRealization
import Langlands.Representation.Category.ClassInvariants

/-! # Torus, Borel subgroup and unramified principal series of a standard chart -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct

set_option linter.unusedSectionVars false

universe u v w uL uV

namespace Langlands.Shimura.KottwitzUnramified

open Langlands.Global.AdelicFunctoriality

variable {E : Type u} {K : Type v} {A : Type w}
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [Algebra.IsQuadraticExtension E K]
variable [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower E K A]
variable [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
variable {σ : SecondKindInvolution E K A} {p : HeightOneSpectrum (𝓞 ℚ)} {n : ℕ}

section Involution

variable (σ) in
/-- The scalar extension of the involution, `σ ⊗ 1` on `ℚ_p ⊗_ℚ A`. -/
abbrev localInvolution := σ.rationalInvolution.baseChange (p.adicCompletion ℚ)

theorem chartEquiv_localInvolution (φ : PlaceCharts K A p n)
    (y : p.adicCompletion ℚ ⊗[ℚ] A) :
    chartEquiv φ (localInvolution σ (p := p) y) =
      transportedInvolution σ φ (chartEquiv φ y) := by
  simp [transportedInvolution]

theorem transportedInvolution_mul (φ : PlaceCharts K A p n) (x y : MatrixProduct K p n) :
    transportedInvolution σ φ (x * y) =
      transportedInvolution σ φ y * transportedInvolution σ φ x := by
  simp only [transportedInvolution, map_mul, AlgebraInvolution.apply_mul]

theorem transportedInvolution_one (φ : PlaceCharts K A p n) :
    transportedInvolution σ φ 1 = 1 := by
  simp only [transportedInvolution, map_one, AlgebraInvolution.apply_one]

theorem transportedInvolution_transportedInvolution (φ : PlaceCharts K A p n)
    (x : MatrixProduct K p n) :
    transportedInvolution σ φ (transportedInvolution σ φ x) = x := by
  simp only [transportedInvolution, RingEquiv.symm_apply_apply,
    AlgebraInvolution.apply_apply, RingEquiv.apply_symm_apply]

/-- The scalars `ℚ_p` go to the scalar matrices of the completions. -/
theorem chartEquiv_algebraMap (φ : PlaceCharts K A p n) (s : p.adicCompletion ℚ)
    (w : FinitePlacesAbove K p) :
    chartEquiv φ (algebraMap (p.adicCompletion ℚ) (p.adicCompletion ℚ ⊗[ℚ] A) s) w =
      algebraMap (w.1.adicCompletion K) (Matrix (Fin n) (Fin n) (w.1.adicCompletion K))
        (FiniteExtension.completionMap p w.1 s) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  change φ w (PlaceTensor.placeTensorEquiv (K := K) p A (s ⊗ₜ[ℚ] (1 : A)) w) = _
  rw [PlaceTensor.placeTensorEquiv_tmul]
  have h : (FiniteExtension.completionMap p w.1 s ⊗ₜ[K] (1 : A)) =
      algebraMap (w.1.adicCompletion K) (w.1.adicCompletion K ⊗[K] A)
        (FiniteExtension.completionMap p w.1 s) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [h, AlgEquiv.commutes]

end Involution

section Triangular

variable (K p n) in
/-- Every component is upper triangular. -/
def IsUpper (x : MatrixProduct K p n) : Prop :=
  ∀ w, (x w).BlockTriangular id

variable (K p n) in
/-- Every component is lower triangular. -/
def IsLower (x : MatrixProduct K p n) : Prop :=
  ∀ w, (x w).BlockTriangular OrderDual.toDual

theorem isUpper_one : IsUpper K p n 1 := fun _ => Matrix.blockTriangular_one

theorem isLower_one : IsLower K p n 1 := fun _ => Matrix.blockTriangular_one

theorem IsUpper.mul {x y : MatrixProduct K p n} (hx : IsUpper K p n x) (hy : IsUpper K p n y) :
    IsUpper K p n (x * y) := fun w => (hx w).mul (hy w)

theorem IsLower.mul {x y : MatrixProduct K p n} (hx : IsLower K p n x) (hy : IsLower K p n y) :
    IsLower K p n (x * y) := fun w => (hx w).mul (hy w)

/-- The component of the inverse of a unit is the matrix inverse of its component. -/
theorem inv_val_apply (u : (MatrixProduct K p n)ˣ) (w : FinitePlacesAbove K p) :
    ((u⁻¹ : (MatrixProduct K p n)ˣ) : MatrixProduct K p n) w = ((u : MatrixProduct K p n) w)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  have h := congrFun u.inv_mul w
  simpa using h

/-- The component of a unit, as an invertible matrix. -/
abbrev componentInvertible (u : (MatrixProduct K p n)ˣ) (w : FinitePlacesAbove K p) :
    Invertible ((u : MatrixProduct K p n) w) where
  invOf := ((u⁻¹ : (MatrixProduct K p n)ˣ) : MatrixProduct K p n) w
  invOf_mul_self := by simpa using congrFun u.inv_mul w
  mul_invOf_self := by simpa using congrFun u.mul_inv w

theorem IsUpper.inv {u : (MatrixProduct K p n)ˣ} (hu : IsUpper K p n u) :
    IsUpper K p n ((u⁻¹ : (MatrixProduct K p n)ˣ) : MatrixProduct K p n) := by
  intro w
  rw [inv_val_apply]
  let := componentInvertible u w
  exact Matrix.blockTriangular_inv_of_blockTriangular (hu w)

theorem IsLower.inv {u : (MatrixProduct K p n)ˣ} (hu : IsLower K p n u) :
    IsLower K p n ((u⁻¹ : (MatrixProduct K p n)ˣ) : MatrixProduct K p n) := by
  intro w
  rw [inv_val_apply]
  let := componentInvertible u w
  exact Matrix.blockTriangular_inv_of_blockTriangular (hu w)

/-- Upper and lower triangular matrices are exactly the diagonal ones. -/
theorem isUpper_and_isLower_iff (x : MatrixProduct K p n) :
    (IsUpper K p n x ∧ IsLower K p n x) ↔ ∀ w, Matrix.IsDiag (x w) := by
  constructor
  · rintro ⟨hu, hl⟩ w i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hl w (show OrderDual.toDual j < OrderDual.toDual i from h)
    · exact hu w h
  · intro h
    exact ⟨fun w i j hij => h w (ne_of_gt hij),
      fun w i j hij => h w (ne_of_lt (show i < j from hij))⟩

end Triangular

section Subgroups

variable (c : UnramifiedChart σ p n)

/-- The Borel subgroup of the chart: points whose matrix coordinates are upper
triangular. -/
def UnramifiedChart.borel : Subgroup (LocalPoints σ p) where
  carrier := {g | IsUpper K p n (pointUnit c.charts g : MatrixProduct K p n)}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, map_mul, Units.val_mul]
    exact hg.mul hh
  one_mem' := by
    simp only [Set.mem_ofPred_eq, map_one, Units.val_one]
    exact isUpper_one
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq, map_inv]
    exact IsUpper.inv hg

/-- The maximal torus of the chart: points whose matrix coordinates are diagonal. -/
def UnramifiedChart.torus : Subgroup (LocalPoints σ p) where
  carrier := {g | IsUpper K p n (pointUnit c.charts g : MatrixProduct K p n) ∧
    IsLower K p n (pointUnit c.charts g : MatrixProduct K p n)}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, map_mul, Units.val_mul]
    exact ⟨hg.1.mul hh.1, hg.2.mul hh.2⟩
  one_mem' := by
    simp only [Set.mem_ofPred_eq, map_one, Units.val_one]
    exact ⟨isUpper_one, isLower_one⟩
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq, map_inv]
    exact ⟨IsUpper.inv hg.1, IsLower.inv hg.2⟩

theorem UnramifiedChart.mem_torus_iff (g : LocalPoints σ p) :
    g ∈ c.torus ↔ ∀ w, Matrix.IsDiag ((pointUnit c.charts g : MatrixProduct K p n) w) :=
  isUpper_and_isLower_iff _

theorem UnramifiedChart.torus_le_borel : c.torus ≤ c.borel := fun _ h => h.1

end Subgroups

section Diagonal

variable (K p n) in
/-- The diagonal part of every component. -/
def diagPart (x : MatrixProduct K p n) : MatrixProduct K p n :=
  fun w => Matrix.diagonal fun k => x w k k

theorem diagPart_apply (x : MatrixProduct K p n) (w : FinitePlacesAbove K p) (k l : Fin n) :
    diagPart K p n x w k l = if k = l then x w k k else 0 := by
  simp only [diagPart, Matrix.diagonal_apply]

theorem diagPart_one : diagPart K p n 1 = 1 := by
  funext w
  simp only [diagPart, Pi.one_apply, Matrix.one_apply_eq, Matrix.diagonal_one]

theorem diagPart_mul_of_isUpper {x y : MatrixProduct K p n} (hx : IsUpper K p n x)
    (hy : IsUpper K p n y) : diagPart K p n (x * y) = diagPart K p n x * diagPart K p n y := by
  funext w
  simp only [diagPart, Pi.mul_apply, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · intro j _ hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · rw [hx w (show id j < id k from h), zero_mul]
    · rw [hy w (show id k < id j from h), mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem isUpper_diagPart (x : MatrixProduct K p n) : IsUpper K p n (diagPart K p n x) :=
  fun _ => Matrix.blockTriangular_diagonal _

theorem isLower_diagPart (x : MatrixProduct K p n) : IsLower K p n (diagPart K p n x) :=
  fun _ => Matrix.blockTriangular_diagonal _

variable (c : UnramifiedChart σ p n)

theorem UnramifiedChart.transportedInvolution_apply (x : MatrixProduct K p n)
    (w : FinitePlacesAbove K p) (k l : Fin n) :
    transportedInvolution σ c.charts x w k l =
      c.conj w (x (placeConj (E := E) p w) (Fin.rev l) (Fin.rev k)) :=
  c.involution_eq x w k l

theorem UnramifiedChart.isUpper_transportedInvolution {x : MatrixProduct K p n}
    (hx : IsUpper K p n x) : IsUpper K p n (transportedInvolution σ c.charts x) := by
  intro w k l hlk
  rw [c.transportedInvolution_apply]
  have h : Fin.rev k < Fin.rev l := Fin.rev_lt_rev.mpr hlk
  rw [hx (placeConj (E := E) p w) (show id (Fin.rev k) < id (Fin.rev l) from h), map_zero]

theorem UnramifiedChart.transportedInvolution_diagPart (x : MatrixProduct K p n) :
    transportedInvolution σ c.charts (diagPart K p n x) =
      diagPart K p n (transportedInvolution σ c.charts x) := by
  funext w
  ext k l
  rw [c.transportedInvolution_apply, diagPart_apply, diagPart_apply,
    c.transportedInvolution_apply]
  by_cases h : k = l
  · subst h
    simp
  · have h' : Fin.rev l ≠ Fin.rev k := fun e => h (Fin.rev_injective e).symm
    simp [h, h']

/-- Scalars of `ℚ_p` are diagonal in every chart. -/
theorem diagPart_chartEquiv_algebraMap (φ : PlaceCharts K A p n) (s : p.adicCompletion ℚ) :
    diagPart K p n (chartEquiv φ (algebraMap _ (p.adicCompletion ℚ ⊗[ℚ] A) s)) =
      chartEquiv φ (algebraMap _ (p.adicCompletion ℚ ⊗[ℚ] A) s) := by
  funext w
  simp only [diagPart, chartEquiv_algebraMap, Matrix.algebraMap_eq_diagonal,
    Matrix.diagonal_apply_eq]

/-- The diagonal part of an upper triangular unit. -/
def diagUnit (u : (MatrixProduct K p n)ˣ) (hu : IsUpper K p n u) : (MatrixProduct K p n)ˣ where
  val := diagPart K p n u
  inv := diagPart K p n ((u⁻¹ : (MatrixProduct K p n)ˣ) : MatrixProduct K p n)
  val_inv := by rw [← diagPart_mul_of_isUpper hu (IsUpper.inv hu), u.mul_inv, diagPart_one]
  inv_val := by rw [← diagPart_mul_of_isUpper (IsUpper.inv hu) hu, u.inv_mul, diagPart_one]

end Diagonal

section Points

variable (φ : PlaceCharts K A p n)

/-- The similitude equation of a point, read in the matrix coordinates. -/
theorem pointUnit_similitude (g : LocalPoints σ p) :
    (pointUnit φ g : MatrixProduct K p n) * transportedInvolution σ φ (pointUnit φ g) =
      chartEquiv φ (algebraMap (p.adicCompletion ℚ) (p.adicCompletion ℚ ⊗[ℚ] A)
        (g.1.2 : p.adicCompletion ℚ)) := by
  have h := ((localInvolution σ (p := p)).mem_similitudes_iff g.1).mp g.2
  rw [pointUnit_val, ← chartEquiv_localInvolution, ← map_mul, h]

/-- A point is determined by its matrix coordinates and its multiplier. -/
theorem points_ext {g h : LocalPoints σ p}
    (hu : (pointUnit φ g : MatrixProduct K p n) = pointUnit φ h) (hm : g.1.2 = h.1.2) :
    g = h := by
  apply Subtype.ext
  apply Prod.ext _ hm
  apply Units.ext
  apply (chartEquiv φ).injective
  rw [← pointUnit_val, ← pointUnit_val, hu]

/-- The point with prescribed matrix coordinates and multiplier, when they satisfy the
transported similitude equation. -/
def mkPoint (u : (MatrixProduct K p n)ˣ) (s : (p.adicCompletion ℚ)ˣ)
    (h : (u : MatrixProduct K p n) * transportedInvolution σ φ u =
      chartEquiv φ (algebraMap (p.adicCompletion ℚ) (p.adicCompletion ℚ ⊗[ℚ] A)
        (s : p.adicCompletion ℚ))) : LocalPoints σ p :=
  ⟨(Units.map (chartEquiv φ).symm.toMonoidHom u, s), by
    rw [AlgebraInvolution.mem_similitudes_iff]
    apply (chartEquiv φ).injective
    rw [map_mul, chartEquiv_localInvolution]
    simpa using h⟩

@[simp] theorem pointUnit_mkPoint (u : (MatrixProduct K p n)ˣ) (s : (p.adicCompletion ℚ)ˣ) (h) :
    pointUnit φ (mkPoint (σ := σ) φ u s h) = u := by
  apply Units.ext
  rw [pointUnit_val]
  change chartEquiv φ ((chartEquiv φ).symm (u : MatrixProduct K p n)) = u
  exact RingEquiv.apply_symm_apply _ _

@[simp] theorem mkPoint_multiplier (u : (MatrixProduct K p n)ˣ) (s : (p.adicCompletion ℚ)ˣ) (h) :
    (mkPoint (σ := σ) φ u s h).1.2 = s := rfl

end Points

section Projection

variable (c : UnramifiedChart σ p n)

theorem UnramifiedChart.diagUnit_similitude (g : c.borel) :
    ((diagUnit (pointUnit c.charts g.1) g.2 : (MatrixProduct K p n)ˣ) : MatrixProduct K p n) *
        transportedInvolution σ c.charts (diagUnit (pointUnit c.charts g.1) g.2) =
      chartEquiv c.charts (algebraMap (p.adicCompletion ℚ) (p.adicCompletion ℚ ⊗[ℚ] A)
        (g.1.1.2 : p.adicCompletion ℚ)) := by
  change diagPart K p n _ * transportedInvolution σ c.charts (diagPart K p n _) = _
  rw [c.transportedInvolution_diagPart,
    ← diagPart_mul_of_isUpper g.2 (c.isUpper_transportedInvolution g.2),
    pointUnit_similitude, diagPart_chartEquiv_algebraMap]

/-- The diagonal part of a point of the Borel subgroup, a point of the torus. -/
def UnramifiedChart.torusPart (g : c.borel) : c.torus :=
  ⟨mkPoint c.charts (diagUnit (pointUnit c.charts g.1) g.2) g.1.1.2 (c.diagUnit_similitude g), by
    change IsUpper K p n (pointUnit c.charts (mkPoint _ _ _ _) : MatrixProduct K p n) ∧
      IsLower K p n (pointUnit c.charts (mkPoint _ _ _ _) : MatrixProduct K p n)
    rw [pointUnit_mkPoint]
    exact ⟨isUpper_diagPart _, isLower_diagPart _⟩⟩

theorem UnramifiedChart.pointUnit_torusPart (g : c.borel) :
    (pointUnit c.charts (c.torusPart g).1 : MatrixProduct K p n) =
      diagPart K p n (pointUnit c.charts g.1) := by
  simp [UnramifiedChart.torusPart, diagUnit]

/-- The projection of the Borel subgroup onto the torus, taking diagonal parts. -/
def UnramifiedChart.torusProjection : c.borel →* c.torus where
  toFun := c.torusPart
  map_one' := by
    apply Subtype.ext
    apply points_ext c.charts
    · rw [c.pointUnit_torusPart]
      simp [diagPart_one]
    · rfl
  map_mul' g h := by
    apply Subtype.ext
    apply points_ext c.charts
    · rw [Subgroup.coe_mul, map_mul, Units.val_mul, c.pointUnit_torusPart, c.pointUnit_torusPart,
        c.pointUnit_torusPart, Subgroup.coe_mul, map_mul, Units.val_mul]
      exact diagPart_mul_of_isUpper g.2 h.2
    · rfl

theorem UnramifiedChart.torusProjection_of_mem_torus (t : c.borel) (ht : t.1 ∈ c.torus) :
    (c.torusProjection t : LocalPoints σ p) = t := by
  apply points_ext c.charts
  · change (pointUnit c.charts (c.torusPart t).1 : MatrixProduct K p n) = _
    rw [c.pointUnit_torusPart]
    funext w
    exact ((c.mem_torus_iff t.1).mp ht w).diagonal_diag
  · rfl

end Projection

section Cocharacters

variable (E K p n) in
/-- The lattice of `ℚ_p`-rational cocharacters of the diagonal torus: integer exponents
`m w k` at the places `w ∣ p` and positions `k`, and a multiplier exponent `m_c`,
with `m w k + m w̄ (rev k) = m_c`. -/
def localCocharacters : AddSubgroup ((FinitePlacesAbove K p → Fin n → ℤ) × ℤ) where
  carrier := {m | ∀ w k, m.1 w k + m.1 (placeConj (E := E) p w) (Fin.rev k) = m.2}
  add_mem' {a b} ha hb w k := by
    have h1 := ha w k
    have h2 := hb w k
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    omega
  zero_mem' w k := by simp
  neg_mem' {a} ha w k := by
    have h1 := ha w k
    simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply]
    omega

theorem mem_localCocharacters (m : (FinitePlacesAbove K p → Fin n → ℤ) × ℤ) :
    m ∈ localCocharacters E K p n ↔
      ∀ w k, m.1 w k + m.1 (placeConj (E := E) p w) (Fin.rev k) = m.2 :=
  Iff.rfl

variable (p) in
/-- The rational prime below the place `p`. -/
abbrev residuePrime : ℕ := Rat.HeightOneSpectrum.natGenerator p

theorem residuePrime_ne_zero : residuePrime p ≠ 0 :=
  (Rat.HeightOneSpectrum.prime_natGenerator p).ne_zero

theorem residuePrime_cast_ne_zero (w : FinitePlacesAbove K p) :
    (residuePrime p : w.1.adicCompletion K) ≠ 0 := by
  rw [← map_natCast (algebraMap K (w.1.adicCompletion K))]
  exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr residuePrime_ne_zero)

theorem residuePrime_rational_ne_zero : (residuePrime p : p.adicCompletion ℚ) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ (p.adicCompletion ℚ))]
  exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr residuePrime_ne_zero)

variable (p) in
/-- The prime `p` as a unit of `K_w`. -/
def primeUnit (w : FinitePlacesAbove K p) : (w.1.adicCompletion K)ˣ :=
  Units.mk0 (residuePrime p : w.1.adicCompletion K) (residuePrime_cast_ne_zero w)

variable (p) in
/-- The prime `p` as a unit of `ℚ_p`. -/
def rationalPrimeUnit : (p.adicCompletion ℚ)ˣ :=
  Units.mk0 (residuePrime p : p.adicCompletion ℚ) residuePrime_rational_ne_zero

theorem map_primeUnit {w w' : FinitePlacesAbove K p}
    (f : w.1.adicCompletion K →+* w'.1.adicCompletion K) (z : ℤ) :
    f ((primeUnit p w ^ z : (w.1.adicCompletion K)ˣ) : w.1.adicCompletion K) =
      ((primeUnit p w' ^ z : (w'.1.adicCompletion K)ˣ) : w'.1.adicCompletion K) := by
  have h : Units.map f.toMonoidHom (primeUnit p w) = primeUnit p w' := by
    apply Units.ext
    simp [primeUnit]
  rw [← h, ← map_zpow]
  rfl

theorem completionMap_rationalPrimeUnit (w : FinitePlacesAbove K p) (z : ℤ) :
    FiniteExtension.completionMap p w.1
        ((rationalPrimeUnit p ^ z : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) =
      ((primeUnit p w ^ z : (w.1.adicCompletion K)ˣ) : w.1.adicCompletion K) := by
  have h : Units.map (FiniteExtension.completionMap p w.1).toMonoidHom (rationalPrimeUnit p) =
      primeUnit p w := by
    apply Units.ext
    simp [rationalPrimeUnit, primeUnit]
  rw [← h, ← map_zpow]
  rfl

variable (K p n) in
/-- The diagonal unit `(diag(p^{m w k})_k)_w`. -/
def cocharMatrixUnit (m : FinitePlacesAbove K p → Fin n → ℤ) : (MatrixProduct K p n)ˣ where
  val := fun w => Matrix.diagonal fun k => ((primeUnit p w ^ m w k : (w.1.adicCompletion K)ˣ) :
    w.1.adicCompletion K)
  inv := fun w => Matrix.diagonal fun k => ((primeUnit p w ^ (-m w k) : (w.1.adicCompletion K)ˣ) :
    w.1.adicCompletion K)
  val_inv := by
    funext w
    simp only [Pi.mul_apply, Pi.one_apply, Matrix.diagonal_mul_diagonal, ← Units.val_mul,
      ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, Matrix.diagonal_one]
  inv_val := by
    funext w
    simp only [Pi.mul_apply, Pi.one_apply, Matrix.diagonal_mul_diagonal, ← Units.val_mul,
      ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, Matrix.diagonal_one]

theorem cocharMatrixUnit_add (m m' : FinitePlacesAbove K p → Fin n → ℤ) :
    cocharMatrixUnit K p n (m + m') = cocharMatrixUnit K p n m * cocharMatrixUnit K p n m' := by
  apply Units.ext
  funext w
  simp only [cocharMatrixUnit, Units.val_mul, Pi.mul_apply, Matrix.diagonal_mul_diagonal,
    Pi.add_apply, zpow_add, Units.val_mul]

theorem cocharMatrixUnit_zero : cocharMatrixUnit K p n 0 = 1 := by
  apply Units.ext
  funext w
  simp [cocharMatrixUnit]

variable (c : UnramifiedChart σ p n)

theorem cocharMatrixUnit_val (m : FinitePlacesAbove K p → Fin n → ℤ) (w : FinitePlacesAbove K p) :
    ((cocharMatrixUnit K p n m : (MatrixProduct K p n)ˣ) : MatrixProduct K p n) w =
      Matrix.diagonal fun k => ((primeUnit p w ^ m w k : (w.1.adicCompletion K)ˣ) :
        w.1.adicCompletion K) :=
  rfl

theorem UnramifiedChart.transportedInvolution_cocharMatrix
    (m : FinitePlacesAbove K p → Fin n → ℤ) :
    transportedInvolution σ c.charts (cocharMatrixUnit K p n m) =
      cocharMatrixUnit K p n (fun w k => m (placeConj (E := E) p w) (Fin.rev k)) := by
  funext w
  apply Matrix.ext
  intro k l
  rw [c.transportedInvolution_apply, cocharMatrixUnit_val, cocharMatrixUnit_val,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : k = l
  · subst h
    simp only [↓reduceIte, map_primeUnit]
  · have h' : Fin.rev l ≠ Fin.rev k := fun e => h (Fin.rev_injective e).symm
    simp only [h, h', ↓reduceIte, map_zero]

theorem UnramifiedChart.cocharMatrix_similitude (m : localCocharacters E K p n) :
    ((cocharMatrixUnit K p n m.1.1 : (MatrixProduct K p n)ˣ) : MatrixProduct K p n) *
        transportedInvolution σ c.charts (cocharMatrixUnit K p n m.1.1) =
      chartEquiv c.charts (algebraMap (p.adicCompletion ℚ) (p.adicCompletion ℚ ⊗[ℚ] A)
        ((rationalPrimeUnit p ^ m.1.2 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) := by
  rw [c.transportedInvolution_cocharMatrix]
  funext w
  rw [Pi.mul_apply, cocharMatrixUnit_val, cocharMatrixUnit_val, Matrix.diagonal_mul_diagonal,
    chartEquiv_algebraMap, completionMap_rationalPrimeUnit, Matrix.algebraMap_eq_diagonal]
  congr 1
  funext k
  rw [← Units.val_mul, ← zpow_add, m.2 w k]
  rfl

/-- The point `λ(p)` of the torus attached to a rational cocharacter `λ`: matrix
coordinates `diag(p^{m w k})` and multiplier `p^{m_c}`. -/
def UnramifiedChart.cocharPoint (m : localCocharacters E K p n) : c.torus :=
  ⟨mkPoint c.charts (cocharMatrixUnit K p n m.1.1) (rationalPrimeUnit p ^ m.1.2)
      (c.cocharMatrix_similitude m), by
    change IsUpper K p n (pointUnit c.charts (mkPoint _ _ _ _) : MatrixProduct K p n) ∧
      IsLower K p n (pointUnit c.charts (mkPoint _ _ _ _) : MatrixProduct K p n)
    rw [pointUnit_mkPoint]
    exact ⟨fun w => by rw [cocharMatrixUnit_val]; exact Matrix.blockTriangular_diagonal _,
      fun w => by rw [cocharMatrixUnit_val]; exact Matrix.blockTriangular_diagonal _⟩⟩

theorem UnramifiedChart.pointUnit_cocharPoint (m : localCocharacters E K p n) :
    pointUnit c.charts (c.cocharPoint m).1 = cocharMatrixUnit K p n m.1.1 :=
  pointUnit_mkPoint (σ := σ) c.charts _ _ (c.cocharMatrix_similitude m)

theorem UnramifiedChart.cocharPoint_multiplier (m : localCocharacters E K p n) :
    (c.cocharPoint m).1.1.2 = rationalPrimeUnit p ^ m.1.2 :=
  rfl

theorem UnramifiedChart.cocharPoint_zero : c.cocharPoint 0 = 1 := by
  apply Subtype.ext
  apply points_ext c.charts
  · rw [c.pointUnit_cocharPoint]
    simp [cocharMatrixUnit_zero]
  · rw [c.cocharPoint_multiplier]
    simp only [ZeroMemClass.coe_zero, Prod.snd_zero, zpow_zero]
    rfl

theorem UnramifiedChart.cocharPoint_add (a b : localCocharacters E K p n) :
    c.cocharPoint (a + b) = c.cocharPoint a * c.cocharPoint b := by
  apply Subtype.ext
  apply points_ext c.charts
  · rw [Subgroup.coe_mul, map_mul, Units.val_mul, c.pointUnit_cocharPoint,
      c.pointUnit_cocharPoint, c.pointUnit_cocharPoint, AddSubgroup.coe_add, Prod.fst_add,
      cocharMatrixUnit_add, Units.val_mul]
  · change rationalPrimeUnit p ^ (a + b).1.2 =
      rationalPrimeUnit p ^ a.1.2 * rationalPrimeUnit p ^ b.1.2
    rw [AddSubgroup.coe_add, Prod.snd_add, zpow_add]

/-- `λ ↦ λ(p)` as a homomorphism from the cocharacter lattice to the torus. -/
def UnramifiedChart.cocharHom : Multiplicative (localCocharacters E K p n) →* c.torus where
  toFun m := c.cocharPoint (Multiplicative.toAdd m)
  map_one' := c.cocharPoint_zero
  map_mul' a b := c.cocharPoint_add (Multiplicative.toAdd a) (Multiplicative.toAdd b)

open Classical in
variable (E p n) in
/-- The cocharacter `λ_{w,k}`: exponent `1` at position `k` of the place `w`, exponent
`-1` at position `rev k` of the conjugate place `w̄`, multiplier exponent `0`. Its value
`λ_{w,k}(p) = d θ(d)⁻¹`, for `d` the diagonal matrix with `p` at `(w,k)`, is the norm
of the corresponding uniformizer element. -/
def positionCocharacter (w : FinitePlacesAbove K p) (k : Fin n) : localCocharacters E K p n :=
  ⟨(fun w' j => (if w' = w ∧ j = k then 1 else 0) -
      (if w' = placeConj (E := E) p w ∧ j = Fin.rev k then 1 else 0), 0), by
    intro w' j
    have e1 : (placeConj (E := E) p w' = w ∧ Fin.rev j = k) ↔
        (w' = placeConj (E := E) p w ∧ j = Fin.rev k) := by
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [← h1, placeConj_placeConj], by rw [← h2, Fin.rev_rev]⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [h1, placeConj_placeConj], by rw [h2, Fin.rev_rev]⟩
    have e2 : (placeConj (E := E) p w' = placeConj (E := E) p w ∧ Fin.rev j = Fin.rev k) ↔
        (w' = w ∧ j = k) := by
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [← placeConj_placeConj (E := E) p w', h1, placeConj_placeConj],
          Fin.rev_injective h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [h1], by rw [h2]⟩
    simp only [e1, e2]
    split_ifs <;> simp⟩

end Cocharacters

section Weyl

variable (E K p n) in
/-- The relative Weyl group of the diagonal torus: permutations `s_w` of the positions
at each place with `s_{w̄}(rev k) = rev (s_w k)`. -/
def localWeylGroup : Subgroup (FinitePlacesAbove K p → Equiv.Perm (Fin n)) where
  carrier := {s | ∀ w k, s (placeConj (E := E) p w) (Fin.rev k) = Fin.rev (s w k)}
  mul_mem' {s t} hs ht w k := by
    simp only [Pi.mul_apply, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [ht w k, hs w (t w k)]
  one_mem' w k := by simp
  inv_mem' {s} hs w k := by
    simp only [Pi.inv_apply]
    apply (s (placeConj (E := E) p w)).injective
    rw [hs w ((s w)⁻¹ k)]
    simp

/-- The Weyl group acts on cocharacters by permuting the positions. -/
def weylAct (s : localWeylGroup E K p n) (m : localCocharacters E K p n) :
    localCocharacters E K p n :=
  ⟨(fun w k => m.1.1 w ((s.1 w)⁻¹ k), m.1.2), by
    intro w k
    have hs : ((s.1 (placeConj (E := E) p w))⁻¹ (Fin.rev k)) = Fin.rev ((s.1 w)⁻¹ k) :=
      ((localWeylGroup E K p n).inv_mem s.2 w k)
    change m.1.1 w _ + m.1.1 (placeConj (E := E) p w) _ = m.1.2
    rw [hs]
    exact m.2 w _⟩

theorem weylAct_one (m : localCocharacters E K p n) : weylAct 1 m = m := by
  apply Subtype.ext
  rfl

theorem weylAct_mul (s t : localWeylGroup E K p n) (m : localCocharacters E K p n) :
    weylAct (s * t) m = weylAct s (weylAct t m) := by
  apply Subtype.ext
  rfl

/-- The inertia degree `f_w` of a place `w ∣ p` of `K` over `ℚ`. -/
abbrev inertiaDegree (w : FinitePlacesAbove K p) : ℕ := w.1.asIdeal.inertiaDeg (𝓞 ℚ)

variable (E K) in
/-- The CM conjugation of `𝓞 K` as an automorphism of `𝓞 ℚ`-algebras. -/
def integerConjugationAlgEquiv : 𝓞 K ≃ₐ[𝓞 ℚ] 𝓞 K :=
  AlgEquiv.ofRingEquiv (f := integerConjugation E K) integerConjugation_algebraMap

open scoped Pointwise in
/-- Conjugate places have the same inertia degree. -/
theorem inertiaDegree_placeConj (w : FinitePlacesAbove K p) :
    inertiaDegree (placeConj (E := E) p w) = inertiaDegree w := by
  have h : (placeConj (E := E) p w).1.asIdeal =
      (integerConjugationAlgEquiv E K)⁻¹ • w.1.asIdeal := by
    rw [Ideal.pointwise_smul_eq_comap]
    ext x
    rw [mem_placeConj, Ideal.mem_comap]
    rfl
  unfold inertiaDegree
  rw [h, Ideal.inertiaDeg_smul]

/-- The exponent `⟨2ρ, σλ - λ⟩ = Σ_w f_w Σ_j (j - σ_w j) λ_{w,j}` of the shift relating the
Weyl action on unnormalized and on unitarily normalized characters. -/
def weylExponent (σ : localWeylGroup E K p n) (m : localCocharacters E K p n) : ℤ :=
  ∑ w : FinitePlacesAbove K p, ∑ j : Fin n,
    (inertiaDegree w : ℤ) * (((j : ℕ) : ℤ) - ((σ.1 w j : ℕ) : ℤ)) * m.1.1 w j

theorem weylExponent_one (m : localCocharacters E K p n) : weylExponent 1 m = 0 := by
  simp [weylExponent]

theorem weylExponent_mul (σ τ : localWeylGroup E K p n) (m : localCocharacters E K p n) :
    weylExponent (σ * τ) m = weylExponent σ (weylAct τ m) + weylExponent τ m := by
  simp only [weylExponent, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h := Equiv.sum_comp (τ.1 w) (fun j : Fin n =>
    (inertiaDegree w : ℤ) * (((j : ℕ) : ℤ) - ((σ.1 w j : ℕ) : ℤ)) * m.1.1 w ((τ.1 w)⁻¹ j))
  change _ = ∑ j : Fin n, ((inertiaDegree w : ℤ) * (((j : ℕ) : ℤ) - ((σ.1 w j : ℕ) : ℤ)) *
      m.1.1 w ((τ.1 w)⁻¹ j) + _)
  rw [Finset.sum_add_distrib, ← h, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (τ.1 w)⁻¹ ((τ.1 w) i) = i := by simp
  simp only [Subgroup.coe_mul, Pi.mul_apply, Equiv.Perm.coe_mul, Function.comp_apply, hi]
  ring

end Weyl

section Representations

variable (c : UnramifiedChart σ p n)
variable {L : Type uL} [Field L]

/-- A character of the torus is unramified when it is trivial on the integral points
`T ∩ K_p`. -/
def UnramifiedChart.IsUnramifiedCharacter {k : Type*} [Monoid k] (ξ : c.torus →* kˣ) : Prop :=
  ∀ t : c.torus, (t : LocalPoints σ p) ∈ c.level → ξ t = 1

/-- The line `L` on which the Borel subgroup acts through the torus projection and a
character `ξ` of the torus. -/
def UnramifiedChart.borelLine {k : Type*} [Field k] (ξ : c.torus →* kˣ) :
    Representation k c.borel k :=
  (Algebra.lmul k k).toMonoidHom.comp ((Units.coeHom k).comp (ξ.comp c.torusProjection))

theorem UnramifiedChart.borelLine_apply {k : Type*} [Field k] (ξ : c.torus →* kˣ) (b : c.borel)
    (x : k) : c.borelLine ξ b x = (ξ (c.torusProjection b) : k) * x :=
  rfl

variable (p L) in
/-- A square root of `p` in the coefficient field: Kottwitz's chosen `√p` (in `L̄`, or in any
field containing the values of the parameters). -/
def SqrtPrime : Type uL := {s : Lˣ // (s : L) ^ 2 = (residuePrime p : L)}

/-- The other square root. -/
def SqrtPrime.neg (s : SqrtPrime p L) : SqrtPrime p L :=
  ⟨-s.1, by rw [Units.val_neg, neg_sq]; exact s.2⟩

/-- The value of the unitarily normalized parameter at the position cocharacter
`λ_{w,k}`: `ξ(λ_{w,k}(p)) · (√p)^{f_w (n + 1 - 2k)}`, where positions are numbered
`k = 1, …, n` (so `n + 1 - 2k = n - 1 - 2 k.val`). Here `s` is the chosen square root of
`p` in `L`; the factor is `δ_B^{-1/2}(λ_{w,k}(p))`, which turns the principal-series
character into the unitarily normalized one. -/
def UnramifiedChart.positionValue (s : SqrtPrime p L) (ξ : c.torus →* Lˣ)
    (w : FinitePlacesAbove K p) (k : Fin n) : Lˣ :=
  ξ (c.cocharHom (Multiplicative.ofAdd (positionCocharacter E p n w k))) *
    s.1 ^ ((inertiaDegree w : ℤ) * ((n : ℤ) - 1 - 2 * (k : ℤ)))

/-- Changing the square root of `p` to its negative multiplies each position value by an
explicit sign. -/
theorem UnramifiedChart.positionValue_neg (s : SqrtPrime p L) (ξ : c.torus →* Lˣ)
    (w : FinitePlacesAbove K p) (k : Fin n) :
    c.positionValue s.neg ξ w k =
      (-1) ^ ((inertiaDegree w : ℤ) * ((n : ℤ) - 1 - 2 * (k : ℤ))) * c.positionValue s ξ w k := by
  rw [UnramifiedChart.positionValue, UnramifiedChart.positionValue,
    show s.neg.1 = (-1) * s.1 from (neg_one_mul s.1).symm, mul_zpow]
  ac_rfl

open Classical in
theorem positionCocharacter_coord (w : FinitePlacesAbove K p) (k : Fin n)
    (w' : FinitePlacesAbove K p) (j : Fin n) :
    (positionCocharacter E p n w k).1.1 w' j =
      (if w' = w ∧ j = k then 1 else 0) -
        (if w' = placeConj (E := E) p w ∧ j = Fin.rev k then 1 else 0) :=
  rfl

open Classical in
theorem weylAct_positionCocharacter (σ : localWeylGroup E K p n) (w : FinitePlacesAbove K p)
    (k : Fin n) :
    weylAct σ (positionCocharacter E p n w k) = positionCocharacter E p n w (σ.1 w k) := by
  apply Subtype.ext
  refine Prod.ext ?_ rfl
  funext w' j
  change (positionCocharacter E p n w k).1.1 w' ((σ.1 w')⁻¹ j) = _
  rw [positionCocharacter_coord, positionCocharacter_coord]
  have h1 : (w' = w ∧ (σ.1 w')⁻¹ j = k) ↔ (w' = w ∧ j = σ.1 w k) := by
    constructor
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, by rw [← h]; simp⟩
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, by rw [h]; simp⟩
  have h2 : (w' = placeConj (E := E) p w ∧ (σ.1 w')⁻¹ j = Fin.rev k) ↔
      (w' = placeConj (E := E) p w ∧ j = Fin.rev (σ.1 w k)) := by
    constructor
    · rintro ⟨rfl, h⟩
      refine ⟨rfl, ?_⟩
      rw [← σ.2 w k, ← h]
      simp
    · rintro ⟨rfl, h⟩
      refine ⟨rfl, ?_⟩
      rw [h, ← σ.2 w k]
      simp
  simp only [h1, h2]

open Classical in
theorem sum_mul_indicator (g : FinitePlacesAbove K p → Fin n → ℤ) (a : FinitePlacesAbove K p)
    (b : Fin n) :
    ∑ w', ∑ j, g w' j * (if w' = a ∧ j = b then (1 : ℤ) else 0) = g a b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  · intro w' _ hw
    simp [hw]
  · simp

open Classical in
theorem sum_mul_indicator_sub (g : FinitePlacesAbove K p → Fin n → ℤ)
    (a a' : FinitePlacesAbove K p) (b b' : Fin n) :
    ∑ w', ∑ j, g w' j * ((if w' = a ∧ j = b then (1 : ℤ) else 0) -
      (if w' = a' ∧ j = b' then (1 : ℤ) else 0)) = g a b - g a' b' := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [sum_mul_indicator, sum_mul_indicator]

theorem rev_val_cast (k : Fin n) : (((Fin.rev k : Fin n) : ℕ) : ℤ) = (n : ℤ) - 1 - ((k : ℕ) : ℤ) := by
  rw [Fin.val_rev]
  have := k.isLt
  omega

theorem weylExponent_positionCocharacter (σ : localWeylGroup E K p n)
    (w : FinitePlacesAbove K p) (k : Fin n) :
    weylExponent σ (positionCocharacter E p n w k) =
      2 * (inertiaDegree w : ℤ) * (((k : ℕ) : ℤ) - ((σ.1 w k : ℕ) : ℤ)) := by
  classical
  simp only [weylExponent, positionCocharacter_coord]
  rw [sum_mul_indicator_sub
    (fun w' j => (inertiaDegree w' : ℤ) * (((j : ℕ) : ℤ) - ((σ.1 w' j : ℕ) : ℤ)))]
  rw [σ.2 w k, inertiaDegree_placeConj, rev_val_cast, rev_val_cast]
  ring

/-- Under Weyl equivalence the normalized position values at each place are permuted by
the Weyl element. -/
theorem UnramifiedChart.positionValue_of_weyl {s : SqrtPrime p L} {ξ ξ' : c.torus →* Lˣ}
    (σ : localWeylGroup E K p n)
    (hσ : ∀ m : localCocharacters E K p n, ξ' (c.cocharHom (Multiplicative.ofAdd m)) =
      ξ (c.cocharHom (Multiplicative.ofAdd (weylAct σ m))) * s.1 ^ weylExponent σ m)
    (w : FinitePlacesAbove K p) (k : Fin n) :
    c.positionValue s ξ' w k = c.positionValue s ξ w (σ.1 w k) := by
  rw [UnramifiedChart.positionValue, UnramifiedChart.positionValue, hσ,
    weylAct_positionCocharacter, weylExponent_positionCocharacter, mul_assoc, ← zpow_add]
  congr 2
  ring

/-- Weyl equivalence of characters of the torus, for the chosen square root `s` of `p`:
the unitarily normalized characters `ξ δ_B^{-1/2}` and `ξ' δ_B^{-1/2}` are conjugate under
the relative Weyl group, read on the points `λ(p)`. Since
`δ_B^{1/2}(λ(p)) = s^{-⟨2ρ, λ⟩}`, this says
`ξ'(λ(p)) = ξ((σλ)(p)) · s^{⟨2ρ, σλ - λ⟩}`. -/
def UnramifiedChart.WeylEquivalent (s : SqrtPrime p L) (ξ ξ' : c.torus →* Lˣ) : Prop :=
  ∃ σ : localWeylGroup E K p n, ∀ m : localCocharacters E K p n,
    ξ' (c.cocharHom (Multiplicative.ofAdd m)) =
      ξ (c.cocharHom (Multiplicative.ofAdd (weylAct σ m))) * s.1 ^ weylExponent σ m

theorem UnramifiedChart.weylEquivalent_refl (s : SqrtPrime p L) (ξ : c.torus →* Lˣ) :
    c.WeylEquivalent s ξ ξ :=
  ⟨1, fun m => by rw [weylAct_one, weylExponent_one, zpow_zero, mul_one]⟩

theorem UnramifiedChart.WeylEquivalent.trans {s : SqrtPrime p L} {ξ ξ' ξ'' : c.torus →* Lˣ}
    (h : c.WeylEquivalent s ξ ξ') (h' : c.WeylEquivalent s ξ' ξ'') :
    c.WeylEquivalent s ξ ξ'' := by
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨τ, hτ⟩ := h'
  refine ⟨σ * τ, fun m => ?_⟩
  rw [hτ, hσ, weylAct_mul, weylExponent_mul, zpow_add, mul_assoc]

theorem UnramifiedChart.WeylEquivalent.symm {s : SqrtPrime p L} {ξ ξ' : c.torus →* Lˣ}
    (h : c.WeylEquivalent s ξ ξ') : c.WeylEquivalent s ξ' ξ := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ⁻¹, fun m => ?_⟩
  have h0 := weylExponent_mul σ σ⁻¹ m
  rw [mul_inv_cancel, weylExponent_one] at h0
  rw [hσ, ← weylAct_mul, mul_inv_cancel, weylAct_one, mul_assoc, ← zpow_add]
  rw [show weylExponent σ (weylAct σ⁻¹ m) + weylExponent σ⁻¹ m = 0 by omega, zpow_zero,
    mul_one]

/-- `π` is a subquotient of `ρ`: some subrepresentation of `ρ` maps onto `π` by an
intertwining map. The two carriers may lie in different universes. -/
def IsSubquotientOf {k : Type*} [Field k] {G : Type*} [Group G] {V W : Type*}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (π : Representation k G W) : Prop :=
  ∃ (S : Subrepresentation ρ) (f : S.toRepresentation.IntertwiningMap π),
    Function.Surjective f.toLinearMap

/-- Extension of scalars of a representation from `L` to an `L`-algebra `Ω`: `g` acts on
`Ω ⊗[L] V` by `1 ⊗ ρ(g)` (Mathlib's `Module.End.baseChangeHom`). -/
def scalarExtension {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module L V]
    (Ω : Type*) [Field Ω] [Algebra L Ω] (ρ : Representation L G V) :
    Representation Ω G (Ω ⊗[L] V) :=
  (Module.End.baseChangeHom L Ω V).toMonoidHom.comp ρ

theorem scalarExtension_tmul {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module L V] (Ω : Type*) [Field Ω] [Algebra L Ω] (ρ : Representation L G V) (g : G)
    (a : Ω) (x : V) : scalarExtension Ω ρ g (a ⊗ₜ x) = a ⊗ₜ ρ g x :=
  rfl

/-- An equivalence of representations extends to their scalar extensions. -/
def scalarExtensionEquiv {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module L V]
    [AddCommGroup W] [Module L W] (Ω : Type*) [Field Ω] [Algebra L Ω]
    {ρ : Representation L G V} {σ' : Representation L G W} (e : ρ.Equiv σ') :
    (scalarExtension Ω ρ).Equiv (scalarExtension Ω σ') :=
  Representation.Equiv.mk (LinearEquiv.baseChange L Ω V W e.toLinearEquiv) (fun g => by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    change (a ⊗ₜ e (ρ g x) : Ω ⊗[L] W) = a ⊗ₜ σ' g (e x)
    exact congrArg (a ⊗ₜ[L] ·)
      (Representation.IntertwiningMap.isIntertwining ρ σ' e.toIntertwiningMap g x))

/-- Irreducibility is transported along equivalences of representations. -/
theorem isIrreducible_of_repEquiv {k : Type*} [Field k] {G : Type*} [Group G]
    {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ' : Representation k G W} (e : ρ.Equiv σ')
    (h : ρ.IsIrreducible) : σ'.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at h ⊢
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ e.toIntertwiningMap)
    e.bijective).1 h

variable [Module.Finite ℚ A]

/-- The (unnormalized) unramified principal series `Ind_B^G(ξ)` over a field `Ω`: the
published smooth induction from the Borel subgroup of the line `borelLine ξ`, that is,
smooth functions `f` on `G(ℚ_p)` with `f(b g) = ξ(b) f(g)`. -/
def UnramifiedChart.principalSeries {Ω : Type*} [Field Ω] (ξ : c.torus →* Ωˣ) :
    SmoothRep Ω (LocalPoints σ p) :=
  SmoothRep.of (Induction.smoothInduced c.borel (c.borelLine ξ))
    (Induction.smoothInduced_smooth c.borel (c.borelLine ξ))

/-- `π`, a smooth representation of `G(ℚ_p)` over `L`, is `K_p`-spherical and irreducible over
the extension `Ω`: `p` is unramified in `K`, the scalar extension `Ω ⊗_L π` is irreducible,
and `π` has a nonzero `K_p`-fixed vector. For `Ω = L̄` this is Kottwitz's "irreducible over
`L̄`" (printed p.657). -/
def UnramifiedChart.IsSphericalIrreducible (Ω : Type*) [Field Ω] [Algebra L Ω]
    (π : SmoothRep.{uL, w, uV} L (LocalPoints σ p)) : Prop :=
  IsUnramifiedAt p K ∧ (scalarExtension Ω π.representation).IsIrreducible ∧
    fixedVectors π.representation c.level ≠ ⊥

/-- `ξ`, a character of the torus with values in an extension `Ω` of `L`, is a principal-series
parameter of `π`: `π` is `K_p`-spherical and irreducible over `Ω`, `ξ` is unramified, and the
scalar extension `Ω ⊗_L π` is a subquotient of the unnormalized principal series
`Ind_B^G(ξ)` over `Ω`. -/
def UnramifiedChart.HasPrincipalSeriesParameter
    (π : SmoothRep.{uL, w, uV} L (LocalPoints σ p)) {Ω : Type*} [Field Ω] [Algebra L Ω]
    (ξ : c.torus →* Ωˣ) : Prop :=
  c.IsSphericalIrreducible Ω π ∧ c.IsUnramifiedCharacter ξ ∧
    IsSubquotientOf (c.principalSeries ξ).representation (scalarExtension Ω π.representation)

/-- Kottwitz's setting: parameters with values in the algebraic closure `L̄` of `L`. -/
abbrev UnramifiedChart.HasUnramifiedParameter
    (π : SmoothRep.{uL, w, uV} L (LocalPoints σ p)) (ξ : c.torus →* (AlgebraicClosure L)ˣ) :
    Prop :=
  c.HasPrincipalSeriesParameter π ξ

/-- The principal-series parameters of a representation depend only on its
equivalence class. -/
theorem UnramifiedChart.HasPrincipalSeriesParameter.of_equiv
    {π π' : SmoothRep.{uL, w, uV} L (LocalPoints σ p)}
    (e : π.representation.Equiv π'.representation) {Ω : Type*} [Field Ω] [Algebra L Ω]
    {ξ : c.torus →* Ωˣ} (h : c.HasPrincipalSeriesParameter π ξ) :
    c.HasPrincipalSeriesParameter π' ξ := by
  obtain ⟨⟨hun, hirr, hfix⟩, hξ, S, f, hf⟩ := h
  let e' := scalarExtensionEquiv Ω e
  refine ⟨⟨hun, isIrreducible_of_repEquiv e' hirr,
    (fixedVectors_ne_bot_iff_of_equiv e c.level).mp hfix⟩, hξ, S,
    e'.toIntertwiningMap.comp f, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := e'.bijective.2 y
  obtain ⟨z, rfl⟩ := hf x
  exact ⟨z, rfl⟩

end Representations

end Langlands.Shimura.KottwitzUnramified
