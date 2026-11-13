import Langlands.Geometry.FormalGroup.HomAlgebra
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Formal O-modules in finite coordinates -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {S : Type w} [CommRing S] [Algebra O S]
variable {σ τ κ : Type} [Finite σ] [Finite τ]

namespace CoordinateMap

/-- The matrix of linear coefficients, with target coordinates indexing rows. -/
def linearCoeff (f : CoordinateMap R σ τ) : Matrix τ σ R :=
  fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (f.series i)

/-- The tangent map in the chosen formal coordinates. -/
def linearPart (f : CoordinateMap R σ τ) : (σ → R) →ₗ[R] (τ → R) :=
  let : Fintype σ := Fintype.ofFinite σ
  Matrix.mulVecLin f.linearCoeff

/-- The coefficient matrix of scalar multiplication. -/
def scalarLinearCoeff (a : R) (i j : σ) : R := by
  classical
  exact if j = i then a else 0

theorem linearPart_scalar {f : CoordinateMap R σ σ} {a : R}
    (h : ∀ i j, f.linearCoeff i j = scalarLinearCoeff a i j) (x : σ → R) :
    f.linearPart x = a • x := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  funext i
  change (∑ j, f.linearCoeff i j * x j) = a * x i
  simp only [h, scalarLinearCoeff]
  simp

omit [Finite σ] [Finite τ] in
@[simp]
theorem linearCoeff_map (φ : R →+* S) (f : CoordinateMap R σ τ) (i : τ) (j : σ) :
    (f.map φ).linearCoeff i j = φ (f.linearCoeff i j) :=
  MvPowerSeries.coeff_map φ _ _

omit [Finite σ] in
theorem map_scalarLinearCoeff (φ : R →+* S) (a : R) (i j : σ) :
    φ (scalarLinearCoeff a i j) = scalarLinearCoeff (φ a) i j := by
  classical
  by_cases h : j = i <;> simp [scalarLinearCoeff, h]

end CoordinateMap

/-- A finite-coordinate formal O-module: a commutative formal group law with
a unital ring action on formal endomorphisms and the natural tangent action. -/
structure ModuleLaw (O : Type u) [CommRing O] (R : Type v) [CommRing R]
    [Algebra O R] (σ : Type) [Finite σ] where
  groupLaw : CommLaw R σ
  action : O →+* CommLaw.Hom groupLaw groupLaw
  linear_natural : ∀ a i j, (action a).toCoordinateMap.linearCoeff i j =
    CoordinateMap.scalarLinearCoeff (algebraMap O R a) i j

namespace ModuleLaw

variable (M : ModuleLaw O R σ)

/-- The natural tangent condition as an equality on every tangent vector. -/
theorem action_on_tangent (a : O) (x : σ → R) :
    (M.action a).toCoordinateMap.linearPart x = (algebraMap O R a) • x :=
  CoordinateMap.linearPart_scalar (M.linear_natural a) x

/-- Points indexed by the formal module, so their O-module structure is canonical. -/
def Point (κ : Type) := M.groupLaw.Point κ

instance : AddCommGroup (M.Point κ) :=
  inferInstanceAs (AddCommGroup (M.groupLaw.Point κ))

instance : SMul O (M.Point κ) :=
  ⟨fun a x => (M.action a).onPoints x⟩

instance : Module O (M.Point κ) where
  one_smul x := by
    change (M.action 1).onPoints x = x
    rw [_root_.map_one]
    exact CommLaw.Hom.onPoints_id x
  mul_smul a b x := by
    change (M.action (a * b)).onPoints x = (M.action a).onPoints ((M.action b).onPoints x)
    rw [_root_.map_mul]
    exact CommLaw.Hom.onPoints_comp _ _ x
  smul_zero a := (M.action a).onPoints.map_zero
  smul_add a x y := (M.action a).onPoints.map_add x y
  add_smul a b x := by
    change (M.action (a + b)).onPoints x =
      (M.action a).onPoints x + (M.action b).onPoints x
    rw [_root_.map_add]
    exact CommLaw.Hom.onPoints_add _ _ x
  zero_smul x := by
    change (M.action 0).onPoints x = 0
    rw [_root_.map_zero]
    exact CommLaw.Hom.onPoints_zero x

@[simp]
theorem smul_point (a : O) (x : M.Point κ) :
    a • x = (M.action a).onPoints x := rfl

/-- Coefficient extension of a formal O-module along an O-algebra homomorphism. -/
def map (φ : R →ₐ[O] S) : ModuleLaw O S σ where
  groupLaw := M.groupLaw.map φ.toRingHom
  action := (CommLaw.Hom.mapEnd M.groupLaw φ.toRingHom).comp M.action
  linear_natural a i j := by
    change ((M.action a).toCoordinateMap.map φ.toRingHom).linearCoeff i j = _
    rw [CoordinateMap.linearCoeff_map, M.linear_natural,
      CoordinateMap.map_scalarLinearCoeff]
    exact congrArg (fun b : S => CoordinateMap.scalarLinearCoeff b i j) (φ.commutes a)

/-- Coefficient change is O-linear on series points. -/
def mapPoints (φ : R →ₐ[O] S) : M.Point κ →ₗ[O] (M.map φ).Point κ where
  toFun := SeriesPoint.map φ.toRingHom
  map_add' := (M.groupLaw.mapPoints φ.toRingHom).map_add
  map_smul' a x := by
    change SeriesPoint R σ κ at x
    change (SeriesPoint.eval (M.action a).toCoordinateMap x).map φ.toRingHom =
      SeriesPoint.eval ((M.action a).toCoordinateMap.map φ.toRingHom) (x.map φ.toRingHom)
    exact SeriesPoint.map_eval _ _ _

/-- Points over a commutative coefficient O-algebra extending R. -/
def AlgebraPoint (A : Type w) [CommRing A] [Algebra O A] [Algebra R A]
    [IsScalarTower O R A] :=
  (M.map (IsScalarTower.toAlgHom O R A)).Point Empty

instance (A : Type w) [CommRing A] [Algebra O A] [Algebra R A] [IsScalarTower O R A] :
    AddCommGroup (M.AlgebraPoint A) :=
  inferInstanceAs (AddCommGroup ((M.map (IsScalarTower.toAlgHom O R A)).Point Empty))

instance (A : Type w) [CommRing A] [Algebra O A] [Algebra R A] [IsScalarTower O R A] :
    Module O (M.AlgebraPoint A) :=
  inferInstanceAs (Module O ((M.map (IsScalarTower.toAlgHom O R A)).Point Empty))

/-- The underlying module points are exactly nilpotent tuples. -/
def algebraPointEquiv (A : Type w) [CommRing A] [Algebra O A] [Algebra R A]
    [IsScalarTower O R A] :
    M.AlgebraPoint A ≃ {x : σ → A // ∀ i, IsNilpotent (x i)} :=
  SeriesPoint.nilpotentEquiv

end ModuleLaw

end Langlands.FormalGroup
