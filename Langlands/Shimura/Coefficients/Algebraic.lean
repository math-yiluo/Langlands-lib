import Langlands.Shimura.Unitary.Adelic
import Langlands.Global.AdelicFunctoriality.Extension
import Mathlib.Algebra.Algebra.Hom.Rat

/-!
# Algebraic representations of the similitude group

An algebraic representation of the similitude group of `σ` on an `R`-module
`W` is a natural family of homomorphisms from the points over every
commutative `R`-algebra `S` to the `S`-linear automorphisms of `S ⊗[R] W`.
-/

noncomputable section

universe u v w

namespace Langlands.Shimura.AlgebraInvolution

open scoped TensorProduct

section General

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
variable (σ : AlgebraInvolution R A)
variable (W : Type w) [AddCommGroup W] [Module R W]

theorem pointsMap_diagonalPoints {S : Type*} {T : Type*} [CommRing S] [Algebra R S]
    [CommRing T] [Algebra R T] (f : S →ₐ[R] T) (g : σ.similitudes) :
    σ.pointsMap f (σ.diagonalPoints S g) = σ.diagonalPoints T g := by
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    change changeCoefficients (A := A) f ((1 : S) ⊗ₜ[R] (g.1.1 : A)) = (1 : T) ⊗ₜ[R] (g.1.1 : A)
    simp
  · apply Units.ext
    exact f.commutes _

/-- An algebraic representation of the similitude group functor of `σ` on `W`,
in the functor-of-points form: a homomorphism on the points over each commutative
`R`-algebra in the universe of `R`, natural in the algebra. -/
structure AlgebraicRepresentation where
  /-- The action of the points over `S` on the scalar extension `S ⊗[R] W`. -/
  act (S : Type u) [CommRing S] [Algebra R S] :
    σ.Points S →* ((S ⊗[R] W) ≃ₗ[S] (S ⊗[R] W))
  /-- Naturality along every `R`-algebra map. -/
  naturality {S T : Type u} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
    (f : S →ₐ[R] T) (g : σ.Points S) (x : S ⊗[R] W) :
    act T (σ.pointsMap f g) (f.toLinearMap.rTensor W x) =
      f.toLinearMap.rTensor W (act S g x)

namespace AlgebraicRepresentation

variable {σ W}

/-- The `k`th power of the similitude multiplier, acting by scalars. -/
def multiplierPower (k : ℤ) : σ.AlgebraicRepresentation W where
  act S _ _ := (DistribMulAction.toModuleAut S (S ⊗[R] W)).comp
    ((zpowGroupHom k).comp (Points.multiplier σ S))
  naturality {S T} _ _ _ _ f g x := by
    induction x using TensorProduct.inductionOn with
    | tmul s w =>
      simp only [MonoidHom.coe_comp, Function.comp_apply, zpowGroupHom_apply,
        DistribMulAction.toModuleAut_apply, DistribMulAction.toLinearEquiv_apply,
        pointsMap_multiplier, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        Units.smul_def, TensorProduct.smul_tmul', smul_eq_mul]
      congr 1
      rw [_root_.map_mul, ← map_zpow]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The trivial representation. -/
def trivial : σ.AlgebraicRepresentation W := multiplierPower 0

/-- The action of the rational points `σ.similitudes` on `W` itself. -/
def rationalAction (ρ : σ.AlgebraicRepresentation W) : σ.similitudes →* (W ≃ₗ[R] W) where
  toFun g := (TensorProduct.lid R W).symm ≪≫ₗ
    (ρ.act R (σ.diagonalPoints R g)).restrictScalars R ≪≫ₗ TensorProduct.lid R W
  map_one' := by
    ext w
    simp
  map_mul' g h := by
    ext w
    simp [LinearEquiv.mul_apply]

theorem rationalAction_apply (ρ : σ.AlgebraicRepresentation W) (g : σ.similitudes) (w : W) :
    ρ.rationalAction g w =
      TensorProduct.lid R W (ρ.act R (σ.diagonalPoints R g) (1 ⊗ₜ w)) := rfl

/-- On rational points, the action over `S` is the scalar extension of the
rational action. -/
theorem act_diagonalPoints (ρ : σ.AlgebraicRepresentation W) (S : Type u) [CommRing S]
    [Algebra R S] (g : σ.similitudes) :
    ρ.act S (σ.diagonalPoints S g) = (ρ.rationalAction g).baseChange R S W W := by
  have key : ∀ w : W, ρ.act S (σ.diagonalPoints S g) ((1 : S) ⊗ₜ[R] w) =
      (1 : S) ⊗ₜ[R] ρ.rationalAction g w := by
    intro w
    have e : ρ.act R (σ.diagonalPoints R g) ((1 : R) ⊗ₜ[R] w) =
        (1 : R) ⊗ₜ[R] ρ.rationalAction g w := by
      rw [rationalAction_apply]
      exact ((TensorProduct.lid R W).symm_apply_apply _).symm.trans
        (TensorProduct.lid_symm_apply _)
    have h := ρ.naturality (Algebra.ofId R S) (σ.diagonalPoints R g) ((1 : R) ⊗ₜ[R] w)
    rw [pointsMap_diagonalPoints, e] at h
    simpa only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, _root_.map_one] using h
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul s w =>
    have hs : ∀ v : W, s ⊗ₜ[R] v = s • ((1 : S) ⊗ₜ[R] v) := fun v => by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [LinearEquiv.baseChange_tmul, hs w, hs (ρ.rationalAction g w), LinearEquiv.map_smul, key]
  | add x y hx hy => simp only [map_add, hx, hy]

end AlgebraicRepresentation

/-- The standard representation on `A` by left multiplication. -/
def standardRepresentation : σ.AlgebraicRepresentation A where
  act S _ _ := (DistribMulAction.toModuleAut S (S ⊗[R] A)).comp
    (σ.baseChange S).underlyingUnit
  naturality {S T} _ _ _ _ f g x := by
    let g' : (σ.baseChange S).similitudes := g
    change changeCoefficients (A := A) f (g'.1.1 : S ⊗[R] A) * f.toLinearMap.rTensor A x =
      f.toLinearMap.rTensor A ((g'.1.1 : S ⊗[R] A) * x)
    have h : ∀ y : S ⊗[R] A, f.toLinearMap.rTensor A y = changeCoefficients (A := A) f y := by
      intro y
      induction y using TensorProduct.inductionOn with
      | tmul s a => rfl
      | add y z hy hz => simp only [map_add, hy, hz]
    rw [h, h, _root_.map_mul]

end General

section Tower

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A)
variable (L : Type u) [Field L] [Algebra ℚ L]
variable (S : Type u) [CommRing S] [Algebra ℚ S] [Algebra L S]

/-- The comparison `S ⊗[ℚ] A → S ⊗[L] (L ⊗[ℚ] A)`, `s ⊗ a ↦ s ⊗ (1 ⊗ a)`. -/
def towerMap : S ⊗[ℚ] A →ₐ[S] S ⊗[L] (L ⊗[ℚ] A) :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft (S := S))
    ((Algebra.TensorProduct.includeRight.restrictScalars ℚ).comp
      Algebra.TensorProduct.includeRight)
    (fun s a => by
      change Commute (s ⊗ₜ[L] (1 : L ⊗[ℚ] A)) ((1 : S) ⊗ₜ[L] ((1 : L) ⊗ₜ[ℚ] a))
      simp [Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul])

@[simp] theorem towerMap_tmul (s : S) (a : A) :
    towerMap L S (s ⊗ₜ[ℚ] a) = s ⊗ₜ[L] ((1 : L) ⊗ₜ[ℚ] a) := by
  simp [towerMap, Algebra.TensorProduct.tmul_mul_tmul]

theorem towerMap_involution (x : S ⊗[ℚ] A) :
    towerMap L S (σ.baseChange S x) = (σ.baseChange L).baseChange S (towerMap L S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem towerMap_scalar (s : S) :
    towerMap L S (algebraMap S (S ⊗[ℚ] A) s) = algebraMap S (S ⊗[L] (L ⊗[ℚ] A)) s := by
  simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.one_def]

/-- Points over an `L`-algebra `S` of the rational group, viewed as points of
the group obtained by first extending scalars to `L`. -/
def towerPoints : σ.Points S →* (σ.baseChange L).Points S :=
  (σ.baseChange S).map ((σ.baseChange L).baseChange S)
    (towerMap L S).toRingHom (RingHom.id S)
    (towerMap_involution σ L S) (towerMap_scalar L S)

theorem towerPoints_multiplier (g : σ.Points S) :
    Points.multiplier (σ.baseChange L) S (σ.towerPoints L S g) =
      Points.multiplier σ S g := by
  apply Units.ext
  rfl

/-- Rational points go to rational points of the scalar-extended group. -/
theorem towerPoints_diagonalPoints (g : σ.similitudes) :
    σ.towerPoints L S (σ.diagonalPoints S g) =
      (σ.baseChange L).diagonalPoints S (σ.diagonalPoints L g) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    change towerMap L S ((1 : S) ⊗ₜ[ℚ] (g.1.1 : A)) =
      (1 : S) ⊗ₜ[L] ((1 : L) ⊗ₜ[ℚ] (g.1.1 : A))
    rw [towerMap_tmul]
  · apply Units.ext
    change algebraMap ℚ S (g.1.2 : ℚ) = algebraMap L S (algebraMap ℚ L (g.1.2 : ℚ))
    exact (RingHom.congr_fun (Subsingleton.elim ((algebraMap L S).comp (algebraMap ℚ L))
      (algebraMap ℚ S)) _).symm

end Tower

section Local

open Langlands.Global

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A)
variable {L : Type u} [Field L] [Algebra ℚ L]
variable {W : Type w} [AddCommGroup W] [Module L W]

namespace AlgebraicRepresentation

variable {σ}

/-- A representation `ρ` of the group over `L`, evaluated on the points of the
rational group over a `ℚ`-algebra `T` through a `ℚ`-algebra map `φ : T → S`
to an `L`-algebra `S`. -/
def actVia (ρ : (σ.baseChange L).AlgebraicRepresentation W) {T : Type*} [CommRing T]
    [Algebra ℚ T] {S : Type u} [CommRing S] [Algebra ℚ S] [Algebra L S] (φ : T →ₐ[ℚ] S) :
    σ.Points T →* ((S ⊗[L] W) ≃ₗ[S] (S ⊗[L] W)) :=
  (ρ.act S).comp ((σ.towerPoints L S).comp (σ.pointsMap φ))

theorem actVia_diagonalPoints (ρ : (σ.baseChange L).AlgebraicRepresentation W) {T : Type*}
    [CommRing T] [Algebra ℚ T] {S : Type u} [CommRing S] [Algebra ℚ S] [Algebra L S]
    (φ : T →ₐ[ℚ] S) (g : σ.similitudes) :
    ρ.actVia φ (σ.diagonalPoints T g) =
      (ρ.rationalAction (σ.diagonalPoints L g)).baseChange L S W W := by
  rw [actVia, MonoidHom.comp_apply, MonoidHom.comp_apply, pointsMap_diagonalPoints,
    towerPoints_diagonalPoints]
  exact act_diagonalPoints ρ S _

/-- Harris's `ρ` on `W(L_v)`, `L_v = L ⊗_ℚ ℚ_v`, as a representation of the
points over the completion at a finite place `v`. -/
def harrisLocal (ρ : (σ.baseChange L).AlgebraicRepresentation W) (v : FinitePlace ℚ) :
    σ.Points (FiniteCompletion ℚ v) →*
      (((L ⊗[ℚ] FiniteCompletion ℚ v) ⊗[L] W) ≃ₗ[L ⊗[ℚ] FiniteCompletion ℚ v]
        ((L ⊗[ℚ] FiniteCompletion ℚ v) ⊗[L] W)) :=
  ρ.actVia Algebra.TensorProduct.includeRight

/-- The action of the finite adelic points through their component at `v`. -/
def finiteAdelicVia [Module.Finite ℚ A] (ρ : (σ.baseChange L).AlgebraicRepresentation W)
    (v : FinitePlace ℚ) {S : Type u} [CommRing S] [Algebra ℚ S] [Algebra L S]
    (φ : FiniteCompletion ℚ v →ₐ[ℚ] S) :
    σ.FiniteAdelicPoints →* ((S ⊗[L] W) ≃ₗ[S] (S ⊗[L] W)) :=
  (ρ.actVia φ).comp (σ.finiteLocalMap v).toMonoidHom

theorem finiteAdelicVia_diagonal [Module.Finite ℚ A]
    (ρ : (σ.baseChange L).AlgebraicRepresentation W) (v : FinitePlace ℚ) {S : Type u}
    [CommRing S] [Algebra ℚ S] [Algebra L S] (φ : FiniteCompletion ℚ v →ₐ[ℚ] S)
    (g : σ.similitudes) :
    ρ.finiteAdelicVia v φ (σ.finiteAdelicDiagonal g) =
      (ρ.rationalAction (σ.diagonalPoints L g)).baseChange L S W W := by
  rw [finiteAdelicVia, MonoidHom.comp_apply]
  erw [finiteLocalMap_diagonal]
  exact ρ.actVia_diagonalPoints φ g

section Place

variable [NumberField L]

/-- The `λ`-adic action: finite adelic points act on `W ⊗_L L_λ` through
their component at the prime `p` below `λ`. -/
def placeAction [Module.Finite ℚ A] (ρ : (σ.baseChange L).AlgebraicRepresentation W)
    (p : FinitePlace ℚ) (l : FinitePlace L) [l.asIdeal.LiesOver p.asIdeal] :
    σ.FiniteAdelicPoints →*
      ((FiniteCompletion L l ⊗[L] W) ≃ₗ[FiniteCompletion L l] (FiniteCompletion L l ⊗[L] W)) :=
  ρ.finiteAdelicVia p (AdelicFunctoriality.FiniteExtension.completionMap p l).toRatAlgHom

theorem placeAction_diagonal [Module.Finite ℚ A]
    (ρ : (σ.baseChange L).AlgebraicRepresentation W)
    (p : FinitePlace ℚ) (l : FinitePlace L) [l.asIdeal.LiesOver p.asIdeal]
    (g : σ.similitudes) :
    ρ.placeAction p l (σ.finiteAdelicDiagonal g) =
      (ρ.rationalAction (σ.diagonalPoints L g)).baseChange L (FiniteCompletion L l) W W :=
  ρ.finiteAdelicVia_diagonal p _ g

end Place

end AlgebraicRepresentation

end Local

end Langlands.Shimura.AlgebraInvolution
