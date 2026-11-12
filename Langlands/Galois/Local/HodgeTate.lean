import Langlands.Galois.CoefficientRepresentation
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Hodge-Tate decompositions of `ℓ`-adic representations of local Galois groups

For a finite extension `F` of `ℚ_p`, `Closure p F` is Mathlib's algebraic
closure `F̄` of `F` with the spectral norm over `ℚ_p`, and `Completed p F` is
its completion `C_F`. Every element of `Gal(F̄/F)` is an isometry of `F̄` and
extends continuously to `C_F`. With the `p`-adic cyclotomic character this
gives the twists `C_F(j)`.

`HasHodgeTateDecomposition p F Λ A n m k` says that, for a continuous
representation `A` of `Gal(F̄/F)` on a finite-dimensional vector space `V`
over a field `Λ` with a `ℚ_p`-algebra structure, there is a
`C_F`-linear, `Λ`-linear and `Gal(F̄/F)`-equivariant isomorphism
`⊕_{i < n} ((C_F ⊗_{ℚ_p} Λ)(k i))^m ≅ C_F ⊗_{ℚ_p} V`.
-/

noncomputable section

open scoped TensorProduct

universe u uL uV

namespace Langlands.GaloisRepresentation.HodgeTate

variable (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Algebra ℚ_[p] F]

/-- The algebraic closure `F̄` of `F`, to be given the spectral norm over `ℚ_p`. -/
def Closure (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Algebra ℚ_[p] F] : Type u :=
  AlgebraicClosure F

namespace Closure

instance : Field (Closure p F) := inferInstanceAs (Field (AlgebraicClosure F))

instance : Algebra F (Closure p F) := inferInstanceAs (Algebra F (AlgebraicClosure F))

instance : Algebra ℚ_[p] (Closure p F) := inferInstanceAs (Algebra ℚ_[p] (AlgebraicClosure F))

instance : IsScalarTower ℚ_[p] F (Closure p F) :=
  inferInstanceAs (IsScalarTower ℚ_[p] F (AlgebraicClosure F))

variable [FiniteDimensional ℚ_[p] F]

instance isAlgebraic : Algebra.IsAlgebraic ℚ_[p] (Closure p F) :=
  haveI : Algebra.IsAlgebraic F (Closure p F) := AlgebraicClosure.isAlgebraic F
  Algebra.IsAlgebraic.trans ℚ_[p] F (Closure p F)

/-- The spectral norm over `ℚ_p`, the unique norm extending that of `ℚ_p`. -/
instance normedField : NormedField (Closure p F) := spectralNorm.normedField ℚ_[p] (Closure p F)

instance normedAlgebra : NormedAlgebra ℚ_[p] (Closure p F) :=
  spectralNorm.normedAlgebra ℚ_[p] (Closure p F)

instance : UniformContinuousConstSMul ℚ_[p] (Closure p F) :=
  uniformContinuousConstSMul_of_continuousConstSMul ℚ_[p] (Closure p F)

variable {p F} in
/-- An element of `Gal(F̄/F)` as an automorphism of `Closure p F`. -/
def galois (σ : Field.absoluteGaloisGroup F) : Closure p F ≃ₐ[F] Closure p F := σ

/-- Every element of `Gal(F̄/F)` preserves the spectral norm. -/
theorem norm_galois (σ : Field.absoluteGaloisGroup F) (x : Closure p F) :
    ‖galois σ x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv ((galois σ).restrictScalars ℚ_[p]) x).symm

/-- Every element of `Gal(F̄/F)` is an isometry of `F̄`. -/
theorem isometry_galois (σ : Field.absoluteGaloisGroup F) :
    Isometry (galois (p := p) σ) :=
  AddMonoidHomClass.isometry_of_norm (galois (p := p) σ).toRingEquiv.toAddMonoidHom
    (norm_galois p F σ)

instance isAlgClosed : IsAlgClosed (Closure p F) :=
  inferInstanceAs (IsAlgClosed (AlgebraicClosure F))

instance charZero : CharZero (Closure p F) :=
  (RingHom.charZero_iff (algebraMap ℚ_[p] (Closure p F)).injective).mp inferInstance

instance hasEnoughRootsOfUnity (i : ℕ) : HasEnoughRootsOfUnity (Closure p F) (p ^ i) :=
  haveI : NeZero (p : Closure p F) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  inferInstance

omit [FiniteDimensional ℚ_[p] F] in
/-- `cyclotomicCharacter` is the `p`-adic cyclotomic character of `Gal(F̄/F)`: an element
`σ` raises every `p^n`-th root of unity of `F̄` to the power `χ(σ) mod p^n`. -/
theorem galois_apply_of_pow_eq_one (σ : Field.absoluteGaloisGroup F) {n : ℕ} (t : Closure p F)
    (ht : t ^ p ^ n = 1) :
    galois σ t = t ^ ((cyclotomicCharacter (Closure p F) p
      (galois (p := p) σ).toRingEquiv).val.toZModPow n).val :=
  cyclotomicCharacter.spec p (galois (p := p) σ).toRingEquiv t ht

end Closure

variable [FiniteDimensional ℚ_[p] F]

/-- The completion `C_F` of `F̄` for the spectral norm. -/
abbrev Completed : Type u := UniformSpace.Completion (Closure p F)

variable {F}

/-- The continuous extension to `C_F` of an element `σ` of `Gal(F̄/F)`. -/
def galoisRingHom (σ : Field.absoluteGaloisGroup F) : Completed p F →+* Completed p F :=
  UniformSpace.Completion.mapRingHom (Closure.galois σ).toRingEquiv.toRingHom
    (Closure.isometry_galois p F σ).continuous

theorem galoisRingHom_coe (σ : Field.absoluteGaloisGroup F) (x : Closure p F) :
    galoisRingHom p σ (x : Completed p F) = ((Closure.galois σ x : Closure p F) : Completed p F) :=
  UniformSpace.Completion.mapRingHom_coe _ x

/-- The extensions form an action of `Gal(F̄/F)` on `C_F`. -/
theorem continuous_galoisRingHom (σ : Field.absoluteGaloisGroup F) :
    Continuous (galoisRingHom p σ) :=
  UniformSpace.Completion.continuous_map

theorem galoisRingHom_mul (σ τ : Field.absoluteGaloisGroup F) :
    galoisRingHom p (σ * τ) = (galoisRingHom p σ).comp (galoisRingHom p τ) := by
  refine RingHom.ext fun x => ?_
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (continuous_galoisRingHom p _)
      ((continuous_galoisRingHom p σ).comp (continuous_galoisRingHom p τ))) fun a => ?_
  rw [RingHom.comp_apply, galoisRingHom_coe, galoisRingHom_coe, galoisRingHom_coe]
  rfl

theorem galoisRingHom_one : galoisRingHom p (1 : Field.absoluteGaloisGroup F) = RingHom.id _ := by
  refine RingHom.ext fun x => ?_
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (continuous_galoisRingHom p _) continuous_id) fun a => ?_
  rw [galoisRingHom_coe]
  rfl

/-- The extension of `σ` to `C_F` fixes `ℚ_p`, so it is `ℚ_p`-linear. -/
def galoisLinear (σ : Field.absoluteGaloisGroup F) : Completed p F →ₗ[ℚ_[p]] Completed p F where
  toFun := galoisRingHom p σ
  map_add' := map_add _
  map_smul' c x := by
    rw [Algebra.smul_def, map_mul, RingHom.id_apply, Algebra.smul_def,
      UniformSpace.Completion.algebraMap_def, galoisRingHom_coe]
    congr 2
    exact ((Closure.galois (p := p) σ).restrictScalars ℚ_[p]).commutes c

/-- The `p`-adic cyclotomic character `χ(σ)` of `σ ∈ Gal(F̄/F)`, as an element of `C_F`. -/
def cyclotomic (σ : Field.absoluteGaloisGroup F) : Completed p F :=
  algebraMap ℚ_[p] (Completed p F)
    ((cyclotomicCharacter (Closure p F) p (Closure.galois σ).toRingEquiv :
      ℤ_[p]) : ℚ_[p])

theorem cyclotomic_mul (σ τ : Field.absoluteGaloisGroup F) :
    cyclotomic p (σ * τ) = cyclotomic p σ * cyclotomic p τ := by
  have h : (Closure.galois (p := p) (σ * τ)).toRingEquiv =
      (Closure.galois (p := p) σ).toRingEquiv * (Closure.galois (p := p) τ).toRingEquiv := rfl
  rw [cyclotomic, cyclotomic, cyclotomic, h, map_mul, Units.val_mul, PadicInt.coe_mul, map_mul]

theorem cyclotomic_ne_zero (σ : Field.absoluteGaloisGroup F) : cyclotomic p σ ≠ 0 := by
  rw [cyclotomic, ne_eq, map_eq_zero_iff _ (algebraMap ℚ_[p] (Completed p F)).injective,
    PadicInt.coe_eq_zero]
  exact Units.ne_zero _

variable (F) (Λ : Type uL) [Field Λ] [TopologicalSpace Λ] [Algebra ℚ_[p] Λ]

/-- A Hodge-Tate decomposition of `A` in which each twist `C_F(k i)`, `i < n`, occurs
`m` times over `Λ`: a `C_F`-linear isomorphism
`Φ : ⊕_{i < n} ((C_F ⊗_{ℚ_p} Λ)(k i))^m ≅ C_F ⊗_{ℚ_p} V` that commutes with the
action of `Λ` on the second factors and intertwines the semilinear actions of
`σ ∈ Gal(F̄/F)`: `x ↦ χ(σ)^{k i} (σ ⊗ 1)(x)` on the summand of index `i`, and
`σ ⊗ ρ(σ)` on `C_F ⊗_{ℚ_p} V`. The space `V` is a `ℚ_p`-vector space through
`ℚ_p → Λ`. -/
def HasHodgeTateDecomposition (A : Objects.{u, uL, uV} F Λ) (n m : ℕ) (k : Fin n → ℤ) :
    Prop :=
  letI : Module ℚ_[p] A.val := Module.compHom A.val (algebraMap ℚ_[p] Λ)
  haveI : IsScalarTower ℚ_[p] Λ A.val := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  ∃ Φ : (Fin n → Fin m → Completed p F ⊗[ℚ_[p]] Λ) ≃ₗ[Completed p F]
      (Completed p F ⊗[ℚ_[p]] A.val),
    (∀ (a : Λ) (x : Fin n → Fin m → Completed p F ⊗[ℚ_[p]] Λ),
      Φ (fun i j => LinearMap.lTensor (Completed p F) (LinearMap.mulLeft ℚ_[p] a) (x i j)) =
        LinearMap.lTensor (Completed p F)
          ((a • LinearMap.id : A.val →ₗ[Λ] A.val).restrictScalars ℚ_[p]) (Φ x)) ∧
    ∀ (σ : Field.absoluteGaloisGroup F) (x : Fin n → Fin m → Completed p F ⊗[ℚ_[p]] Λ),
      Φ (fun i j => cyclotomic p σ ^ k i •
          LinearMap.rTensor Λ (galoisLinear p σ) (x i j)) =
        TensorProduct.map (galoisLinear p σ)
          ((A.val.representation σ).restrictScalars ℚ_[p]) (Φ x)

end Langlands.GaloisRepresentation.HodgeTate
