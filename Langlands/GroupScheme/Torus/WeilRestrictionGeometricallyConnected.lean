import Langlands.GroupScheme.Torus.WeilRestrictionBaseChange
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Geometric connectedness of `Res_{B/A} 𝔾ₘ`

For a field `k` and a finite `k`-algebra `B` with basis `b₁, …, bₙ`, the functor
`R ↦ (B ⊗[k] R)ˣ` is corepresented by the localized polynomial algebra
`k[X₁, …, Xₙ][N⁻¹]`, where `N` is the determinant of multiplication by the generic element
`∑ bᵢ Xᵢ`. This algebra is a domain, so `Res_{B/k} 𝔾ₘ` is connected. Over an arbitrary
commutative ring `A` and a finite projective `A`-algebra `B`, every fibre of
`Res_{B/A} 𝔾ₘ` over a field `κ` is `Res_{(κ ⊗[A] B)/κ} 𝔾ₘ`, so `Res_{B/A} 𝔾ₘ` has
geometrically connected fibres. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.WeilGm

namespace Connected

section Coordinates

variable {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B]
  {n : ℕ} (b : Module.Basis (Fin n) k B)

/-- The matrix of multiplication by the generic element `∑ bᵢ Xᵢ` in the basis `b`:
its `(j, l)` entry is `∑ᵢ cᵢₗⱼ Xᵢ`, where `bᵢ bₗ = ∑ⱼ cᵢₗⱼ bⱼ`. -/
def genericMatrix : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) k) :=
  Matrix.of fun j l => ∑ i, MvPolynomial.C (b.repr (b i * b l) j) * MvPolynomial.X i

/-- The norm form: the determinant of multiplication by the generic element. -/
def normPoly : MvPolynomial (Fin n) k := (genericMatrix b).det

/-- The coordinates `r ↦ ∑ bᵢ ⊗ rᵢ` of `B ⊗ R`. -/
def coordEquiv (R : Type u) [CommRing R] [Algebra k R] : (Fin n → R) ≃ B ⊗[k] R :=
  (Algebra.TensorProduct.basis R b).equivFun.symm.toEquiv.trans
    (TensorProduct.comm k R B).toEquiv

theorem coordEquiv_apply (R : Type u) [CommRing R] [Algebra k R] (r : Fin n → R) :
    coordEquiv b R r = ∑ i, b i ⊗ₜ[k] r i := by
  simp only [coordEquiv, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
    Module.Basis.equivFun_symm_apply, Algebra.TensorProduct.basis_apply, map_sum,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.comm_tmul]

theorem lTensor_coordEquiv {R S : Type u} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
    (g : R →ₐ[k] S) (r : Fin n → R) :
    Algebra.TensorProduct.lTensor (S := B) B g (coordEquiv b R r) =
      coordEquiv b S (fun i => g (r i)) := by
  rw [coordEquiv_apply, coordEquiv_apply, map_sum]
  simp

/-- Multiplication by the element with coordinates `r` has the specialized generic matrix. -/
theorem leftMulMatrix_comm_coordEquiv (R : Type u) [CommRing R] [Algebra k R]
    (r : Fin n → R) :
    Algebra.leftMulMatrix (Algebra.TensorProduct.basis R b)
        (Algebra.TensorProduct.comm k B R (coordEquiv b R r)) =
      (genericMatrix b).map (MvPolynomial.aeval r) := by
  ext j l
  rw [Algebra.leftMulMatrix_eq_repr_mul, coordEquiv_apply, map_sum, Finset.sum_mul, map_sum]
  simp only [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.TensorProduct.basis_repr_tmul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
    smul_eq_mul, genericMatrix, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

/-- An element of an algebra is a unit exactly when multiplication by it is. -/
theorem isUnit_iff_isUnit_lmul {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (y : S) :
    IsUnit y ↔ IsUnit (Algebra.lmul R S y) := by
  refine ⟨fun h => h.map (Algebra.lmul R S), fun h => ?_⟩
  obtain ⟨g, hg⟩ := h.exists_right_inv
  refine IsUnit.of_mul_eq_one (g 1) ?_
  have h1 := congrArg (fun f : Module.End R S => f 1) hg
  simpa using h1

/-- `x ∈ B ⊗ R` with coordinates `r` is a unit exactly when the norm form at `r` is. -/
theorem isUnit_coordEquiv_iff (R : Type u) [CommRing R] [Algebra k R] (r : Fin n → R) :
    IsUnit (coordEquiv b R r) ↔ IsUnit (MvPolynomial.aeval r (normPoly b)) := by
  have : Module.Finite R (R ⊗[k] B) := Module.Finite.of_basis (Algebra.TensorProduct.basis R b)
  have : Module.Free R (R ⊗[k] B) := Module.Free.of_basis (Algebra.TensorProduct.basis R b)
  rw [← MulEquiv.isUnit_map (Algebra.TensorProduct.comm k B R).toMulEquiv]
  change IsUnit (Algebra.TensorProduct.comm k B R (coordEquiv b R r)) ↔ _
  rw [isUnit_iff_isUnit_lmul (R := R), LinearMap.isUnit_iff_isUnit_det,
    ← LinearMap.det_toMatrix (Algebra.TensorProduct.basis R b),
    ← Algebra.leftMulMatrix_apply, leftMulMatrix_comm_coordEquiv, normPoly, AlgHom.map_det]
  rfl

/-- The norm form is nonzero: it takes a unit value at the coordinates of `1`. -/
theorem normPoly_ne_zero : normPoly b ≠ 0 := by
  intro h
  have hu : IsUnit (coordEquiv b k ((coordEquiv b k).symm 1)) := by
    rw [Equiv.apply_symm_apply]
    exact isUnit_one
  rw [isUnit_coordEquiv_iff, h, map_zero] at hu
  exact not_isUnit_zero hu

end Coordinates

section Corepresentation

variable {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B]
  {n : ℕ} (b : Module.Basis (Fin n) k B)

/-- The localized polynomial algebra `k[X₁, …, Xₙ][N⁻¹]`. -/
abbrev locAlg : Type u := Localization.Away (normPoly b)

theorem aeval_normPoly_isUnit (R : Type u) [CommRing R] [Algebra k R]
    (f : locAlg b →ₐ[k] R) :
    IsUnit (MvPolynomial.aeval
      (fun i => f (algebraMap (MvPolynomial (Fin n) k) (locAlg b) (MvPolynomial.X i)))
      (normPoly b)) := by
  have hcomp : f.comp (IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k) (locAlg b)) =
      MvPolynomial.aeval
        (fun i => f (algebraMap (MvPolynomial (Fin n) k) (locAlg b) (MvPolynomial.X i))) :=
    MvPolynomial.algHom_ext fun i => by simp
  rw [← hcomp]
  exact (IsLocalization.Away.algebraMap_isUnit (normPoly b)).map f

theorem lift_algebraMap (R : Type u) [CommRing R] [Algebra k R] (r : Fin n → R)
    (hr : IsUnit (MvPolynomial.aeval r (normPoly b))) (x : MvPolynomial (Fin n) k) :
    IsLocalization.Away.liftAlgHom (normPoly b) (f := MvPolynomial.aeval r) hr
        (algebraMap (MvPolynomial (Fin n) k) (locAlg b) x) = MvPolynomial.aeval r x := by
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

variable [Module.Finite k B]

/-- `k[X][N⁻¹]` corepresents `R ↦ (B ⊗ R)ˣ`. -/
def corep :
    (WeilGm.functor (CommRingCat.of k) B ⋙ forget GrpCat).CorepresentableBy
      (CommAlgCat.of (CommRingCat.of k) (locAlg b)) where
  homEquiv {R} :=
    { toFun := fun f =>
        ((isUnit_coordEquiv_iff b R _).2 (aeval_normPoly_isUnit b R f.hom)).unit
      invFun := fun u =>
        let u' : (B ⊗[k] R)ˣ := u
        CommAlgCat.ofHom (IsLocalization.Away.liftAlgHom (normPoly b)
          (f := MvPolynomial.aeval ((coordEquiv b R).symm (u' : B ⊗[k] R)))
          ((isUnit_coordEquiv_iff b R _).1 (by
            rw [Equiv.apply_symm_apply]
            exact u'.isUnit)))
      left_inv := fun f => by
        apply CommAlgCat.hom_ext
        apply AlgHom.coe_ringHom_injective
        apply IsLocalization.ringHom_ext (Submonoid.powers (normPoly b))
        apply MvPolynomial.ringHom_ext
        · intro a
          simp only [RingHom.comp_apply, AlgHom.coe_toRingHom]
          rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
            AlgHom.commutes, AlgHom.commutes]
        · intro i
          simp only [RingHom.comp_apply, AlgHom.coe_toRingHom]
          erw [lift_algebraMap]
          simp only [MvPolynomial.aeval_X, IsUnit.unit_spec, Equiv.symm_apply_apply]
      right_inv := fun u => by
        let u' : (B ⊗[k] R)ˣ := u
        apply Units.ext
        change coordEquiv b R _ = (u' : B ⊗[k] R)
        conv_rhs => rw [← Equiv.apply_symm_apply (coordEquiv b R) (u' : B ⊗[k] R)]
        congr 1
        funext i
        dsimp only
        erw [lift_algebraMap]
        simp only [MvPolynomial.aeval_X]
        rfl }
  homEquiv_comp {R R'} g f := by
    apply Units.ext
    change coordEquiv b R' _ =
      Algebra.TensorProduct.lTensor (S := B) B g.hom (coordEquiv b R _)
    rw [lTensor_coordEquiv]
    rfl

end Corepresentation

end Connected

/-- Over a field `k`, `Res_{B/k} 𝔾ₘ` is connected for every finite `k`-algebra `B`: its
coordinate algebra is isomorphic to a localization of a polynomial ring. -/
theorem connectedSpace_groupScheme (k : Type u) [Field k] (B : Type u) [CommRing B]
    [Algebra k B] [Module.Finite k B] :
    ConnectedSpace (groupScheme (CommRingCat.of k) B).X.left := by
  classical
  let b : Module.Basis (Fin (Module.finrank k B)) k B := Module.finBasis k B
  have hN : Connected.normPoly b ≠ 0 := Connected.normPoly_ne_zero b
  have : IsDomain (Connected.locAlg b) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hN)
  let e := Connected.corep b
  let iso := (corepresentableBy (CommRingCat.of k) B).uniqueUpToIso e
  let isoS := (Over.forget _).mapIso ((algSpec (CommRingCat.of k)).mapIso iso.op.symm)
  have hP : ConnectedSpace (Spec (CommRingCat.of (Connected.locAlg b))) := inferInstance
  have : ConnectedSpace ((Over.forget (Spec (CommRingCat.of k))).obj
      ((algSpec (CommRingCat.of k)).obj
        (Opposite.op (CommAlgCat.of (CommRingCat.of k) (Connected.locAlg b))))) := hP
  exact (Scheme.homeoOfIso isoS.symm).surjective.connectedSpace
    (Scheme.homeoOfIso isoS.symm).continuous

/-- For a finite projective `A`-algebra `B`, `Res_{B/A} 𝔾ₘ` is geometrically connected over
`Spec A`: its base change to any field `κ` is `Res_{(κ ⊗[A] B)/κ} 𝔾ₘ`. -/
theorem geometricallyConnected (A : Type u) [CommRing A] (B : Type u) [CommRing B]
    [Algebra A B] [Module.Finite A B] [Module.Projective A B] :
    GeometricallyConnected (groupScheme (CommRingCat.of A) B).X.hom := by
  rw [geometricallyConnected_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro κ _ _
  let e := algebraBaseChangeIso (CommRingCat.of A) (CommRingCat.of κ) B
  let φ : ((GroupScheme.baseChange (baseMap (CommRingCat.of A)
      (CommRingCat.of κ))).obj (groupScheme (CommRingCat.of A) B)).X.left ≅
      (groupScheme (CommRingCat.of κ) (κ ⊗[A] B)).X.left :=
    (Over.forget _).mapIso ((Grp.forget _).mapIso e)
  have : ConnectedSpace (groupScheme (CommRingCat.of κ) (κ ⊗[A] B)).X.left :=
    connectedSpace_groupScheme κ (κ ⊗[A] B)
  have h : ConnectedSpace ((GroupScheme.baseChange (baseMap (CommRingCat.of A)
      (CommRingCat.of κ))).obj (groupScheme (CommRingCat.of A) B)).X.left :=
    (Scheme.homeoOfIso φ.symm).surjective.connectedSpace (Scheme.homeoOfIso φ.symm).continuous
  exact h

end Langlands.GroupScheme.WeilGm
