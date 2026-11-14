import Langlands.GroupScheme.IntegralModel.Smoothening.Hopf
import Langlands.GroupScheme.Absolute.RationalPointClosureProof
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Smoothness of the integral functions

Let `R` be a discrete valuation ring with algebraically closed residue field `k` and
fraction field `K`, and `A` a commutative Hopf algebra over `R` with smooth generic
fibre. If the Hopf algebra `B` of integral functions is finitely generated, then it is
smooth over `R`:

* the special fibre `k ⊗[R] B` is reduced, because the values at `R`-points detect the
  maximal ideal on `B`; a reduced finitely generated Hopf algebra over an algebraically
  closed field is smooth;
* the generic fibre `K ⊗[R] B` is isomorphic to `K ⊗[R] A`;
* `B` is flat and finitely presented, so the fibrewise criterion applies. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

namespace Langlands.GroupScheme.IntegralModel.Smoothening

section Group

/-- A reduced finitely generated commutative Hopf algebra over an algebraically closed
field is smooth. -/
theorem smooth_of_isReduced_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    (H : Type u) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [_root_.IsReduced H] :
    Algebra.Smooth k H := by
  let G := (hopfSpec (CommRingCat.of k)).obj (op (CommHopfAlgCat.of (CommRingCat.of k) H))
  have h₁ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k H))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom,
      RingHom.finiteType_algebraMap]
    infer_instance
  have : LocallyOfFiniteType G.X.hom := h₁
  have : GrpObj (Over.mk G.X.hom) := inferInstanceAs (GrpObj G.X)
  have : IsReduced G.X.left := inferInstanceAs (IsReduced (Spec (CommRingCat.of H)))
  have h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k H))) :=
    RationalPointClosure.smooth_of_grpObj_of_isAlgClosed G.X.hom
  rw [HasRingHomProperty.Spec_iff (P := @Smooth), CommRingCat.hom_ofHom,
    RingHom.smooth_algebraMap] at h
  exact h

end Group

section Transfer

variable {R : Type*} [CommRing R]

/-- Formal smoothness of a base change transfers along an algebra map of the bases. -/
theorem formallySmooth_tensor_of_algHom {F L : Type*} [CommRing F] [CommRing L]
    [Algebra R F] [Algebra R L] (B : Type*) [CommRing B] [Algebra R B] (f : F →ₐ[R] L)
    [Algebra.FormallySmooth F (F ⊗[R] B)] : Algebra.FormallySmooth L (L ⊗[R] B) := by
  let := f.toRingHom.toAlgebra
  have : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact .of_equiv (Algebra.TensorProduct.cancelBaseChange R F L L B)

end Transfer

variable {R : Type u} {K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Type u} [CommRing A]

section Generic

variable [Algebra R A]

variable (R K A) in
/-- The map `K ⊗[R] B → K ⊗[R] A` induced by the inclusion `B ⊆ K ⊗[R] A`. -/
def genericMul : K ⊗[R] integralFunctions R K A →ₐ[K] K ⊗[R] A :=
  Algebra.TensorProduct.lift (Algebra.ofId K (K ⊗[R] A)) (integralFunctions R K A).val
    fun _ _ => .all _ _

variable (R K A) in
/-- The map `K ⊗[R] A → K ⊗[R] B` induced by the inclusion `A → B`. -/
def genericMap : K ⊗[R] A →ₐ[K] K ⊗[R] integralFunctions R K A :=
  Algebra.TensorProduct.map (AlgHom.id K K) (incl R K A)

omit [IsDomain R] [IsFractionRing R K] in
theorem genericMul_genericMap (x : K ⊗[R] A) : genericMul R K A (genericMap R K A x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul c a =>
    simp [genericMul, genericMap, Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem genericMap_surjective : Function.Surjective (genericMap R K A) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul c b =>
    obtain ⟨s, a, hs, hsa⟩ := exists_smul_eq_one_tmul K A (b : K ⊗[R] A)
    have hb : s • b = incl R K A a := Subtype.ext hsa
    have hs' : algebraMap R K s ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hs
    refine ⟨(c * (algebraMap R K s)⁻¹) ⊗ₜ a, ?_⟩
    rw [genericMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ← hb,
      ← TensorProduct.smul_tmul, Algebra.smul_def]
    congr 1
    field_simp
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩

variable (R K A) in
/-- The generic fibres of `A` and of its integral functions agree. -/
def genericEquiv : K ⊗[R] A ≃ₐ[K] K ⊗[R] integralFunctions R K A :=
  AlgEquiv.ofBijective (genericMap R K A)
    ⟨Function.LeftInverse.injective genericMul_genericMap, genericMap_surjective⟩

end Generic

section DVR

variable [IsDiscreteValuationRing R]

open IsLocalRing

/-- The special fibre of the integral functions is reduced. -/
theorem isReduced_residueField_tensor [Algebra R A] :
    _root_.IsReduced (ResidueField R ⊗[R] integralFunctions R K A) := by
  refine ⟨fun z ⟨n, hn⟩ => ?_⟩
  obtain ⟨b, rfl⟩ := exists_one_tmul_eq z
  rw [Algebra.TensorProduct.tmul_pow, one_pow] at hn
  rw [one_tmul_eq_zero_iff]
  refine detectsMaximal_point (K := K) b fun φ => ?_
  have h := congrArg (reduceForm (point (K := K) φ).toLinearMap) hn
  rw [reduceForm_one_tmul, map_zero, AlgHom.toLinearMap_apply, map_pow, map_pow] at h
  exact (residue_eq_zero_iff _).1 (IsNilpotent.eq_zero ⟨n, h⟩)

/-- The residue field of `R` maps to the residue field of the maximal ideal. -/
def residueFieldToMaximal : ResidueField R →ₐ[R] (maximalIdeal R).ResidueField :=
  Ideal.Quotient.liftₐ (maximalIdeal R) (Algebra.ofId R _) fun _ ha =>
    Ideal.algebraMap_residueField_eq_zero.2 ha

/-- Fibre criterion over a discrete valuation ring: a flat algebra of finite type whose
generic and special fibres are smooth is smooth. -/
theorem smooth_of_smooth_fibres (C : Type u) [CommRing C] [Algebra R C]
    [Module.Flat R C] [Algebra.FiniteType R C] [Algebra.FormallySmooth K (K ⊗[R] C)]
    [Algebra.FormallySmooth (ResidueField R) (ResidueField R ⊗[R] C)] :
    Algebra.Smooth R C := by
  have : Algebra.FinitePresentation R C := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  refine Algebra.Smooth.of_formallySmooth_fiber fun I _ => ?_
  by_cases h : I = ⊥
  · subst h
    exact formallySmooth_tensor_of_algHom _ (IsLocalization.algEquiv (nonZeroDivisors R) K _).toAlgHom
  · obtain rfl := IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal ‹_› h)
    exact formallySmooth_tensor_of_algHom _ residueFieldToMaximal

variable [IsAlgClosed (ResidueField R)] [HopfAlgebra R A]

/-- If the integral functions of a Hopf algebra with smooth generic fibre over a discrete
valuation ring with algebraically closed residue field are finitely generated, they are
smooth. -/
theorem smooth_integralFunctions [Algebra.Smooth K (K ⊗[R] A)]
    [Algebra.FiniteType R (integralFunctions R K A)] :
    Algebra.Smooth R (integralFunctions R K A) := by
  have : _root_.IsReduced (ResidueField R ⊗[R] integralFunctions R K A) :=
    isReduced_residueField_tensor
  have : Algebra.Smooth (ResidueField R) (ResidueField R ⊗[R] integralFunctions R K A) :=
    smooth_of_isReduced_of_isAlgClosed _
  have : Algebra.FormallySmooth K (K ⊗[R] integralFunctions R K A) :=
    .of_equiv (genericEquiv R K A)
  exact smooth_of_smooth_fibres (K := K) _

end DVR

end Langlands.GroupScheme.IntegralModel.Smoothening
