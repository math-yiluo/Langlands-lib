import Langlands.GroupScheme.Lie.AdjointDifferentialBaseChange
import Langlands.GroupScheme.Lie.AdjointGenericConjugation
import Langlands.GroupScheme.Rational.MaximalTorusConjugatorReductionCases

/-! # The generic Lie element is not central -/

noncomputable section

universe u v w t s s'

open CategoryTheory AlgebraicGeometry Module
open scoped TensorProduct

namespace Langlands.LinearAlgebra

variable {k : Type u} [Field k]
    {V : Type v} [AddCommGroup V] [Module k V]
    {W : Type w} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {I : Type t} [Fintype I] [DecidableEq I]

/-- If some scalar extension of a linear family of endomorphisms has a nonnilpotent member,
then every member of any scalar extension whose basis coordinates are algebraically
independent over the ground field is nonnilpotent. -/
theorem not_isNilpotent_endomorphismFamilyBaseChange_of_algebraicIndependent
    (φ : V →ₗ[k] Module.End k W) (b : Basis I k V)
    {L : Type s} [Field L] [Algebra k L]
    (hgeo : ∃ z : L ⊗[k] V, ¬ IsNilpotent (endomorphismFamilyBaseChange φ L z))
    {K : Type s'} [Field K] [Algebra k K] {z : K ⊗[k] V}
    (hz : AlgebraicIndependent k fun i => (Algebra.TensorProduct.basis K b).repr z i) :
    ¬ IsNilpotent (endomorphismFamilyBaseChange φ K z) := by
  obtain ⟨z₀, hz₀⟩ := hgeo
  obtain ⟨i, hi, hp⟩ := exists_polyCharpoly_coeff_ne_zero_of_baseChange φ b hz₀
  intro hnil
  apply hp
  apply hz.eq_zero_of_aeval_eq_zero
  have he := LinearMap.polyCharpoly_coeff_eval (endomorphismFamilyBaseChange φ K)
    (Algebra.TensorProduct.basis K b) z i
  rw [hnil.charpoly_eq_X_pow_finrank, Polynomial.coeff_X_pow,
    ite_eq_right_of_eq_false _ _ (eq_false (by rw [Module.finrank_baseChange]; exact hi.ne))] at he
  rw [endomorphismFamilyBaseChange, LinearMap.polyCharpoly_baseChange, Polynomial.coeff_map,
    MvPolynomial.eval_map] at he
  rw [MvPolynomial.aeval_def]
  exact he

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- An isomorphism of schemes is undone on global sections by its inverse. -/
theorem appTop_inv_appTop_hom {X Y : Scheme.{u}} (e : X ≅ Y) (y : Γ(Y, ⊤)) :
    e.inv.appTop (e.hom.appTop y) = y :=
  ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop e.inv_hom_id) y

/-- An isomorphism of schemes is undone on global sections after its inverse. -/
theorem appTop_hom_appTop_inv {X Y : Scheme.{u}} (e : X ≅ Y) (x : Γ(X, ⊤)) :
    e.hom.appTop (e.inv.appTop x) = x :=
  ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop e.hom_inv_id) x

variable (k : Type u) [Field k] (m : Type u)

/-- The `k`-algebra structure of the rational function field sends a constant to the germ at
the generic point of its pullback to affine space. -/
theorem algebraMap_rationalFunctionField_apply (a : k) :
    algebraMap k (𝔸(m; Spec (CommRingCat.of k))).functionField a =
      (𝔸(m; Spec (CommRingCat.of k))).presheaf.germ ⊤ (genericPoint _) trivial
        ((𝔸(m; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)) := by
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (Spec.preimage (rationalFunctionFieldOver k m).hom))
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)
  rw [Spec.map_preimage, CommRingCat.comp_apply, CommRingCat.comp_apply,
    Iso.inv_hom_id_apply] at h
  refine h.symm.trans ?_
  change (Scheme.ΓSpecIso _).hom (((𝔸(m; Spec (CommRingCat.of k))).fromSpecStalk
      (genericPoint _) ≫ (𝔸(m; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  exact Lie.ΓSpecIso_hom_fromSpecStalk_appTop _ _

/-- The coordinate functions of `𝔸(m; Spec k)` are algebraically independent over `k` in its
function field. -/
theorem algebraicIndependent_rationalFunctionFieldCoordinate :
    AlgebraicIndependent k (rationalFunctionFieldCoordinate k m) := by
  have : Nonempty (⊤ : (𝔸(m; Spec (CommRingCat.of k))).Opens) := ⟨⟨genericPoint _, trivial⟩⟩
  let Φ : MvPolynomial m k →+* Γ(𝔸(m; Spec (CommRingCat.of k)), ⊤) :=
    ((AffineSpace.SpecIso m (CommRingCat.of k)).hom.appTop).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m k))).inv.hom
  have hΦ : Function.Injective Φ := by
    intro p q hpq
    have h := congrArg (fun x => (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m k))).hom
      ((AffineSpace.SpecIso m (CommRingCat.of k)).inv.appTop x)) hpq
    simpa only [Φ, RingHom.comp_apply, appTop_inv_appTop_hom, Iso.inv_hom_id_apply] using h
  have he : (MvPolynomial.aeval (rationalFunctionFieldCoordinate k m)).toRingHom =
      ((𝔸(m; Spec (CommRingCat.of k))).germToFunctionField ⊤).hom.comp Φ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have hC : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m k))).inv.hom
          (MvPolynomial.C a) = (AffineSpace.SpecIso m (CommRingCat.of k)).inv.appTop.hom
            ((𝔸(m; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).appTop
              ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)) := by
        have h₁ := ConcreteCategory.congr_hom
          (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
            (MvPolynomial.C : k →+* MvPolynomial m k))) a
        have h₂ : Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial m k)) =
            (AffineSpace.SpecIso m (CommRingCat.of k)).inv ≫
              (𝔸(m; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) :=
          (AffineSpace.SpecIso_inv_over (R := CommRingCat.of k)).symm
        rw [CommRingCat.comp_apply, CommRingCat.comp_apply, h₂, Scheme.Hom.comp_appTop,
          CommRingCat.comp_apply] at h₁
        exact h₁
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C,
        RingHom.comp_apply, Φ]
      rw [algebraMap_rationalFunctionField_apply, hC]
      exact congrArg ((𝔸(m; Spec (CommRingCat.of k))).presheaf.germ ⊤ (genericPoint _)
        trivial).hom (appTop_hom_appTop_inv _ _).symm
    · intro i
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X,
        RingHom.comp_apply, Φ]
      have hX : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m k))).inv.hom
          (MvPolynomial.X i) = (AffineSpace.SpecIso m (CommRingCat.of k)).inv.appTop.hom
            (AffineSpace.coord _ i) :=
        (AffineSpace.SpecIso_inv_appTop_coord (R := CommRingCat.of k) i).symm
      rw [hX]
      exact congrArg ((𝔸(m; Spec (CommRingCat.of k))).germToFunctionField ⊤).hom
        (appTop_hom_appTop_inv _ _).symm
  rw [algebraicIndependent_iff_injective_aeval]
  change Function.Injective (MvPolynomial.aeval (rationalFunctionFieldCoordinate k m)).toRingHom
  rw [he]
  exact ((𝔸(m; Spec (CommRingCat.of k))).germToFunctionField_injective ⊤).comp hΦ

end Langlands.GroupScheme

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {d : ℕ} (c : FiniteCoordinates G d)

/-- The basis of the base Lie kernel whose coordinates are those of `c`. -/
def coordinateBasis : Basis (Fin d) k (Additive (lieKernel G k)) :=
  (Pi.basisFun k (Fin d)).map (c.equiv (.of (CommRingCat.of k) k)).symm

/-- The scalar extension of the coordinate basis reads off the coordinates of the
scalar-extended Lie vector. -/
theorem coordinateBasis_baseChange_repr {K : Type u} [Field K] [Algebra k K]
    (z : K ⊗[k] Additive (lieKernel G k)) (i : Fin d) :
    (Algebra.TensorProduct.basis K (coordinateBasis c)).repr z i =
      c.equiv (.of (CommRingCat.of k) K) (kernelScalarExtension G K z) i := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    have h := c.naturality (A := .of (CommRingCat.of k) k) (B := .of (CommRingCat.of k) K)
      (CommAlgCat.ofHom (Algebra.ofId k K)) x
    rw [kernelScalarExtension_tmul, map_smul, Pi.smul_apply, smul_eq_mul,
      Algebra.TensorProduct.basis_repr_tmul]
    change _ = a * c.equiv (.of (CommRingCat.of k) K)
      (lieKernelMapLinear G (CommAlgCat.ofHom (Algebra.ofId k K)).hom x) i
    rw [h]
    simp [coordinateBasis]
  | add x y hx hy =>
    rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add]
    rfl

/-- **Nonnilpotence at algebraically independent coordinates.** If some scalar extension of
the actual adjoint differential family of `G` has a nonnilpotent member, then the adjoint
differential of every Lie vector over a field extension `K` of `k` whose coordinates are
algebraically independent over `k` is nonnilpotent. -/
theorem not_isNilpotent_tangentMatrix_of_algebraicIndependent
    {L : Type u} [Field L] [Algebra k L]
    (hgeo : ∃ z : L ⊗[k] Additive (lieKernel G k),
      ¬ IsNilpotent
        (LinearAlgebra.endomorphismFamilyBaseChange (adjointDifferentialFamily c) L z))
    {K : Type u} [Field K] [Algebra k K] (X : Additive (lieKernel G K))
    (hX : AlgebraicIndependent k (c.equiv (.of (CommRingCat.of k) K) X)) :
    ¬ IsNilpotent (Matrix.toLin' ((adjointRepresentation c).tangentMatrix K X.toMul)) := by
  have hz := LinearAlgebra.not_isNilpotent_endomorphismFamilyBaseChange_of_algebraicIndependent
    (adjointDifferentialFamily c) (coordinateBasis c) hgeo
    (z := (kernelScalarExtension G K).symm X) (by
      simpa only [coordinateBasis_baseChange_repr, LinearEquiv.apply_symm_apply] using hX)
  intro hnil
  apply hz
  have h := coordinateTensorEquiv_conj_adjointDifferentialFamily c
    ((kernelScalarExtension G K).symm X)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [← h] at hnil
  simpa only [RingEquiv.symm_apply_apply] using
    hnil.map (coordinateTensorEquiv (k := k) (K := K) d).conjRingEquiv.symm

set_option backward.isDefEq.respectTransparency true in
/-- The base change of `G` to an algebraic closure has affine structure morphism. -/
instance isAffineHom_baseChange_algebraicClosure :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k (AlgebraicClosure k))).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap k (AlgebraicClosure k)))
  infer_instance

set_option backward.isDefEq.respectTransparency true in
omit [LocallyOfFiniteType G.X.hom] in
/-- `HasNoncentralGeometricSemisimpleElement`, restated through `algebraBaseMap`. -/
theorem exists_isSemisimpleElement_of_hasNoncentralGeometricSemisimpleElement
    (hS : HasNoncentralGeometricSemisimpleElement G) :
    ∃ X : lieKernel ((GroupScheme.baseChange (algebraBaseMap k (AlgebraicClosure k))).obj G)
        (AlgebraicClosure k),
      IsSemisimpleElement ((GroupScheme.baseChange (algebraBaseMap k (AlgebraicClosure k))).obj G) X ∧
      elementCentralizerLie ((GroupScheme.baseChange (algebraBaseMap k (AlgebraicClosure k))).obj G)
        X ≠ ⊤ := by
  obtain ⟨X, hX, hne⟩ := hS
  exact ⟨X, hX, hne⟩

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency true in
/-- **The generic Lie element is not central.** If the base change of `G` to an algebraic
closure of `k` has a semisimple Lie element whose Lie centralizer is not everything, then the
adjoint differential of the generic Lie element, over the function field of `𝔸^d`, is
nonnilpotent. -/
theorem not_isNilpotent_tangentMatrix_genericLieElement
    (hS : HasNoncentralGeometricSemisimpleElement G) :
    ¬ IsNilpotent (Matrix.toLin' ((adjointRepresentation c).tangentMatrix
      (𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k))).functionField
      (genericLieElement c).toMul)) := by
  refine not_isNilpotent_tangentMatrix_of_algebraicIndependent c
    (L := AlgebraicClosure k) (exists_nonnilpotent_adjointFamilyBaseChange c
      (K := AlgebraicClosure k)
      (exists_isSemisimpleElement_of_hasNoncentralGeometricSemisimpleElement hS)) _ ?_
  rw [genericLieElement, LinearEquiv.apply_symm_apply]
  exact (algebraicIndependent_rationalFunctionFieldCoordinate k (ULift.{u} (Fin d))).comp
    ULift.up ULift.up_injective

end Langlands.GroupScheme.Lie
