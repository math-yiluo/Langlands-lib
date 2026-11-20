import Langlands.Automorphic.RankOneHeckeRegularAlgebraic
import Langlands.Automorphic.ConjugateContragredient
import Langlands.Automorphic.HeckeTwist.ContragredientTwist

/-!
# Conjugate self-duality of the automorphic `GL(1)` realization of a Hecke character

For a CM field `E` and a Hecke character `χ` with `χ ∘ c = χ⁻¹` on idele classes, the
`GL(1)` realization of `χ` is isomorphic to its contragredient composed with the CM involution:
the pairing `B(y, x) = φ(y) φ(x)`, where `φ` reads the scalar of a vector of the line, is
invariant under the conjugate-twisted finite, compact and Lie operators, because the
determinant scalars of `χ` at `g` and at `c(g)` are inverse to each other.
-/

noncomputable section

universe u uP

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.Global.CMConjugation
open Langlands.Global.AdelicFunctoriality NumberField

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RankOneHecke

variable {E : Type u} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/-- Conjugation is the pair of the infinite and finite conjugations. -/
theorem adelicConj_pair (a : InfiniteAdelicGL E n) (b : FiniteAdelicGL E n) :
    adelicConj E n (AdelicGL.pair E n a b) =
      AdelicGL.pair E n (infiniteConj E n a) (finiteConj E n b) := by
  apply Units.ext
  ext i j
  rfl

/-- For a conjugate-inverse Hecke character, the determinant character at the conjugate of an
adelic matrix is the inverse of its value at the matrix. -/
theorem adelicDeterminant_adelicConj {χ : HeckeCharacter E}
    (hχ : ∀ x, χ (ideleClassComplexConj x) = (χ x)⁻¹) (g : AdelicGL E n) :
    χ.adelicDeterminant n (adelicConj E n g) = (χ.adelicDeterminant n g)⁻¹ := by
  have hdet : AdelicGL.determinant E n (adelicConj E n g) =
      ideleEquiv (fieldConj E) (AdelicGL.determinant E n g) := by
    apply Units.ext
    change ((adeleEquiv (fieldConj E)).toRingHom.mapMatrix (g : Matrix (Fin n) (Fin n) _)).det =
      adeleEquiv (fieldConj E) ((g : Matrix (Fin n) (Fin n) _).det)
    exact (RingHom.map_det (adeleEquiv (fieldConj E)).toRingHom _).symm
  change χ.onIdeles (AdelicGL.determinant E n (adelicConj E n g)) =
    (χ.onIdeles (AdelicGL.determinant E n g))⁻¹
  rw [hdet]
  exact hχ (QuotientGroup.mk (AdelicGL.determinant E n g))

theorem adelicDeterminant_ofFinite_finiteConj {χ : HeckeCharacter E}
    (hχ : ∀ x, χ (ideleClassComplexConj x) = (χ x)⁻¹) (d : FiniteAdelicGL E n) :
    χ.adelicDeterminant n (AdelicGL.ofFinite E n (finiteConj E n d)) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite E n d))⁻¹ := by
  have h : AdelicGL.ofFinite E n (finiteConj E n d) = adelicConj E n (AdelicGL.ofFinite E n d) := by
    change AdelicGL.pair E n 1 (finiteConj E n d) = adelicConj E n (AdelicGL.pair E n 1 d)
    rw [adelicConj_pair, map_one]
  rw [h, adelicDeterminant_adelicConj hχ]

theorem adelicDeterminant_ofInfinite_infiniteConj {χ : HeckeCharacter E}
    (hχ : ∀ x, χ (ideleClassComplexConj x) = (χ x)⁻¹) (a : InfiniteAdelicGL E n) :
    χ.adelicDeterminant n (AdelicGL.ofInfinite E n (infiniteConj E n a)) =
      (χ.adelicDeterminant n (AdelicGL.ofInfinite E n a))⁻¹ := by
  have h : AdelicGL.ofInfinite E n (infiniteConj E n a) =
      adelicConj E n (AdelicGL.ofInfinite E n a) := by
    change AdelicGL.pair E n (infiniteConj E n a) 1 = adelicConj E n (AdelicGL.pair E n a 1)
    rw [adelicConj_pair, map_one]
  rw [h, adelicDeterminant_adelicConj hχ]

section Lie

open scoped Classical

/-- The entrywise conjugation of archimedean matrices, as a continuous real-linear map. -/
def matrixConj : ArchimedeanMatrix E n →L[ℝ] ArchimedeanMatrix E n :=
  LinearMap.toContinuousLinearMap ((mixedConj E).mapMatrix (m := Fin n)).toLinearEquiv.toLinearMap

omit [IsCMField E] in
theorem matrixConj_apply (M : ArchimedeanMatrix E n) (i j : Fin n) :
    matrixConj (E := E) (n := n) M i j = mixedConj E (M i j) := rfl

omit [IsCMField E] in
theorem matrixConj_one : matrixConj (E := E) (n := n) 1 = 1 := by
  change (mixedConj E).mapMatrix (1 : ArchimedeanMatrix E n) = 1
  exact map_one _

/-- For a conjugate-inverse Hecke character, the derivative at `1` of its archimedean
determinant character is odd under the CM involution of the Lie algebra. -/
theorem characterDifferential_lieConj {χ : HeckeCharacter E}
    (hχ : ∀ x, χ (ideleClassComplexConj x) = (χ x)⁻¹) (X : RealLieAlgebra E n) :
    characterDifferential (χ.infiniteDeterminantCharacter n)
        (χ.infiniteDeterminantCharacter_mem_smoothFunctions n) (lieConj E n X) +
      characterDifferential (χ.infiniteDeterminantCharacter n)
        (χ.infiniteDeterminantCharacter_mem_smoothFunctions n) X = 0 := by
  set f := characterFunction (χ.infiniteDeterminantCharacter n)
    (χ.infiniteDeterminantCharacter_mem_smoothFunctions n) with hf
  set Ec := coordinateExtension E n f with hEc
  have hD : ∀ Y : RealLieAlgebra E n, characterDifferential (χ.infiniteDeterminantCharacter n)
      (χ.infiniteDeterminantCharacter_mem_smoothFunctions n) Y =
        fderiv ℝ Ec 1 (realLieAlgebraToMatrix E n Y) := by
    intro Y
    change (smoothDifferential E n Y f).val 1 = _
    rw [smoothDifferential_apply, map_one, Units.val_one, one_mul]
  have hEc1 : Ec 1 = 1 := by
    have h := coordinateExtension_apply E n f 1
    rw [Units.val_one] at h
    rw [hEc, h, map_one]
    change ((χ.adelicDeterminant n (AdelicGL.ofInfinite E n 1) : ℂˣ) : ℂ) = 1
    rw [map_one, map_one, Units.val_one]
  have hdiff : DifferentiableAt ℝ Ec 1 := by
    have h := (coordinateExtension_contDiffAt E n f 1).differentiableAt (by simp)
    rwa [Units.val_one] at h
  have hconj : (fun M => Ec (matrixConj M) * Ec M) =ᶠ[nhds 1] fun _ => (1 : ℂ) := by
    filter_upwards [Units.isOpenEmbedding_val.isOpen_range.mem_nhds
      (show (1 : ArchimedeanMatrix E n) ∈
        Set.range (Units.val : ArchimedeanGL E n → ArchimedeanMatrix E n) from ⟨1, rfl⟩)]
      with M hM
    obtain ⟨h, rfl⟩ := hM
    set h' : ArchimedeanGL E n := Matrix.GeneralLinearGroup.map (mixedConj E).toRingEquiv.toRingHom h
    have hval : matrixConj (h : ArchimedeanMatrix E n) = (h' : ArchimedeanMatrix E n) :=
      Matrix.ext fun i j => rfl
    have hsymm : (archimedeanGLCoordinates E n).symm h' =
        infiniteConj E n ((archimedeanGLCoordinates E n).symm h) := by
      apply (archimedeanGLCoordinates E n).injective
      rw [ContinuousMulEquiv.apply_symm_apply]
      apply Units.ext
      refine Matrix.ext fun i j => ?_
      rw [coordinates_infiniteConj, ContinuousMulEquiv.apply_symm_apply]
      rfl
    change Ec (matrixConj (h : ArchimedeanMatrix E n)) * Ec (h : ArchimedeanMatrix E n) = 1
    rw [hEc, hval, coordinateExtension_apply, coordinateExtension_apply, hsymm]
    change ((χ.adelicDeterminant n (AdelicGL.ofInfinite E n
        (infiniteConj E n ((archimedeanGLCoordinates E n).symm h))) : ℂˣ) : ℂ) *
      ((χ.adelicDeterminant n (AdelicGL.ofInfinite E n
        ((archimedeanGLCoordinates E n).symm h)) : ℂˣ) : ℂ) = 1
    rw [adelicDeterminant_ofInfinite_infiniteConj hχ, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  have hcomp : HasFDerivAt (fun M => Ec (matrixConj M))
      ((fderiv ℝ Ec 1).comp (matrixConj (E := E) (n := n))) 1 := by
    have h1 : HasFDerivAt Ec (fderiv ℝ Ec 1) (matrixConj (E := E) (n := n) 1) := by
      rw [matrixConj_one]
      exact hdiff.hasFDerivAt
    exact h1.comp (1 : ArchimedeanMatrix E n) (matrixConj (E := E) (n := n)).hasFDerivAt
  have hprod : HasFDerivAt (fun M => Ec (matrixConj M) * Ec M)
      (Ec (matrixConj 1) • fderiv ℝ Ec 1 + Ec 1 • (fderiv ℝ Ec 1).comp matrixConj) 1 :=
    hcomp.mul hdiff.hasFDerivAt
  have hzero : fderiv ℝ (fun M => Ec (matrixConj M) * Ec M) 1 = 0 := by
    rw [hconj.fderiv_eq]
    exact fderiv_const_apply _
  rw [hprod.fderiv, matrixConj_one, hEc1] at hzero
  have hX := congrArg (fun T : ArchimedeanMatrix E n →L[ℝ] ℂ => T (realLieAlgebraToMatrix E n X))
    hzero
  simp only [one_smul, add_apply, ContinuousLinearMap.comp_apply, zero_apply] at hX
  rw [hD, hD]
  have hL : realLieAlgebraToMatrix E n (lieConj E n X) =
      matrixConj (realLieAlgebraToMatrix E n X) :=
    Matrix.ext fun i j => rfl
  rw [hL, add_comm]
  exact hX

end Lie

section Pairing

local instance rankOneCSDRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions E n) := Submodule.addCommGroup _
local instance rankOneCSDContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions E n) := Submodule.addCommGroup _
local instance rankOneCSDSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions E n) := Submodule.addCommGroup _
local instance rankOneCSDFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms E n) := Submodule.addCommGroup _
local instance rankOneCSDStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions E n) := Submodule.addCommGroup _
local instance rankOneCSDSpaceGroup {m : ℕ} (S : OperatorRealization E m) :
    AddCommGroup S.Space := Submodule.addCommGroup _

omit [IsCMField E] in
set_option maxHeartbeats 2000000 in
/-- Every functional on the constant line is smooth for the finite adelic group: the finite
action on constants is trivial. -/
theorem constant_isSmoothVector (l : Module.Dual ℂ (ConstantFunctions.realization E 1).Space) :
    IsSmoothVector (ConstantFunctions.realization E 1).finiteRepresentation.dual l := by
  refine ⟨⊤, (Representation.mem_invariants _ _).mpr fun g => ?_⟩
  apply LinearMap.ext
  intro y
  obtain ⟨c, rfl⟩ := (ConstantFunctions.scalarEquiv E 1).surjective y
  exact congrArg l (ConstantFunctions.finiteRepresentation_scalarEquiv E 1 _ c)

omit [IsCMField E] in
/-- Every functional on the constant line is finite for the compact group: the dual is
finite-dimensional. -/
theorem constant_isFiniteVector (l : Module.Dual ℂ (ConstantFunctions.realization E 1).Space) :
    FiniteVectors.IsFiniteVector (ConstantFunctions.realization E 1).compactRepresentation.dual l := by
  have hfd : FiniteDimensional ℂ (Module.Dual ℂ (ConstantFunctions.realization E 1).Space) :=
    LinearEquiv.finiteDimensional (ConstantFunctions.scalarEquiv E 1).dualMap.symm
  exact FiniteDimensional.finiteDimensional_submodule _

omit [IsCMField E] in
/-- Every functional on the constant line is contragredient. -/
theorem constant_isContragredientFunctional (l : Module.Dual ℂ (ConstantFunctions.realization E 1).Space) :
    (ConstantFunctions.realization E 1).IsContragredientFunctional l :=
  ⟨constant_isSmoothVector l, constant_isFiniteVector l⟩

variable (χ : HeckeCharacter E)

omit [IsCMField E] in
/-- Every functional on the `GL(1)` realization of `χ` is contragredient. -/
theorem twist_isContragredientFunctional
    (l : Module.Dual ℂ ((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).Space) :
    ((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).IsContragredientFunctional l := by
  have h := OperatorRealization.isContragredientFunctional_comp_heckeDeterminantTwistEquiv_symm χ
    (constant_isContragredientFunctional (l ∘ₗ
      ((ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ).toLinearEquiv.toLinearMap))
  have he : (l ∘ₗ ((ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ).toLinearEquiv.toLinearMap) ∘ₗ
      ((ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ).toLinearEquiv.symm.toLinearMap =
        l := by
    apply LinearMap.ext
    intro y
    exact congrArg l
      (((ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ).toLinearEquiv.apply_symm_apply y)
  rw [he] at h
  exact h

/-- The scalar of a vector of the `GL(1)` realization of `χ`. -/
def lineScalar :
    ((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).Space →ₗ[ℂ] ℂ :=
  (ConstantFunctions.scalarEquiv E 1).symm.toLinearMap ∘ₗ
    ((ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ).toLinearEquiv.symm.toLinearMap

/-- The basis vector `χ ∘ det` of the line. -/
def lineVector : ((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).Space :=
  (ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ (ConstantFunctions.scalarEquiv E 1 1)

omit [IsCMField E] in
theorem lineScalar_twist (c : ℂ) :
    lineScalar χ ((ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ
      (ConstantFunctions.scalarEquiv E 1 c)) = c := by
  change (ConstantFunctions.scalarEquiv E 1).symm
    (((ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ).toLinearEquiv.symm
      (((ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ).toLinearEquiv
        (ConstantFunctions.scalarEquiv E 1 c))) = c
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

omit [IsCMField E] in
theorem eq_twist_lineScalar
    (y : ((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).Space) :
    y = (ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ
      (ConstantFunctions.scalarEquiv E 1 (lineScalar χ y)) := by
  change y = ((ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ).toLinearEquiv
    ((ConstantFunctions.scalarEquiv E 1) ((ConstantFunctions.scalarEquiv E 1).symm
      (((ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ).toLinearEquiv.symm y)))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

omit [IsCMField E] in
set_option maxHeartbeats 2000000 in
theorem eq_lineScalar_smul
    (y : ((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).Space) :
    y = lineScalar χ y • lineVector χ := by
  have h1 : ConstantFunctions.scalarEquiv E 1 (lineScalar χ y) =
      lineScalar χ y • ConstantFunctions.scalarEquiv E 1 1 := by
    have h := (ConstantFunctions.scalarEquiv E 1).map_smul (lineScalar χ y) 1
    rwa [smul_eq_mul, mul_one] at h
  exact (eq_twist_lineScalar χ y).trans
    ((congrArg ((ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ) h1).trans
      (((ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ).map_smul _ _))

omit [IsCMField E] in
theorem lineScalar_lineVector : lineScalar χ (lineVector χ) = 1 :=
  lineScalar_twist χ 1

omit [IsCMField E] in
set_option maxHeartbeats 2000000 in
/-- The finite action on the line is multiplication by `χ(det d)`. -/
theorem lineScalar_finite (d : FiniteAdelicGL E 1)
    (y : ((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).Space) :
    lineScalar χ (((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).finiteRepresentation
      d y) = (χ.adelicDeterminant 1 (AdelicGL.ofFinite E 1 d) : ℂ) * lineScalar χ y := by
  obtain ⟨a, rfl⟩ : ∃ a, y = (ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ
      (ConstantFunctions.scalarEquiv E 1 a) := ⟨_, eq_twist_lineScalar χ y⟩
  rw [(ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv_finite χ d,
    ConstantFunctions.finiteRepresentation_scalarEquiv, LinearMap.map_smul_of_tower,
    lineScalar_twist, smul_eq_mul]

omit [IsCMField E] in
set_option maxHeartbeats 2000000 in
/-- The compact action on the line is multiplication by `χ(det k)`. -/
theorem lineScalar_compact (k : standardInfiniteCompact E 1)
    (y : ((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).Space) :
    lineScalar χ (((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).compactRepresentation
      k y) = (χ.adelicDeterminant 1 (AdelicGL.ofInfinite E 1 k.val) : ℂ) * lineScalar χ y := by
  obtain ⟨a, rfl⟩ : ∃ a, y = (ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ
      (ConstantFunctions.scalarEquiv E 1 a) := ⟨_, eq_twist_lineScalar χ y⟩
  rw [(ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv_compact χ k,
    ConstantFunctions.compactRepresentation_scalarEquiv, LinearMap.map_smul_of_tower,
    lineScalar_twist, smul_eq_mul]

omit [IsCMField E] in
set_option maxHeartbeats 2000000 in
/-- The real Lie action on the line is multiplication by the derivative of `χ ∘ det`. -/
theorem lineScalar_lie (X : RealLieAlgebra E 1)
    (y : ((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).Space) :
    lineScalar χ (((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).lieAction X y) =
      characterDifferential (χ.infiniteDeterminantCharacter 1)
        (χ.infiniteDeterminantCharacter_mem_smoothFunctions 1) X * lineScalar χ y := by
  obtain ⟨a, rfl⟩ : ∃ a, y = (ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ
      (ConstantFunctions.scalarEquiv E 1 a) := ⟨_, eq_twist_lineScalar χ y⟩
  have ha : heckeEnvelopingShift 1 χ (envelopingGenerator E 1 (complexify E 1 X)) =
      envelopingGenerator E 1 (complexify E 1 X) +
        algebraMap ℂ (EnvelopingAlgebra E 1) (characterDifferential
          (χ.infiniteDeterminantCharacter 1) (χ.infiniteDeterminantCharacter_mem_smoothFunctions 1) X) := by
    rw [heckeEnvelopingShift, characterShift, envelopingShift_generator, complexify_apply,
      complexCharacterDifferential_tmul, one_mul]
  have hzero : (ConstantFunctions.realization E 1).lieAction X (ConstantFunctions.scalarEquiv E 1 a) =
      0 := by
    change (ConstantFunctions.realization E 1).envelopingAction _ (ConstantFunctions.scalarEquiv E 1 a) = 0
    rw [ConstantFunctions.envelopingAction_scalarEquiv, augmentation_envelopingGenerator, zero_mul]
    exact (ConstantFunctions.scalarEquiv E 1).map_zero
  rw [OperatorRealization.lieAction_heckeDeterminantTwistEquiv _ χ X ha, hzero, zero_add,
    ContinuousLinearEquiv.map_smul, LinearMap.map_smul_of_tower, lineScalar_twist, smul_eq_mul]

/-- The pairing `B(y, x) = φ(y) φ(x)` on the line. -/
def linePairing :
    ((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).Space →ₗ[ℂ]
      ((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).Space →ₗ[ℂ] ℂ :=
  (LinearMap.mul ℂ ℂ).compl₁₂ (lineScalar χ) (lineScalar χ)

omit [IsCMField E] in
theorem linePairing_apply (y x : ((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).Space) :
    linePairing χ y x = lineScalar χ y * lineScalar χ x := rfl

set_option maxHeartbeats 2000000 in
theorem linePairing_finite (hχ : ∀ x, χ (ideleClassComplexConj x) = (χ x)⁻¹)
    (d : FiniteAdelicGL E 1)
    (y x : ((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).Space) :
    linePairing χ (((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).finiteRepresentation
        (finiteConj E 1 d) y)
      (((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).finiteRepresentation d x) =
      linePairing χ y x := by
  rw [linePairing_apply, linePairing_apply, lineScalar_finite, lineScalar_finite]
  have hu : ((χ.adelicDeterminant 1 (AdelicGL.ofFinite E 1 (finiteConj E 1 d)) : ℂˣ) : ℂ) *
      ((χ.adelicDeterminant 1 (AdelicGL.ofFinite E 1 d) : ℂˣ) : ℂ) = 1 := by
    rw [adelicDeterminant_ofFinite_finiteConj hχ, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  linear_combination (lineScalar χ y * lineScalar χ x) * hu

set_option maxHeartbeats 2000000 in
theorem linePairing_compact (hχ : ∀ x, χ (ideleClassComplexConj x) = (χ x)⁻¹)
    (k : standardInfiniteCompact E 1)
    (y x : ((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).Space) :
    linePairing χ (((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).compactRepresentation
        (compactConj E 1 k) y)
      (((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).compactRepresentation k x) =
      linePairing χ y x := by
  rw [linePairing_apply, linePairing_apply, lineScalar_compact, lineScalar_compact]
  have hu : ((χ.adelicDeterminant 1 (AdelicGL.ofInfinite E 1 (compactConj E 1 k).val) : ℂˣ) : ℂ) *
      ((χ.adelicDeterminant 1 (AdelicGL.ofInfinite E 1 k.val) : ℂˣ) : ℂ) = 1 := by
    rw [compactConj_val, adelicDeterminant_ofInfinite_infiniteConj hχ, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  linear_combination (lineScalar χ y * lineScalar χ x) * hu

set_option maxHeartbeats 2000000 in
theorem linePairing_lie (hχ : ∀ x, χ (ideleClassComplexConj x) = (χ x)⁻¹)
    (X : RealLieAlgebra E 1)
    (y x : ((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).Space) :
    linePairing χ (((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).lieAction
        (lieConj E 1 X) y) x +
      linePairing χ y (((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).lieAction X x) =
      0 := by
  rw [linePairing_apply, linePairing_apply, lineScalar_lie, lineScalar_lie]
  linear_combination (lineScalar χ y * lineScalar χ x) * characterDifferential_lieConj hχ X

omit [IsCMField E] in
set_option maxHeartbeats 2000000 in
theorem linePairing_flip_injective : Function.Injective (linePairing χ).flip := by
  intro x₁ x₂ h
  have h1 := LinearMap.congr_fun h (lineVector χ)
  change linePairing χ (lineVector χ) x₁ = linePairing χ (lineVector χ) x₂ at h1
  rw [linePairing_apply, linePairing_apply, lineScalar_lineVector, one_mul, one_mul] at h1
  rw [eq_twist_lineScalar χ x₁, eq_twist_lineScalar χ x₂, h1]

omit [IsCMField E] in
set_option maxHeartbeats 2000000 in
theorem linePairing_flip_surjective
    (l : Module.Dual ℂ ((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).Space) :
    ∃ x, (linePairing χ).flip x = l := by
  refine ⟨(ConstantFunctions.realization E 1).heckeDeterminantTwistEquiv χ
    (ConstantFunctions.scalarEquiv E 1 (l (lineVector χ))), LinearMap.ext fun y => ?_⟩
  change linePairing χ y _ = l y
  rw [linePairing_apply, lineScalar_twist]
  conv_rhs => rw [eq_lineScalar_smul χ y]
  rw [LinearMap.map_smul_of_tower, smul_eq_mul]

set_option maxHeartbeats 2000000 in
/-- **Conjugate self-duality of the `GL(1)` line.** If `χ ∘ c = χ⁻¹` on idele classes, the line
`χ ∘ det` is isomorphic to its contragredient composed with the CM involution. -/
theorem twist_isConjugateSelfDual (hχ : ∀ x, χ (ideleClassComplexConj x) = (χ x)⁻¹) :
    ((ConstantFunctions.realization E 1).heckeDeterminantTwist χ).IsConjugateSelfDual :=
  ⟨linePairing χ, ⟨linePairing_finite χ hχ, linePairing_compact χ hχ, linePairing_lie χ hχ⟩,
    fun _ => twist_isContragredientFunctional χ _, linePairing_flip_injective χ,
    fun l _ => linePairing_flip_surjective χ l⟩

end Pairing

/-- The automorphic `GL(1)` realization of a conjugate-inverse Hecke character of a CM field is
conjugate self-dual. -/
theorem cuspidal_isConjugateSelfDual [CompactSpace (AdeleQuotient E)] (χ : HeckeCharacter E)
    (hχ : ∀ x, χ (ideleClassComplexConj x) = (χ x)⁻¹) :
    (cuspidal χ).isoClass.IsConjugateSelfDual :=
  (CuspidalOperatorRealization.isoClass_isConjugateSelfDual_iff _).mpr
    (twist_isConjugateSelfDual χ hχ)

end RankOneHecke

end Langlands.Automorphic
