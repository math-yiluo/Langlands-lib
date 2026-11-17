import Langlands.Global.RankinSelberg.ArchimedeanPlaces
import Langlands.Global.RankinSelberg.UnequalAnalyticProof
import Langlands.Automorphic.IrreducibleCentralCharacterProof
import Langlands.Automorphic.CuspidalUnitaryForm
import Langlands.Automorphic.PlaceLieAction
import Langlands.LocalFactor.ArchimedeanAttachment

/-! # Rank-one automorphic realizations at a real place

For `GL₁` the whole automorphic operator algebra is commutative: `1 × 1` matrices commute,
so the finite and compact groups are commutative, the adjoint action is trivial and the
enveloping algebra is commutative. By Schur's lemma every compact translation and every
enveloping operator acts on an irreducible realization by a scalar. At a real place `v` the
Lie operator of `1 ∈ 𝔤𝔩₁(ℝ)` and the compact element `-1 ∈ O(1)` therefore act by scalars `λ`
and `ε`, and the archimedean restriction `g ↦ φ(ι_v(g) a)` of a realized vector `φ` is
`φ(a) · ε^[g < 0] · |g|^λ`. See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealRankZero

open Langlands.Automorphic Langlands.Global.ArchimedeanGL

/-! ### `1 × 1` matrices commute -/

theorem matrix_fin_one_mul_comm {R : Type*} [CommSemiring R]
    (A B : Matrix (Fin 1) (Fin 1) R) : A * B = B * A := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem gl_fin_one_mul_comm {R : Type*} [CommRing R]
    (g h : Matrix.GeneralLinearGroup (Fin 1) R) : g * h = h * g :=
  Units.ext (matrix_fin_one_mul_comm _ _)

variable {F : Type u} [Field F]

/-! ### The adjoint action and the enveloping algebra of `GL₁` -/

theorem realLieConjugation_rankOne (g : InfiniteAdelicGL F 1) (X : RealLieAlgebra F 1) :
    realLieConjugation F 1 g X = X := by
  apply (realLieAlgebraToMatrix F 1).injective
  rw [realLieAlgebraToMatrix_realLieConjugation,
    matrix_fin_one_mul_comm (archimedeanGLCoordinates F 1 g).val, mul_assoc,
    ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, mul_one]

theorem complexLieConjugation_rankOne (g : InfiniteAdelicGL F 1) (X : ComplexLieAlgebra F 1) :
    complexLieConjugation F 1 g X = X := by
  induction X using TensorProduct.inductionOn with
  | tmul z Y => rw [complexLieConjugation_tmul, realLieConjugation_rankOne]
  | add X Y hX hY => rw [map_add, hX, hY]

attribute [local instance 100] LieRing.ofAssociativeRing in
theorem envelopingConjugation_rankOne (g : InfiniteAdelicGL F 1) (a : EnvelopingAlgebra F 1) :
    envelopingConjugation F 1 g a = a := by
  have h : (envelopingConjugation F 1 g).toAlgHom = AlgHom.id ℂ (EnvelopingAlgebra F 1) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro X
    change envelopingConjugation F 1 g (envelopingGenerator F 1 X) = envelopingGenerator F 1 X
    rw [envelopingConjugation_generator, complexLieConjugation_rankOne]
  exact AlgHom.congr_fun h a

theorem realLieAlgebra_lie_rankOne (X Y : RealLieAlgebra F 1) : ⁅X, Y⁆ = 0 := by
  apply (realLieAlgebraToMatrix F 1).injective
  rw [realLieAlgebraToMatrix_lie, matrix_fin_one_mul_comm (realLieAlgebraToMatrix F 1 X),
    sub_self, map_zero]

theorem complexLieAlgebra_lie_rankOne (X Y : ComplexLieAlgebra F 1) : ⁅X, Y⁆ = 0 := by
  induction X using TensorProduct.inductionOn with
  | tmul z X' =>
    induction Y using TensorProduct.inductionOn with
    | tmul w Y' =>
      rw [complexLieAlgebra_lie_tmul, realLieAlgebra_lie_rankOne, TensorProduct.tmul_zero]
    | add Y₁ Y₂ h₁ h₂ =>
      exact (lie_add (L := ComplexLieAlgebra F 1) (M := ComplexLieAlgebra F 1) _ Y₁ Y₂).trans
        (by rw [h₁, h₂, add_zero])
  | add X₁ X₂ h₁ h₂ =>
    exact (add_lie (L := ComplexLieAlgebra F 1) (M := ComplexLieAlgebra F 1) X₁ X₂ Y).trans
      (by rw [h₁, h₂, add_zero])

/-- The enveloping algebra of `GL₁` is commutative. -/
theorem envelopingAlgebra_mul_comm_rankOne (a b : EnvelopingAlgebra F 1) : a * b = b * a := by
  have hgen : ∀ X : ComplexLieAlgebra F 1,
      envelopingGenerator F 1 X ∈ Subalgebra.center ℂ (EnvelopingAlgebra F 1) := by
    intro X
    let S := Subalgebra.centralizer ℂ {envelopingGenerator F 1 X}
    have hY (Y : ComplexLieAlgebra F 1) : envelopingGenerator F 1 Y ∈ S := by
      apply (Subalgebra.mem_centralizer_iff ℂ).mpr
      intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      have h := envelopingGenerator_lie F 1 X Y
      rw [complexLieAlgebra_lie_rankOne, map_zero] at h
      exact (sub_eq_zero.mp h.symm)
    have hle : Algebra.adjoin ℂ (Set.range (envelopingGenerator F 1)) ≤ S := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨Y, rfl⟩
      exact hY Y
    rw [Subalgebra.mem_center_iff]
    intro c
    have hc : c ∈ Algebra.adjoin ℂ (Set.range (envelopingGenerator F 1)) := by
      change c ∈ Algebra.adjoin ℂ
        (Set.range (UniversalEnvelopingAlgebra.ι ℂ :
          ComplexLieAlgebra F 1 → EnvelopingAlgebra F 1))
      rw [Langlands.Algebra.LieCasimir.enveloping_adjoin_range]
      trivial
    exact ((Subalgebra.mem_centralizer_iff ℂ).mp (hle hc) _ (Set.mem_singleton _)).symm
  have hle : Algebra.adjoin ℂ (Set.range (envelopingGenerator F 1)) ≤
      Subalgebra.center ℂ (EnvelopingAlgebra F 1) := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨Y, rfl⟩
    exact hgen Y
  have ha : a ∈ Algebra.adjoin ℂ (Set.range (envelopingGenerator F 1)) := by
    change a ∈ Algebra.adjoin ℂ
      (Set.range (UniversalEnvelopingAlgebra.ι ℂ :
        ComplexLieAlgebra F 1 → EnvelopingAlgebra F 1))
    rw [Langlands.Algebra.LieCasimir.enveloping_adjoin_range]
    trivial
  exact ((Subalgebra.mem_center_iff).mp (hle ha) b).symm

/-! ### Schur scalars on an irreducible rank-one realization -/

section Schur

variable [NumberField F]

local instance realRankZeroRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F 1) :=
  Submodule.addCommGroup _
local instance realRankZeroContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F 1) :=
  Submodule.addCommGroup _
local instance realRankZeroSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F 1) :=
  Submodule.addCommGroup _
local instance realRankZeroFormsAddCommGroup : AddCommGroup (AutomorphicForms F 1) :=
  Submodule.addCommGroup _
local instance realRankZeroStableAddCommGroup : AddCommGroup (StableAutomorphicFunctions F 1) :=
  Submodule.addCommGroup _
local instance realRankZeroRealizationAddCommGroup (S : OperatorRealization F 1) :
    AddCommGroup S.Space := Submodule.addCommGroup _

theorem compactRepresentation_commute_rankOne (S : OperatorRealization F 1)
    (k k' : standardInfiniteCompact F 1) (f : S.Space) :
    S.compactRepresentation k (S.compactRepresentation k' f) =
      S.compactRepresentation k' (S.compactRepresentation k f) := by
  have hkk : k * k' = k' * k := Subtype.ext (gl_fin_one_mul_comm k.val k'.val)
  calc S.compactRepresentation k (S.compactRepresentation k' f)
      = S.compactRepresentation (k * k') f :=
        (LinearMap.congr_fun (map_mul S.compactRepresentation k k') f).symm
    _ = S.compactRepresentation (k' * k) f :=
        congrArg (fun y => S.compactRepresentation y f) hkk
    _ = S.compactRepresentation k' (S.compactRepresentation k f) :=
        LinearMap.congr_fun (map_mul S.compactRepresentation k' k) f

theorem compactRepresentation_envelopingAction_rankOne (S : OperatorRealization F 1)
    (k : standardInfiniteCompact F 1) (a : EnvelopingAlgebra F 1) (f : S.Space) :
    S.compactRepresentation k (S.envelopingAction a f) =
      S.envelopingAction a (S.compactRepresentation k f) := by
  exact (S.compactRepresentation_envelopingAction k a f).trans
    (congrArg (fun b => S.envelopingAction b (S.compactRepresentation k f))
      (envelopingConjugation_rankOne k.val a))

theorem envelopingAction_commute_rankOne (S : OperatorRealization F 1)
    (a b : EnvelopingAlgebra F 1) (f : S.Space) :
    S.envelopingAction a (S.envelopingAction b f) =
      S.envelopingAction b (S.envelopingAction a f) := by
  calc S.envelopingAction a (S.envelopingAction b f)
      = S.envelopingAction (a * b) f :=
        (LinearMap.congr_fun (map_mul S.envelopingAction a b) f).symm
    _ = S.envelopingAction (b * a) f :=
        congrArg (fun y => S.envelopingAction y f) (envelopingAlgebra_mul_comm_rankOne a b)
    _ = S.envelopingAction b (S.envelopingAction a f) :=
        LinearMap.congr_fun (map_mul S.envelopingAction b a) f

/-- On an irreducible rank-one realization every compact translation is a scalar. -/
theorem exists_compactRepresentation_eq_smul (S : OperatorRealization F 1)
    (hS : S.IsIrreducible) (k : standardInfiniteCompact F 1) :
    ∃ c : ℂ, ∀ f : S.Space, S.compactRepresentation k f = c • f := by
  refine S.exists_eq_smul_of_commute hS (S.compactRepresentation k)
    (S.commute_representation_of_commute _ ?_ ?_ ?_)
  · intro d f
    exact (S.finiteRepresentation_compactRepresentation d k f).symm
  · intro k' f
    exact compactRepresentation_commute_rankOne S k k' f
  · intro a f
    exact compactRepresentation_envelopingAction_rankOne S k a f

/-- On an irreducible rank-one realization every enveloping operator is a scalar. -/
theorem exists_envelopingAction_eq_smul (S : OperatorRealization F 1)
    (hS : S.IsIrreducible) (a : EnvelopingAlgebra F 1) :
    ∃ c : ℂ, ∀ f : S.Space, S.envelopingAction a f = c • f := by
  refine S.exists_eq_smul_of_commute hS (S.envelopingAction a)
    (S.commute_representation_of_commute _ ?_ ?_ ?_)
  · intro d f
    exact (S.finiteRepresentation_envelopingAction d a f).symm
  · intro k f
    exact (compactRepresentation_envelopingAction_rankOne S k a f).symm
  · intro b f
    exact envelopingAction_commute_rankOne S a b f

end Schur

/-! ### The rank-one Whittaker function is the cusp function -/

section Whittaker

local instance realRankZeroSchemeAffine (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance realRankZeroSchemeSmooth (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable [NumberField F]

/-- `N₁` is trivial: every adelic point of the upper unitriangular subgroup functor of `GL₁`
is the identity. -/
theorem upperUnipotent_one_adelicPoints_eq_one
    (z : AdelicSubgroupPoints.adelicPoints F
      (Scheme F 1) (upperUnipotent F 1)) :
    z = 1 := by
  obtain ⟨z, hz⟩ := z
  apply Subtype.ext
  change z = 1
  have h := (GroupScheme.GeneralLinear.mem_blockUnipotent (upperUnipotentWeight 1)).mp hz
  apply (GroupScheme.GeneralLinear.pointsEquiv _ _ _).injective
  rw [map_one]
  ext i j
  fin_cases i
  fin_cases j
  exact h 0 0 le_rfl

/-- For `GL₁` the global Whittaker coefficient of a cusp form is the form itself: the
quotient `N₁(F) \ N₁(𝔸)` is a point of mass one and the generic character is trivial. -/
theorem cuspWhittaker_rankZero [CompactSpace (AdeleQuotient F)]
    (T : CuspidalOperatorRealization F 0) (ψ : AddChar (Adeles F) ℂ) (x : T.Space) :
    cuspWhittaker F T ψ x = cuspFunction F T x := by
  funext g
  have hsub : Subsingleton (AdelicSubgroupPoints.adelicPoints F
      (Scheme F 1) (upperUnipotent F 1)) :=
    ⟨fun a b => (upperUnipotent_one_adelicPoints_eq_one a).trans
      (upperUnipotent_one_adelicPoints_eq_one b).symm⟩
  have hq : Subsingleton (AdelicSubgroupPoints.RationalQuotient F
      (Scheme F 1) (upperUnipotent F 1)) :=
    ⟨fun a b => Quotient.inductionOn₂ a b fun y z => congrArg _ (Subsingleton.elim y z)⟩
  have := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F
      (Scheme F 1) (upperUnipotent F 1)
  unfold cuspWhittaker generalLinearWhittakerFunction subgroupCharacterCoefficient
  have hone : ∀ q : AdelicSubgroupPoints.RationalQuotient F
      (Scheme F 1) (upperUnipotent F 1),
      Quotient.out q = 1 := fun q => upperUnipotent_one_adelicPoints_eq_one _
  simp only [hone, OneMemClass.coe_one, one_mul, genericCharacter, Finset.univ_eq_empty,
    Finset.sum_empty, AddChar.map_zero_eq_one, map_one, mul_one, integral_const, probReal_univ,
    one_smul]

end Whittaker

/-! ### Coordinates at a real place -/

section Coordinates

open scoped Classical Matrix.Norms.Operator

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}

variable (F)

/-- Archimedean invertible matrices are determined by their matrices at all infinite
places. -/
theorem archimedeanGL_ext {n : ℕ} {g h : ArchimedeanGL F n}
    (hr : ∀ w : RP, ArchimedeanGL.realMatrix F n g w = ArchimedeanGL.realMatrix F n h w)
    (hc : ∀ w : CP, ArchimedeanGL.complexMatrix F n g w = ArchimedeanGL.complexMatrix F n h w) :
    g = h :=
  Units.ext <| Matrix.ext fun i j => Prod.ext (funext fun w => congrFun (congrFun (hr w) i) j)
    (funext fun w => congrFun (congrFun (hc w) i) j)

theorem realMatrix_realPlaceGL (n : ℕ) (v w : RP) (g : Matrix.GeneralLinearGroup (Fin n) ℝ) :
    ArchimedeanGL.realMatrix F n (realPlaceGL F n v g) w =
      ((Pi.mulSingle v g : RP → Matrix.GeneralLinearGroup (Fin n) ℝ) w :
        Matrix (Fin n) (Fin n) ℝ) := rfl

theorem complexMatrix_realPlaceGL (n : ℕ) (v : RP) (w : CP)
    (g : Matrix.GeneralLinearGroup (Fin n) ℝ) :
    ArchimedeanGL.complexMatrix F n (realPlaceGL F n v g) w = 1 := rfl

/-- The orthogonal element `k` at the real place `v` of the standard compact subgroup is the
completion-coordinate form of `realPlaceGL v k`. -/
theorem realPlaceCompactInclusion_val (n : ℕ) (v : RP) (k : Matrix.unitaryGroup (Fin n) ℝ) :
    ((realPlaceCompactInclusion F n v k : standardInfiniteCompact F n) :
        Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing F)) =
      (archimedeanGLCoordinates F n).symm (realPlaceGL F n v (Unitary.toUnits k)) := by
  apply (archimedeanGLCoordinates F n).injective
  rw [ContinuousMulEquiv.apply_symm_apply]
  apply archimedeanGL_ext F
  · intro w
    rw [realMatrix_realPlaceCompactInclusion, realMatrix_realPlaceGL]
    by_cases hw : w = v
    · subst hw
      simp only [Pi.mulSingle_eq_same]
      rfl
    · simp only [Pi.mulSingle_eq_of_ne hw]
      rfl
  · intro w
    rw [complexMatrix_realPlaceCompactInclusion, complexMatrix_realPlaceGL]

/-- Nonzero real scalars as invertible `1 × 1` matrices. -/
def scalarUnit : ℝˣ →* Matrix.GeneralLinearGroup (Fin 1) ℝ :=
  Units.map (algebraMap ℝ (Matrix (Fin 1) (Fin 1) ℝ)).toMonoidHom

theorem scalarUnit_val (t : ℝˣ) :
    ((scalarUnit t : Matrix.GeneralLinearGroup (Fin 1) ℝ) : Matrix (Fin 1) (Fin 1) ℝ) =
      algebraMap ℝ (Matrix (Fin 1) (Fin 1) ℝ) t := rfl

/-- Every invertible `1 × 1` real matrix is the scalar of its entry. -/
theorem scalarUnit_entry (g : Matrix.GeneralLinearGroup (Fin 1) ℝ) :
    scalarUnit (Units.mk0 ((g : Matrix (Fin 1) (Fin 1) ℝ) 0 0)
      (fun h0 => by
        have h := congrFun (congrFun g.mul_inv 0) 0
        simp [Matrix.mul_apply, h0] at h)) = g := by
  apply Units.ext
  rw [scalarUnit_val]
  ext i j
  fin_cases i
  fin_cases j
  rw [Matrix.algebraMap_matrix_apply]
  simp

/-- At the real place `v`, the one-parameter subgroup of `1 ∈ 𝔤𝔩₁(ℝ)` is `exp u` at `v`. -/
theorem oneParameter_realPlaceLieInclusion_one [NumberField F] (v : RP) (u : ℝ) :
    oneParameter F 1 (realPlaceLieInclusion F 1 v 1) u =
      realPlaceGL F 1 v (scalarUnit (Units.mk0 (Real.exp u) (Real.exp_pos u).ne')) := by
  apply archimedeanGL_ext F
  · intro w
    rw [realMatrix_realPlaceGL]
    have h : ArchimedeanGL.realMatrix F 1 (oneParameter F 1 (realPlaceLieInclusion F 1 v 1) u) w =
        (realPlaceScalarProjection F w).mapMatrix
          (NormedSpace.exp (u • realLieAlgebraToMatrix F 1 (realPlaceLieInclusion F 1 v 1))) :=
      rfl
    have hc : Continuous ((realPlaceScalarProjection F w).mapMatrix :
        ArchimedeanMatrix F 1 → Matrix (Fin 1) (Fin 1) ℝ) :=
      continuous_id.matrix_map ((continuous_apply w).comp continuous_fst)
    rw [h, NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (𝔸 := ArchimedeanMatrix F 1)
      (𝔹 := Matrix (Fin 1) (Fin 1) ℝ) _ hc _
      ((NormedSpace.expSeries_radius_eq_top ℝ (ArchimedeanMatrix F 1)).symm ▸ edist_lt_top _ _), map_smul]
    have hp : (realPlaceScalarProjection F w).mapMatrix
        (realLieAlgebraToMatrix F 1 (realPlaceLieInclusion F 1 v 1)) =
          (Pi.single v (1 : Matrix (Fin 1) (Fin 1) ℝ) : RP → Matrix (Fin 1) (Fin 1) ℝ) w :=
      realProjection_realInclusion F 1 w v 1
    rw [hp]
    by_cases hw : w = v
    · subst hw
      rw [Pi.single_eq_same, Pi.mulSingle_eq_same, scalarUnit_val, ← Algebra.algebraMap_eq_smul_one,
        ← NormedSpace.algebraMap_exp_comm, ← Real.exp_eq_exp_ℝ]
      rfl
    · rw [Pi.single_eq_of_ne hw, Pi.mulSingle_eq_of_ne hw, smul_zero, NormedSpace.exp_zero,
        Units.val_one]
  · intro w
    rw [complexMatrix_realPlaceGL]
    have h : ArchimedeanGL.complexMatrix F 1
        (oneParameter F 1 (realPlaceLieInclusion F 1 v 1) u) w =
        (complexPlaceScalarProjection F w).mapMatrix
          (NormedSpace.exp (u • realLieAlgebraToMatrix F 1 (realPlaceLieInclusion F 1 v 1))) :=
      rfl
    have hc : Continuous ((complexPlaceScalarProjection F w).mapMatrix :
        ArchimedeanMatrix F 1 → Matrix (Fin 1) (Fin 1) ℂ) :=
      continuous_id.matrix_map ((continuous_apply w).comp continuous_snd)
    rw [h, NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (𝔸 := ArchimedeanMatrix F 1)
      (𝔹 := Matrix (Fin 1) (Fin 1) ℂ) _ hc _
      ((NormedSpace.expSeries_radius_eq_top ℝ (ArchimedeanMatrix F 1)).symm ▸ edist_lt_top _ _), map_smul]
    have hp : (complexPlaceScalarProjection F w).mapMatrix
        (realLieAlgebraToMatrix F 1 (realPlaceLieInclusion F 1 v 1)) = 0 :=
      complexProjection_realInclusion F 1 w v 1
    rw [hp, smul_zero, NormedSpace.exp_zero]

end Coordinates

/-! ### A linear differential equation -/

/-- A function `h : ℝ → ℂ` with `h' = m h` is `h(u) = exp(m u) h(0)`. -/
theorem eq_exp_mul_of_hasDerivAt {h : ℝ → ℂ} {m : ℂ}
    (hh : ∀ u, HasDerivAt h (m * h u) u) (u : ℝ) :
    h u = Complex.exp (m * u) * h 0 := by
  let k : ℝ → ℂ := fun t => Complex.exp (-(m * t)) * h t
  have hk : ∀ t, HasDerivAt k 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -(m * (t : ℂ))) (-m) t := by
      have h0 := ((hasDerivAt_id t).ofReal_comp.const_mul m).neg
      convert h0 using 1
      · funext y
        simp
      · simp
    convert h1.cexp.mul (hh t) using 1
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t => (hk t).differentiableAt)
    (fun t => (hk t).deriv) u 0
  simp only [k, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul] at hconst
  calc h u = Complex.exp (m * u) * (Complex.exp (-(m * u)) * h u) := by
        rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
    _ = _ := by rw [hconst]

/-! ### The character of an irreducible rank-one realization at a real place -/

section Place

open scoped TensorProduct
open Langlands.LocalFactor.Archimedean

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}

/-- The orthogonal element `-1 ∈ O(1)`. -/
def minusOneOrthogonal : Matrix.unitaryGroup (Fin 1) ℝ :=
  ⟨-1, by rw [Matrix.mem_unitaryGroup_iff]; simp⟩

theorem toUnits_minusOneOrthogonal :
    Unitary.toUnits minusOneOrthogonal = scalarUnit (-1) := by
  apply Units.ext
  rw [Unitary.val_toUnits_apply, scalarUnit_val]
  simp [minusOneOrthogonal]

theorem determinant_scalarUnit (t : ℝˣ) : GeneralLinear.determinant (scalarUnit t) = t := by
  apply Units.ext
  change (algebraMap ℝ (Matrix (Fin 1) (Fin 1) ℝ) t).det = t
  rw [Matrix.det_fin_one, Matrix.algebraMap_matrix_apply]
  simp

variable [NumberField F]

local instance realRankZeroPlaceRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F 1) :=
  Submodule.addCommGroup _
local instance realRankZeroPlaceContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F 1) :=
  Submodule.addCommGroup _
local instance realRankZeroPlaceSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F 1) :=
  Submodule.addCommGroup _
local instance realRankZeroPlaceFormsAddCommGroup : AddCommGroup (AutomorphicForms F 1) :=
  Submodule.addCommGroup _
local instance realRankZeroPlaceStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F 1) :=
  Submodule.addCommGroup _
local instance realRankZeroPlaceRealizationAddCommGroup (S : OperatorRealization F 1) :
    AddCommGroup S.Space := Submodule.addCommGroup _

variable (F) in
/-- The adelic point `ι_v(g)` of `g ∈ GL₁(ℝ)` at the real place `v`, as a homomorphism. -/
def realPlaceAdelic (v : RP) : Matrix.GeneralLinearGroup (Fin 1) ℝ →* AdelicGL F 1 :=
  (AdelicGL.ofInfinite F 1).toMonoidHom.comp
    ((archimedeanGLCoordinates F 1).symm.toMulEquiv.toMonoidHom.comp (realPlaceGL F 1 v))

theorem evaluate_smul (S : OperatorRealization F 1) (c : ℂ) (f : S.Space) (y : AdelicGL F 1) :
    ContinuousRationalFunctions.evaluate F 1 (S.toContinuous (c • f)) y =
      c * ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f) y := by
  rw [map_smul]
  rfl

/-- Right translation by `ι_v(g)` multiplies realized vectors by `χ(g)`, once it does so for
`g = -1` and for the Lie operator of `1 ∈ 𝔤𝔩₁(ℝ)`. -/
theorem evaluate_mul_realPlaceAdelic (S : OperatorRealization F 1) (v : RP)
    (c : RealCharacterData)
    (hε : ∀ f : S.Space, S.realPlaceCompactRepresentation v minusOneOrthogonal f =
      ((c.character (-1) : ℂˣ) : ℂ) • f)
    (hμ : ∀ f : S.Space, S.realPlaceLieAction v ((1 : ℂ) ⊗ₜ[ℝ] (1 : Matrix (Fin 1) (Fin 1) ℝ)) f =
      c.exponent • f)
    (g : Matrix.GeneralLinearGroup (Fin 1) ℝ) (f : S.Space) (y : AdelicGL F 1) :
    ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f) (y * realPlaceAdelic F v g) =
      ((c.character (GeneralLinear.determinant g) : ℂˣ) : ℂ) *
        ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f) y := by
  let P : Matrix.GeneralLinearGroup (Fin 1) ℝ → Prop := fun g => ∀ (f : S.Space) (y : AdelicGL F 1),
    ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f) (y * realPlaceAdelic F v g) =
      ((c.character (GeneralLinear.determinant g) : ℂˣ) : ℂ) *
        ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f) y
  have hmul : ∀ g h, P g → P h → P (g * h) := by
    intro g h hg hh f y
    have hy : y * realPlaceAdelic F v (g * h) = (y * realPlaceAdelic F v g) * realPlaceAdelic F v h :=
      by rw [map_mul, mul_assoc]
    have hχ : ((c.character (GeneralLinear.determinant (g * h)) : ℂˣ) : ℂ) =
        ((c.character (GeneralLinear.determinant h) : ℂˣ) : ℂ) *
          ((c.character (GeneralLinear.determinant g) : ℂˣ) : ℂ) := by
      rw [map_mul, map_mul, Units.val_mul, mul_comm]
    calc ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f)
          (y * realPlaceAdelic F v (g * h))
        = ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f)
          ((y * realPlaceAdelic F v g) * realPlaceAdelic F v h) :=
          congrArg (ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f)) hy
      _ = ((c.character (GeneralLinear.determinant h) : ℂˣ) : ℂ) *
          ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f)
            (y * realPlaceAdelic F v g) := hh f _
      _ = ((c.character (GeneralLinear.determinant h) : ℂˣ) : ℂ) *
          (((c.character (GeneralLinear.determinant g) : ℂˣ) : ℂ) *
            ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f) y) := by rw [hg f y]
      _ = _ := by rw [hχ, mul_assoc]
  have hneg : P (scalarUnit (-1)) := by
    intro f y
    have hι : realPlaceAdelic F v (scalarUnit (-1)) =
        AdelicGL.ofInfinite F 1 (realPlaceCompactInclusion F 1 v minusOneOrthogonal).val := by
      rw [realPlaceCompactInclusion_val, toUnits_minusOneOrthogonal]
      rfl
    have hdet : ((c.character (GeneralLinear.determinant (scalarUnit (-1))) : ℂˣ) : ℂ) =
        ((c.character (-1) : ℂˣ) : ℂ) := by rw [determinant_scalarUnit]
    calc ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f)
          (y * realPlaceAdelic F v (scalarUnit (-1)))
        = ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f)
          (y * AdelicGL.ofInfinite F 1 (realPlaceCompactInclusion F 1 v minusOneOrthogonal).val) :=
          congrArg (fun z => ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f) (y * z)) hι
      _ = ContinuousRationalFunctions.evaluate F 1
            (S.toContinuous (S.realPlaceCompactRepresentation v minusOneOrthogonal f)) y :=
          (S.evaluate_realPlaceCompactRepresentation v minusOneOrthogonal f y).symm
      _ = ContinuousRationalFunctions.evaluate F 1
            (S.toContinuous (((c.character (-1) : ℂˣ) : ℂ) • f)) y :=
          congrArg (fun z => ContinuousRationalFunctions.evaluate F 1 (S.toContinuous z) y) (hε f)
      _ = ((c.character (-1) : ℂˣ) : ℂ) *
          ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f) y := evaluate_smul S _ f y
      _ = _ := congrArg (· * ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f) y) hdet.symm
  have hexp : ∀ u : ℝ, P (scalarUnit (Units.mk0 (Real.exp u) (Real.exp_pos u).ne')) := by
    intro u f y
    let X := realPlaceLieInclusion F 1 v 1
    have hι : ∀ t : ℝ, realPlaceAdelic F v (scalarUnit (Units.mk0 (Real.exp t) (Real.exp_pos t).ne')) =
        AdelicGL.ofInfinite F 1 (infiniteOneParameter F 1 X t) := by
      intro t
      rw [infiniteOneParameter, oneParameter_realPlaceLieInclusion_one]
      rfl
    have hlie : ∀ z : S.Space, S.lieOperator X z = c.exponent • z := hμ
    let h : ℝ → ℂ := fun t => ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f)
      (y * AdelicGL.ofInfinite F 1 (infiniteOneParameter F 1 X t))
    have hh : ∀ t, HasDerivAt h (c.exponent * h t) t := by
      intro t
      have hd := S.hasDerivAt_evaluate_oneParameter X f y t
      have he : ContinuousRationalFunctions.evaluate F 1 (S.toContinuous (S.lieOperator X f))
          (y * AdelicGL.ofInfinite F 1 (infiniteOneParameter F 1 X t)) = c.exponent * h t :=
        (congrArg (fun z => ContinuousRationalFunctions.evaluate F 1 (S.toContinuous z)
          (y * AdelicGL.ofInfinite F 1 (infiniteOneParameter F 1 X t))) (hlie f)).trans
          (evaluate_smul S _ f _)
      exact he ▸ hd
    have h0 : h 0 = ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f) y := by
      change ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f)
        (y * AdelicGL.ofInfinite F 1 (infiniteOneParameter F 1 X 0)) = _
      have h1 : y * AdelicGL.ofInfinite F 1 (infiniteOneParameter F 1 X 0) = y := by
        rw [infiniteOneParameter_zero, map_one, mul_one]
      exact congrArg (ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f)) h1
    have hsol := eq_exp_mul_of_hasDerivAt hh u
    have hχ : Complex.exp (c.exponent * u) =
        ((c.character (GeneralLinear.determinant
          (scalarUnit (Units.mk0 (Real.exp u) (Real.exp_pos u).ne'))) : ℂˣ) : ℂ) := by
      rw [determinant_scalarUnit, c.character_eq]
      simp only [Units.val_mk0, abs_of_pos (Real.exp_pos u), div_self (Real.exp_pos u).ne',
        Complex.ofReal_one, one_pow, one_mul]
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
        ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp, mul_comm]
    calc ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f)
          (y * realPlaceAdelic F v (scalarUnit (Units.mk0 (Real.exp u) (Real.exp_pos u).ne')))
        = h u :=
          congrArg (fun z => ContinuousRationalFunctions.evaluate F 1 (S.toContinuous f) (y * z))
            (hι u)
      _ = Complex.exp (c.exponent * u) * h 0 := hsol
      _ = _ := congrArg₂ (· * ·) hχ h0
  have hpos : ∀ t : ℝˣ, 0 < (t : ℝ) → P (scalarUnit t) := by
    intro t ht
    have heq : Units.mk0 (Real.exp (Real.log t)) (Real.exp_pos _).ne' = t :=
      Units.ext (by simp [Real.exp_log ht])
    exact heq ▸ hexp _
  have hall : ∀ t : ℝˣ, P (scalarUnit t) := by
    intro t
    rcases lt_or_gt_of_ne t.ne_zero with ht | ht
    · have heq : scalarUnit (-1) * scalarUnit (-t) = scalarUnit t := by
        rw [← map_mul, neg_mul_neg, one_mul]
      exact heq ▸ hmul _ _ hneg (hpos _ (by simpa using ht))
    · exact hpos t ht
  have hg : P g := scalarUnit_entry g ▸ hall _
  exact hg f y

end Place

end Langlands.Global.RankinSelbergGlobal.RealRankZero
