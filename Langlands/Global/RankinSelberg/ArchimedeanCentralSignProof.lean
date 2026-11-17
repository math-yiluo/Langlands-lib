import Langlands.Global.RankinSelberg.ArchimedeanCentralSignStatement
import Langlands.Automorphic.CentralCharacterTopCoefficient
import Langlands.Automorphic.IrreducibleCentralCharacterProof
import Langlands.Automorphic.ContragredientSphericalSpectrum
import Langlands.Global.IdeleClosedSubgroupDensity

/-! # Proof of the central sign identity over the infinite places and `S`

See the paired Markdown.
-/

noncomputable section
universe u uQ
open NumberField
open scoped Classical
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.CentralSign

open Langlands.Global Langlands.Automorphic ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F]

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

local instance centralSignRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance centralSignContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance centralSignSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance centralSignFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance centralSignStableAddCommGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance centralSignRealizationAddCommGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance centralSignLocalAddCommGroup {n : ℕ} {v : FinitePlace F}
    (S : LocalRealization F n v) : AddCommGroup S.Space := Submodule.addCommGroup _

/-! ### Functions of a realization determined by their values -/

section Evaluation

variable {n : ℕ} (S : OperatorRealization F n)

/-- A vector of a realization whose function is `c` times the function of `f` is `c • f`. -/
theorem eq_smul_of_evaluate {f g : S.Space} {c : ℂ}
    (h : ∀ x, evaluate F n (S.toContinuous g) x = c * evaluate F n (S.toContinuous f) x) :
    g = c • f := by
  apply S.toContinuous_injective
  apply toContinuousMap_injective F n
  ext x
  change evaluate F n (S.toContinuous g) x = evaluate F n (S.toContinuous (c • f)) x
  rw [h x, S.evaluate_toContinuous_smul]

/-- Two scalars agreeing on a vector whose function does not vanish at some point agree. -/
theorem smul_cancel {f₀ : S.Space} {x₀ : AdelicGL F n}
    (h0 : evaluate F n (S.toContinuous f₀) x₀ ≠ 0) {a b : ℂ} (h : a • f₀ = b • f₀) :
    a = b := by
  have h' := congrArg (fun g => evaluate F n (S.toContinuous g) x₀) h
  simp only [S.evaluate_toContinuous_smul] at h'
  exact mul_right_cancel₀ h0 h'

end Evaluation

/-! ### Scalar ideles at the infinite places -/

section Infinite

/-- The archimedean idele which is `-1` at the infinite place `w` and `1` at every other
infinite place. -/
def placeSign (w : InfinitePlace F) : (InfiniteAdeles F)ˣ where
  val := Pi.mulSingle w (-1)
  inv := Pi.mulSingle w (-1)
  val_inv := by
    have h : (Pi.mulSingle w (-1) * Pi.mulSingle w (-1) : ∀ v : InfinitePlace F, v.Completion) =
        1 := by
      rw [← Pi.mulSingle_mul, neg_one_mul, neg_neg, Pi.mulSingle_one]
    exact h
  inv_val := by
    have h : (Pi.mulSingle w (-1) * Pi.mulSingle w (-1) : ∀ v : InfinitePlace F, v.Completion) =
        1 := by
      rw [← Pi.mulSingle_mul, neg_one_mul, neg_neg, Pi.mulSingle_one]
    exact h

/-- The product of the signs at all infinite places is `-1`. -/
theorem prod_placeSign : ∏ w, (placeSign w : (InfiniteAdeles F)ˣ) = -1 := by
  apply Units.ext
  rw [Units.coe_prod, Units.val_neg, Units.val_one]
  change (∏ w, (Pi.mulSingle w (-1) : ∀ v : InfinitePlace F, v.Completion)) =
    (-1 : ∀ v : InfinitePlace F, v.Completion)
  rw [Finset.univ_prod_mulSingle (fun w : InfinitePlace F => (-1 : w.Completion))]
  rfl

/-- Splitting the product of the signs into the real and the complex places. -/
theorem prod_real_mul_prod_complex_placeSign :
    (∏ v : RP, (placeSign v.1 : (InfiniteAdeles F)ˣ)) * ∏ w : CP, placeSign w.1 = -1 := by
  rw [← prod_placeSign, ← Fintype.prod_subtype_mul_prod_subtype
    (fun w : InfinitePlace F => InfinitePlace.IsReal w)]
  congr 1
  exact Fintype.prod_equiv (Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex).symm
    _ _ fun _ => rfl

variable (n : ℕ)

/-- The scalar matrix of an archimedean idele is the archimedean scalar matrix. -/
theorem scalar_infiniteIdelesInclusion (z : (InfiniteAdeles F)ˣ) :
    AdelicGL.scalar F n (infiniteIdelesInclusion F z) =
      AdelicGL.ofInfinite F n (Matrix.GeneralLinearGroup.scalar (Fin n) z) := by
  apply Units.ext
  ext i j
  apply Prod.ext
  · change (Matrix.scalar (Fin n) ((infiniteIdelesInclusion F z : Ideles F) : Adeles F) i j).1 =
      (Matrix.scalar (Fin n) (z : InfiniteAdeles F)) i j
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> rfl
  · change (Matrix.scalar (Fin n) ((infiniteIdelesInclusion F z : Ideles F) : Adeles F) i j).2 =
      (1 : Matrix (Fin n) (Fin n) (FiniteAdeles F)) i j
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> rfl

omit [NumberField F] in
/-- The compact element `-1` at a real place `v` is the scalar matrix of `placeSign v`. -/
theorem realPlaceCompactInclusion_neg_one (v : RP) :
    (realPlaceCompactInclusion F n v (-1)).val =
      Matrix.GeneralLinearGroup.scalar (Fin n) (placeSign v.1) := by
  apply (archimedeanGLCoordinates F n).injective
  apply Units.ext
  ext i j w
  · have h := congrFun (congrFun (realMatrix_realPlaceCompactInclusion F n v w (-1)) i) j
    change ArchimedeanGL.realMatrix F n
      (archimedeanGLCoordinates F n (realPlaceCompactInclusion F n v (-1)).val) w i j = _
    rw [h, archimedeanGLCoordinates_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    change _ = InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
      ((Matrix.scalar (Fin n) (Pi.mulSingle v.1 (-1) : InfiniteAdeles F)) i j w.1)
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    by_cases hw : w = v
    · subst hw
      rw [Pi.mulSingle_eq_same]
      change (-1 : Matrix (Fin n) (Fin n) ℝ) i j = _
      rw [Matrix.neg_apply, Matrix.one_apply]
      split_ifs <;> simp
    · have hw' : w.1 ≠ v.1 := fun h => hw (Subtype.ext h)
      rw [Pi.mulSingle_eq_of_ne hw]
      change (1 : Matrix (Fin n) (Fin n) ℝ) i j = _
      rw [Matrix.one_apply]
      split_ifs
      · rw [Pi.mulSingle_eq_of_ne hw', map_one]
      · rw [Pi.zero_apply, map_zero]
  · have h := congrFun (congrFun (complexMatrix_realPlaceCompactInclusion F n v w (-1)) i) j
    change ArchimedeanGL.complexMatrix F n
      (archimedeanGLCoordinates F n (realPlaceCompactInclusion F n v (-1)).val) w i j = _
    rw [h, archimedeanGLCoordinates_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    change _ = InfinitePlace.Completion.extensionEmbedding w.1
      ((Matrix.scalar (Fin n) (Pi.mulSingle v.1 (-1) : InfiniteAdeles F)) i j w.1)
    have hw' : w.1 ≠ v.1 := fun h =>
      InfinitePlace.not_isReal_iff_isComplex.mpr w.2 (h ▸ v.2)
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs
    · rw [Pi.mulSingle_eq_of_ne hw', map_one]
    · rw [Pi.zero_apply, map_zero]

omit [NumberField F] in
/-- The compact element `-1` at a complex place `w` is the scalar matrix of `placeSign w`. -/
theorem complexPlaceCompactInclusion_neg_one (v : CP) :
    (complexPlaceCompactInclusion F n v (-1)).val =
      Matrix.GeneralLinearGroup.scalar (Fin n) (placeSign v.1) := by
  apply (archimedeanGLCoordinates F n).injective
  apply Units.ext
  ext i j w
  · have h := congrFun (congrFun (realMatrix_complexPlaceCompactInclusion F n v w (-1)) i) j
    change ArchimedeanGL.realMatrix F n
      (archimedeanGLCoordinates F n (complexPlaceCompactInclusion F n v (-1)).val) w i j = _
    rw [h, archimedeanGLCoordinates_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    change _ = InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
      ((Matrix.scalar (Fin n) (Pi.mulSingle v.1 (-1) : InfiniteAdeles F)) i j w.1)
    have hw' : w.1 ≠ v.1 := fun h =>
      InfinitePlace.not_isReal_iff_isComplex.mpr v.2 (h ▸ w.2)
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs
    · rw [Pi.mulSingle_eq_of_ne hw', map_one]
    · rw [Pi.zero_apply, map_zero]
  · have h := congrFun (congrFun (complexMatrix_complexPlaceCompactInclusion F n v w (-1)) i) j
    change ArchimedeanGL.complexMatrix F n
      (archimedeanGLCoordinates F n (complexPlaceCompactInclusion F n v (-1)).val) w i j = _
    rw [h, archimedeanGLCoordinates_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    change _ = InfinitePlace.Completion.extensionEmbedding w.1
      ((Matrix.scalar (Fin n) (Pi.mulSingle v.1 (-1) : InfiniteAdeles F)) i j w.1)
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    by_cases hw : w = v
    · subst hw
      rw [Pi.mulSingle_eq_same]
      change (-1 : Matrix (Fin n) (Fin n) ℂ) i j = _
      rw [Matrix.neg_apply, Matrix.one_apply]
      split_ifs <;> simp
    · have hw' : w.1 ≠ v.1 := fun h => hw (Subtype.ext h)
      rw [Pi.mulSingle_eq_of_ne hw]
      change (1 : Matrix (Fin n) (Fin n) ℂ) i j = _
      rw [Matrix.one_apply]
      split_ifs
      · rw [Pi.mulSingle_eq_of_ne hw', map_one]
      · rw [Pi.zero_apply, map_zero]

/-- The adelic image of the compact element `-1` at a real place `v` is the scalar matrix of the
idele `placeSign v`. -/
theorem ofInfinite_realPlaceCompactInclusion_neg_one (v : RP) :
    AdelicGL.ofInfinite F n (realPlaceCompactInclusion F n v (-1)).val =
      AdelicGL.scalar F n (infiniteIdelesInclusion F (placeSign v.1)) := by
  rw [realPlaceCompactInclusion_neg_one, scalar_infiniteIdelesInclusion]

/-- The adelic image of the compact element `-1` at a complex place `w` is the scalar matrix of
the idele `placeSign w`. -/
theorem ofInfinite_complexPlaceCompactInclusion_neg_one (w : CP) :
    AdelicGL.ofInfinite F n (complexPlaceCompactInclusion F n w (-1)).val =
      AdelicGL.scalar F n (infiniteIdelesInclusion F (placeSign w.1)) := by
  rw [complexPlaceCompactInclusion_neg_one, scalar_infiniteIdelesInclusion]

end Infinite

/-! ### The local component at a finite place -/

section Finite

variable (n : ℕ)

/-- The local scalar matrix of `-1` is the element `-1` of the local general linear group. -/
theorem generalLinear_scalar_neg_one (v : FinitePlace F) :
    Matrix.GeneralLinearGroup.scalar (Fin n) (-1 : (FiniteCompletion F v)ˣ) = -1 := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one, map_neg, map_one]

/-- The element `-1` at a finite place `v` is the scalar matrix of the local idele `-1` at `v`. -/
theorem ofFinite_localInclusion_neg_one (v : FinitePlace F) :
    AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v (-1)) =
      AdelicGL.scalar F n (finiteIdeleInclusion F v (-1)) := by
  rw [AdelicGL.scalar_finiteIdeleInclusion, generalLinear_scalar_neg_one]

/-- A vector of a local realization whose function is `c` times the function of `f` is
`c • f`. -/
theorem local_eq_smul_of_evaluate {v : FinitePlace F} (L : LocalRealization F n v)
    {f g : L.Space} {c : ℂ}
    (h : ∀ x, evaluate F n (L.toContinuous g) x = c * evaluate F n (L.toContinuous f) x) :
    g = c • f := by
  apply L.toContinuous_injective
  apply toContinuousMap_injective F n
  ext x
  change evaluate F n (L.toContinuous g) x = evaluate F n (L.toContinuous (c • f)) x
  rw [h x, map_smul]
  rfl

end Finite

/-! ### Density: integral units outside `S` -/

section Density

open Langlands.Global.HeckeFunctionalEquation

/-- A variant of `IdeleDensity.integralUnitIdeles_mem` needing only the local integral units
outside `S`: an idele of integral units equal to one on `S` lies in every closed subgroup
containing the local integral unit groups at all finite places outside `S`. -/
theorem integralUnitIdeles_mem_of_units (H : Subgroup (Ideles F)) (S : Finset (FinitePlace F))
    (hH : IsClosed (H : Set (Ideles F)))
    (hloc : ∀ v ∉ S, ∀ x : (v.adicCompletionIntegers F)ˣ,
      integralUnitIdeles F (Pi.mulSingle v x) ∈ H)
    (u : ∀ v : FinitePlace F, (v.adicCompletionIntegers F)ˣ) (hu : ∀ v ∈ S, u v = 1) :
    integralUnitIdeles F u ∈ H := by
  have hcl : IsClosed ((integralUnitIdeles F) ⁻¹' (H : Set (Ideles F))) :=
    hH.preimage (integralUnitIdeles F).continuous
  have hmem : u ∈ closure ((integralUnitIdeles F) ⁻¹' (H : Set (Ideles F))) := by
    rw [mem_closure_iff_nhds]
    intro N hN
    rw [nhds_pi, Filter.mem_pi'] at hN
    obtain ⟨T, t, ht, hTN⟩ := hN
    let u₁ : ∀ v : FinitePlace F, (v.adicCompletionIntegers F)ˣ :=
      ∏ v ∈ T, Pi.mulSingle v (u v)
    have hu₁ : ∀ j, u₁ j = if j ∈ T then u j else 1 := by
      intro j
      simp only [u₁, Finset.prod_apply]
      exact Finset.prod_pi_mulSingle j u T
    refine ⟨u₁, hTN fun j hj => ?_, ?_⟩
    · have hj' : j ∈ T := hj
      simp only [hu₁ j, hj', ↓reduceIte]
      exact mem_of_mem_nhds (ht j)
    · change integralUnitIdeles F u₁ ∈ H
      simp only [u₁, map_prod]
      apply H.prod_mem
      intro v _
      by_cases hvS : v ∈ S
      · rw [hu v hvS, Pi.mulSingle_one, map_one]
        exact H.one_mem
      · exact hloc v hvS _
  rw [hcl.closure_eq] at hmem
  exact hmem

variable [CompactSpace (AdeleQuotient F)] {t : ℕ} (T : CuspidalOperatorRealization F t)
  (χ : IdeleClasses F →ₜ* ℂˣ) (hχ : T.realization.HasCentralCharacter χ)

include hχ

/-- The central character of `T` is trivial on the integral unit ideles which are `1` on a
finite set `S` containing the exceptional places of a spectral presentation. -/
theorem centralIdeleCharacter_integralUnitIdeles (P : CuspidalSpectralPresentation.{u, uQ} T)
    (S : Finset (FinitePlace F)) (hS : P.exceptional ⊆ S)
    (u : ∀ v : FinitePlace F, (v.adicCompletionIntegers F)ˣ) (hu : ∀ v ∈ S, u v = 1) :
    centralIdeleCharacter F χ (integralUnitIdeles F u) = 1 := by
  have hmem : integralUnitIdeles F u ∈ T.realization.centralCharacterSubgroup 1 := by
    apply integralUnitIdeles_mem_of_units _ S (T.realization.isClosed_centralCharacterSubgroup 1)
      _ u hu
    intro v hv x
    rw [integralUnitIdeles_mulSingle]
    exact CuspidalOperatorRealization.finiteIdeleInclusion_units_mem_centralCharacterSubgroup v T P
      1 (fun _ _ => rfl) (fun h => hv (hS h)) _ ⟨x.val.property, x⁻¹.val.property⟩
  obtain ⟨f₀, x₀, h0⟩ := T.realization.exists_evaluate_ne_zero T.irreducible
  have h1 := (T.realization.mem_centralCharacterSubgroup 1 _).mp hmem f₀ x₀
  rw [T.realization.centralCharacter_evaluate χ hχ f₀ (integralUnitIdeles F u) x₀] at h1
  apply Units.ext
  rw [mul_right_cancel₀ h0 h1]
  rfl

end Density

/-! ### The scalars at the infinite places and at the places of `S` -/

section Scalars

variable [CompactSpace (AdeleQuotient F)] {t : ℕ} (T : CuspidalOperatorRealization F t)
  (χ : IdeleClasses F →ₜ* ℂˣ) (hχ : T.realization.HasCentralCharacter χ)

include hχ

/-- The compact element `-1` at a real place `v` acts by the central character at
`placeSign v`. -/
theorem realPlace_neg_one_apply (v : RP) (f : T.realization.Space) :
    T.realization.realPlaceCompactRepresentation v (-1) f =
      (centralIdeleCharacter F χ (infiniteIdelesInclusion F (placeSign v.1)) : ℂ) • f := by
  apply eq_smul_of_evaluate
  intro x
  rw [OperatorRealization.evaluate_realPlaceCompactRepresentation,
    ofInfinite_realPlaceCompactInclusion_neg_one]
  have hc : x * AdelicGL.scalar F (t + 1) (infiniteIdelesInclusion F (placeSign v.1)) =
      AdelicGL.scalar F (t + 1) (infiniteIdelesInclusion F (placeSign v.1)) * x :=
    (AdelicGL.scalar_commute F (t + 1) _ x).eq.symm
  exact (congrArg (evaluate F (t + 1) (T.realization.toContinuous f)) hc).trans
    (T.realization.centralCharacter_evaluate χ hχ f _ x)

/-- The compact element `-1` at a complex place `w` acts by the central character at
`placeSign w`. -/
theorem complexPlace_neg_one_apply (w : CP) (f : T.realization.Space) :
    T.realization.complexPlaceCompactRepresentation w (-1) f =
      (centralIdeleCharacter F χ (infiniteIdelesInclusion F (placeSign w.1)) : ℂ) • f := by
  apply eq_smul_of_evaluate
  intro x
  rw [OperatorRealization.evaluate_complexPlaceCompactRepresentation,
    ofInfinite_complexPlaceCompactInclusion_neg_one]
  have hc : x * AdelicGL.scalar F (t + 1) (infiniteIdelesInclusion F (placeSign w.1)) =
      AdelicGL.scalar F (t + 1) (infiniteIdelesInclusion F (placeSign w.1)) * x :=
    (AdelicGL.scalar_commute F (t + 1) _ x).eq.symm
  exact (congrArg (evaluate F (t + 1) (T.realization.toContinuous f)) hc).trans
    (T.realization.centralCharacter_evaluate χ hχ f _ x)

theorem realMinusOneScalar_eq (v : RP) :
    realMinusOneScalar T v =
      (centralIdeleCharacter F χ (infiniteIdelesInclusion F (placeSign v.1)) : ℂ) := by
  obtain ⟨f₀, x₀, h0⟩ := T.realization.exists_evaluate_ne_zero T.irreducible
  have h := realMinusOneScalar_spec T v ⟨_, realPlace_neg_one_apply T χ hχ v⟩ f₀
  rw [realPlace_neg_one_apply T χ hχ v] at h
  exact (smul_cancel T.realization h0 h).symm

theorem complexMinusOneScalar_eq (w : CP) :
    complexMinusOneScalar T w =
      (centralIdeleCharacter F χ (infiniteIdelesInclusion F (placeSign w.1)) : ℂ) := by
  obtain ⟨f₀, x₀, h0⟩ := T.realization.exists_evaluate_ne_zero T.irreducible
  have h := complexMinusOneScalar_spec T w ⟨_, complexPlace_neg_one_apply T χ hχ w⟩ f₀
  rw [complexPlace_neg_one_apply T χ hχ w] at h
  exact (smul_cancel T.realization h0 h).symm

/-- The element `-1` at a finite place `v` acts on the local component at `v` by the central
character at the local idele `-1`. -/
theorem localComponent_neg_one_apply (P : CuspidalSpectralPresentation.{u, uQ} T)
    (v : FinitePlace F) (y : (P.localComponent v).Space) :
    (P.localComponent v).representation (-1) y =
      (centralIdeleCharacter F χ (finiteIdeleInclusion F v (-1)) : ℂ) • y := by
  have hL : (P.localComponent v).HasCentralCharacter χ := fun f hf =>
    hχ (P.localComponent_le_image v hf)
  apply local_eq_smul_of_evaluate
  intro x
  rw [LocalRealization.evaluate_representation, ofFinite_localInclusion_neg_one]
  have hc : x * AdelicGL.scalar F (t + 1) (finiteIdeleInclusion F v (-1)) =
      AdelicGL.scalar F (t + 1) (finiteIdeleInclusion F v (-1)) * x :=
    (AdelicGL.scalar_commute F (t + 1) _ x).eq.symm
  exact (congrArg (evaluate F (t + 1) ((P.localComponent v).toContinuous y)) hc).trans
    ((P.localComponent v).centralCharacter_evaluate χ hL y _ x)

end Scalars

/-! ### The idele identity -/

open Langlands.Global.HeckeFunctionalEquation in
/-- The principal idele `-1` is the product of the archimedean idele `-1`, the local ideles
`-1` at the places of `S`, and the integral unit idele which is `1` on `S` and `-1` off `S`. -/
theorem diagonalUnits_neg_one_eq (S : Finset (FinitePlace F)) :
    diagonalUnits F (-1) = infiniteIdelesInclusion F (-1) *
      (∏ v : S, finiteIdeleInclusion F v.1 (-1)) *
        integralUnitIdeles F (fun v => if v ∈ S then 1 else -1) := by
  have hneg : diagonalUnits F (-1) = -1 := by
    apply Units.ext
    simp
  rw [hneg]
  apply IdeleDensity.idele_ext
  · rw [map_mul, map_mul, map_prod, IdeleDensity.infPart_infiniteIdelesInclusion,
      IdeleDensity.infPart_integralUnitIdeles]
    simp only [IdeleDensity.infPart_finiteIdeleInclusion, Finset.prod_const_one, mul_one,
      Units.val_neg, Units.val_one]
    rfl
  · intro w
    rw [map_mul, map_mul, map_prod, IdeleDensity.coord_infiniteIdelesInclusion,
      IdeleDensity.coord_integralUnitIdeles]
    simp only [IdeleDensity.coord_finiteIdeleInclusion]
    rw [Finset.prod_coe_sort S (fun v => (Pi.mulSingle v
      ((-1 : (FiniteCompletion F v)ˣ) : FiniteCompletion F v) :
        ∀ w : FinitePlace F, FiniteCompletion F w) w), Finset.prod_pi_mulSingle]
    have h1 : IdeleDensity.coord w (-1 : Ideles F) = -1 := by
      change (finiteProjection F w) ((-1 : Ideles F) : Adeles F) = -1
      rw [Units.val_neg, Units.val_one, map_neg, map_one]
    rw [h1]
    by_cases hw : w ∈ S <;> simp [hw]

end Langlands.Global.RankinSelbergGlobal.CentralSign

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Global Langlands.Automorphic Langlands.Global.HeckeFunctionalEquation
open CentralSign

/-- **The central sign identity** (Cogdell 2004, proof of Theorem 4.1, p.220). -/
theorem archimedeanCentralSign : ArchimedeanCentralSignStatement.{u, uQ} := by
  intro F _ _ _ t T' P' hI' S hS ψv ζ hζ
  obtain ⟨χ, hχ, -⟩ := T'.realization.existsUnique_hasCentralCharacter T'.irreducible
  have hcu := centralIdeleCharacter_integralUnitIdeles T' χ hχ P' S hS
    (fun v => if v ∈ S then 1 else -1) (fun v hv => by simp [hv])
  have hdiag : centralIdeleCharacter F χ (diagonalUnits F (-1)) = 1 :=
    centralIdeleCharacter_principal F χ (-1)
  rw [diagonalUnits_neg_one_eq S, map_mul, map_mul, hcu, mul_one] at hdiag
  have hζv : ∀ v : S, ζ v = centralIdeleCharacter F χ (finiteIdeleInclusion F v.1 (-1)) := by
    intro v
    let _ := (CompletionPadic.padicField v.1).canonicalTopologicalData.topology
    let _ := (CompletionPadic.padicField v.1).canonicalGeneralLinearTopology (t + 1)
    obtain ⟨ℓ, hℓ, hζ'⟩ := hζ v
    refine RankinSelberg.HasModelMinusOneScalar.unique hℓ hζ' ?_
    intro f g
    obtain ⟨y, hy⟩ := f.property
    rw [← hy]
    show ℓ.val ((P'.localComponent v.1).representation ((-1) * g) y) =
      (centralIdeleCharacter F χ (finiteIdeleInclusion F v.1 (-1)) : ℂ) *
        ℓ.val ((P'.localComponent v.1).representation g y)
    refine (congrArg ℓ.val (LinearMap.congr_fun
      (map_mul (P'.localComponent v.1).representation (-1) g) y)).trans ?_
    refine (congrArg ℓ.val (localComponent_neg_one_apply T' χ hχ P' v.1 _)).trans ?_
    exact map_smul ℓ.val _ _
  have key : centralIdeleCharacter F χ (infiniteIdelesInclusion F
        (∏ v : {v : InfinitePlace F // v.IsReal}, placeSign v.1)) *
      centralIdeleCharacter F χ (infiniteIdelesInclusion F
        (∏ w : {v : InfinitePlace F // v.IsComplex}, placeSign w.1)) *
      centralIdeleCharacter F χ (∏ v : S, finiteIdeleInclusion F v.1 (-1)) = 1 := by
    rw [← map_mul, ← map_mul (infiniteIdelesInclusion F),
      prod_real_mul_prod_complex_placeSign]
    exact hdiag
  calc (∏ v, realMinusOneScalar T' v) * (∏ w, complexMinusOneScalar T' w) *
        ∏ v : S, (ζ v : ℂ)
      = ((centralIdeleCharacter F χ (infiniteIdelesInclusion F
            (∏ v : {v : InfinitePlace F // v.IsReal}, placeSign v.1)) *
          centralIdeleCharacter F χ (infiniteIdelesInclusion F
            (∏ w : {v : InfinitePlace F // v.IsComplex}, placeSign w.1)) *
          centralIdeleCharacter F χ (∏ v : S, finiteIdeleInclusion F v.1 (-1)) : ℂˣ) : ℂ) := by
        simp only [map_prod, Units.val_mul, Units.coe_prod]
        congr 1
        · congr 1
          · exact Finset.prod_congr rfl fun v _ => realMinusOneScalar_eq T' χ hχ v
          · exact Finset.prod_congr rfl fun w _ => complexMinusOneScalar_eq T' χ hχ w
        · exact Finset.prod_congr rfl fun v _ => congrArg Units.val (hζv v)
    _ = 1 := by rw [key, Units.val_one]

end Langlands.Global.RankinSelbergGlobal
