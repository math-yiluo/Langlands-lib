import Langlands.Global.RankinSelberg.UnequalLocalKernelProducts
import Langlands.Global.RankinSelberg.StandardCompactPadding
import Langlands.Global.RankinSelberg.WhittakerCellDecomposition
import Langlands.Global.RankinSelberg.ArchimedeanWhittakerProducts
import Langlands.Global.RankinSelberg.FiniteWhittakerDualProduct
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof
import Langlands.Global.RankinSelberg.UnequalDualEulerFactorizationReduction

/-! # Adelic points for unequal-rank Whittaker products -/

noncomputable section
open NumberField Langlands.Automorphic Langlands.GeneralLinear
open Langlands.Global.FiniteAdelicGL Langlands.Global.CompletionPadic
open Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.ClassField.Global.RelativeWeilGroup
open scoped Classical CategoryTheory.MonObj TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal.UnequalWhittakerProducts

open FiniteWhittakerTensor FiniteWhittakerSemilocal FiniteWhittakerDual
open UnipotentClass

local instance (F : Type u) [Field F] (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance (F : Type u) [Field F] (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

section MatrixMaps

variable {R K : Type*} [CommRing R] [Field K] (f : R →+* K)

private theorem map_blockSum {m n : ℕ} (g : Langlands.GeneralLinear m R)
    (w : Langlands.GeneralLinear n R) :
    Matrix.GeneralLinearGroup.map f (GeneralLinear.blockSum (g, w)) =
      GeneralLinear.blockSum (Matrix.GeneralLinearGroup.map f g,
        Matrix.GeneralLinearGroup.map f w) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp only [Matrix.GeneralLinearGroup.map_apply, GeneralLinear.blockSum_apply_left,
      GeneralLinear.blockSum_apply_right, GeneralLinear.blockSum_apply_left_right,
      GeneralLinear.blockSum_apply_right_left, map_zero]

private theorem map_reindex {m n : ℕ} (e : Fin m ≃ Fin n) (g : Langlands.GeneralLinear m R) :
    Matrix.GeneralLinearGroup.map f (GeneralLinear.reindex e g) =
      GeneralLinear.reindex e (Matrix.GeneralLinearGroup.map f g) := by
  apply Units.ext
  rfl

private theorem map_weylLong (n : ℕ) :
    Matrix.GeneralLinearGroup.map f (weylLong n R) = weylLong n K := by
  apply Units.ext
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, weylLong_entry]
  split_ifs <;> simp

private theorem map_unfoldingWeyl {r t : ℕ} (h : t < r) :
    Matrix.GeneralLinearGroup.map f (GeneralLinear.reindex
        (finCongr (Nat.add_sub_of_le (Nat.le_of_lt (Nat.succ_lt_succ h))))
        (GeneralLinear.blockSum (1, weylLong ((r + 1) - (t + 1)) R))) =
      ArchimedeanLocal.unfoldingWeyl h := by
  simp only [ArchimedeanLocal.unfoldingWeyl, map_reindex, map_blockSum, map_weylLong, map_one]

private theorem map_rectangularPoint {r t : ℕ} (h : t < r) (g : Langlands.GeneralLinear (t + 1) R)
    (y : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) R) :
    Matrix.GeneralLinearGroup.map f (RectangularSupport.rectGL h g y) =
      ArchimedeanLocal.rectangularPoint h (Matrix.GeneralLinearGroup.map f g) (y.map f) := by
  apply Units.ext
  ext i j
  change (Matrix.GeneralLinearGroup.map f (RectangularSupport.rectGL h g y)) i j =
    RectangularSupport.rectGL h (Matrix.GeneralLinearGroup.map f g) (y.map f) i j
  simp only [Matrix.GeneralLinearGroup.map_apply, RectangularSupport.rectGL_apply]
  split_ifs <;> simp

end MatrixMaps

section Components

variable (F : Type u) [Field F] [NumberField F]
variable {r t : ℕ} (h : t < r)

private def realRingProjection (v : {v : InfinitePlace F // v.IsReal}) : Adeles F →+* ℝ :=
  ((Pi.evalRingHom (fun _ : {v : InfinitePlace F // v.IsReal} => ℝ) v).comp
    (RingHom.fst _ _)).comp
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _))

private def complexRingProjection (v : {v : InfinitePlace F // v.IsComplex}) : Adeles F →+* ℂ :=
  ((Pi.evalRingHom (fun _ : {v : InfinitePlace F // v.IsComplex} => ℂ) v).comp
    (RingHom.snd _ _)).comp
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _))

private theorem realComponent_eq_map (n : ℕ) (v : {v : InfinitePlace F // v.IsReal})
    (g : Points F n) : realComponent F n v g =
      Matrix.GeneralLinearGroup.map (realRingProjection F v)
        (GeneralLinearGroupPoints.adelicEquiv F n g) := Units.ext rfl

private theorem complexComponent_eq_map (n : ℕ) (v : {v : InfinitePlace F // v.IsComplex})
    (g : Points F n) : complexComponent F n v g =
      Matrix.GeneralLinearGroup.map (complexRingProjection F v)
        (GeneralLinearGroupPoints.adelicEquiv F n g) := Units.ext rfl

private theorem finiteComponent_eq_map (n : ℕ) (v : FinitePlace F) (g : Points F n) :
    finiteComponent F n v g = Matrix.GeneralLinearGroup.map (finiteProjection F v)
      (GeneralLinearGroupPoints.adelicEquiv F n g) := Units.ext rfl

/-- Projection commutes with the ordinary matrix in the larger rank. -/
theorem realComponent_pad (v : {v : InfinitePlace F // v.IsReal}) (g : Points F (t + 1)) :
    realComponent F (r + 1) v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g) =
      padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) (realComponent F (t + 1) v g) := by
  simp only [realComponent_eq_map, pad, MulEquiv.apply_symm_apply, map_padGL]

/-- Projection commutes with the ordinary matrix in the larger rank. -/
theorem complexComponent_pad (v : {v : InfinitePlace F // v.IsComplex}) (g : Points F (t + 1)) :
    complexComponent F (r + 1) v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g) =
      padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) (complexComponent F (t + 1) v g) := by
  simp only [complexComponent_eq_map, pad, MulEquiv.apply_symm_apply, map_padGL]

/-- Projection commutes with the ordinary matrix in the larger rank. -/
theorem finiteComponent_pad (v : FinitePlace F) (g : Points F (t + 1)) :
    finiteComponent F (r + 1) v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g) =
      padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) (finiteComponent F (t + 1) v g) := by
  simp only [finiteComponent_eq_map, pad, MulEquiv.apply_symm_apply, map_padGL]

/-- Real projection of the rectangular point. -/
theorem realComponent_rectangularPoint (v : {v : InfinitePlace F // v.IsReal})
    (g : Points F (t + 1)) (y : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F)) :
    realComponent F (r + 1) v (rectangularPoint F h g y) =
      ArchimedeanLocal.rectangularPoint h (realComponent F (t + 1) v g) (realRectCoordinates F v y) := by
  simp only [realComponent_eq_map, rectangularPoint, MulEquiv.apply_symm_apply]
  exact map_rectangularPoint (realRingProjection F v) h _ y

/-- Complex projection of the rectangular point. -/
theorem complexComponent_rectangularPoint (v : {v : InfinitePlace F // v.IsComplex})
    (g : Points F (t + 1)) (y : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F)) :
    complexComponent F (r + 1) v (rectangularPoint F h g y) =
      ArchimedeanLocal.rectangularPoint h (complexComponent F (t + 1) v g)
        (complexRectCoordinates F v y) := by
  simp only [complexComponent_eq_map, rectangularPoint, MulEquiv.apply_symm_apply]
  exact map_rectangularPoint (complexRingProjection F v) h _ y

/-- The global and real block Weyl elements agree under projection. -/
theorem realComponent_unfoldingWeyl (v : {v : InfinitePlace F // v.IsReal}) :
    realComponent F (r + 1) v (unfoldingWeyl F h) = ArchimedeanLocal.unfoldingWeyl h := by
  rw [realComponent_eq_map, unfoldingWeyl, MulEquiv.apply_symm_apply]
  exact map_unfoldingWeyl (realRingProjection F v) h

/-- The global and complex block Weyl elements agree under projection. -/
theorem complexComponent_unfoldingWeyl (v : {v : InfinitePlace F // v.IsComplex}) :
    complexComponent F (r + 1) v (unfoldingWeyl F h) = ArchimedeanLocal.unfoldingWeyl h := by
  rw [complexComponent_eq_map, unfoldingWeyl, MulEquiv.apply_symm_apply]
  exact map_unfoldingWeyl (complexRingProjection F v) h

/-- The global and finite block Weyl elements agree under projection. -/
theorem finiteComponent_unfoldingWeyl (v : FinitePlace F) :
    finiteComponent F (r + 1) v (unfoldingWeyl F h) = ArchimedeanLocal.unfoldingWeyl h := by
  rw [finiteComponent_eq_map, unfoldingWeyl, MulEquiv.apply_symm_apply]
  exact map_unfoldingWeyl (finiteProjection F v) h

end Components

section IntegralRepresentatives

variable (F : Type u) [Field F] [NumberField F]

/-- Every class in the partial domain has a representative integral away from `S`. -/
theorem exists_integral_rep {n : ℕ} (S : Finset (FinitePlace F))
    (q : WhittakerQuotient F n) (hq : q ∈ unipotentIntegralClasses F n S) :
    ∃ g : Points F n, LeftCosetSpace.mk (unipotentAdelic F n) g = q ∧
      ∀ v ∉ S, finiteComponent F n v g ∈ localIntegral F n v := by
  have hq' : q.out ∈ unipotentIntegralOutside F n S := hq
  obtain ⟨y, _, _, hy⟩ := exists_semilocal_of_mem_unipotentIntegralOutside F n S hq'
  refine ⟨semilocalEmbedding F n S y, ?_, ?_⟩
  · rw [← Quotient.out_eq q]
    exact (LeftCosetSpace.mk_eq_mk_iff _ _ _).mpr hy
  · intro v hv
    rw [semilocalEmbedding_apply, finiteComponent_adelicSplit_of_not_mem F n S _ hv]
    exact y.2.2.property ⟨v, hv⟩

/-- Integral finite components are in the local `N K` domains. -/
theorem mem_partial_of_integral {n : ℕ} (S : Finset (FinitePlace F)) (g : Points F n)
    (hg : ∀ v ∉ S, finiteComponent F n v g ∈ localIntegral F n v) :
    g ∈ unipotentIntegralOutside F n S := by
  intro v hv
  exact ⟨(finiteComponent F n v g)⁻¹, (localIntegral F n v).inv_mem (hg v hv),
    by simp, by
      intro i j hij
      simp [Matrix.one_apply_ne hij.ne']⟩

end IntegralRepresentatives

section FiniteProduct

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
variable (S : Finset (FinitePlace F))

omit [CompactSpace (AdeleQuotient F)] in
private theorem infinitePoint_mul_finitePart (g : Points F (r + 1)) :
    infinitePoint S g * (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
      (AdelicGL.ofFinite F (r + 1) (AdelicGL.finite F (r + 1)
        (GeneralLinearGroupPoints.adelicEquiv F (r + 1) g))) = g := by
  obtain ⟨z, rfl⟩ := (adelicSplit F (r + 1) S).surjective g
  simp only [infinitePoint, ContinuousMulEquiv.symm_apply_apply,
    adelicEquiv_adelicSplit, AdelicGL.finite_pair]
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  simp only [map_mul, MulEquiv.apply_symm_apply, adelicEquiv_adelicSplit]
  apply AdelicGL.ext_infinite_finite F (r + 1)
  · simp [AdelicGL.infinite_pair]
  · simp [AdelicGL.finite_pair]

local instance : AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F (r + 1)) := Submodule.addCommGroup _
local instance {v : FinitePlace F} (L : LocalRealization F (r + 1) v) :
    AddCommGroup L.Space := Submodule.addCommGroup _
local instance (T : CuspidalOperatorRealization F r) : AddCommGroup T.Space :=
  Submodule.addCommGroup _

variable {T : CuspidalOperatorRealization F r}
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (hI : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible)
    (hPS : P.exceptional ⊆ S)

/-- Finite separation for a single Whittaker function on integral representatives, at any rank. -/
theorem coefficient_eq_product
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1))
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (a₀ : ∀ v : S, P.localFactor v) (ha₀ : ∀ v : S, (ℓ v).val (a₀ v) = 1)
    (a : ∀ v : S, P.localFactor v)
    (τ : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (g : Points F (r + 1)) (hg : ∀ v ∉ S, finiteComponent F (r + 1) v g ∈ localIntegral F (r + 1) v) :
    cuspWhittaker F T ψ.complex (P.allPlaceTensorEquiv hI (P.finitePure S hPS a ⊗ₜ[ℂ] τ)) g =
      (∏ v : S, (ℓ v).val ((P.localFactor v).representation
        (finiteComponent F (r + 1) v.1 g) (a v))) *
      infiniteResidual S P hI hPS ψ.complex a₀ τ g := by
  let d := AdelicGL.finite F (r + 1) (GeneralLinearGroupPoints.adelicEquiv F (r + 1) g)
  let x := P.allPlaceTensorEquiv hI (P.finitePure S hPS a ⊗ₜ[ℂ] τ)
  have he : infinitePoint S g * (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
      (AdelicGL.ofFinite F (r + 1) d) = g := infinitePoint_mul_finitePart S g
  change cuspWhittaker F T ψ.complex x g = _
  refine (congrArg (cuspWhittaker F T ψ.complex x) he.symm).trans ?_
  exact translated_coefficient_eq_product P hI S hPS ψ hψ ψv hψv ℓ a₀ ha₀
    (infinitePoint S g) (infinitePoint_finite S g) d hg τ a

end FiniteProduct

section QuotientKernels

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r t : ℕ} (h : t < r) (T : CuspidalOperatorRealization F r)
    (T' : CuspidalOperatorRealization F t) (χ : AddChar (Adeles F) ℂ)
    (hχ : IsStandardAdditiveCharacter F χ) (x : T.Space) (x' : T'.Space)
    (s : ℂ) (q : WhittakerQuotient F (t + 1)) (g : Points F (t + 1))
    (hg : LeftCosetSpace.mk (unipotentAdelic F (t + 1)) g = q)

omit [CompactSpace (AdeleQuotient F)] in
include hg in
private theorem exists_unipotent_rep : ∃ n : unipotentAdelic F (t + 1), q.out = n.val * g := by
  have hn := (LeftCosetSpace.mk_eq_mk_iff _ _ _).mp (hg.trans (Quotient.out_eq q).symm)
  refine ⟨⟨q.out * g⁻¹, hn⟩, ?_⟩
  simp

include hχ hg in
/-- The ordinary integrand can be evaluated at any representative of the adelic class. -/
theorem ordinaryKernel_of_rep :
    unequalWhittakerIntegrand F h (cuspWhittaker F T χ x) (cuspWhittaker F T' χ⁻¹ x') s q =
      Unfolding.ordinaryKernel F h (cuspWhittaker F T χ x) (cuspWhittaker F T' χ⁻¹ x') s g := by
  obtain ⟨n, hn⟩ := exists_unipotent_rep F q g hg
  rw [Unfolding.unequalWhittakerIntegrand_eq, hn,
    Unfolding.ordinaryKernel_whittaker_unipotent_mul F h T T' χ hχ x x']

include hχ hg in
/-- The dual kernel can be evaluated at any representative of the adelic class. -/
theorem dualKernel_of_rep (y : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F)) :
    dualWhittakerKernel F h (Unfolding.dualWhittaker F h T χ x)
        (dualFunction F (t + 1) (cuspWhittaker F T' χ⁻¹ x')) s q y =
      Unfolding.dualWhittaker F h T χ x (rectangularPoint F h g y) *
        dualFunction F (t + 1) (cuspWhittaker F T' χ⁻¹ x') g *
        detPower F (t + 1) g (s - ((r - t : ℕ) : ℂ) / 2) := by
  obtain ⟨n, hn⟩ := exists_unipotent_rep F q g hg
  have hne := Unfolding.genericCharacter_ne_zero F t χ hχ (fun _ => 1) n
  simp only [dualWhittakerKernel]
  rw [hn, Unfolding.rectangularPoint_mul_left, Unfolding.dualWhittaker_pad_mul F h T χ hχ x n,
    Unfolding.dualCuspWhittaker_unipotent_mul F T' χ hχ x' n,
    Unfolding.detPower_unipotent_mul F (t + 1) n]
  field_simp

end QuotientKernels

section Support

open LocalPointFactorization UnequalDualEuler RectangularSupport

variable {F : Type u} [Field F] [NumberField F]
variable {r t : ℕ} (h : t < r)

private theorem localIntegral_iff_canonical (v : FinitePlace F) (n : ℕ)
    (k : FiniteLocalGL F (n + 1) v) :
    k ∈ localIntegral F (n + 1) v ↔ k ∈ Conductor.integralSubgroup (canonicalValuation v).integer n := by
  rw [WhittakerCell.mem_localIntegral_iff_mem_integralSubgroup,
    integer_eq_of_isEquiv (valued_isEquiv_canonical v)]

private theorem localRect_mem_canonical_iff (v : FinitePlace F)
    (y : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F)) :
    (∀ i j, localRectCoordinates F v y i j ∈ (canonicalValuation v).integer) ↔
      ∀ i j, finiteProjection F v (y i j) ∈ v.adicCompletionIntegers F := by
  rw [← integer_eq_of_isEquiv (valued_isEquiv_canonical v)]
  rfl

/-- Padding preserves integrality at each finite place. -/
theorem pad_integral (v : FinitePlace F) (g : Points F (t + 1))
    (hg : finiteComponent F (t + 1) v g ∈ localIntegral F (t + 1) v) :
    finiteComponent F (r + 1) v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g) ∈
      localIntegral F (r + 1) v := by
  rw [localIntegral_iff_canonical, UnequalDualEuler.finiteComponent_pad]
  exact rectGL_mem_integralSubgroup h ((localIntegral_iff_canonical v t _).mp hg)
    (fun i j => zero_mem _)

/-- The translated rectangular point is integral whenever its leading block and rectangle are. -/
theorem rect_weyl_integral (v : FinitePlace F) (g : Points F (t + 1))
    (hg : finiteComponent F (t + 1) v g ∈ localIntegral F (t + 1) v)
    (y : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F))
    (hy : ∀ i j, finiteProjection F v (y i j) ∈ v.adicCompletionIntegers F) :
    finiteComponent F (r + 1) v (rectangularPoint F h g y * unfoldingWeyl F h) ∈
      localIntegral F (r + 1) v := by
  rw [localIntegral_iff_canonical, UnipotentClass.finiteComponent_mul,
    UnequalDualEuler.finiteComponent_rectangularPoint]
  exact (Conductor.integralSubgroup (canonicalValuation v).integer r).mul_mem
    (rectGL_mem_integralSubgroup h ((localIntegral_iff_canonical v t _).mp hg)
      ((localRect_mem_canonical_iff v y).mpr hy)) (finiteComponent_unfoldingWeyl_mem h v)

/-- The dual argument sends an integral finite component to an integral one. -/
theorem dualPoint_integral (n : ℕ) (v : FinitePlace F) (g : Points F n)
    (hg : finiteComponent F n v g ∈ localIntegral F n v) :
    finiteComponent F n v (Unfolding.dualPoint F n g) ∈ localIntegral F n v := by
  rw [FiniteWhittakerDual.finiteComponent_dualPoint]
  exact (localIntegral F n v).mul_mem (weylLong_mem_localIntegral n v)
    (ContragredientDual.inverseTranspose_mem_localIntegral F n v hg)

variable [CompactSpace (AdeleQuotient F)]

/-- The translated dual vanishes if the rectangular block has a nonintegral entry at a
spherical place of conductor zero. No choice of a contragredient vector is needed. -/
theorem dualWhittaker_eq_zero_of_not_rectIntegral
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : IsStandardAdditiveCharacter F ψ.complex)
    (T : CuspidalOperatorRealization F r) (x : T.Space) (S : Finset (FinitePlace F))
    (hx : IsSphericalOutside F T S x) (v : FinitePlace F) (hv : v ∉ S)
    (ψv : Correspondence.NontrivialAdditiveCharacter (padicField v))
    (hψv : IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (hcond : (padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    (g : Points F (t + 1)) (y : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F))
    (hy : ¬ ∀ i j, finiteProjection F v (y i j) ∈ v.adicCompletionIntegers F) :
    Unfolding.dualWhittaker F h T ψ.complex x (rectangularPoint F h g y) = 0 := by
  let := (padicField v).canonicalTopologicalData.topology
  let W := cuspWhittaker F T ψ.complex x
  let p := rectangularPoint F h g y
  let b := finiteComponent F (r + 1) v (unfoldingWeyl F h)
  let X := (p * unfoldingWeyl F h) *
    (localPoint F (r + 1) v (finiteComponent F (r + 1) v (p * unfoldingWeyl F h)))⁻¹
  have hX : finiteComponent F (r + 1) v X = 1 :=
    finiteComponent_mul_inv_localPoint F (r + 1) v _
  let f (Q : FiniteLocalGL F (r + 1) v) :=
    dualFunction F (r + 1) W (X * localPoint F (r + 1) v (Q * b))
  have hθ (u : Langlands.GeneralLinear.upperUnipotent (r + 1) (FiniteCompletion F v)) :
      (Whittaker.inverseStandardCharacter ψv r u : ℂ) =
        (ψv.complex (∑ i : Fin r, u.val i.castSucc i.succ))⁻¹ :=
    Whittaker.inverseStandardCharacter_apply ψv r u
  have hχ : ∀ z ∉ (canonicalValuation v).integer,
      ∃ c ∈ (canonicalValuation v).integer, (ψv.complex (c * z))⁻¹ ≠ 1 := by
    intro z hz
    obtain ⟨c, hc, hcz⟩ := exists_ne_one_of_conductor hcond z hz
    exact ⟨c, hc, fun he => hcz (by simpa only [inv_inv, inv_one] using congrArg Inv.inv he)⟩
  have hf (u : Langlands.GeneralLinear.upperUnipotent (r + 1) (FiniteCompletion F v))
      (Q : FiniteLocalGL F (r + 1) v) : f (u.val * Q) =
        (Whittaker.inverseStandardCharacter ψv r u : ℂ) * f Q := by
    let U : unipotentAdelic F (r + 1) :=
      ⟨localPoint F (r + 1) v u.val, UnequalDualEuler.localPoint_mem_unipotentAdelic F v u.property⟩
    have hcov := Unfolding.dualCuspWhittaker_unipotent_mul F T ψ.complex⁻¹
      (Unfolding.isStandardAdditiveCharacter_inv F ψ.complex hψ) x U
      (X * localPoint F (r + 1) v (Q * b))
    rw [inv_inv, UnramifiedWhittaker.genericCharacter_inv] at hcov
    have hU : genericCharacter F r ψ.complex (fun _ => 1) U =
        (Whittaker.standardCharacter ψv r u : ℂ) :=
      UnramifiedWhittaker.genericCharacter_localPoint F ψ v ψv hψv u
    rw [hU] at hcov
    unfold f
    rw [mul_assoc u.val Q b, localPoint_mul, ← mul_assoc,
      ← localPoint_mul_comm F (r + 1) v u.val hX, mul_assoc]
    exact hcov
  have hb := finiteComponent_unfoldingWeyl_mem h v
  have hK (Q : FiniteLocalGL F (r + 1) v) (k : FiniteLocalGL F (r + 1) v)
      (hk : k ∈ Conductor.integralSubgroup (canonicalValuation v).integer r) :
      f (Q * k) = f Q := by
    let k' := b⁻¹ * k * b
    have hk' : k' ∈ Conductor.integralSubgroup (canonicalValuation v).integer r :=
      (Conductor.integralSubgroup (canonicalValuation v).integer r).mul_mem
        ((Conductor.integralSubgroup (canonicalValuation v).integer r).mul_mem
          ((Conductor.integralSubgroup (canonicalValuation v).integer r).inv_mem hb) hk) hb
    have hk'' := ContragredientDual.inverseTranspose_mem_localIntegral F (r + 1) v
      ((localIntegral_iff_canonical v r k').mpr hk')
    have he : Q * k * b = (Q * b) * k' := by dsimp [k']; group
    unfold f
    rw [he, localPoint_mul, ← mul_assoc, Unfolding.dualFunction_eq,
      ContragredientDualSplit.dualPoint_mul_localPoint]
    let k'' := inverseTranspose (r + 1) (FiniteCompletion F v) k'
    have hact := UnramifiedWhittaker.cuspWhittaker_finiteRepresentation F ψ.complex T
      (localInclusion F (r + 1) v k'') x
      (Unfolding.dualPoint F (r + 1) (X * localPoint F (r + 1) v (Q * b)))
    rw [hx v hv k'' hk''] at hact
    exact hact.symm
  have hz := RectangularSupport.apply_rectGL (v := canonicalValuation v)
    (χ := fun z => (ψv.complex z)⁻¹) h hθ hχ hf hK
    (finiteComponent F (t + 1) v g) (localRectCoordinates F v y)
  rw [ite_eq_right (fun hy' => hy ((localRect_mem_canonical_iff v y).mp hy'))] at hz
  have hp : RectangularSupport.rectGL h (finiteComponent F (t + 1) v g)
      (localRectCoordinates F v y) * b = finiteComponent F (r + 1) v (p * unfoldingWeyl F h) := by
    rw [UnipotentClass.finiteComponent_mul, UnequalDualEuler.finiteComponent_rectangularPoint]
    rfl
  unfold f at hz
  rw [hp] at hz
  change dualFunction F (r + 1) W (p * unfoldingWeyl F h) = 0
  simpa only [X, inv_mul_cancel_right] using hz

end Support

end Langlands.Global.RankinSelbergGlobal.UnequalWhittakerProducts
