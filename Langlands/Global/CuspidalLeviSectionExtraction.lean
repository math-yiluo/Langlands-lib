import Langlands.Automorphic.CuspidalOperatorDirectSum
import Langlands.Automorphic.ProjectedBlockSectionKernel
import Langlands.Global.Factors.CuspidalSupportInducedReduction
import Langlands.Global.FiniteParametrizedCuspidalNormalization
import Langlands.Global.FiniteParametrizedSectionIntertwiner
import Langlands.Global.FiniteParametrizedSectionSupport
import Langlands.Representation.TensorProduct.FiniteSupportCoordinates
import Langlands.Representation.TensorProduct.ProductFunctionSlices

/-! Extraction of a normalized induced subquotient from actual cuspidal Levi tensors. -/

noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global

open Automorphic ArchimedeanGL FiniteParametrizedBlockInduction FiniteVectors GeneralLinear
  _root_.Representation

attribute [local instance] subquotientRationalGroup subquotientContinuousGroup
  subquotientSmoothGroup subquotientFormGroup subquotientStableGroup subquotientRealizationGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r k : ℕ} {m : Fin k → ℕ} (hm : ∑ i, (m i + 1) = r + 1)

local notation "B" => (⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩ : BlockShape (r + 1))

variable (ν : Fin k → HeckeCharacter F)

/-- Restore the block character twists, then absorb the inverse half modulus
in the resulting genuine cuspidal realizations. -/
def cuspidalLeviSectionBlocks (T : ∀ i, CuspidalOperatorRealization F (m i)) :
    ∀ i, CuspidalOperatorRealization F (m i) :=
  normalizedCuspidalBlocks hm (fun i => (T i).heckeDeterminantTwist (ν i))

/-- The product of the restoring determinant characters on the finite Levi. -/
def cuspidalLeviRestoringScalar (p : AdelicBlockParabolic.Finite F B) : ℂ :=
  ∏ i, ((ν i).finiteAdelicDeterminant (m i + 1) ((B).leviProjection (FiniteAdeles F) p i) : ℂ)

private def restoredCoefficientEquiv (T : ∀ i, CuspidalOperatorRealization F (m i)) :
    PiTensorProduct ℂ (fun i => (T i).realization.Space) ≃ₗ[ℂ]
      PiTensorProduct ℂ (fun i => ((T i).heckeDeterminantTwist (ν i)).realization.Space) :=
  PiTensorProduct.congr fun i => ((T i).realization.heckeDeterminantTwistEquiv (ν i)).toLinearEquiv

private theorem tensorEquiv_scalar_covariance {I : Type*} [Fintype I] [DecidableEq I]
    {U W : I → Type*} [∀ i, AddCommGroup (U i)] [∀ i, Module ℂ (U i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (E : ∀ i, U i ≃ₗ[ℂ] W i) (a : ∀ i, Module.End ℂ (U i))
    (b : ∀ i, Module.End ℂ (W i)) (c : I → ℂ)
    (h : ∀ i v, b i (E i v) = c i • E i (a i v)) (t : PiTensorProduct ℂ U) :
    PiTensorProduct.congr E ((∏ i, c i) • PiTensorProduct.map a t) =
      PiTensorProduct.map b (PiTensorProduct.congr E t) := by
  let e := (PiTensorProduct.congr E).toLinearMap
  have he : e ∘ₗ ((∏ i, c i) • PiTensorProduct.map a) = PiTensorProduct.map b ∘ₗ e := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change e ((∏ i, c i) • PiTensorProduct.map a (PiTensorProduct.tprod ℂ v)) =
      PiTensorProduct.map b (e (PiTensorProduct.tprod ℂ v))
    simp only [e, map_smul, PiTensorProduct.map_tprod, LinearEquiv.coe_coe,
      PiTensorProduct.congr_tprod, h, (PiTensorProduct.tprod ℂ).map_smul_univ]
  exact LinearMap.congr_fun he t

private theorem restoredCoefficientEquiv_covariance
    (T : ∀ i, CuspidalOperatorRealization F (m i)) (p : AdelicBlockParabolic.Finite F B)
    (t : PiTensorProduct ℂ (fun i => (T i).realization.Space)) :
    restoredCoefficientEquiv ν T (cuspidalLeviRestoringScalar hm ν p •
      (B).blockTensor (fun i => (T i).realization.finiteRepresentation)
        ((B).leviProjection (FiniteAdeles F) p) t) =
    (B).blockTensor (fun i => ((T i).heckeDeterminantTwist (ν i)).realization.finiteRepresentation)
      ((B).leviProjection (FiniteAdeles F) p) (restoredCoefficientEquiv ν T t) := by
  let d := (B).leviProjection (FiniteAdeles F) p
  exact tensorEquiv_scalar_covariance
    (fun i => ((T i).realization.heckeDeterminantTwistEquiv (ν i)).toLinearEquiv)
    (fun i => (T i).realization.finiteRepresentation (d i))
    (fun i => ((T i).heckeDeterminantTwist (ν i)).realization.finiteRepresentation (d i))
    (fun i => ((ν i).finiteAdelicDeterminant (m i + 1) (d i) : ℂ))
    (fun i x => (T i).realization.heckeDeterminantTwistEquiv_finite (ν i) (d i) x) t

attribute [local instance 100] LieRing.ofAssociativeRing

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (A : automorphicOperatorAlgebra F (r + 1) →ₐ[ℂ] Module.End ℂ V)

local notation "ρf" => A.toMonoidHom.comp (finiteOperator F (r + 1))
local notation "ρc" => A.toMonoidHom.comp (compactOperator F (r + 1))
local notation "L" => operatorAlgebraComplexLieAction A

omit [CompactSpace (AdeleQuotient F)] in
private theorem coefficient_finite_compact (g : FiniteAdelicGL F (r + 1))
    (h : standardInfiniteCompact F (r + 1)) (x : V) :
    ρf g (ρc h x) = ρc h (ρf g x) := by
  have he : finiteOperator F (r + 1) g * compactOperator F (r + 1) h =
      compactOperator F (r + 1) h * finiteOperator F (r + 1) g := by
    apply Subtype.ext
    change finiteSmoothRightAction F (r + 1) (AdelicGL.ofFinite F (r + 1) g) *
        finiteSmoothRightAction F (r + 1) (AdelicGL.ofInfinite F (r + 1) h.val) =
      finiteSmoothRightAction F (r + 1) (AdelicGL.ofInfinite F (r + 1) h.val) *
        finiteSmoothRightAction F (r + 1) (AdelicGL.ofFinite F (r + 1) g)
    rw [← map_mul, ← map_mul, AdelicGL.ofInfinite_commute]
  exact LinearMap.congr_fun (by simpa only [map_mul] using congrArg A he) x

omit [CompactSpace (AdeleQuotient F)] in
set_option maxHeartbeats 850000 in
private theorem exists_sectionSubquotient (B₀ : BlockShape (r + 1))
    {Q J₀ : Type*} [AddCommGroup Q] [Module ℂ Q]
    {τ : Representation ℂ (automorphicOperatorAlgebra F (r + 1)) Q} [τ.IsIrreducible]
    (q : IntertwiningMap A.toMonoidHom τ) (hq : Function.Surjective q)
    (v : V) (hv : orbitSpan A.toMonoidHom v = ⊤)
    (hκ : IsFiniteVector ρc v) (hρ : IsSmooth ρf)
    (hderiv : CompactDualDerivative ρc L)
    {W : J₀ → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    {U : J₀ → Fin B₀.length → Type*} [∀ j i, AddCommGroup (U j i)] [∀ j i, Module ℂ (U j i)]
    (σ₀ : ∀ j i, Representation ℂ (FiniteAdelicGL F (B₀.size i)) (U j i))
    (e₀ : ∀ j, V →ₗ[ℂ] W j) (e₁ : ∀ j, V →ₗ[ℂ] PiTensorProduct ℂ (U j))
    (hzero : ∀ j x, e₁ j x = 0 ↔ e₀ j x = 0)
    (hpoint : ∀ x, {j | e₀ j x ≠ 0}.Finite)
    (hkill : ∀ x, (∀ j l g, e₀ j (ρc l (ρf g x)) = 0) → q x = 0)
    (hpar : ∀ j (p : AdelicBlockParabolic.Finite F B₀) x,
      e₁ j (ρf p.val x) = finiteCoefficient F B₀ (σ₀ j) p (e₁ j x))
    (hU : ∀ j X x, IsStrictUpperBlockLie F B₀ X → e₀ j (L (complexify F (r + 1) X) x) = 0)
    (hD : ∀ j i (X : RealLieAlgebra F (B₀.size i)) x, e₀ j x = 0 →
      e₀ j (L (complexify F (r + 1) (blockShapeRealLieInclusion F B₀ i X)) x) = 0) :
    ∃ j, HasSubquotient B₀ (σ₀ j) (τ.comp (finiteOperator F (r + 1))) := by
  classical
  let E (j : J₀) (l : standardInfiniteCompact F (r + 1)) (g : FiniteAdelicGL F (r + 1)) :=
    (e₁ j).comp ((ρc l).comp (ρf g))
  have hEpar (j : J₀) (l : standardInfiniteCompact F (r + 1)) (p : AdelicBlockParabolic.Finite F B₀)
      (g : FiniteAdelicGL F (r + 1)) (x : V) :
      E j l (p.val * g) x = finiteCoefficient F B₀ (σ₀ j) p (E j l g x) := by
    change e₁ j (ρc l (ρf (p.val * g) x)) = finiteCoefficient F B₀ (σ₀ j) p
      (e₁ j (ρc l (ρf g x)))
    rw [map_mul, Module.End.mul_apply, ← coefficient_finite_compact A p.val, hpar]
  have hEtrans (j : J₀) (l : standardInfiniteCompact F (r + 1)) (g d : FiniteAdelicGL F (r + 1))
      (x : V) : E j l g (ρf d x) = E j l (g * d) x := by
    simp only [E, map_mul, Module.End.mul_apply, LinearMap.comp_apply]
  let Y (j : J₀) : Type _ := Sections F B₀ (σ₀ j)
  let addY : ∀ j, AddCommGroup (Y j) := fun _ => Submodule.addCommGroup _
  let moduleY : ∀ j, Module ℂ (Y j) := fun _ => Submodule.module _
  let σI (j : J₀) : Representation ℂ (FiniteAdelicGL F (r + 1)) (Y j) :=
    induced F B₀ (σ₀ j)
  let f (j : J₀) : IntertwiningMap ρf (σI j) :=
    linearEvaluationIntertwiner B₀ (σ₀ j) hρ (E j) (hEpar j) (hEtrans j)
  have hfzero (j : J₀) (x : V) : f j x = 0 ↔ ∀ l g, E j l g x = 0 :=
    linearEvaluationIntertwiner_eq_zero_iff B₀ (σ₀ j) hρ (E j) (hEpar j) (hEtrans j) x
  let K (j : J₀) := projectedBlockSectionKernel A B₀ (e₀ j) hderiv (hU j) (hD j)
  have hK (j : J₀) (x : V) : x ∈ K j ↔ f j x = 0 :=
    (mem_projectedBlockSectionKernel A B₀ (e₀ j) hderiv (hU j) (hD j) x).trans
      ((forall_congr' fun l => forall_congr' fun g => (hzero j (ρc l (ρf g x))).symm).trans
        (hfzero j x).symm)
  have hEpoint (g : FiniteAdelicGL F (r + 1)) (x : V) : {j | E j 1 g x ≠ 0}.Finite :=
    (hpoint (ρc 1 (ρf g x))).subset fun j hj hz => hj ((hzero j _).mpr hz)
  have hEcompact (j : J₀) (l : standardInfiniteCompact F (r + 1)) (g : FiniteAdelicGL F (r + 1))
      (x : V) : E j l g x = E j 1 g (ρc l x) := by
    simp only [E, LinearMap.comp_apply, map_one, Module.End.one_apply, coefficient_finite_compact A]
  have hsupport : {j | f j v ≠ 0}.Finite := by
    apply (finiteSectionEvaluationSupport B₀ ρc ρf E hEpoint hEcompact hEtrans
      (fun j l p g x hz => by rw [hEpar, hz, map_zero]) v hκ (hρ v)).subset
    intro j hj
    by_contra hn
    exact hj ((hfzero j v).mpr (fun l g => by
      by_contra hz
      exact hn ⟨l, g, hz⟩))
  have hsep : ∀ x, (∀ j, f j x = 0) → q x = 0 :=
    fun x hx => hkill x (fun j l g => (hzero j _).mp ((hfzero j x).mp (hx j) l g))
  change ∃ j, Correspondence.IsSubquotientOf (σI j) (τ.comp (finiteOperator F (r + 1)))
  exact @exists_subquotient_of_cyclicProjections (automorphicOperatorAlgebra F (r + 1))
    (FiniteAdelicGL F (r + 1)) V Q J₀ inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance Y addY moduleY A.toMonoidHom τ inferInstance
    (finiteOperator F (r + 1)) q hq σI f K hK hsep v hv hsupport

private theorem projectedCoordinateDerivative_eq_zero
    {I : Type*} [DecidableEq I] {U W : I → Type*}
    [∀ i, AddCommGroup (U i)] [∀ i, Module ℂ (U i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (p : ∀ i, U i →ₗ[ℂ] W i) (i : I)
    (a : Module.End ℂ (U i)) (b : Module.End ℂ (W i))
    (hp : (p i).comp a = b.comp (p i))
    (s t : PiTensorProduct ℂ U) (c : ℂ)
    (h : s = tensorCoordinateEnd i a t + c • t) (ht : PiTensorProduct.map p t = 0) :
    PiTensorProduct.map p s = 0 := by
  rw [h, map_add, map_smul, tensorCoordinateEnd_intertwines p i a b hp, ht,
    map_zero, smul_zero, add_zero]

variable (S : ∀ i : Fin k, OperatorRealization F (m i + 1))
  (D : ∀ i, CuspidalOperatorDirectSum (S i))

local notation "C" => PiTensorProduct ℂ (fun i => (S i).Space)
local notation "J" => (∀ i, (D i).Index)
local notation "σ" => (fun i => (S i).finiteRepresentation)

private abbrev factorTuple (j : J) : ∀ i, CuspidalOperatorRealization F (m i) :=
  fun i => (D i).factor (j i)

local instance leviExtractionSourceGroups : ∀ i, AddCommGroup (S i).Space :=
  fun _ => Submodule.addCommGroup _
local instance leviExtractionFactorGroups (j : J) :
    ∀ i, AddCommGroup ((factorTuple S D j) i).realization.Space :=
  fun _ => Submodule.addCommGroup _
local instance leviExtractionNormalizedGroups (j : J) :
    ∀ i, AddCommGroup (cuspidalLeviSectionBlocks hm ν (factorTuple S D j) i).realization.Space :=
  fun _ => Submodule.addCommGroup _

private def projectCoefficient (j : J) :
    ((B).blockTensor σ).IntertwiningMap ((B).blockTensor
      (fun i => ((factorTuple S D j) i).realization.finiteRepresentation)) :=
  FiniteTensor.externalMap fun i =>
    { toLinearMap := ((D i).project (j i)).toLinearMap
      isIntertwining' := fun g => ((D i).project (j i)).isIntertwining'
        (finiteOperator F (m i + 1) g) }

private def normalizedProjectCoefficient (j : J) :
    C →ₗ[ℂ] PiTensorProduct ℂ (fun i => (cuspidalLeviSectionBlocks hm ν (factorTuple S D j) i).realization.Space) :=
  (normalizedCuspidalCoefficientEquiv hm (fun i =>
      ((factorTuple S D j) i).heckeDeterminantTwist (ν i))).toLinearEquiv.toLinearMap ∘ₗ
    (restoredCoefficientEquiv ν (factorTuple S D j)).toLinearMap ∘ₗ
      (projectCoefficient hm S D j).toLinearMap

set_option maxHeartbeats 2200000 in
set_option synthInstance.maxHeartbeats 90000 in
private theorem normalizedProjectCoefficient_covariance (j : J)
    (p : AdelicBlockParabolic.Finite F B) (t : C) :
    normalizedProjectCoefficient hm ν S D j (cuspidalLeviRestoringScalar hm ν p •
      (B).blockTensor σ ((B).leviProjection (FiniteAdeles F) p) t) =
    finiteCoefficient F B (fun i => (cuspidalLeviSectionBlocks hm ν (factorTuple S D j) i).realization.finiteRepresentation)
      p (normalizedProjectCoefficient hm ν S D j t) := by
  let T := factorTuple S D j
  let a := (B).leviProjection (FiniteAdeles F) p
  let P := projectCoefficient hm S D j
  let N := normalizedCuspidalCoefficientEquiv hm (fun i => (T i).heckeDeterminantTwist (ν i))
  let E := restoredCoefficientEquiv ν T
  change N (E (P (cuspidalLeviRestoringScalar hm ν p • (B).blockTensor σ a t))) = _
  have hP := IntertwiningMap.isIntertwining _ _ P a t
  have he := P.toLinearMap.map_smul (cuspidalLeviRestoringScalar hm ν p) ((B).blockTensor σ a t)
  exact (congrArg (fun y => N (E y))
    (he.trans (congrArg (cuspidalLeviRestoringScalar hm ν p • ·) hP))).trans
    ((congrArg N (restoredCoefficientEquiv_covariance hm ν T p (P t))).trans
      (IntertwiningMap.isIntertwining _ _ N.toIntertwiningMap p (E (P t))))

set_option maxHeartbeats 1300000 in
set_option synthInstance.maxHeartbeats 90000 in
private theorem normalizedProjectCoefficient_eq_zero_iff (j : J) (t : C) :
    normalizedProjectCoefficient hm ν S D j t = 0 ↔ projectCoefficient hm S D j t = 0 := by
  let P := projectCoefficient hm S D j
  let E := (restoredCoefficientEquiv ν (factorTuple S D j))
  let N := (normalizedCuspidalCoefficientEquiv hm (fun i =>
    ((factorTuple S D j) i).heckeDeterminantTwist (ν i))).toLinearEquiv
  change N (E (P t)) = 0 ↔ P t = 0
  exact (N.map_eq_zero_iff (x := E (P t))).trans (E.map_eq_zero_iff (x := P t))

include D in
set_option maxHeartbeats 3500000 in
set_option synthInstance.maxHeartbeats 140000 in
/-- Extract the simple finite subquotient from a single projected cuspidal
Levi tensor. The restoring scalar accounts for the characters used to
unitarize the coefficient carriers. -/
theorem exists_finiteParametrizedSubquotient_of_cuspidalLeviCoefficients
    {Q : Type*} [AddCommGroup Q] [Module ℂ Q]
    {τ : Representation ℂ (automorphicOperatorAlgebra F (r + 1)) Q} [τ.IsIrreducible]
    (q : IntertwiningMap A.toMonoidHom τ) (hq : Function.Surjective q)
    (v : V) (hv : orbitSpan A.toMonoidHom v = ⊤)
    (hκ : IsFiniteVector ρc v) (hρ : IsSmooth ρf)
    (hderiv : CompactDualDerivative ρc L)
    (e : V →ₗ[ℂ] C)
    (hkill : ∀ x, (∀ l g, e (ρc l (ρf g x)) = 0) → q x = 0)
    (hcov : ∀ (p : AdelicBlockParabolic.Finite F B) x,
      e (ρf p.val x) = cuspidalLeviRestoringScalar hm ν p •
        (B).blockTensor σ ((B).leviProjection (FiniteAdeles F) p) (e x))
    (hupper : ∀ X x, IsStrictUpperBlockLie F B X → e (L (complexify F (r + 1) X) x) = 0)
    (hblock : ∀ i (X : RealLieAlgebra F (m i + 1)) x,
      ∃ c : ℂ, e (L (complexify F (r + 1) (blockShapeRealLieInclusion F B i X)) x) =
        tensorCoordinateEnd i ((S i).complexLieAction (complexify F (m i + 1) X)) (e x) + c • e x) :
    ∃ T : ∀ i, CuspidalOperatorRealization F (m i), HasSubquotient B
      (fun i => (T i).realization.finiteRepresentation) (τ.comp (finiteOperator F (r + 1))) := by
  classical
  let T (j : J) := cuspidalLeviSectionBlocks hm ν (factorTuple S D j)
  let σ' (j : J) := fun i => (T j i).realization.finiteRepresentation
  let e₀ (j : J) := (projectCoefficient hm S D j).toLinearMap ∘ₗ e
  let e₁ (j : J) := (normalizedProjectCoefficient hm ν S D j).comp e
  have hzero (j : J) (x : V) : e₁ j x = 0 ↔ e₀ j x = 0 :=
    normalizedProjectCoefficient_eq_zero_iff hm ν S D j (e x)
  have hpar (j : J) (p : AdelicBlockParabolic.Finite F B) (x : V) :
      e₁ j (ρf p.val x) = finiteCoefficient F B (σ' j) p (e₁ j x) :=
    (congrArg (normalizedProjectCoefficient hm ν S D j) (hcov p x)).trans
      (normalizedProjectCoefficient_covariance hm ν S D j p (e x))
  have hU (j : J) (X : RealLieAlgebra F (r + 1)) (x : V) (hX : IsStrictUpperBlockLie F B X) :
      e₀ j (L (complexify F (r + 1) X) x) = 0 := by
    simp only [e₀, LinearMap.comp_apply, hupper X x hX, map_zero]
  have hD (j : J) (i : Fin k) (X : RealLieAlgebra F (m i + 1)) (x : V) (hx : e₀ j x = 0) :
      e₀ j (L (complexify F (r + 1) (blockShapeRealLieInclusion F B i X)) x) = 0 := by
    let p (b : Fin k) := ((D b).project (j b)).toLinearMap
    let a := (S i).complexLieAction (complexify F (m i + 1) X)
    let b := ((factorTuple S D j) i).realization.complexLieAction (complexify F (m i + 1) X)
    have hp : (p i).comp a = b.comp (p i) :=
      ((D i).project (j i)).isIntertwining'
        (differentialOperator F (m i + 1) (envelopingGenerator F (m i + 1) (complexify F (m i + 1) X)))
    obtain ⟨c, hc⟩ := hblock i X x
    change PiTensorProduct.map p (e (L (complexify F (r + 1) (blockShapeRealLieInclusion F B i X)) x)) = 0
    change PiTensorProduct.map p (e x) = 0 at hx
    exact projectedCoordinateDerivative_eq_zero p i a b hp _ (e x) c hc hx
  let p (i : Fin k) (j : (D i).Index) := ((D i).project j).toLinearMap
  have hfin (i : Fin k) (x : (S i).Space) : ∃ s : Finset ((D i).Index), ∀ j ∉ s, p i j x = 0 := by
    obtain ⟨s, hn, _⟩ := (D i).finite_sum x
    exact ⟨s, hn⟩
  have hpoint (x : V) : {j | e₀ j x ≠ 0}.Finite :=
    finiteSupportTensorCoordinateMap_finite p hfin (e x)
  have hsep (x : V) (hx : ∀ j l g, e₀ j (ρc l (ρf g x)) = 0) : q x = 0 := by
    apply hkill x
    intro l g
    exact finiteSupportTensorCoordinateMap_detects p hfin
      (fun i y hy => CuspidalOperatorDirectSum.project_eq_zero_detects (S i) (D i) y hy)
      _ (fun j => hx j l g)
  obtain ⟨j, hj⟩ := exists_sectionSubquotient A B q hq v hv hκ hρ hderiv σ'
    e₀ e₁ hzero hpoint hsep hpar hU hD
  exact ⟨T j, hj⟩

end Langlands.Global
