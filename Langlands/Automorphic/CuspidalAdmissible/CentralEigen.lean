import Langlands.Automorphic.CuspidalAdmissible.Finiteness
import Langlands.Algebra.LieCasimir
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # A central law from an eigenvector of the central archimedean derivative -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct Matrix.Norms.Operator
open NumberField

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

/-- The identity matrix as a real Lie algebra direction. -/
def unitDirection : RealLieAlgebra K n := (realLieAlgebraToMatrix K n).symm 1

@[simp]
theorem realLieAlgebraToMatrix_unitDirection :
    realLieAlgebraToMatrix K n (unitDirection K n) = 1 :=
  (realLieAlgebraToMatrix K n).apply_symm_apply 1

theorem unitDirection_lie (X : RealLieAlgebra K n) : ⁅unitDirection K n, X⁆ = 0 := by
  apply (realLieAlgebraToMatrix K n).injective
  rw [realLieAlgebraToMatrix_lie, realLieAlgebraToMatrix_unitDirection, one_mul, mul_one,
    sub_self, map_zero]

theorem complexify_unitDirection_lie (X : ComplexLieAlgebra K n) :
    ⁅complexify K n (unitDirection K n), X⁆ = 0 := by
  induction X using TensorProduct.inductionOn with
  | tmul z Y =>
    rw [complexify_apply, complexLieAlgebra_lie_tmul, unitDirection_lie, TensorProduct.tmul_zero]
  | add X Y hX hY =>
    exact (lie_add (L := ComplexLieAlgebra K n) (M := ComplexLieAlgebra K n) _ X Y).trans
      (by rw [hX, hY, add_zero])

/-- The enveloping generator of the central direction `1`. -/
def centralGenerator : EnvelopingAlgebra K n :=
  envelopingGenerator K n (complexify K n (unitDirection K n))

theorem centralGenerator_mem_center :
    centralGenerator K n ∈ Subalgebra.center ℂ (EnvelopingAlgebra K n) := by
  let S := Subalgebra.centralizer ℂ {centralGenerator K n}
  have hcomplex (X : ComplexLieAlgebra K n) : envelopingGenerator K n X ∈ S := by
    apply (Subalgebra.mem_centralizer_iff ℂ).mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    have h := envelopingGenerator_lie K n (complexify K n (unitDirection K n)) X
    rw [complexify_unitDirection_lie, map_zero] at h
    exact (sub_eq_zero.mp h.symm)
  have hle : Algebra.adjoin ℂ (Set.range (envelopingGenerator K n)) ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨X, rfl⟩
    exact hcomplex X
  rw [Subalgebra.mem_center_iff]
  intro a
  have ha : a ∈ Algebra.adjoin ℂ (Set.range (envelopingGenerator K n)) := by
    change a ∈ Algebra.adjoin ℂ
      (Set.range (UniversalEnvelopingAlgebra.ι ℂ :
        ComplexLieAlgebra K n → EnvelopingAlgebra K n))
    rw [Langlands.Algebra.LieCasimir.enveloping_adjoin_range]
    trivial
  exact ((Subalgebra.mem_centralizer_iff ℂ).mp (hle ha) _ (Set.mem_singleton _)).symm

/-- The central generator as an element of the enveloping center. -/
def centralElement : EnvelopingCenter K n :=
  ⟨centralGenerator K n, centralGenerator_mem_center K n⟩

end Langlands.Global.ArchimedeanGL

namespace Langlands.Automorphic.OperatorRealization

open Langlands.Global Langlands.Automorphic.CuspidalL2 ContinuousRationalFunctions

/-- A solution of `h' = λ h` on the real line is `h t = e^{λ t} h 0`. -/
theorem eq_exp_mul_of_hasDerivAt {h : ℝ → ℂ} {lam : ℂ}
    (hd : ∀ t, HasDerivAt h (lam * h t) t) (t : ℝ) :
    h t = Complex.exp (lam * t) * h 0 := by
  let k : ℝ → ℂ := fun s => Complex.exp (-(lam * (s : ℂ))) * h s
  have hk : ∀ s, HasDerivAt k 0 s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => -(lam * (s : ℂ))) (-(lam * 1)) s :=
      ((hasDerivAt_id s).ofReal_comp.const_mul lam).neg
    have h2 := h1.cexp.mul (hd s)
    convert h2 using 1
    ring
  have hc := is_const_of_deriv_eq_zero (fun s => (hk s).differentiableAt)
    (fun s => (hk s).deriv) t 0
  simp only [k, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul] at hc
  rw [← hc, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

omit [NumberField F] in
theorem ringEquiv_mixedSpace_infiniteRealEmbedding (r : ℝ) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (PositiveRealIdeles.infiniteRealEmbedding F r) =
      r • (1 : mixedEmbedding.mixedSpace F) := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · apply Complex.ofReal_injective
    change ((InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2
      (PositiveRealIdeles.realEmbedding F v.1 r) : ℝ) : ℂ) = ((r * 1 : ℝ) : ℂ)
    rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply,
      PositiveRealIdeles.extensionEmbedding_realEmbedding, mul_one]
  · change InfinitePlace.Completion.extensionEmbedding v.1
      (PositiveRealIdeles.realEmbedding F v.1 r) = r • (1 : ℂ)
    rw [PositiveRealIdeles.extensionEmbedding_realEmbedding, Complex.real_smul, mul_one]

omit [NumberField F] in
variable (F n) in
/-- In mixed coordinates, right translation by `e^t · 1` is multiplication by `e^t`. -/
theorem archimedeanGLCoordinates_mul_torInf (a : InfiniteAdelicGL F n) (t : ℝ) :
    ((archimedeanGLCoordinates F n (a * torInf F n fun _ => t) : ArchimedeanGL F n) :
        ArchimedeanMatrix F n) =
      Real.exp t • ((archimedeanGLCoordinates F n a : ArchimedeanGL F n) :
        ArchimedeanMatrix F n) := by
  rw [map_mul, Units.val_mul]
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Matrix.smul_apply, Finset.sum_eq_single j]
  · rw [archimedeanGLCoordinates_apply F n (torInf F n fun _ => t), torInf_val,
      Matrix.diagonal_apply_eq, ringEquiv_mixedSpace_infiniteRealEmbedding, mul_smul_comm,
      mul_one]
  · intro k _ hkj
    rw [archimedeanGLCoordinates_apply F n (torInf F n fun _ => t), torInf_val,
      Matrix.diagonal_apply_ne _ hkj, map_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

open scoped Classical in
/-- **Central law for smooth functions.** A smooth function with `D₁ s = λ s` for the central
direction `1` satisfies `s(a · e^t) = e^{λ t} s(a)`. -/
theorem smooth_mul_torInf_of_differential (s : ArchimedeanGL.SmoothFunctions F n) (lam : ℂ)
    (hs : ArchimedeanGL.smoothDifferential F n (ArchimedeanGL.unitDirection F n) s = lam • s)
    (a : InfiniteAdelicGL F n) (t : ℝ) :
    s.val (a * torInf F n fun _ => t) = Complex.exp (lam * t) * s.val a := by
  have hE : ∀ t : ℝ, s.val (a * torInf F n fun _ => t) =
      ArchimedeanGL.coordinateExtension F n s (Real.exp t •
        ((archimedeanGLCoordinates F n a : ArchimedeanGL F n) : ArchimedeanMatrix F n)) := by
    intro t
    rw [← archimedeanGLCoordinates_mul_torInf F n a t, ArchimedeanGL.coordinateExtension_apply,
      ContinuousMulEquiv.symm_apply_apply]
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => s.val (a * torInf F n fun _ => t))
      (lam * s.val (a * torInf F n fun _ => t)) t := by
    intro t
    have hfun : (fun t : ℝ => s.val (a * torInf F n fun _ => t)) =
        fun t : ℝ => ArchimedeanGL.coordinateExtension F n s (Real.exp t •
          ((archimedeanGLCoordinates F n a : ArchimedeanGL F n) : ArchimedeanMatrix F n)) :=
      funext hE
    rw [hfun]
    have hγ : HasDerivAt (fun t : ℝ => Real.exp t •
          ((archimedeanGLCoordinates F n a : ArchimedeanGL F n) : ArchimedeanMatrix F n))
        (Real.exp t • ((archimedeanGLCoordinates F n a : ArchimedeanGL F n) :
          ArchimedeanMatrix F n)) t :=
      (Real.hasDerivAt_exp t).smul_const (F := ArchimedeanMatrix F n)
        ((archimedeanGLCoordinates F n a : ArchimedeanGL F n) : ArchimedeanMatrix F n)
    have hdiff : DifferentiableAt ℝ (ArchimedeanGL.coordinateExtension F n s)
        (Real.exp t • ((archimedeanGLCoordinates F n a : ArchimedeanGL F n) :
          ArchimedeanMatrix F n)) := by
      rw [← archimedeanGLCoordinates_mul_torInf F n a t]
      exact (ArchimedeanGL.coordinateExtension_contDiffAt F n s _).differentiableAt (by simp)
    have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt t hγ
    have hval : fderiv ℝ (ArchimedeanGL.coordinateExtension F n s)
        (Real.exp t • ((archimedeanGLCoordinates F n a : ArchimedeanGL F n) :
          ArchimedeanMatrix F n))
        (Real.exp t • ((archimedeanGLCoordinates F n a : ArchimedeanGL F n) :
          ArchimedeanMatrix F n)) =
        lam * s.val (a * torInf F n fun _ => t) := by
      have h1 := ArchimedeanGL.smoothDifferential_apply F n (ArchimedeanGL.unitDirection F n) s
        (a * torInf F n fun _ => t)
      rw [ArchimedeanGL.realLieAlgebraToMatrix_unitDirection, mul_one,
        archimedeanGLCoordinates_mul_torInf F n a t, hs] at h1
      exact h1.symm
    rw [← hval]
    exact hcomp
  have h := eq_exp_mul_of_hasDerivAt hd t
  have h0 : (torInf F n fun _ => (0 : ℝ)) = 1 := torInf_zero F n
  rw [h, h0, mul_one]

variable (S : OperatorRealization F n)

local instance cuspidalAdmCentralAddCommGroupRationalInvariant :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance cuspidalAdmCentralAddCommGroupContinuousRational :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance cuspidalAdmCentralAddCommGroupFiniteSmoothRational :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance cuspidalAdmCentralAddCommGroupAutomorphicForms :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance cuspidalAdmCentralAddCommGroupStableAutomorphic :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance cuspidalAdmCentralAddCommGroupSpace : AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- The slice of the central derivative is the central directional derivative of the slice. -/
theorem finiteSmoothSlice_centralGenerator (f : S.Space) (y : FiniteAdelicGL F n) :
    finiteSmoothSlice F n y (S.ambient (S.envelopingAction (ArchimedeanGL.centralGenerator F n) f)) =
      ArchimedeanGL.smoothDifferential F n (ArchimedeanGL.unitDirection F n)
        (finiteSmoothSlice F n y (S.ambient f)) := by
  rw [S.ambient_envelopingAction, finiteSmoothSlice_envelopingAction,
    ArchimedeanGL.centralGenerator, ArchimedeanGL.envelopingAction_real_generator]

/-- **Central law.** An eigenvector of the central derivative with eigenvalue `λ` satisfies
`f(g · (e^t · 1)) = e^{λ t} f(g)`. -/
theorem evaluate_mul_centralTorus (lam : ℂ) (f : S.Space)
    (hf : S.envelopingAction (ArchimedeanGL.centralGenerator F n) f = lam • f)
    (g : AdelicGL F n) (t : ℝ) :
    evaluate F n (S.toContinuous f) (g * centralTorus F n t) =
      Complex.exp (lam * t) * evaluate F n (S.toContinuous f) g := by
  have hs : ArchimedeanGL.smoothDifferential F n (ArchimedeanGL.unitDirection F n)
      (finiteSmoothSlice F n (AdelicGL.finite F n g) (S.ambient f)) =
      lam • finiteSmoothSlice F n (AdelicGL.finite F n g) (S.ambient f) := by
    rw [← S.finiteSmoothSlice_centralGenerator, hf, ← map_smul]
    rfl
  have key := smooth_mul_torInf_of_differential _ lam hs (AdelicGL.infinite F n g) t
  rw [S.finiteSmoothSlice_ambient_apply, S.finiteSmoothSlice_ambient_apply,
    ← AdelicGL.eq_ofInfinite_mul_ofFinite] at key
  rw [← key]
  congr 1
  conv_lhs => rw [AdelicGL.eq_ofInfinite_mul_ofFinite F n g]
  rw [centralTorus, map_mul, mul_assoc, mul_assoc,
    AdelicGL.ofInfinite_commute F n (torInf F n fun _ => t)]

theorem finiteRepresentation_centralEigen (lam : ℂ) (d : FiniteAdelicGL F n) (f : S.Space)
    (hf : S.envelopingAction (ArchimedeanGL.centralGenerator F n) f = lam • f) :
    S.envelopingAction (ArchimedeanGL.centralGenerator F n) (S.finiteRepresentation d f) =
      lam • S.finiteRepresentation d f := by
  calc S.envelopingAction (ArchimedeanGL.centralGenerator F n) (S.finiteRepresentation d f)
      = S.finiteRepresentation d (S.envelopingAction (ArchimedeanGL.centralGenerator F n) f) :=
        (S.finiteRepresentation_envelopingAction d _ f).symm
    _ = S.finiteRepresentation d (lam • f) := congrArg _ hf
    _ = lam • S.finiteRepresentation d f := map_smul _ _ _

/-- The eigenspace of the central derivative, a subrepresentation of the finite action. -/
def centralEigenspace (lam : ℂ) : Subrepresentation S.finiteRepresentation where
  toSubmodule := Module.End.eigenspace (S.envelopingAction (ArchimedeanGL.centralGenerator F n)) lam
  apply_mem_toSubmodule d f hf := Module.End.mem_eigenspace_iff.mpr
    (S.finiteRepresentation_centralEigen lam d f (Module.End.mem_eigenspace_iff.mp hf))

theorem mem_centralEigenspace (lam : ℂ) (f : S.Space) :
    f ∈ (centralEigenspace S lam).toSubmodule ↔
      S.envelopingAction (ArchimedeanGL.centralGenerator F n) f = lam • f :=
  Module.End.mem_eigenspace_iff

/-- The archimedean slices of a vector, as a linear map to slice families. -/
def sliceFamilyMap : S.Space →ₗ[ℂ] SmoothSliceFamily F n where
  toFun f b := finiteSmoothSlice F n b (S.ambient f)
  map_add' f g := funext fun b => map_add (finiteSmoothSlice F n b) (S.ambient f) (S.ambient g)
  map_smul' c f := funext fun b => map_smul (finiteSmoothSlice F n b) c (S.ambient f)

theorem sliceFamilyMap_eq (f : S.Space) :
    S.sliceFamilyMap f = smoothSliceFamily F n (finiteSmoothInclusion F n (S.ambient f)) :=
  rfl

theorem sliceFamilyMap_injective : Function.Injective S.sliceFamilyMap := by
  intro f g h
  rw [sliceFamilyMap_eq, sliceFamilyMap_eq] at h
  have h1 := smoothSliceFamily_injective F n h
  have h2 : S.ambient f = S.ambient g :=
    Submodule.inclusion_injective (finiteSmoothRational_le_smooth F n) h1
  exact Subtype.ext (Subtype.ext h2)

theorem sliceFamilyMap_envelopingAction (z : ArchimedeanGL.EnvelopingCenter F n)
    (f : S.Space) :
    S.sliceFamilyMap (S.envelopingAction z.val f) =
      centerFamilyOrbitMap F n (S.sliceFamilyMap f) z := by
  funext b
  change finiteSmoothSlice F n b (S.ambient (S.envelopingAction z.val f)) =
    ArchimedeanGL.centerAction F n z (finiteSmoothSlice F n b (S.ambient f))
  rw [S.ambient_envelopingAction, finiteSmoothSlice_envelopingAction,
    ArchimedeanGL.centerAction_apply, ArchimedeanGL.centerInclusion_apply]

/-- A finite-dimensional nonzero invariant subspace contains an eigenvector. -/
theorem _root_.Langlands.Automorphic.CuspidalAdmissible.exists_eigenvector_of_invariant
    {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (W : Submodule ℂ M)
    [Module.Finite ℂ W] (hW : W ≠ ⊥) (hT : ∀ v ∈ W, T v ∈ W) :
    ∃ (lam : ℂ) (v : M), v ≠ 0 ∧ T v = lam • v := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue (T.restrict hT)
  obtain ⟨v, hv⟩ := hlam.exists_hasEigenvector
  refine ⟨lam, v.val, fun h => hv.2 (Subtype.ext h), ?_⟩
  have h := congrArg Subtype.val hv.apply_eq_smul
  rw [LinearMap.restrict_apply] at h
  exact h

/-- Applying the enveloping center to a fixed vector. -/
def centerOrbitMap (f : S.Space) : ArchimedeanGL.EnvelopingCenter F n →ₗ[ℂ] S.Space :=
  LinearMap.applyₗ f ∘ₗ S.envelopingAction.toLinearMap ∘ₗ
    (ArchimedeanGL.centerInclusion F n).toLinearMap

theorem centerOrbitMap_apply (f : S.Space) (z : ArchimedeanGL.EnvelopingCenter F n) :
    S.centerOrbitMap f z = S.envelopingAction z.val f :=
  rfl

/-- The orbit of a realized vector under the enveloping center is finite-dimensional. -/
theorem finite_range_centerOrbitMap (f : S.Space) :
    Module.Finite ℂ (LinearMap.range (S.centerOrbitMap f)) := by
  have hJΦ : S.sliceFamilyMap ∘ₗ S.centerOrbitMap f =
      centerFamilyOrbitMap F n (S.sliceFamilyMap f) :=
    LinearMap.ext fun z => by
      rw [LinearMap.comp_apply, centerOrbitMap_apply, S.sliceFamilyMap_envelopingAction]
  have hcen : IsCenterFinite F n (finiteSmoothInclusion F n (S.ambient f)) :=
    (S.isAutomorphicForm_ambient f).2.2.1
  have hfinOrbit : Module.Finite ℂ (centerFamilyOrbitSpan F n (S.sliceFamilyMap f)) := by
    rw [sliceFamilyMap_eq]
    exact hcen
  rw [centerFamilyOrbitSpan_eq_range, ← hJΦ, LinearMap.range_comp] at hfinOrbit
  exact Module.Finite.equiv (Submodule.equivMapOfInjective _ S.sliceFamilyMap_injective _).symm

theorem self_mem_range_centerOrbitMap (f : S.Space) :
    f ∈ LinearMap.range (S.centerOrbitMap f) :=
  ⟨1, by rw [centerOrbitMap_apply]; exact LinearMap.congr_fun (map_one S.envelopingAction) f⟩

set_option maxHeartbeats 1000000 in
theorem centralGenerator_mem_range_centerOrbitMap (f v : S.Space)
    (hv : v ∈ LinearMap.range (S.centerOrbitMap f)) :
    S.envelopingAction (ArchimedeanGL.centralGenerator F n) v ∈
      LinearMap.range (S.centerOrbitMap f) := by
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hv
  refine LinearMap.mem_range.mpr ⟨⟨ArchimedeanGL.centralGenerator F n * z.val,
    Subalgebra.mul_mem _ (ArchimedeanGL.centralGenerator_mem_center F n) z.2⟩, ?_⟩
  rw [centerOrbitMap_apply, centerOrbitMap_apply]
  exact LinearMap.congr_fun
    (map_mul S.envelopingAction (ArchimedeanGL.centralGenerator F n) z.val) f

set_option maxHeartbeats 1000000 in
/-- **Existence of a central eigenvector.** A nonzero realization contains a nonzero eigenvector
of the central derivative. -/
theorem exists_centralEigenvector [Nontrivial S.Space] :
    ∃ (lam : ℂ) (f : S.Space), f ≠ 0 ∧
      S.envelopingAction (ArchimedeanGL.centralGenerator F n) f = lam • f := by
  obtain ⟨f, hf⟩ := exists_ne (0 : S.Space)
  have := S.finite_range_centerOrbitMap f
  refine CuspidalAdmissible.exists_eigenvector_of_invariant _
    (LinearMap.range (S.centerOrbitMap f)) ?_ (S.centralGenerator_mem_range_centerOrbitMap f)
  intro h
  have hmem := S.self_mem_range_centerOrbitMap f
  rw [h] at hmem
  exact hf ((Submodule.mem_bot ℂ).mp hmem)

end Langlands.Automorphic.OperatorRealization
