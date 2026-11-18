import Langlands.Global.RankinSelberg.PartialIntegralExhaustion
import Langlands.Global.RankinSelberg.LocalPointFactorization
import Langlands.Global.RankinSelberg.ArchimedeanFactorizationReduction
import Langlands.Global.FiniteAdelicGL.SplitAtPlaces
import Langlands.Global.FiniteAdelicGL.StandardIntegralCompact
import Langlands.Global.GeneralLinearGlobalWhittaker

/-! # The classes `unipotentIntegralClasses` as a quotient of a semilocal product group

For a number field `F`, `m : ℕ` and a finite set `S` of finite places, let
`𝒢 = (∏_v GL_m(ℝ) × ∏_w GL_m(ℂ)) × (∏_(v ∈ S) GL_m(F_v) × K^S)`, where `K^S` is the subgroup
of the restricted product of the `GL_m(F_v)`, `v ∉ S`, integral at every place. The natural map
`Ψ : 𝒢 → GL_m(𝔸)` is an injective continuous homomorphism and an open embedding. The preimage
of `N_m(𝔸)` is the product `𝒩` of the local upper unitriangular subgroups, and `Ψ` descends to
an open embedding `𝒩 \ 𝒢 → N_m(𝔸) \ GL_m(𝔸)` whose image is `unipotentIntegralClasses F m S`.
The local classes of the image of `[x]` are the classes of the components of `x`.
See the paired Markdown.
-/

noncomputable section
universe u
open NumberField MeasureTheory Topology CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open scoped RestrictedProduct
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.UnipotentClass

/-! ### General linear groups over products of rings -/

section GLSplit

variable (A B : Type*) [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
  [IsTopologicalRing A] [IsTopologicalRing B] (n : ℕ)

/-- The matrix over `A × B` with the given components. -/
def prodMatrix (a : Matrix (Fin n) (Fin n) A) (b : Matrix (Fin n) (Fin n) B) :
    Matrix (Fin n) (Fin n) (A × B) :=
  fun i j => (a i j, b i j)

omit [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] in
theorem prodMatrix_mul (a a' : Matrix (Fin n) (Fin n) A) (b b' : Matrix (Fin n) (Fin n) B) :
    prodMatrix A B n a b * prodMatrix A B n a' b' = prodMatrix A B n (a * a') (b * b') := by
  ext i j
  · change (RingHom.fst A B) (∑ k, (a i k, b i k) * (a' k j, b' k j)) = _
    rw [map_sum]
    rfl
  · change (RingHom.snd A B) (∑ k, (a i k, b i k) * (a' k j, b' k j)) = _
    rw [map_sum]
    rfl

omit [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] in
theorem prodMatrix_one : prodMatrix A B n 1 1 = 1 := by
  ext i j <;> by_cases h : i = j <;> simp [prodMatrix, Matrix.one_apply, h]

/-- `GL_n(A × B) ≃ GL_n(A) × GL_n(B)` as topological groups. -/
def glProdEquiv :
    Matrix.GeneralLinearGroup (Fin n) (A × B) ≃ₜ*
      Matrix.GeneralLinearGroup (Fin n) A × Matrix.GeneralLinearGroup (Fin n) B where
  toFun g := (Matrix.GeneralLinearGroup.map (RingHom.fst A B) g,
    Matrix.GeneralLinearGroup.map (RingHom.snd A B) g)
  invFun p :=
    { val := prodMatrix A B n p.1.val p.2.val
      inv := prodMatrix A B n p.1.inv p.2.inv
      val_inv := by rw [prodMatrix_mul, p.1.val_inv, p.2.val_inv, prodMatrix_one]
      inv_val := by rw [prodMatrix_mul, p.1.inv_val, p.2.inv_val, prodMatrix_one] }
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' g h := Prod.ext (map_mul _ g h) (map_mul _ g h)
  continuous_toFun :=
    continuous_fst.generalLinearGroup_map.prodMk continuous_snd.generalLinearGroup_map
  continuous_invFun := by
    rw [Units.continuous_iff]
    constructor
    · exact continuous_pi fun i => continuous_pi fun j =>
        ((continuous_apply j).comp
          (Matrix.GeneralLinearGroup.continuous_apply _ continuous_fst i)).prodMk
          ((continuous_apply j).comp
            (Matrix.GeneralLinearGroup.continuous_apply _ continuous_snd i))
    · exact continuous_pi fun i => continuous_pi fun j =>
        ((continuous_apply j).comp
          (Matrix.GeneralLinearGroup.continuous_apply _ continuous_fst.inv i)).prodMk
          ((continuous_apply j).comp
            (Matrix.GeneralLinearGroup.continuous_apply _ continuous_snd.inv i))

variable {Idx : Type*} (R : Idx → Type*) [∀ i, CommRing (R i)] [∀ i, TopologicalSpace (R i)]
  [∀ i, IsTopologicalRing (R i)]

/-- The matrix over `∀ i, R i` with the given components. -/
def piMatrix (a : ∀ i, Matrix (Fin n) (Fin n) (R i)) : Matrix (Fin n) (Fin n) (∀ i, R i) :=
  fun r s i => a i r s

omit [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)] in
theorem piMatrix_mul (a b : ∀ i, Matrix (Fin n) (Fin n) (R i)) :
    piMatrix n R a * piMatrix n R b = piMatrix n R (a * b) := by
  ext r s i
  simp [piMatrix, Matrix.mul_apply, Finset.sum_apply]

omit [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)] in
theorem piMatrix_one : piMatrix n R 1 = 1 := by
  ext r s i
  by_cases h : r = s <;> simp [piMatrix, Matrix.one_apply, h]

/-- `GL_n(∀ i, R i) ≃ ∀ i, GL_n(R i)` as topological groups. -/
def glPiEquiv :
    Matrix.GeneralLinearGroup (Fin n) (∀ i, R i) ≃ₜ*
      ∀ i, Matrix.GeneralLinearGroup (Fin n) (R i) where
  toFun g i := Matrix.GeneralLinearGroup.map (Pi.evalRingHom R i) g
  invFun p :=
    { val := piMatrix n R fun i => (p i).val
      inv := piMatrix n R fun i => (p i).inv
      val_inv := by
        rw [piMatrix_mul]
        convert piMatrix_one n R
        funext i
        exact (p i).val_inv
      inv_val := by
        rw [piMatrix_mul]
        convert piMatrix_one n R
        funext i
        exact (p i).inv_val }
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' g h := funext fun i => map_mul _ g h
  continuous_toFun := continuous_pi fun i => (continuous_apply i).generalLinearGroup_map
  continuous_invFun := by
    rw [Units.continuous_iff]
    constructor
    · exact continuous_pi fun r => continuous_pi fun s => continuous_pi fun i =>
        (continuous_apply s).comp
          (Matrix.GeneralLinearGroup.continuous_apply _ (continuous_apply i) r)
    · refine continuous_pi fun r => continuous_pi fun s => continuous_pi fun i => ?_
      exact (continuous_apply s).comp
        (Matrix.GeneralLinearGroup.continuous_apply
          (fun a : ∀ i, Matrix.GeneralLinearGroup (Fin n) (R i) => (a i)⁻¹)
          (continuous_apply i).inv r)

end GLSplit

/-- The product of two isomorphisms of topological groups. -/
def prodCongr {A B C D : Type*} [Mul A] [Mul B] [Mul C] [Mul D] [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    (e₁ : A ≃ₜ* B) (e₂ : C ≃ₜ* D) : A × C ≃ₜ* B × D where
  toFun x := (e₁ x.1, e₂ x.2)
  invFun y := (e₁.symm y.1, e₂.symm y.2)
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := Prod.ext (map_mul e₁ x.1 y.1) (map_mul e₂ x.2 y.2)
  continuous_toFun :=
    ((map_continuous e₁).comp continuous_fst).prodMk ((map_continuous e₂).comp continuous_snd)
  continuous_invFun :=
    ((map_continuous e₁.symm).comp continuous_fst).prodMk
      ((map_continuous e₂.symm).comp continuous_snd)

/-! ### The semilocal product group and its embedding -/

section Adelic

variable (F : Type u) [Field F] [NumberField F] (m : ℕ) (S : Finset (FinitePlace F))

local instance unipotentClassSchemeAffine (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unipotentClassSchemeSmooth (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance unipotentClassDecEq : DecidableEq (FinitePlace F) := Classical.decEq _

/-- `∏_v GL_m(ℝ)` over the real places `v` of `F`. -/
abbrev RealGL := ∀ _ : {v : InfinitePlace F // v.IsReal}, Langlands.GeneralLinear m ℝ

/-- `∏_w GL_m(ℂ)` over the complex places `w` of `F`. -/
abbrev ComplexGL := ∀ _ : {v : InfinitePlace F // v.IsComplex}, Langlands.GeneralLinear m ℂ

/-- `∏_(v ∈ S) GL_m(F_v)`. -/
abbrev LocalGL := ∀ v : S, FiniteLocalGL F m v.1

/-- The restricted product of the `GL_m(F_v)` over the finite places `v ∉ S`, with respect to
the subgroups `GL_m(𝒪_v)`. -/
abbrev AwayGL := FiniteAdelicGL.AwayRestrictedProduct F m (· ∈ S)

/-- `GL_m(F_∞) ≃ ∏_v GL_m(ℝ) × ∏_w GL_m(ℂ)` through the mixed coordinates. -/
def archSplit : InfiniteAdelicGL F m ≃ₜ* RealGL F m × ComplexGL F m :=
  (archimedeanGLCoordinates F m).trans
    ((glProdEquiv _ _ m).trans
      (prodCongr (glPiEquiv m fun _ : {v : InfinitePlace F // v.IsReal} => ℝ)
        (glPiEquiv m fun _ : {v : InfinitePlace F // v.IsComplex} => ℂ)))

/-- `GL_m(𝔸) ≃ (∏_v GL_m(ℝ) × ∏_w GL_m(ℂ)) × (∏_(v ∈ S) GL_m(F_v) × GL_m(𝔸^S))` as topological
groups. -/
def adelicSplit :
    (RealGL F m × ComplexGL F m) × (LocalGL F m S × AwayGL F m S) ≃ₜ* Points F m :=
  (prodCongr (archSplit F m).symm (FiniteAdelicGL.splitAtPlaces F m (· ∈ S)).symm).trans
    ((AdelicGL.split F m).symm.trans (GeneralLinearGroupPoints.adelicHomeomorph F m).symm)

theorem adelicEquiv_adelicSplit
    (w : (RealGL F m × ComplexGL F m) × (LocalGL F m S × AwayGL F m S)) :
    GeneralLinearGroupPoints.adelicEquiv F m (adelicSplit F m S w) =
      AdelicGL.pair F m ((archSplit F m).symm w.1)
        ((FiniteAdelicGL.splitAtPlaces F m (· ∈ S)).symm w.2) :=
  (GeneralLinearGroupPoints.adelicHomeomorph F m).apply_symm_apply _

omit [NumberField F] in
theorem archSplit_symm_apply (z : RealGL F m × ComplexGL F m) (i j : Fin m) :
    ((archSplit F m).symm z) i j =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        ((fun v => z.1 v i j), fun v => z.2 v i j) :=
  rfl

theorem realComponent_eq (v : {v : InfinitePlace F // v.IsReal}) (g : Points F m) :
    realComponent F m v g =
      (archSplit F m (AdelicGL.infinite F m (GeneralLinearGroupPoints.adelicEquiv F m g))).1 v := by
  apply Units.ext
  rfl

theorem complexComponent_eq (v : {v : InfinitePlace F // v.IsComplex}) (g : Points F m) :
    complexComponent F m v g =
      (archSplit F m (AdelicGL.infinite F m (GeneralLinearGroupPoints.adelicEquiv F m g))).2 v := by
  apply Units.ext
  rfl

theorem realComponent_adelicSplit
    (w : (RealGL F m × ComplexGL F m) × (LocalGL F m S × AwayGL F m S))
    (v : {v : InfinitePlace F // v.IsReal}) :
    realComponent F m v (adelicSplit F m S w) = w.1.1 v := by
  rw [realComponent_eq, adelicEquiv_adelicSplit, AdelicGL.infinite_pair,
    ContinuousMulEquiv.apply_symm_apply]

theorem complexComponent_adelicSplit
    (w : (RealGL F m × ComplexGL F m) × (LocalGL F m S × AwayGL F m S))
    (v : {v : InfinitePlace F // v.IsComplex}) :
    complexComponent F m v (adelicSplit F m S w) = w.1.2 v := by
  rw [complexComponent_eq, adelicEquiv_adelicSplit, AdelicGL.infinite_pair,
    ContinuousMulEquiv.apply_symm_apply]

theorem finiteComponent_adelicSplit_of_mem
    (w : (RealGL F m × ComplexGL F m) × (LocalGL F m S × AwayGL F m S))
    {v : FinitePlace F} (hv : v ∈ S) :
    finiteComponent F m v (adelicSplit F m S w) = w.2.1 ⟨v, hv⟩ := by
  change FiniteAdelicGL.localProjection F m v
    (AdelicGL.finite F m (GeneralLinearGroupPoints.adelicEquiv F m (adelicSplit F m S w))) = _
  rw [adelicEquiv_adelicSplit, AdelicGL.finite_pair]
  exact FiniteAdelicGL.localProjection_splitAtPlaces_symm_of_pos F m (· ∈ S) w.2 hv

theorem finiteComponent_adelicSplit_of_not_mem
    (w : (RealGL F m × ComplexGL F m) × (LocalGL F m S × AwayGL F m S))
    {v : FinitePlace F} (hv : v ∉ S) :
    finiteComponent F m v (adelicSplit F m S w) = w.2.2 ⟨v, hv⟩ := by
  change FiniteAdelicGL.localProjection F m v
    (AdelicGL.finite F m (GeneralLinearGroupPoints.adelicEquiv F m (adelicSplit F m S w))) = _
  rw [adelicEquiv_adelicSplit, AdelicGL.finite_pair]
  exact FiniteAdelicGL.localProjection_splitAtPlaces_symm_of_neg F m (· ∈ S) w.2 hv

theorem realComponent_mul (v : {v : InfinitePlace F // v.IsReal}) (g h : Points F m) :
    realComponent F m v (g * h) = realComponent F m v g * realComponent F m v h := by
  simp only [realComponent_eq, map_mul, Prod.fst_mul, Pi.mul_apply]

theorem complexComponent_mul (v : {v : InfinitePlace F // v.IsComplex}) (g h : Points F m) :
    complexComponent F m v (g * h) = complexComponent F m v g * complexComponent F m v h := by
  simp only [complexComponent_eq, map_mul, Prod.snd_mul, Pi.mul_apply]

theorem finiteComponent_mul (v : FinitePlace F) (g h : Points F m) :
    finiteComponent F m v (g * h) = finiteComponent F m v g * finiteComponent F m v h :=
  by apply Langlands.Global.RankinSelbergGlobal.finiteComponent_mul

theorem realComponent_inv (v : {v : InfinitePlace F // v.IsReal}) (g : Points F m) :
    realComponent F m v g⁻¹ = (realComponent F m v g)⁻¹ := by
  simp only [realComponent_eq, map_inv, Prod.fst_inv, Pi.inv_apply]

theorem complexComponent_inv (v : {v : InfinitePlace F // v.IsComplex}) (g : Points F m) :
    complexComponent F m v g⁻¹ = (complexComponent F m v g)⁻¹ := by
  simp only [complexComponent_eq, map_inv, Prod.snd_inv, Pi.inv_apply]

theorem finiteComponent_inv (v : FinitePlace F) (g : Points F m) :
    finiteComponent F m v g⁻¹ = (finiteComponent F m v g)⁻¹ :=
  by apply Langlands.Global.RankinSelbergGlobal.LocalPointFactorization.finiteComponent_inv

theorem realComponent_mem {g : Points F m} (hg : g ∈ unipotentAdelic F m)
    (v : {v : InfinitePlace F // v.IsReal}) :
    realComponent F m v g ∈ Langlands.GeneralLinear.upperUnipotent m ℝ := by
  rw [Unfolding.mem_unipotentAdelic_iff] at hg
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change (InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((GeneralLinearGroupPoints.adelicEquiv F m g : Matrix (Fin m) (Fin m) (Adeles F)) i j).1).1
        v = 0
    rw [hg.1 hij]
    exact congrArg (fun z => z.1 v) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
  · change (InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((GeneralLinearGroupPoints.adelicEquiv F m g : Matrix (Fin m) (Fin m) (Adeles F)) i i).1).1
        v = 1
    rw [hg.2 i]
    exact congrArg (fun z => z.1 v) (map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F))

theorem complexComponent_mem {g : Points F m} (hg : g ∈ unipotentAdelic F m)
    (v : {v : InfinitePlace F // v.IsComplex}) :
    complexComponent F m v g ∈ Langlands.GeneralLinear.upperUnipotent m ℂ := by
  rw [Unfolding.mem_unipotentAdelic_iff] at hg
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change (InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((GeneralLinearGroupPoints.adelicEquiv F m g : Matrix (Fin m) (Fin m) (Adeles F)) i j).1).2
        v = 0
    rw [hg.1 hij]
    exact congrArg (fun z => z.2 v) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
  · change (InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((GeneralLinearGroupPoints.adelicEquiv F m g : Matrix (Fin m) (Fin m) (Adeles F)) i i).1).2
        v = 1
    rw [hg.2 i]
    exact congrArg (fun z => z.2 v) (map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F))

theorem finiteComponent_mem {g : Points F m} (hg : g ∈ unipotentAdelic F m)
    (v : FinitePlace F) :
    finiteComponent F m v g ∈ Langlands.GeneralLinear.upperUnipotent m (FiniteCompletion F v) := by
  rw [Unfolding.mem_unipotentAdelic_iff] at hg
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change ((GeneralLinearGroupPoints.adelicEquiv F m g : Matrix (Fin m) (Fin m) (Adeles F))
      i j).2 v = 0
    rw [hg.1 hij]
    rfl
  · change ((GeneralLinearGroupPoints.adelicEquiv F m g : Matrix (Fin m) (Fin m) (Adeles F))
      i i).2 v = 1
    rw [hg.2 i]
    rfl

/-- A point of `GL_m(𝔸)` lies in `N_m(𝔸)` iff all its components are upper unitriangular. -/
theorem adelicSplit_mem_iff
    (w : (RealGL F m × ComplexGL F m) × (LocalGL F m S × AwayGL F m S)) :
    adelicSplit F m S w ∈ unipotentAdelic F m ↔
      ((∀ v, w.1.1 v ∈ Langlands.GeneralLinear.upperUnipotent m ℝ) ∧
        ∀ v, w.1.2 v ∈ Langlands.GeneralLinear.upperUnipotent m ℂ) ∧
      (∀ v : S, w.2.1 v ∈ Langlands.GeneralLinear.upperUnipotent m (FiniteCompletion F v.1)) ∧
        ∀ v : {v : FinitePlace F // v ∉ S},
          w.2.2 v ∈ Langlands.GeneralLinear.upperUnipotent m (FiniteCompletion F v.1) := by
  constructor
  · intro h
    refine ⟨⟨fun v => ?_, fun v => ?_⟩, fun v => ?_, fun v => ?_⟩
    · rw [← realComponent_adelicSplit F m S w v]
      exact realComponent_mem F m h v
    · rw [← complexComponent_adelicSplit F m S w v]
      exact complexComponent_mem F m h v
    · rw [← finiteComponent_adelicSplit_of_mem F m S w v.2]
      exact finiteComponent_mem F m h v.1
    · rw [← finiteComponent_adelicSplit_of_not_mem F m S w v.2]
      exact finiteComponent_mem F m h v.1
  · rintro ⟨⟨hR, hC⟩, hS, hA⟩
    rw [Unfolding.mem_unipotentAdelic_iff, adelicEquiv_adelicSplit]
    have hfin : ∀ i j, ∀ v : FinitePlace F,
        ((FiniteAdelicGL.splitAtPlaces F m (· ∈ S)).symm w.2) i j v =
          if hv : v ∈ S then w.2.1 ⟨v, hv⟩ i j else w.2.2 ⟨v, hv⟩ i j := by
      intro i j v
      change FiniteAdelicGL.localProjection F m v
        ((FiniteAdelicGL.splitAtPlaces F m (· ∈ S)).symm w.2) i j = _
      split_ifs with hv
      · rw [FiniteAdelicGL.localProjection_splitAtPlaces_symm_of_pos F m (· ∈ S) w.2 hv]
      · rw [FiniteAdelicGL.localProjection_splitAtPlaces_symm_of_neg F m (· ∈ S) w.2 hv]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [AdelicGL.pair_apply]
      refine Prod.ext ?_ ?_
      · change ((archSplit F m).symm w.1 : Matrix (Fin m) (Fin m) (InfiniteAdeleRing F)) i j = 0
        rw [archSplit_symm_apply]
        have h0 : ((fun v => (w.1.1 v : Matrix (Fin m) (Fin m) ℝ) i j),
            fun v => (w.1.2 v : Matrix (Fin m) (Fin m) ℂ) i j) =
            (0 : mixedEmbedding.mixedSpace F) :=
          Prod.ext (funext fun v => (hR v).1 hij) (funext fun v => (hC v).1 hij)
        rw [h0, map_zero]
      · change ((FiniteAdelicGL.splitAtPlaces F m (· ∈ S)).symm w.2 :
          Matrix (Fin m) (Fin m) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j = 0
        apply RestrictedProduct.ext
        intro v
        refine (hfin i j v).trans ?_
        split_ifs with hv
        · exact (hS ⟨v, hv⟩).1 hij
        · exact (hA ⟨v, hv⟩).1 hij
    · rw [AdelicGL.pair_apply]
      refine Prod.ext ?_ ?_
      · change ((archSplit F m).symm w.1 : Matrix (Fin m) (Fin m) (InfiniteAdeleRing F)) i i = 1
        rw [archSplit_symm_apply]
        have h1 : ((fun v => (w.1.1 v : Matrix (Fin m) (Fin m) ℝ) i i),
            fun v => (w.1.2 v : Matrix (Fin m) (Fin m) ℂ) i i) =
            (1 : mixedEmbedding.mixedSpace F) :=
          Prod.ext (funext fun v => (hR v).2 i) (funext fun v => (hC v).2 i)
        rw [h1, map_one]
      · change ((FiniteAdelicGL.splitAtPlaces F m (· ∈ S)).symm w.2 :
          Matrix (Fin m) (Fin m) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i i = 1
        apply RestrictedProduct.ext
        intro v
        refine (hfin i i v).trans ?_
        split_ifs with hv
        · exact (hS ⟨v, hv⟩).2 i
        · exact (hA ⟨v, hv⟩).2 i

/-- The subgroup `K^S` of families integral at every finite place outside `S`. -/
abbrev awayIntegralSubgroup : Subgroup (AwayGL F m S) :=
  (FiniteAdelicGL.awayIntegral F m (· ∈ S)).toSubgroup

/-- The semilocal group `(∏_v GL_m(ℝ) × ∏_w GL_m(ℂ)) × (∏_(v ∈ S) GL_m(F_v) × K^S)`. -/
abbrev SemilocalGL :=
  (RealGL F m × ComplexGL F m) × (LocalGL F m S × awayIntegralSubgroup F m S)

/-- The inclusion of the semilocal group into the product decomposition of `GL_m(𝔸)`. -/
def semilocalInclusion :
    SemilocalGL F m S →* (RealGL F m × ComplexGL F m) × (LocalGL F m S × AwayGL F m S) :=
  (MonoidHom.id _).prodMap ((MonoidHom.id _).prodMap (awayIntegralSubgroup F m S).subtype)

/-- The embedding `Ψ : 𝒢 → GL_m(𝔸)` of the semilocal group. -/
def semilocalEmbedding : SemilocalGL F m S →* Points F m :=
  (adelicSplit F m S).toMulEquiv.toMonoidHom.comp (semilocalInclusion F m S)

theorem semilocalEmbedding_apply (x : SemilocalGL F m S) :
    semilocalEmbedding F m S x = adelicSplit F m S (x.1, (x.2.1, (x.2.2 : AwayGL F m S))) :=
  rfl

theorem isOpenEmbedding_semilocalEmbedding : IsOpenEmbedding (semilocalEmbedding F m S) := by
  have hK : IsOpenEmbedding ((↑) : awayIntegralSubgroup F m S → AwayGL F m S) :=
    (FiniteAdelicGL.awayIntegral F m (· ∈ S)).isOpen.isOpenEmbedding_subtypeVal
  have hI : IsOpenEmbedding (semilocalInclusion F m S) :=
    IsOpenEmbedding.id.prodMap (IsOpenEmbedding.id.prodMap hK)
  exact (adelicSplit F m S).toHomeomorph.isOpenEmbedding.comp hI

/-- The unipotent part of `K^S`: families upper unitriangular at every place. -/
def awayUnipotent : Subgroup (awayIntegralSubgroup F m S) where
  carrier := {k | ∀ v, (k : AwayGL F m S) v ∈
    Langlands.GeneralLinear.upperUnipotent m (FiniteCompletion F v.1)}
  one_mem' v := (Langlands.GeneralLinear.upperUnipotent m (FiniteCompletion F v.1)).one_mem
  mul_mem' hx hy v :=
    (Langlands.GeneralLinear.upperUnipotent m (FiniteCompletion F v.1)).mul_mem (hx v) (hy v)
  inv_mem' hx v :=
    (Langlands.GeneralLinear.upperUnipotent m (FiniteCompletion F v.1)).inv_mem (hx v)

/-- The unipotent subgroup `𝒩` of the semilocal group: the product of the local upper
unitriangular subgroups. -/
def semilocalUnipotent : Subgroup (SemilocalGL F m S) :=
  ((Subgroup.pi Set.univ fun _ => Langlands.GeneralLinear.upperUnipotent m ℝ).prod
      (Subgroup.pi Set.univ fun _ => Langlands.GeneralLinear.upperUnipotent m ℂ)).prod
    ((Subgroup.pi Set.univ fun v : S =>
        Langlands.GeneralLinear.upperUnipotent m (FiniteCompletion F v.1)).prod
      (awayUnipotent F m S))

theorem semilocalEmbedding_mem_iff (x : SemilocalGL F m S) :
    semilocalEmbedding F m S x ∈ unipotentAdelic F m ↔ x ∈ semilocalUnipotent F m S := by
  rw [semilocalEmbedding_apply, adelicSplit_mem_iff]
  simp only [semilocalUnipotent, Subgroup.mem_prod, Subgroup.mem_pi, Set.mem_univ,
    true_implies]
  rfl

theorem isClosed_semilocalUnipotent :
    IsClosed (semilocalUnipotent F m S : Set (SemilocalGL F m S)) := by
  have h := (isClosed_upperUnipotent_adelicPoints F m).preimage
    (isOpenEmbedding_semilocalEmbedding F m S).continuous
  convert h using 1
  ext x
  exact (semilocalEmbedding_mem_iff F m S x).symm

theorem isCompact_awayIntegral :
    IsCompact (awayIntegralSubgroup F m S : Set (AwayGL F m S)) := by
  have hc : IsCompact ((FiniteAdelicGL.splitAtPlaces F m (· ∈ S)) ''
      (FiniteAdelicGL.standardIntegral F m : Set (FiniteAdelicGL F m))) :=
    (FiniteAdelicGL.isCompact_standardIntegral F m).image (map_continuous _)
  have he : (FiniteAdelicGL.splitAtPlaces F m (· ∈ S)) ''
      (FiniteAdelicGL.standardIntegral F m : Set (FiniteAdelicGL F m)) =
      (((FiniteAdelicGL.standardIntegral F m).toSubgroup.map
        (FiniteAdelicGL.splitAtPlaces F m (· ∈ S)).toMonoidHom :
          Subgroup _) : Set _) := by
    rw [Subgroup.coe_map]
    rfl
  rw [he, FiniteAdelicGL.map_standardIntegral_splitAtPlaces] at hc
  convert hc.image continuous_snd using 1
  ext k
  constructor
  · intro hk
    refine ⟨(1, k), ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_prod]
    exact ⟨Subgroup.one_mem _, hk⟩
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_prod] at hy
    exact hy.2

/-! ### The class map `𝒩 \ 𝒢 → N_m(𝔸) \ GL_m(𝔸)` -/

/-- The left quotient `𝒩 \ 𝒢` of the semilocal group. -/
abbrev SemilocalQuotient := LeftCosetSpace (semilocalUnipotent F m S)

/-- `𝒩 x ↦ N_m(𝔸) Ψ(x)`. -/
def classMap : SemilocalQuotient F m S → WhittakerQuotient F m :=
  Quotient.lift (fun x => LeftCosetSpace.mk (unipotentAdelic F m) (semilocalEmbedding F m S x))
    (by
      intro x y h
      have h' : y * x⁻¹ ∈ semilocalUnipotent F m S := QuotientGroup.rightRel_apply.mp h
      refine (LeftCosetSpace.mk_eq_mk_iff _ _ _).mpr ?_
      rw [← map_inv, ← map_mul, semilocalEmbedding_mem_iff]
      exact h')

theorem classMap_mk (x : SemilocalGL F m S) :
    classMap F m S (LeftCosetSpace.mk _ x) =
      LeftCosetSpace.mk (unipotentAdelic F m) (semilocalEmbedding F m S x) :=
  rfl

theorem classMap_injective : Function.Injective (classMap F m S) := by
  intro p q h
  induction p using Quotient.inductionOn with
  | h x =>
  induction q using Quotient.inductionOn with
  | h y =>
  change LeftCosetSpace.mk _ (semilocalEmbedding F m S x) =
    LeftCosetSpace.mk _ (semilocalEmbedding F m S y) at h
  rw [LeftCosetSpace.mk_eq_mk_iff, ← map_inv, ← map_mul, semilocalEmbedding_mem_iff] at h
  exact (LeftCosetSpace.mk_eq_mk_iff _ _ _).mpr h

theorem continuous_classMap : Continuous (classMap F m S) :=
  Continuous.quotient_lift ((LeftCosetSpace.continuous_mk _).comp
    (isOpenEmbedding_semilocalEmbedding F m S).continuous) _

theorem isOpenMap_classMap : IsOpenMap (classMap F m S) := by
  intro U hU
  have hU' : IsOpen (LeftCosetSpace.mk (semilocalUnipotent F m S) ⁻¹' U) :=
    hU.preimage (LeftCosetSpace.continuous_mk _)
  have he : classMap F m S '' U = LeftCosetSpace.mk (unipotentAdelic F m) ''
      (semilocalEmbedding F m S '' (LeftCosetSpace.mk (semilocalUnipotent F m S) ⁻¹' U)) := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective _ p
      exact ⟨semilocalEmbedding F m S x, ⟨x, hp, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨LeftCosetSpace.mk _ x, hx, rfl⟩
  rw [he]
  exact (LeftCosetSpace.isOpenQuotientMap_mk _).isOpenMap _
    ((isOpenEmbedding_semilocalEmbedding F m S).isOpenMap _ hU')

/-- The class map is an open embedding. -/
theorem isOpenEmbedding_classMap : IsOpenEmbedding (classMap F m S) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_classMap F m S)
    (classMap_injective F m S) (isOpenMap_classMap F m S)

omit [NumberField F] in
theorem isUnipotentIntegral_iff [NumberField F] (v : FinitePlace F) (x : FiniteLocalGL F m v) :
    IsUnipotentIntegral F m v x ↔ ∃ k ∈ FiniteAdelicGL.localIntegral F m v,
      x * k ∈ Langlands.GeneralLinear.upperUnipotent m (FiniteCompletion F v) := by
  constructor
  · rintro ⟨k, hk, h1, h2⟩
    exact ⟨k, hk, fun i j hij => h2 i j hij, h1⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨k, hk, h.2, fun i j hij => h.1 hij⟩

/-- `unipotentIntegralOutside` is stable under left multiplication by `N_m(𝔸)`. -/
theorem mul_mem_unipotentIntegralOutside_iff {n : Points F m} (hn : n ∈ unipotentAdelic F m)
    (g : Points F m) :
    n * g ∈ unipotentIntegralOutside F m S ↔ g ∈ unipotentIntegralOutside F m S := by
  have key : ∀ {n g : Points F m}, n ∈ unipotentAdelic F m →
      g ∈ unipotentIntegralOutside F m S → n * g ∈ unipotentIntegralOutside F m S := by
    intro n g hn hg v hv
    obtain ⟨k, hk, h⟩ := (isUnipotentIntegral_iff F m v _).mp (hg v hv)
    refine (isUnipotentIntegral_iff F m v _).mpr ⟨k, hk, ?_⟩
    rw [finiteComponent_mul, mul_assoc]
    exact Subgroup.mul_mem _ (finiteComponent_mem F m hn v) h
  refine ⟨fun h => ?_, key hn⟩
  have h' := key (inv_mem hn) h
  rwa [inv_mul_cancel_left] at h'

theorem mk_mem_unipotentIntegralClasses_iff (g : Points F m) :
    LeftCosetSpace.mk (unipotentAdelic F m) g ∈ unipotentIntegralClasses F m S ↔
      g ∈ unipotentIntegralOutside F m S :=
  by apply Langlands.Global.RankinSelbergGlobal.mk_mem_unipotentIntegralClasses_iff

/-- **Reduction of points of `unipotentIntegralOutside`.** If `g_v ∈ N_m(F_v) GL_m(𝒪_v)` for
every finite place `v ∉ S`, there is `y ∈ 𝒢` with the archimedean and `S` coordinates of `g` such
that `g Ψ(y)⁻¹ ∈ N_m(𝔸)`. -/
theorem exists_semilocal_of_mem_unipotentIntegralOutside {g : Points F m}
    (hg : g ∈ unipotentIntegralOutside F m S) :
    ∃ y : SemilocalGL F m S, y.1 = ((adelicSplit F m S).symm g).1 ∧
      y.2.1 = ((adelicSplit F m S).symm g).2.1 ∧
      g * (semilocalEmbedding F m S y)⁻¹ ∈ unipotentAdelic F m := by
  obtain ⟨w, rfl⟩ : ∃ w, adelicSplit F m S w = g := ⟨_, (adelicSplit F m S).apply_symm_apply g⟩
  choose k hk hkN using fun v : {v : FinitePlace F // v ∉ S} =>
    (isUnipotentIntegral_iff F m v.1 _).mp (hg v.1 v.2)
  let kA : AwayGL F m S := ⟨fun v => k v, Filter.Eventually.of_forall fun v => hk v⟩
  have hkA : kA ∈ awayIntegralSubgroup F m S := fun v => hk v
  refine ⟨(w.1, (w.2.1, (⟨kA, hkA⟩ : awayIntegralSubgroup F m S)⁻¹)), ?_, ?_, ?_⟩
  · rw [ContinuousMulEquiv.symm_apply_apply]
  · rw [ContinuousMulEquiv.symm_apply_apply]
  rw [semilocalEmbedding_apply, ← map_inv, ← map_mul, adelicSplit_mem_iff]
  refine ⟨⟨fun v => ?_, fun v => ?_⟩, fun v => ?_, fun v => ?_⟩
  · change w.1.1 v * (w.1.1 v)⁻¹ ∈ _
    rw [mul_inv_cancel]
    exact Subgroup.one_mem _
  · change w.1.2 v * (w.1.2 v)⁻¹ ∈ _
    rw [mul_inv_cancel]
    exact Subgroup.one_mem _
  · change w.2.1 v * (w.2.1 v)⁻¹ ∈ _
    rw [mul_inv_cancel]
    exact Subgroup.one_mem _
  · change w.2.2 v * ((k v)⁻¹)⁻¹ ∈ _
    rw [inv_inv, ← finiteComponent_adelicSplit_of_not_mem F m S w v.2]
    exact hkN v

/-- **Reduction of points of `unipotentIntegralOutside`, explicit form.** A point `g` with
`g_v ∈ N_m(F_v) GL_m(𝒪_v)` for every finite place `v ∉ S` is `n · g' · k`, where `n ∈ N_m(𝔸)`,
`g'` has the archimedean and `S` components of `g` and identity components outside `S`, and
`k` has identity archimedean and `S` components and components in `GL_m(𝒪_v)` outside `S`. -/
theorem exists_unipotent_mul_mul_of_mem_unipotentIntegralOutside {g : Points F m}
    (hg : g ∈ unipotentIntegralOutside F m S) :
    ∃ n ∈ unipotentAdelic F m, ∃ k ∈ awayIntegralSubgroup F m S,
      g = n * adelicSplit F m S (((adelicSplit F m S).symm g).1,
          (((adelicSplit F m S).symm g).2.1, 1)) * adelicSplit F m S (1, (1, k)) := by
  obtain ⟨y, h1, h2, hn⟩ := exists_semilocal_of_mem_unipotentIntegralOutside F m S hg
  refine ⟨_, hn, y.2.2, y.2.2.2, ?_⟩
  rw [mul_assoc, ← map_mul, ← h1, ← h2]
  have he : ((y.1, (y.2.1, (1 : AwayGL F m S))) *
      ((1 : RealGL F m × ComplexGL F m), ((1 : LocalGL F m S), (y.2.2 : AwayGL F m S)))) =
      (y.1, (y.2.1, (y.2.2 : AwayGL F m S))) := by
    simp
  rw [he, ← semilocalEmbedding_apply, inv_mul_cancel_right]

/-- The image of the class map is `unipotentIntegralClasses F m S`. -/
theorem range_classMap : Set.range (classMap F m S) = unipotentIntegralClasses F m S := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective _ p
    rw [classMap_mk, mk_mem_unipotentIntegralClasses_iff]
    intro v hv
    refine (isUnipotentIntegral_iff F m v _).mpr
      ⟨(finiteComponent F m v (semilocalEmbedding F m S x))⁻¹, ?_, ?_⟩
    · rw [semilocalEmbedding_apply, finiteComponent_adelicSplit_of_not_mem F m S _ hv]
      exact (FiniteAdelicGL.localIntegral F m v).inv_mem (x.2.2.2 ⟨v, hv⟩)
    · rw [mul_inv_cancel]
      exact Subgroup.one_mem _
  · intro hq
    obtain ⟨g, rfl⟩ := LeftCosetSpace.mk_surjective _ q
    rw [mk_mem_unipotentIntegralClasses_iff] at hq
    obtain ⟨y, -, -, hy⟩ := exists_semilocal_of_mem_unipotentIntegralOutside F m S hq
    exact ⟨LeftCosetSpace.mk _ y, (LeftCosetSpace.mk_eq_mk_iff _ _ _).mpr hy⟩

/-! ### Local projections of the classes in the image -/

theorem realQuotientProjection_mk (t : ℕ) (v : {v : InfinitePlace F // v.IsReal})
    (g : Points F (t + 1)) :
    realQuotientProjection F t v (LeftCosetSpace.mk _ g) =
      LeftCosetSpace.mk _ (realComponent F (t + 1) v g) := by
  have hmk : LeftCosetSpace.mk (unipotentAdelic F (t + 1))
      (LeftCosetSpace.mk (unipotentAdelic F (t + 1)) g).out = LeftCosetSpace.mk _ g :=
    Quotient.out_eq _
  have hn := realComponent_mem F (t + 1) ((LeftCosetSpace.mk_eq_mk_iff _ _ _).mp hmk) v
  rw [realComponent_mul, realComponent_inv] at hn
  exact (LeftCosetSpace.mk_eq_mk_iff _ _ _).mpr hn

theorem complexQuotientProjection_mk (t : ℕ) (v : {v : InfinitePlace F // v.IsComplex})
    (g : Points F (t + 1)) :
    complexQuotientProjection F t v (LeftCosetSpace.mk _ g) =
      LeftCosetSpace.mk _ (complexComponent F (t + 1) v g) := by
  have hmk : LeftCosetSpace.mk (unipotentAdelic F (t + 1))
      (LeftCosetSpace.mk (unipotentAdelic F (t + 1)) g).out = LeftCosetSpace.mk _ g :=
    Quotient.out_eq _
  have hn := complexComponent_mem F (t + 1) ((LeftCosetSpace.mk_eq_mk_iff _ _ _).mp hmk) v
  rw [complexComponent_mul, complexComponent_inv] at hn
  exact (LeftCosetSpace.mk_eq_mk_iff _ _ _).mpr hn

theorem finiteQuotientProjection_mk (t : ℕ) (v : FinitePlace F) (g : Points F (t + 1)) :
    finiteQuotientProjection F t v (LeftCosetSpace.mk _ g) =
      Quotient.mk'' (finiteComponent F (t + 1) v g) := by
  have hmk : LeftCosetSpace.mk (unipotentAdelic F (t + 1))
      (LeftCosetSpace.mk (unipotentAdelic F (t + 1)) g).out = LeftCosetSpace.mk _ g :=
    Quotient.out_eq _
  have hn := finiteComponent_mem F (t + 1) ((LeftCosetSpace.mk_eq_mk_iff _ _ _).mp hmk) v
  rw [finiteComponent_mul, finiteComponent_inv] at hn
  exact (LeftCosetSpace.mk_eq_mk_iff _ _ _).mpr hn

theorem realQuotientProjection_classMap (t : ℕ) (x : SemilocalGL F (t + 1) S)
    (v : {v : InfinitePlace F // v.IsReal}) :
    realQuotientProjection F t v (classMap F (t + 1) S (LeftCosetSpace.mk _ x)) =
      LeftCosetSpace.mk _ (x.1.1 v) := by
  rw [classMap_mk, realQuotientProjection_mk, semilocalEmbedding_apply, realComponent_adelicSplit]

theorem complexQuotientProjection_classMap (t : ℕ) (x : SemilocalGL F (t + 1) S)
    (v : {v : InfinitePlace F // v.IsComplex}) :
    complexQuotientProjection F t v (classMap F (t + 1) S (LeftCosetSpace.mk _ x)) =
      LeftCosetSpace.mk _ (x.1.2 v) := by
  rw [classMap_mk, complexQuotientProjection_mk, semilocalEmbedding_apply,
    complexComponent_adelicSplit]

theorem finiteQuotientProjection_classMap (t : ℕ) (x : SemilocalGL F (t + 1) S) (v : S) :
    finiteQuotientProjection F t v.1 (classMap F (t + 1) S (LeftCosetSpace.mk _ x)) =
      Quotient.mk'' (x.2.1 v) := by
  rw [classMap_mk, finiteQuotientProjection_mk, semilocalEmbedding_apply,
    finiteComponent_adelicSplit_of_mem F (t + 1) S _ v.2]

end Adelic

end Langlands.Global.RankinSelbergGlobal.UnipotentClass
