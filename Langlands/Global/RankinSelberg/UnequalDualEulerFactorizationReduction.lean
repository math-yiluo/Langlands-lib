import Langlands.Global.RankinSelberg.UnequalDualEulerFactorizationStatement
import Langlands.Global.RankinSelberg.LocalPointFactorization
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationStatement
import Langlands.Global.RankinSelberg.PartialIntegralExhaustion
import Langlands.Global.RankinSelberg.PartialEulerProductConvergence
import Langlands.Representation.RankinSelberg.UnramifiedUnequalLocalSum
import Langlands.Representation.Whittaker.RectangularSupport
import Langlands.Global.RankinSelberg.EqualDualEulerFactorizationReduction
import Langlands.HarmonicAnalysis.PadicAdditiveCharacterSelfDuality
import Langlands.Global.RankinSelberg.UnfoldingDual
import Langlands.Global.Factors.CuspidalPairFiniteLayer

/-! # Reduction of the unequal-rank dual Euler factorization

The partial Euler factorization `UnequalDualEulerFactorizationStatement` follows from the
one-place factorization of global Whittaker functions
(`UnramifiedWhittakerFactorizationStatement`), the one-place cell decomposition of the
Whittaker quotient measure (`WhittakerCellDecompositionStatement`), the unfolding
statement `UnequalUnfoldingStatement` and the contragredient description of dual Whittaker
functions (`ContragredientDualWhittakerStatement`). See the paired Markdown.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.UnequalDualEuler

open Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa Langlands.GeneralLinear.Spherical
open Langlands.GeneralLinear.RectangularSupport
open LocalPointFactorization
open Langlands.Global.CuspidalPairBoundaryNonvanishing

local instance unequalDualReductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unequalDualReductionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-! ### Adelic points and their components -/

section Points

variable (F : Type u) [Field F] [NumberField F]

theorem adeles_ext {a b : Adeles F} (h1 : a.1 = b.1)
    (h2 : ∀ w : FinitePlace F, a.2 w = b.2 w) : a = b := by
  refine Prod.ext h1 ?_
  apply RestrictedProduct.ext
  exact h2

/-- Two adelic points agree when their infinite parts and all finite components agree. -/
theorem points_ext {m : ℕ} {g g' : Points F m}
    (hinf : AdelicGL.infinite F m (GeneralLinearGroupPoints.adelicEquiv F m g) =
      AdelicGL.infinite F m (GeneralLinearGroupPoints.adelicEquiv F m g'))
    (hfin : ∀ w, finiteComponent F m w g = finiteComponent F m w g') : g = g' := by
  apply (GeneralLinearGroupPoints.adelicEquiv F m).injective
  rw [← AdelicGL.pair_projections F m (GeneralLinearGroupPoints.adelicEquiv F m g),
    ← AdelicGL.pair_projections F m (GeneralLinearGroupPoints.adelicEquiv F m g'), hinf]
  congr 1
  apply FiniteAdelicGL.ext_localProjection
  exact hfin

theorem infinite_localPoint (m : ℕ) (v : FinitePlace F) (h : FiniteLocalGL F m v) :
    AdelicGL.infinite F m (GeneralLinearGroupPoints.adelicEquiv F m (localPoint F m v h)) = 1 := by
  rw [adelicEquiv_localPoint, infinite_ofFinite]

/-- `ι_v(u)` lies in `N_m(𝔸)` for upper unitriangular `u`. -/
theorem localPoint_mem_unipotentAdelic {m : ℕ} (v : FinitePlace F) {u : FiniteLocalGL F m v}
    (hu : u ∈ Langlands.GeneralLinear.upperUnipotent m (FiniteCompletion F v)) :
    localPoint F m v u ∈ unipotentAdelic F m := by
  rw [Unfolding.mem_unipotentAdelic_iff]
  have hinf := infinite_localPoint F m v u
  have e1 : ∀ i j, (GeneralLinearGroupPoints.adelicEquiv F m (localPoint F m v u) i j).1 =
      (1 : Matrix (Fin m) (Fin m) (InfiniteAdeleRing F)) i j := by
    intro i j
    rw [← AdelicGL.infinite_apply, hinf]
    rfl
  have e2 : ∀ i j w, (GeneralLinearGroupPoints.adelicEquiv F m (localPoint F m v u) i j).2 w =
      finiteComponent F m w (localPoint F m v u) i j := fun _ _ _ => rfl
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · apply adeles_ext F
    · rw [e1, Matrix.one_apply_ne (ne_of_gt (show j < i from hij))]
      rfl
    · intro w
      rw [e2]
      by_cases hw : w = v
      · subst hw
        rw [finiteComponent_localPoint]
        exact hu.1 hij
      · rw [finiteComponent_localPoint_of_ne F m hw]
        exact Matrix.one_apply_ne (ne_of_gt (show j < i from hij))
  · apply adeles_ext F
    · rw [e1, Matrix.one_apply_eq]
      rfl
    · intro w
      rw [e2]
      by_cases hw : w = v
      · subst hw
        rw [finiteComponent_localPoint]
        exact hu.2 i
      · rw [finiteComponent_localPoint_of_ne F m hw]
        exact Matrix.one_apply_eq i

theorem finiteComponent_pad {r t : ℕ} (h : t < r) (v : FinitePlace F) (g : Points F (t + 1)) :
    finiteComponent F (r + 1) v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g) =
      rectGL h (finiteComponent F (t + 1) v g) 0 := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rw [finiteComponent_apply]
  simp only [pad, MulEquiv.apply_symm_apply]
  rw [← rectGL_zero h]
  change ((rectGL h (GeneralLinearGroupPoints.adelicEquiv F (t + 1) g) 0 :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) i j).2 v = _
  rw [rectGL_apply, rectGL_apply]
  split_ifs <;> rfl

theorem infinite_pad {r t : ℕ} (h : t < r) (g : Points F (t + 1)) :
    AdelicGL.infinite F (r + 1) (GeneralLinearGroupPoints.adelicEquiv F (r + 1)
        (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g)) =
      rectGL h (AdelicGL.infinite F (t + 1) (GeneralLinearGroupPoints.adelicEquiv F (t + 1) g)) 0 := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rw [AdelicGL.infinite_apply]
  simp only [pad, MulEquiv.apply_symm_apply]
  rw [← rectGL_zero h]
  change ((rectGL h (GeneralLinearGroupPoints.adelicEquiv F (t + 1) g) 0 :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) i j).1 = _
  rw [rectGL_apply, rectGL_apply]
  split_ifs <;> rfl

/-- `pad(ι_v(P)) = ι_v(diag(P, I))`. -/
theorem pad_localPoint {r t : ℕ} (h : t < r) (v : FinitePlace F)
    (P : FiniteLocalGL F (t + 1) v) :
    pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) (localPoint F (t + 1) v P) =
      localPoint F (r + 1) v (rectGL h P 0) := by
  apply points_ext F
  · rw [infinite_pad F h, infinite_localPoint, infinite_localPoint, rectGL_one_zero h]
  · intro w
    rw [finiteComponent_pad F h]
    by_cases hw : w = v
    · subst hw
      rw [finiteComponent_localPoint, finiteComponent_localPoint]
    · rw [finiteComponent_localPoint_of_ne F _ hw, finiteComponent_localPoint_of_ne F _ hw,
        rectGL_one_zero h]

/-- The component at `v` of `[[g,0,0],[x,I,0],[0,0,1]]`. -/
theorem finiteComponent_rectangularPoint {r t : ℕ} (h : t < r) (v : FinitePlace F)
    (g : Points F (t + 1)) (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F)) :
    finiteComponent F (r + 1) v (rectangularPoint F h g x) =
      rectGL h (finiteComponent F (t + 1) v g) (Matrix.of fun i j => (x i j).2 v) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rw [finiteComponent_apply]
  simp only [rectangularPoint, MulEquiv.apply_symm_apply]
  change ((rectGL h (GeneralLinearGroupPoints.adelicEquiv F (t + 1) g) x :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) i j).2 v = _
  rw [rectGL_apply, rectGL_apply]
  split_ifs <;> rfl

theorem unfoldingWeyl_inv {r t : ℕ} (h : t < r) : (unfoldingWeyl F h)⁻¹ = unfoldingWeyl F h := by
  rw [unfoldingWeyl, ← map_inv, ← map_inv, ← map_inv, Prod.inv_mk, inv_one,
    GeneralLinear.weylLong_inv]

theorem imp_or_imp (p : Prop) {a b : Prop} : (p → a) ∨ (¬p → b) := by
  by_cases hp : p
  · exact Or.inr fun h => absurd hp h
  · exact Or.inl fun h => absurd h hp

theorem unfoldingWeyl_entry {r t : ℕ} (h : t < r) (i j : Fin (r + 1)) :
    (GeneralLinearGroupPoints.adelicEquiv F (r + 1) (unfoldingWeyl F h) i j = 0) ∨
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1) (unfoldingWeyl F h) i j = 1) := by
  simp only [unfoldingWeyl, MulEquiv.apply_symm_apply]
  set e := finCongr (Nat.add_sub_of_le (Nat.le_of_lt (Nat.succ_lt_succ h)))
  obtain ⟨i', rfl⟩ := e.surjective i
  obtain ⟨j', rfl⟩ := e.surjective j
  simp only [GeneralLinear.reindex, MulEquiv.coe_mk, Units.coe_mapEquiv]
  change Matrix.reindex e e _ (e i') (e j') = 0 ∨ Matrix.reindex e e _ (e i') (e j') = 1
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i' <;>
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j' <;>
    simp [GeneralLinear.weylLong_entry, Matrix.one_apply] <;>
    exact imp_or_imp _

end Points

/-! ### Local facts -/

section Local

/-- `diag(ϖ^λ, I) = ϖ^(λ, 0)`. -/
theorem rectGL_torus {K : Type*} [Field K] {r t : ℕ} (h : t < r) (ϖ : Kˣ)
    (lam : Fin (t + 1) → ℤ) :
    rectGL h (torus ϖ lam) 0 =
      torus ϖ (_root_.Langlands.RankinSelberg.UnramifiedUnequalLocalSum.padZeroWeight r lam) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rw [rectGL_apply, torus_val, torus_val]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    by_cases hi : (i : ℕ) < t + 1
    · rw [dif_pos hi, dif_pos hi, Matrix.diagonal_apply_eq,
        _root_.Langlands.RankinSelberg.UnramifiedUnequalLocalSum.padZeroWeight_of_lt lam i hi]
    · rw [dif_neg hi, if_pos rfl,
        _root_.Langlands.RankinSelberg.UnramifiedUnequalLocalSum.padZeroWeight_of_le lam i
          (by omega), zpow_zero, Units.val_one]
  · rw [Matrix.diagonal_apply_ne _ hij]
    split_ifs with h1 h2 h3
    · refine Matrix.diagonal_apply_ne _ fun he => hij (Fin.ext ?_)
      have := congrArg Fin.val he
      simpa using this
    · rfl
    · rfl
    · rfl

/-- `∑_(i<j) (λ_i - λ_j) = ∑_i (n - 2 i) λ_i` (the computation of Worker 5130's
`EqualEulerLocal.sum_sub_of_lt_eq`). -/
theorem modulusExponent_eq {n : ℕ} (lam : Fin (n + 1) → ℤ) :
    modulusExponent lam = ∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * lam i := by
  have h0 : modulusExponent lam = ∑ i, ∑ j, if i < j then lam i - lam j else 0 := by
    rw [modulusExponent]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]
  rw [h0]
  have hsplit : ∀ i j : Fin (n + 1), (if i < j then lam i - lam j else 0) =
      (if i < j then lam i else 0) - (if i < j then lam j else 0) := by
    intro i j
    split_ifs <;> simp
  simp only [hsplit, Finset.sum_sub_distrib]
  have h1 : ∀ i : Fin (n + 1), (∑ j, if i < j then lam i else 0) = ((n : ℤ) - i) * lam i := by
    intro i
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
    push_cast [Nat.add_sub_cancel, hi]
    ring
  have h2 : ∀ j : Fin (n + 1), (∑ i, if i < j then lam j else 0) = (j : ℤ) * lam j := by
    intro j
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      Finset.filter_gt_eq_Iio, Fin.card_Iio]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm (f := fun i j =>
    if i < j then lam j else 0), Finset.sum_congr rfl fun j _ => h2 j, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Local

/-! ### The place `v` -/

section Place

variable {F : Type u} [Field F] [NumberField F]

/-- The canonical valuation of `F_v`, that of `padicField v`. -/
abbrev canonicalValuation (v : FinitePlace F) :=
  @ValuativeRel.valuation _ _ (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel

/-- An additive character of conductor `𝒪_v` is trivial on `𝒪_v`. -/
theorem integer_trivial_of_conductor {v : FinitePlace F}
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0) :
    ∀ y ∈ (canonicalValuation v).integer, ψv y = 1 := by
  intro y hy
  have h1 := ((CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor_spec ψv).1 y
  rw [h0] at h1
  exact h1 (((CompletionPadic.padicField v).canonicalTopologicalData.mem_additiveLattice_zero y).2 hy)

/-- An additive character of conductor `𝒪_v` is nontrivial on `𝒪_v z` for `z ∉ 𝒪_v`. -/
theorem exists_ne_one_of_conductor {v : FinitePlace F}
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0) :
    ∀ z ∉ (canonicalValuation v).integer, ∃ c ∈ (canonicalValuation v).integer,
      (@HarmonicAnalysis.UnitaryAdditiveCharacter.complex _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv) (c * z) ≠ 1 := by
  intro z hz
  by_contra hcon
  push_neg at hcon
  have h1 := (CompletionPadic.padicField v).canonicalTopologicalData.mem_additiveLattice_of_forall_complex_mul_eq_one
    ψv 0 z (fun y hy => by
      rw [mul_comm]
      exact hcon y (((CompletionPadic.padicField v).canonicalTopologicalData.mem_additiveLattice_zero
        y).1 hy))
  rw [h0, sub_zero] at h1
  exact hz (((CompletionPadic.padicField v).canonicalTopologicalData.mem_additiveLattice_zero z).1 h1)

/-- `(w_(n,m))_v ∈ GL_(r+1)(𝒪_v)`. -/
theorem finiteComponent_unfoldingWeyl_mem {r t : ℕ} (h : t < r) (v : FinitePlace F) :
    finiteComponent F (r + 1) v (unfoldingWeyl F h) ∈
      Conductor.integralSubgroup (canonicalValuation v).integer r := by
  have hent : ∀ g : Points F (r + 1), g = unfoldingWeyl F h → ∀ i j,
      finiteComponent F (r + 1) v g i j ∈ (canonicalValuation v).integer := by
    rintro g rfl i j
    rw [finiteComponent_apply]
    rcases unfoldingWeyl_entry F h i j with h0 | h1
    · rw [h0]
      exact zero_mem _
    · rw [h1]
      exact one_mem _
  refine (Conductor.mem_integralSubgroup _ r _).2 ⟨hent _ rfl, ?_⟩
  rw [← LocalPointFactorization.finiteComponent_inv, unfoldingWeyl_inv]
  exact hent _ rfl

/-- **Splitting at `v`.** If `Φ(g ι_v(h)) = Φ(g) φ(h)` whenever `g_v = 1`, then
`Φ(ι_v(Q) Y) = φ(Q) Φ(Y)` as soon as `φ(Q Y_v) = φ(Q) φ(Y_v)`. -/
theorem apply_localPoint_mul_of_split {m : ℕ} (v : FinitePlace F) {Φ : Points F m → ℂ}
    {φ : FiniteLocalGL F m v → ℂ}
    (hΦ : ∀ g, finiteComponent F m v g = 1 → ∀ h, Φ (g * localPoint F m v h) = Φ g * φ h)
    (Q : FiniteLocalGL F m v) (Y : Points F m)
    (hsplit : φ (Q * finiteComponent F m v Y) = φ Q * φ (finiteComponent F m v Y)) :
    Φ (localPoint F m v Q * Y) = φ Q * Φ Y := by
  have hY' := finiteComponent_mul_inv_localPoint F m v Y
  have hY : Y = (Y * (localPoint F m v (finiteComponent F m v Y))⁻¹) *
      localPoint F m v (finiteComponent F m v Y) := by group
  rw [localPoint_mul_eq F m v Q Y, hΦ _ hY', hsplit]
  conv_rhs => rw [hY, hΦ _ hY']
  ring

end Place

/-! ### The dual kernel on the cells at `v` -/

section Spherical

variable {F : Type u} [Field F] [NumberField F]

/-- The spherical Whittaker function `W°⁻` at `v` of the inverse standard character of `ψ_v`,
with Satake parameters `a`. -/
def sphInv (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)) (r : ℕ)
    (a : Fin (r + 1) → ℂˣ) : FiniteLocalGL F (r + 1) v → ℂ :=
  sphericalWhittaker (isUniformizingElement_canonical v)
    (@Whittaker.inverseStandardCharacter _ _
      (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv r)
    (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a

/-- The spherical Whittaker function `W°` at `v` of the standard character of `ψ_v`, with
Satake parameters `a`. -/
def sphStd (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)) (r : ℕ)
    (a : Fin (r + 1) → ℂˣ) : FiniteLocalGL F (r + 1) v → ℂ :=
  sphericalWhittaker (isUniformizingElement_canonical v)
    (@Whittaker.standardCharacter _ _
      (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv r)
    (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a

end Spherical

section Kernel

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The two halves of `UnramifiedWhittakerFactorizationStatement` at the uniformizer
`placeUniformizer v`. -/
theorem whittaker_split (hA : UnramifiedWhittakerFactorizationStatement.{u, uQ})
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r : ℕ}
    {T : Automorphic.CuspidalOperatorRealization F r}
    {P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T}
    {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S)
    (hψS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    {x : T.Space} (hx : IsSphericalOutside F T S x) {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    {a : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      P.spectralSystem.eigenvalues v (fun hvP => hv (hP hvP))) :
    (∀ g, finiteComponent F (r + 1) v g = 1 → ∀ h' : FiniteLocalGL F (r + 1) v,
      cuspWhittaker F T ψ.complex x (g * localPoint F (r + 1) v h') =
        cuspWhittaker F T ψ.complex x g * sphStd v ψv r a h') ∧
    (∀ g, finiteComponent F (r + 1) v g = 1 → ∀ h' : FiniteLocalGL F (r + 1) v,
      cuspWhittaker F T ψ.complex⁻¹ x (g * localPoint F (r + 1) v h') =
        cuspWhittaker F T ψ.complex⁻¹ x g * sphInv v ψv r a h') :=
  ⟨fun g hg h' => (hA F ψ hψ r T P S hP hψS x hx v hv ψv hψv (placeUniformizer v)
      (isUniformizingElement_canonical v) a ha g hg h').1,
    fun g hg h' => (hA F ψ hψ r T P S hP hψS x hx v hv ψv hψv (placeUniformizer v)
      (isUniformizingElement_canonical v) a ha g hg h').2⟩

/-- `W̃(rect(ι_v(Q) g, y) w) = W°⁻(diag(Q, I)) W̃(rect(g, y) w)` when `g_v ∈ GL_(t+1)(𝒪_v)`. -/
theorem whittakerInv_rectangularPoint_localPoint_mul
    (hA : UnramifiedWhittakerFactorizationStatement.{u, uQ})
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r t : ℕ} (h : t < r)
    {T : Automorphic.CuspidalOperatorRealization F r}
    {P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T}
    {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S)
    (hψS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    {x : T.Space} (hx : IsSphericalOutside F T S x) {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    {a : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      P.spectralSystem.eigenvalues v (fun hvP => hv (hP hvP)))
    (Q : FiniteLocalGL F (t + 1) v) {g : Points F (t + 1)}
    (hg : finiteComponent F (t + 1) v g ∈
      Conductor.integralSubgroup (canonicalValuation v).integer t)
    (y : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F)) :
    cuspWhittaker F T ψ.complex⁻¹ x
        (rectangularPoint F h (localPoint F (t + 1) v Q * g) y * unfoldingWeyl F h) =
      sphInv v ψv r a (rectGL h Q 0) *
        cuspWhittaker F T ψ.complex⁻¹ x (rectangularPoint F h g y * unfoldingWeyl F h) := by
  rw [Unfolding.rectangularPoint_mul_left, pad_localPoint F h, mul_assoc]
  refine apply_localPoint_mul_of_split v (whittaker_split hA ψ hψ hP hψS hx hv hψv ha).2 _ _ ?_
  rw [finiteComponent_mul, finiteComponent_rectangularPoint F h]
  let _ := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  unfold sphInv
  exact sphericalWhittaker_inverseStandard_rectGL_zero_mul h (isUniformizingElement_canonical v)
    (integer_trivial_of_conductor h0) (exists_ne_one_of_conductor h0) _ a Q hg _
    (finiteComponent_unfoldingWeyl_mem h v)

/-- `W'(ι_v(Q) g) = W°(Q) W'(g)` when `g_v ∈ GL_(t+1)(𝒪_v)`. -/
theorem whittaker_localPoint_mul_of_integral
    (hA : UnramifiedWhittakerFactorizationStatement.{u, uQ})
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {t : ℕ}
    {T : Automorphic.CuspidalOperatorRealization F t}
    {P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T}
    {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S)
    (hψS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    {x : T.Space} (hx : IsSphericalOutside F T S x) {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    {b : Fin (t + 1) → ℂˣ}
    (hb : Unramified.Eigenvalues.ofTuple b =
      P.spectralSystem.eigenvalues v (fun hvP => hv (hP hvP)))
    (Q : FiniteLocalGL F (t + 1) v) {g : Points F (t + 1)}
    (hg : finiteComponent F (t + 1) v g ∈
      Conductor.integralSubgroup (canonicalValuation v).integer t) :
    cuspWhittaker F T ψ.complex x (localPoint F (t + 1) v Q * g) =
      sphStd v ψv t b Q * cuspWhittaker F T ψ.complex x g := by
  refine apply_localPoint_mul_of_split v (whittaker_split hA ψ hψ hP hψS hx hv hψv hb).1 Q g ?_
  let _ := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  have hθ := isIntegrallyTrivial_standardCharacter (integer_trivial_of_conductor h0) t
  unfold sphStd
  rw [sphericalWhittaker_mul_integral _ _ _ hθ Q hg]
  have h1 : sphericalWhittaker (isUniformizingElement_canonical v)
      (@Whittaker.standardCharacter _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv t)
      (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality b
      (finiteComponent F (t + 1) v g) = 1 := by
    rw [← one_mul (finiteComponent F (t + 1) v g), sphericalWhittaker_mul_integral _ _ _ hθ 1 hg,
      sphericalWhittaker_one _ _ _ hθ]
  rw [h1, mul_one]

/-- The multiplier of the dual kernel on the cell of `Q` at `v`:
`W°⁻_a(diag(Q, I)) W°_b(Q) |det Q|_v^(s - (r-t)/2)`. -/
def cellFactor {r t : ℕ} (h : t < r) (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (a : Fin (r + 1) → ℂˣ) (b : Fin (t + 1) → ℂˣ) (s : ℂ) (Q : FiniteLocalGL F (t + 1) v) : ℂ :=
  sphInv v ψv r a (rectGL h Q 0) * sphStd v ψv t b Q *
    Complex.exp ((s - ((r - t : ℕ) : ℂ) / 2) *
      (Real.log ‖(Matrix.GeneralLinearGroup.det Q).val‖ : ℂ))

/-- The dual kernel at `ι_v(Q) g` is `cellFactor Q` times its value at `g`, when
`g_v ∈ GL_(t+1)(𝒪_v)`. -/
theorem dualKernel_localPoint_mul_of_integral
    (hA : UnramifiedWhittakerFactorizationStatement.{u, uQ})
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r t : ℕ} (h : t < r)
    {Td : Automorphic.CuspidalOperatorRealization F r}
    {Td' : Automorphic.CuspidalOperatorRealization F t}
    {Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td}
    {Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td'}
    {S : Finset (FinitePlace F)} (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S)
    (hψS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    {xd : Td.Space} (hxd : IsSphericalOutside F Td S xd)
    {xd' : Td'.Space} (hxd' : IsSphericalOutside F Td' S xd') {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    {a : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      Pd.spectralSystem.eigenvalues v (fun hvP => hv (hPd hvP)))
    {b : Fin (t + 1) → ℂˣ}
    (hb : Unramified.Eigenvalues.ofTuple b =
      Pd'.spectralSystem.eigenvalues v (fun hvP => hv (hPd' hvP)))
    (s : ℂ) (Q : FiniteLocalGL F (t + 1) v) {g : Points F (t + 1)}
    (hg : finiteComponent F (t + 1) v g ∈
      Conductor.integralSubgroup (canonicalValuation v).integer t) :
    Unfolding.dualKernel F h
        (translateFunction F (r + 1) (unfoldingWeyl F h) (cuspWhittaker F Td ψ.complex⁻¹ xd))
        (cuspWhittaker F Td' ψ.complex xd') s (localPoint F (t + 1) v Q * g) =
      cellFactor h v ψv a b s Q *
        Unfolding.dualKernel F h
          (translateFunction F (r + 1) (unfoldingWeyl F h) (cuspWhittaker F Td ψ.complex⁻¹ xd))
          (cuspWhittaker F Td' ψ.complex xd') s g := by
  have hrect : Unfolding.dualRectIntegral F h
      (translateFunction F (r + 1) (unfoldingWeyl F h) (cuspWhittaker F Td ψ.complex⁻¹ xd))
      (localPoint F (t + 1) v Q * g) =
      sphInv v ψv r a (rectGL h Q 0) * Unfolding.dualRectIntegral F h
        (translateFunction F (r + 1) (unfoldingWeyl F h) (cuspWhittaker F Td ψ.complex⁻¹ xd))
        g := by
    unfold Unfolding.dualRectIntegral translateFunction
    simp_rw [whittakerInv_rectangularPoint_localPoint_mul hA ψ hψ h hPd hψS hxd hv hψv h0 ha Q
      hg]
    exact integral_const_mul _ _
  unfold Unfolding.dualKernel
  rw [hrect, whittaker_localPoint_mul_of_integral hA ψ hψ hPd' hψS hxd' hv hψv h0 hb Q hg,
    detPower_localPoint_mul, cellFactor]
  ring

/-- **The cell property of the dual kernel.** At `g` with `g_v ∈ N_(t+1)(F_v) GL_(t+1)(𝒪_v)`,
the dual kernel at `ι_v(ϖ_v^λ) g` is `cellFactor (ϖ_v^λ)` times its value at `g`. -/
theorem dualKernel_localPoint_torus_mul
    (hA : UnramifiedWhittakerFactorizationStatement.{u, uQ})
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r t : ℕ} (h : t < r)
    {T Td : Automorphic.CuspidalOperatorRealization F r}
    {T' Td' : Automorphic.CuspidalOperatorRealization F t}
    {Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td}
    {Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td'}
    {S : Finset (FinitePlace F)} (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S)
    (hψS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    {x : T.Space} {x' : T'.Space}
    {xd : Td.Space} (hxdS : IsSphericalOutside F Td S xd)
    (hxd : cuspWhittaker F Td ψ.complex⁻¹ xd =
      dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x))
    {xd' : Td'.Space} (hxdS' : IsSphericalOutside F Td' S xd')
    (hxd' : cuspWhittaker F Td' ψ.complex xd' =
      dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x'))
    {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    {a : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      Pd.spectralSystem.eigenvalues v (fun hvP => hv (hPd hvP)))
    {b : Fin (t + 1) → ℂˣ}
    (hb : Unramified.Eigenvalues.ofTuple b =
      Pd'.spectralSystem.eigenvalues v (fun hvP => hv (hPd' hvP)))
    (s : ℂ) (lam : Fin (t + 1) → ℤ) {g : Points F (t + 1)}
    (hg : IsUnipotentIntegral F (t + 1) v (finiteComponent F (t + 1) v g)) :
    Unfolding.dualKernel F h (Unfolding.dualWhittaker F h T ψ.complex x)
        (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s
        (localPoint F (t + 1) v (torus (placeUniformizer v) lam) * g) =
      cellFactor h v ψv a b s (torus (placeUniformizer v) lam) *
        Unfolding.dualKernel F h (Unfolding.dualWhittaker F h T ψ.complex x)
          (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s g := by
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  have hN : ∀ n ∈ unipotentAdelic F (t + 1), ∀ y,
      Unfolding.dualKernel F h (Unfolding.dualWhittaker F h T ψ.complex x)
          (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s (n * y) =
        Unfolding.dualKernel F h (Unfolding.dualWhittaker F h T ψ.complex x)
          (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s y :=
    fun n hn y => Unfolding.dualKernel_whittaker_unipotent_mul F h T T' ψ.complex hstd x x' s
      ⟨n, hn⟩ y
  obtain ⟨u, hu, k, hk, hgv⟩ := exists_eq_mul_of_isUnipotentIntegral v hg
  obtain ⟨g₁, rfl⟩ : ∃ g₁, g = localPoint F (t + 1) v u * g₁ :=
    ⟨(localPoint F (t + 1) v u)⁻¹ * g, by group⟩
  have hg₁ : finiteComponent F (t + 1) v g₁ = k := by
    rw [finiteComponent_mul, finiteComponent_localPoint] at hgv
    exact mul_left_cancel hgv
  set ϖt := torus (placeUniformizer v) lam with hϖt
  have e : localPoint F (t + 1) v ϖt * (localPoint F (t + 1) v u * g₁) =
      localPoint F (t + 1) v (ϖt * u * ϖt⁻¹) * (localPoint F (t + 1) v ϖt * g₁) := by
    rw [← mul_assoc (localPoint F (t + 1) v (ϖt * u * ϖt⁻¹)), ← localPoint_mul,
      inv_mul_cancel_right, localPoint_mul, mul_assoc]
  rw [e, hN _ (localPoint_mem_unipotentAdelic F v (torus_mul_mul_inv_mem _ lam hu)),
    hN _ (localPoint_mem_unipotentAdelic F v hu)]
  simp only [Unfolding.dualWhittaker]
  rw [← hxd, ← hxd']
  exact dualKernel_localPoint_mul_of_integral hA ψ hψ h hPd hPd' hψS hxdS hxdS' hv hψv h0 ha hb s
    _ (by rw [hg₁]; exact hk)

end Kernel

/-! ### The local terms and the local Euler factor -/

section LocalTerm

variable {F : Type u} [Field F] [NumberField F]

/-- The residue cardinality of the canonical realization of `F_v` is `N(v)`. -/
theorem residueCardinality_canonical (v : FinitePlace F) :
    (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality =
      Ideal.absNorm v.asIdeal := by
  rw [← CompletionPadic.topologicalData_eq_canonicalTopologicalData]
  exact HeckeEulerProduct.residueCardinality_eq v

/-- The inverse modulus times the cell multiplier is the local term of
`UnramifiedUnequalLocalSum`. -/
theorem zpow_modulusExponent_mul_cellFactor {r t : ℕ} (h : t < r) (v : FinitePlace F)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    (a : Fin (r + 1) → ℂˣ) (b : Fin (t + 1) → ℂˣ) (s : ℂ) (lam : Fin (t + 1) → ℤ) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ modulusExponent lam *
        cellFactor h v ψv a b s (torus (placeUniformizer v) lam) =
      _root_.Langlands.RankinSelberg.UnramifiedUnequalLocalSum.localTerm
        (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a b s lam := by
  let _ := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  have hθ := isIntegrallyTrivial_inverseStandardCharacter (integer_trivial_of_conductor h0) r
  have hθ' := isIntegrallyTrivial_standardCharacter (integer_trivial_of_conductor h0) t
  rw [_root_.Langlands.RankinSelberg.UnramifiedUnequalLocalSum.localTerm_eq_sphericalWhittaker
    (isUniformizingElement_canonical v) hθ hθ', cellFactor]
  unfold sphInv sphStd
  rw [rectGL_torus h, modulusExponent_eq, log_norm_det_torus, residueCardinality_canonical v,
    Real.log_zpow]
  push_cast
  ring_nf

theorem mem_ofTuple {n : ℕ} (a : Fin n → ℂˣ) (i : Fin n) :
    a i ∈ ((Unramified.Eigenvalues.ofTuple a : Unramified.Eigenvalues n) : Multiset ℂˣ) := by
  change a i ∈ ((List.ofFn a : List ℂˣ) : Multiset ℂˣ)
  rw [Multiset.mem_coe, List.mem_ofFn]
  exact ⟨i, rfl⟩

variable [CompactSpace (AdeleQuotient F)]

/-- The unramified pair factor in terms of Satake tuples. -/
theorem partialEulerFactor_eq {r t : ℕ}
    {Td : Automorphic.CuspidalOperatorRealization F r}
    {Td' : Automorphic.CuspidalOperatorRealization F t}
    {Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td}
    {Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td'}
    {S : Finset (FinitePlace F)} (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S)
    (v : {v : FinitePlace F // v ∉ S}) {a : Fin (r + 1) → ℂˣ} {b : Fin (t + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      Pd.spectralSystem.eigenvalues v.1 (fun hvP => v.2 (hPd hvP)))
    (hb : Unramified.Eigenvalues.ofTuple b =
      Pd'.spectralSystem.eigenvalues v.1 (fun hvP => v.2 (hPd' hvP))) (s : ℂ) :
    partialEulerFactor Pd Pd' hPd hPd' v s =
      (∏ i : Fin (r + 1), ∏ j : Fin (t + 1),
        (1 - (a i : ℂ) * b j *
          ((CompletionPadic.padicField v.1).canonicalTopologicalData.residueCardinality : ℂ) ^
            (-s)))⁻¹ := by
  unfold partialEulerFactor
  rw [← ha, ← hb, CuspidalPairFunctionalEquation.pairEulerPolynomial_ofTuple]
  simp [Polynomial.eval_prod, RankinSelberg.spectralPoint]

end LocalTerm

/-! ### The one-place step -/

section Step

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The dual integrand at the class of `ι_v(ϖ_v^λ) g` is `cellFactor (ϖ_v^λ)` times its value at
the class of `g`, for classes with `g_v ∈ N_(t+1)(F_v) GL_(t+1)(𝒪_v)`. -/
theorem integrand_shift (hA : UnramifiedWhittakerFactorizationStatement.{u, uQ})
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r t : ℕ} (h : t < r)
    {T Td : Automorphic.CuspidalOperatorRealization F r}
    {T' Td' : Automorphic.CuspidalOperatorRealization F t}
    {Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td}
    {Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td'}
    {S : Finset (FinitePlace F)} (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S)
    (hψS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    {x : T.Space} {x' : T'.Space}
    {xd : Td.Space} (hxdS : IsSphericalOutside F Td S xd)
    (hxd : cuspWhittaker F Td ψ.complex⁻¹ xd =
      dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x))
    {xd' : Td'.Space} (hxdS' : IsSphericalOutside F Td' S xd')
    (hxd' : cuspWhittaker F Td' ψ.complex xd' =
      dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x'))
    {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    {a : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      Pd.spectralSystem.eigenvalues v (fun hvP => hv (hPd hvP)))
    {b : Fin (t + 1) → ℂˣ}
    (hb : Unramified.Eigenvalues.ofTuple b =
      Pd'.spectralSystem.eigenvalues v (fun hvP => hv (hPd' hvP)))
    (s : ℂ) (lam : Fin (t + 1) → ℤ) {A : Finset (FinitePlace F)} (hvA : v ∉ A)
    {q : WhittakerQuotient F (t + 1)} (hq : q ∈ unipotentIntegralClasses F (t + 1) A) :
    dualWhittakerIntegrand F h (Unfolding.dualWhittaker F h T ψ.complex x)
        (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s
        (LeftCosetSpace.mk (unipotentAdelic F (t + 1))
          (localPoint F (t + 1) v (torus (placeUniformizer v) lam) * q.out)) =
      cellFactor h v ψv a b s (torus (placeUniformizer v) lam) *
        dualWhittakerIntegrand F h (Unfolding.dualWhittaker F h T ψ.complex x)
          (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s q := by
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  rw [Unfolding.dualWhittakerIntegrand_eq, Unfolding.dualWhittakerIntegrand_eq]
  obtain ⟨n, hn⟩ := Unfolding.exists_out_mk_eq (unipotentAdelic F (t + 1))
    (localPoint F (t + 1) v (torus (placeUniformizer v) lam) * q.out)
  rw [hn, Unfolding.dualKernel_whittaker_unipotent_mul F h T T' ψ.complex hstd x x' s n]
  exact dualKernel_localPoint_torus_mul hA ψ hψ h hPd hPd' hψS hxdS hxd hxdS' hxd' hv hψv h0 ha hb
    s lam ((show q.out ∈ unipotentIntegralOutside F (t + 1) A from hq) v hvA)

/-- **The one-place step.** Adding a finite place `v ∉ A` (with `S ⊆ A`) to the set `A`
multiplies the partial dual integral over `unipotentIntegralClasses F (t+1) A` by the sum `L`
of the local terms at `v`. -/
theorem setIntegral_cons_eq (hA : UnramifiedWhittakerFactorizationStatement.{u, uQ})
    (hB : WhittakerCellDecompositionStatement.{u})
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r t : ℕ} (h : t < r)
    {T Td : Automorphic.CuspidalOperatorRealization F r}
    {T' Td' : Automorphic.CuspidalOperatorRealization F t}
    {Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td}
    {Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td'}
    {S : Finset (FinitePlace F)} (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S)
    (hψS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    {x : T.Space} {x' : T'.Space}
    {xd : Td.Space} (hxdS : IsSphericalOutside F Td S xd)
    (hxd : cuspWhittaker F Td ψ.complex⁻¹ xd =
      dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x))
    {xd' : Td'.Space} (hxdS' : IsSphericalOutside F Td' S xd')
    (hxd' : cuspWhittaker F Td' ψ.complex xd' =
      dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x'))
    {v : FinitePlace F} (hv : v ∉ S)
    {ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)}
    (hψv : ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h0 : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    {a : Fin (r + 1) → ℂˣ}
    (ha : Unramified.Eigenvalues.ofTuple a =
      Pd.spectralSystem.eigenvalues v (fun hvP => hv (hPd hvP)))
    {b : Fin (t + 1) → ℂˣ}
    (hb : Unramified.Eigenvalues.ofTuple b =
      Pd'.spectralSystem.eigenvalues v (fun hvP => hv (hPd' hvP)))
    (s : ℂ) {L : ℂ}
    (hL : HasSum (_root_.Langlands.RankinSelberg.UnramifiedUnequalLocalSum.localTerm
      (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a b s) L)
    (hf : Integrable (dualWhittakerIntegrand F h (Unfolding.dualWhittaker F h T ψ.complex x)
      (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s)
      (whittakerQuotientMeasure F (t + 1)))
    {A : Finset (FinitePlace F)} (hvA : v ∉ A) :
    ∫ q in unipotentIntegralClasses F (t + 1) (Finset.cons v A hvA),
        dualWhittakerIntegrand F h (Unfolding.dualWhittaker F h T ψ.complex x)
          (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s q
        ∂whittakerQuotientMeasure F (t + 1) =
      L * ∫ q in unipotentIntegralClasses F (t + 1) A,
        dualWhittakerIntegrand F h (Unfolding.dualWhittaker F h T ψ.complex x)
          (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s q
        ∂whittakerQuotientMeasure F (t + 1) := by
  classical
  set f := dualWhittakerIntegrand F h (Unfolding.dualWhittaker F h T ψ.complex x)
    (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s with hfdef
  obtain ⟨-, hsum⟩ := hB F (t + 1) A v hvA (placeUniformizer v) (isUniformizingElement_valued v)
    f hf
  have hterm : ∀ lam : Fin (t + 1) → ℤ,
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ modulusExponent lam *
          ∫ q in unipotentIntegralClasses F (t + 1) A,
            f (LeftCosetSpace.mk (unipotentAdelic F (t + 1))
              (localPoint F (t + 1) v (torus (placeUniformizer v) lam) * q.out))
            ∂whittakerQuotientMeasure F (t + 1) =
        _root_.Langlands.RankinSelberg.UnramifiedUnequalLocalSum.localTerm
            (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a b s lam *
          ∫ q in unipotentIntegralClasses F (t + 1) A, f q ∂whittakerQuotientMeasure F (t + 1) := by
    intro lam
    have hcell : ∫ q in unipotentIntegralClasses F (t + 1) A,
          f (LeftCosetSpace.mk (unipotentAdelic F (t + 1))
            (localPoint F (t + 1) v (torus (placeUniformizer v) lam) * q.out))
          ∂whittakerQuotientMeasure F (t + 1) =
        ∫ q in unipotentIntegralClasses F (t + 1) A,
          cellFactor h v ψv a b s (torus (placeUniformizer v) lam) * f q
          ∂whittakerQuotientMeasure F (t + 1) :=
      setIntegral_congr_fun (measurableSet_unipotentIntegralClasses (t + 1) A) fun q hq =>
        integrand_shift hA ψ hψ h hPd hPd' hψS hxdS hxd hxdS' hxd' hv hψv h0 ha hb s lam hvA hq
    rw [hcell, integral_const_mul, ← mul_assoc, zpow_modulusExponent_mul_cellFactor h v h0]
  have e : ∫ q in unipotentIntegralClasses F (t + 1) (insert v A), f q
      ∂whittakerQuotientMeasure F (t + 1) =
      L * ∫ q in unipotentIntegralClasses F (t + 1) A, f q ∂whittakerQuotientMeasure F (t + 1) := by
    refine hsum.unique ?_
    have h2 := hL.mul_right
      (∫ q in unipotentIntegralClasses F (t + 1) A, f q ∂whittakerQuotientMeasure F (t + 1))
    convert h2 using 1
    funext lam
    exact hterm lam
  rw [Finset.cons_eq_insert]
  convert e using 4

end Step

/-! ### The reduction -/

/-- **The reduction.** `UnequalDualEulerFactorizationStatement` follows from the one-place
factorization of global Whittaker functions, the one-place cell decomposition of the Whittaker
quotient measure, the unfolding statement and the contragredient description of dual
Whittaker functions. -/
theorem unequalDualEulerFactorization_of_premises
    (hA : UnramifiedWhittakerFactorizationStatement.{u, uQ})
    (hB : WhittakerCellDecompositionStatement.{u})
    (hU : UnequalUnfoldingStatement.{u})
    (hD : ContragredientDualWhittakerStatement.{u}) :
    UnequalDualEulerFactorizationStatement.{u, uQ} := by
  intro F _ _ _ ψ hψ r t h T Td T' Td' hTd hTd' Pd Pd' S hPd hPd' hψS
  obtain ⟨C, -, hC⟩ := hU F r t h T T'
  obtain ⟨σE, hσE⟩ := exists_partialEulerFactor_convergence Pd Pd' hPd hPd'
  obtain ⟨Ab, hAb⟩ := exists_hasSatakeBound_presentation Td Pd
  obtain ⟨Bb, hBb⟩ := exists_hasSatakeBound_presentation Td' Pd'
  obtain ⟨σC, hσC⟩ :=
    _root_.Langlands.RankinSelberg.UnramifiedUnequalLocalSum.exists_hasSum_localTerm h Ab Bb
  refine ⟨max (1 + C) (max σE σC), fun x x' hx hx' => ?_⟩
  intro Wdual W'dual s hs
  have hs1 : 1 + C < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hsE : σE < s.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hsC : σC < s.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  have hconv : DualWhittakerAbsolutelyConvergent F h Wdual W'dual s := by
    have h1 : (1 - s).re < -C := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have h2 := ((hC ψ.complex hstd x x').2 (1 - s) h1).1
    rwa [sub_sub_cancel] at h2
  obtain ⟨xd, hxdS, hxd⟩ := hD F ψ hψ r T Td hTd S x hx
  obtain ⟨xd', hxdS', hxd'⟩ := hD F (inverseCharacter ψ) (inverseCharacter_rational ψ hψ) t T' Td'
    hTd' S x' hx'
  rw [complex_inverseCharacter, inv_inv] at hxd'
  obtain ⟨hsumE, hprod⟩ := hσE s hsE
  refine ⟨hconv, hsumE, _, hprod, ?_⟩
  suffices hstep : ∀ A : Finset (FinitePlace F), S ⊆ A → ∀ v : {v : FinitePlace F // v ∉ S},
      ∀ hv : v.1 ∉ A,
      ∫ q in unipotentIntegralClasses F (t + 1) (Finset.cons v.1 A hv),
          dualWhittakerIntegrand F h Wdual W'dual s q ∂whittakerQuotientMeasure F (t + 1) =
        partialEulerFactor Pd Pd' hPd hPd' v s *
          ∫ q in unipotentIntegralClasses F (t + 1) A,
            dualWhittakerIntegrand F h Wdual W'dual s q ∂whittakerQuotientMeasure F (t + 1) by
    have key := integral_eq_hasProd_mul_setIntegral hconv.2.2 hprod hstep
    rw [dualWhittakerIntegral, key, partialDualWhittakerIntegral, mul_comm]
    rfl
  intro A hSA v hvA
  obtain ⟨ψv, hψv, h0⟩ := hψS v.1 v.2
  obtain ⟨a, ha⟩ := Unramified.Eigenvalues.ofTuple_surjective (r + 1)
    (Pd.spectralSystem.eigenvalues v.1 (fun hvP => v.2 (hPd hvP)))
  obtain ⟨b, hb⟩ := Unramified.Eigenvalues.ofTuple_surjective (t + 1)
    (Pd'.spectralSystem.eigenvalues v.1 (fun hvP => v.2 (hPd' hvP)))
  have hq1 : 1 < (CompletionPadic.padicField v.1).canonicalTopologicalData.residueCardinality :=
    lt_of_lt_of_le one_lt_two (CuspidalPairEulerConvergence.two_le_residueCardinality v.1)
  have hab : ∀ i, ‖(a i : ℂ)‖ ≤
      ((CompletionPadic.padicField v.1).canonicalTopologicalData.residueCardinality : ℝ) ^ Ab :=
    fun i => hAb v.1 (fun hvP => v.2 (hPd hvP)) (a i) (by rw [← ha]; exact mem_ofTuple a i)
  have hbb : ∀ j, ‖(b j : ℂ)‖ ≤
      ((CompletionPadic.padicField v.1).canonicalTopologicalData.residueCardinality : ℝ) ^ Bb :=
    fun j => hBb v.1 (fun hvP => v.2 (hPd' hvP)) (b j) (by rw [← hb]; exact mem_ofTuple b j)
  obtain ⟨-, hL⟩ := hσC _ hq1 a b hab hbb s hsC
  rw [partialEulerFactor_eq hPd hPd' v ha hb s]
  exact setIntegral_cons_eq hA hB ψ hψ h hPd hPd' hψS hxdS hxd hxdS' hxd' v.2 hψv h0 ha hb s hL
    hconv.2.2 hvA

/-- The reduction as a proposition: `UnequalDualEulerFactorizationStatement` follows from
`UnramifiedWhittakerFactorizationStatement`, `WhittakerCellDecompositionStatement`,
`UnequalUnfoldingStatement` and `ContragredientDualWhittakerStatement`. -/
def UnequalDualEulerFactorizationReductionStatement : Prop :=
  UnramifiedWhittakerFactorizationStatement.{u, uQ} → WhittakerCellDecompositionStatement.{u} →
    UnequalUnfoldingStatement.{u} → ContragredientDualWhittakerStatement.{u} →
      UnequalDualEulerFactorizationStatement.{u, uQ}

theorem unequalDualEulerFactorizationReduction :
    UnequalDualEulerFactorizationReductionStatement.{u, uQ} :=
  fun hA hB hU hD => unequalDualEulerFactorization_of_premises hA hB hU hD

end Langlands.Global.RankinSelbergGlobal.UnequalDualEuler
