import Langlands.Global.RankinSelberg.FiniteWhittakerDualProduct
import Langlands.Global.RankinSelberg.RealPlaceWhittakerCovariance

/-! # Products of archimedean Whittaker restrictions and their duals -/

noncomputable section
open NumberField
open scoped Classical CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerProducts

open Langlands.Automorphic Langlands.GeneralLinear

variable {F : Type u} [Field F] [NumberField F]

local instance (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

private theorem map_dualArgument {A K : Type*} [CommRing A] [CommRing K]
    (f : A →+* K) {n : ℕ} (g : Langlands.GeneralLinear n A) :
    Matrix.GeneralLinearGroup.map f (weylLong n A * inverseTranspose n A g) =
      weylLong n K * inverseTranspose n K (Matrix.GeneralLinearGroup.map f g) := by
  have hw : Matrix.GeneralLinearGroup.map f (weylLong n A) = weylLong n K := by
    ext i j
    simp only [Matrix.GeneralLinearGroup.map_apply, weylLong_entry]
    split_ifs <;> simp
  rw [map_mul, hw, UnequalAnalytic.inverseTranspose_map]

/-- The global dual argument projects to the real dual argument. -/
theorem realComponent_dualPoint (n : ℕ) (v : {v : InfinitePlace F // v.IsReal})
    (g : Points F n) :
    realComponent F n v (Unfolding.dualPoint F n g) =
      weylLong n ℝ * inverseTranspose n ℝ (realComponent F n v g) := by
  let f : Adeles F →+* ℝ :=
    ((Pi.evalRingHom (fun _ : {v : InfinitePlace F // v.IsReal} => ℝ) v).comp
      (RingHom.fst _ _)).comp
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _))
  have h (x : Points F n) :
      realComponent F n v x =
        Matrix.GeneralLinearGroup.map f (GeneralLinearGroupPoints.adelicEquiv F n x) :=
    Units.ext rfl
  rw [h, h, Unfolding.dualPoint, MulEquiv.apply_symm_apply]
  exact map_dualArgument f _

/-- The global dual argument projects to the complex dual argument. -/
theorem complexComponent_dualPoint (n : ℕ) (v : {v : InfinitePlace F // v.IsComplex})
    (g : Points F n) :
    complexComponent F n v (Unfolding.dualPoint F n g) =
      weylLong n ℂ * inverseTranspose n ℂ (complexComponent F n v g) := by
  let f : Adeles F →+* ℂ :=
    ((Pi.evalRingHom (fun _ : {v : InfinitePlace F // v.IsComplex} => ℂ) v).comp
      (RingHom.snd _ _)).comp
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _))
  have h (x : Points F n) :
      complexComponent F n v x =
        Matrix.GeneralLinearGroup.map f (GeneralLinearGroupPoints.adelicEquiv F n x) :=
    Units.ext rfl
  rw [h, h, Unfolding.dualPoint, MulEquiv.apply_symm_apply]
  exact map_dualArgument f _

/-- Paired left-unipotent invariance is preserved by the common dual transform. -/
theorem dual_pair_invariant {K : Type*} [Field K] (n : ℕ)
    (W W' : Langlands.GeneralLinear n K → ℂ)
    (h : ∀ (u : Langlands.GeneralLinear.upperUnipotent n K) g,
      W (u.val * g) * W' (u.val * g) = W g * W' g)
    (u : Langlands.GeneralLinear.upperUnipotent n K) (g : Langlands.GeneralLinear n K) :
    ArchimedeanLocal.dualFunction n W (u.val * g) *
      ArchimedeanLocal.dualFunction n W' (u.val * g) =
        ArchimedeanLocal.dualFunction n W g * ArchimedeanLocal.dualFunction n W' g := by
  have hui := (Langlands.GeneralLinear.upperUnipotent n K).inv_mem u.property
  have hu := Unfolding.isUnitriangular_dualConjGL n K u.val ⟨hui.1, hui.2⟩
  let ud : Langlands.GeneralLinear.upperUnipotent n K :=
    ⟨Unfolding.dualConjGL n K u.val, hu.1, hu.2⟩
  have he : weylLong n K * inverseTranspose n K (u.val * g) =
      ud.val * (weylLong n K * inverseTranspose n K g) := by
    simp only [ud, Unfolding.dualConjGL_apply, map_mul, mul_assoc]
    rw [← mul_assoc (weylLong n K) (weylLong n K), weylLong_mul_self, one_mul]
  simp only [ArchimedeanLocal.dualFunction, he]
  exact h ud _

private theorem complexPlacePoint_mul (n : ℕ) (v : {v : InfinitePlace F // v.IsComplex})
    (g h : Langlands.GeneralLinear n ℂ) :
    complexPlacePoint F n v (g * h) =
      complexPlacePoint F n v g * complexPlacePoint F n v h := by
  simpa only [complexPlacePoint, map_mul, one_mul] using
    adelicPoint_mul F n (complexPlaceGL F n v g) (complexPlaceGL F n v h) 1 1

private theorem complexPlacePoint_mem_unipotent (n : ℕ)
    (v : {v : InfinitePlace F // v.IsComplex})
    (u : Langlands.GeneralLinear.upperUnipotent n ℂ) :
    complexPlacePoint F n v u.val ∈ unipotentAdelic F n := by
  have htri : PrimitiveAdelicHeight.IsUnitriangular (complexPlaceGL F n v u.val).val := by
    constructor
    · intro i j hij
      apply Prod.ext
      · funext w
        exact Matrix.one_apply_ne hij.ne'
      · funext w
        change (Pi.mulSingle v u.val : _ → Langlands.GeneralLinear n ℂ) w i j = 0
        by_cases hw : w = v
        · subst w
          simpa only [Pi.mulSingle_eq_same, id_eq] using UpperUnipotent.entry_eq_zero u hij
        · rw [Pi.mulSingle_eq_of_ne hw]
          exact Matrix.one_apply_ne hij.ne'
    · intro i
      apply Prod.ext
      · funext w
        exact Matrix.one_apply_eq i
      · funext w
        change (Pi.mulSingle v u.val : _ → Langlands.GeneralLinear n ℂ) w i i = 1
        by_cases hw : w = v
        · subst w
          simpa only [Pi.mulSingle_eq_same] using UpperUnipotent.entry_diag u i
        · rw [Pi.mulSingle_eq_of_ne hw]
          exact Matrix.one_apply_eq i
  rw [Unfolding.mem_unipotentAdelic_iff]
  simp only [complexPlacePoint, adelicPoint, MulEquiv.apply_symm_apply]
  constructor
  · intro i j hij
    apply Prod.ext
    · change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        ((complexPlaceGL F n v u.val).val i j) = 0
      rw [htri.1 hij, map_zero]
    · exact Matrix.one_apply_ne hij.ne'
  · intro i
    apply Prod.ext
    · change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        ((complexPlaceGL F n v u.val).val i i) = 1
      rw [htri.2 i, map_one]
    · exact Matrix.one_apply_eq i

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

private theorem global_pair_invariant
    (T T' : CuspidalOperatorRealization F r)
    (χ : AddChar (Adeles F) ℂ) (hχ : IsStandardAdditiveCharacter F χ)
    (x : T.Space) (x' : T'.Space) (u : unipotentAdelic F (r + 1))
    (g g' : Points F (r + 1)) :
    cuspWhittaker F T χ x (u.val * g) * cuspWhittaker F T' χ⁻¹ x' (u.val * g') =
      cuspWhittaker F T χ x g * cuspWhittaker F T' χ⁻¹ x' g' := by
  rw [Unfolding.cuspWhittaker_mul_left F T χ hχ,
    Unfolding.cuspWhittaker_mul_left F T' χ⁻¹
      (Unfolding.isStandardAdditiveCharacter_inv F χ hχ),
    UnramifiedWhittaker.genericCharacter_inv]
  let θ := genericCharacter F r χ (fun _ => 1) u
  have hθ : θ ≠ 0 := by
    intro hzero
    have hn : ‖θ‖ = 1 := Unfolding.norm_genericCharacter F r χ hχ.2.2.2 (fun _ => 1) u
    rw [hzero, norm_zero] at hn
    exact zero_ne_one hn
  change (θ * _) * (θ⁻¹ * _) = _
  rw [mul_mul_mul_comm, mul_inv_cancel₀ hθ, one_mul]

/-- Opposite-character restrictions at a complex place have an invariant product. -/
theorem complex_pair_invariant (T T' : CuspidalOperatorRealization F r)
    (χ : AddChar (Adeles F) ℂ) (hχ : IsStandardAdditiveCharacter F χ)
    (v : {v : InfinitePlace F // v.IsComplex})
    {W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ}
    (hW : IsComplexPlaceWhittaker F T χ v W)
    (hW' : IsComplexPlaceWhittaker F T' χ⁻¹ v W')
    (u : Langlands.GeneralLinear.upperUnipotent (r + 1) ℂ)
    (g : Langlands.GeneralLinear (r + 1) ℂ) :
    W (u.val * g) * W' (u.val * g) = W g * W' g := by
  obtain ⟨x, a, rfl⟩ := hW
  obtain ⟨x', a', rfl⟩ := hW'
  simp only [complexPlacePoint_mul, mul_assoc]
  exact global_pair_invariant T T' χ hχ x x'
    ⟨_, complexPlacePoint_mem_unipotent (r + 1) v u⟩ _ _

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerProducts
