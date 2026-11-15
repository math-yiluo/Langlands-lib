import Langlands.Representation.Classification.LeftCuspidalDerivative.Frobenius
import Langlands.Representation.Compact.CharZeroAverage
import Langlands.Representation.CuspidalSupport.ConstituentUniverse
import Langlands.Representation.CuspidalSupport.CuspidalityComparisonProof
import Langlands.Group.GL.BlockIwahoriBasis
import Langlands.Representation.Smooth.Admissibility.FiniteLengthProof
import Langlands.Representation.Parabolic.FiniteLengthFunctorProof
import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Classification.SegmentHeadSupportStep
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Exponents.WeylBranchPiecesStatement

/-!
# Building intertwiners into two-factor external tensors

Generic tools, over a pair of groups `H 0`, `H 1`, for the first-block criterion: a nonzero
first-factor intertwiner `φ : W|_{H 0} → τ 0` from a smooth representation `W` of
`H 0 × H 1` produces a nonzero intertwiner `W → τ 0 ⊠ τ 1` when `τ 1` is the smooth right
regular representation of `H 1` and `τ 0` is admissible; and an irreducible subquotient of
`W|_{H 0}` is a subquotient of a slice of vectors fixed by a compact open subgroup of `H 1`.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Classification.LeftCuspidalDerivative

universe uF uV uG uX uA uS uU

section TensorEvaluation

variable {A : Type uA} {S : Type uS} [AddCommGroup A] [Module ℂ A] [AddCommGroup S] [Module ℂ S]

/-- A nonzero tensor survives contraction against some functional on the left factor. -/
theorem exists_dual_lid_rTensor_ne_zero {w : A ⊗[ℂ] S} (hw : w ≠ 0) :
    ∃ φ : Module.Dual ℂ A, TensorProduct.lid ℂ S (φ.rTensor S w) ≠ 0 := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ A
  let e := TensorProduct.equivFinsuppOfBasisLeft (R := ℂ) (N := S) b
  have hew : e w ≠ 0 := fun h => hw (e.injective (h.trans (map_zero e).symm))
  obtain ⟨i, hi⟩ : ∃ i, e w i ≠ 0 := by
    by_contra h
    push Not at h
    exact hew (Finsupp.ext h)
  refine ⟨b.coord i, ?_⟩
  rw [← TensorProduct.equivFinsuppOfBasisLeft_apply]
  exact hi

variable {X : Type uX}

/-- Evaluation of `a ⊗ s` as the function `x ↦ e s x • a`. -/
def tensorEval (e : S →ₗ[ℂ] (X → ℂ)) : A ⊗[ℂ] S →ₗ[ℂ] (X → A) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun (a : A) (s : S) => fun x => e s x • a)
    (fun a a' s => by funext x; simp [smul_add])
    (fun c a s => by funext x; simp [smul_comm c])
    (fun a s s' => by funext x; simp [add_smul])
    (fun c a s => by funext x; simp [mul_smul]))

@[simp]
theorem tensorEval_tmul (e : S →ₗ[ℂ] (X → ℂ)) (a : A) (s : S) (x : X) :
    tensorEval e (a ⊗ₜ s) x = e s x • a := rfl

theorem tensorEval_dual (e : S →ₗ[ℂ] (X → ℂ)) (φ : Module.Dual ℂ A) (t : A ⊗[ℂ] S) (x : X) :
    φ (tensorEval e t x) = e (TensorProduct.lid ℂ S (φ.rTensor S t)) x := by
  induction t using TensorProduct.inductionOn with
  | tmul a s => simp [mul_comm]
  | add t t' ht ht' =>
    simp only [map_add, Pi.add_apply] at ht ht' ⊢
    rw [ht, ht']

theorem tensorEval_injective (e : S →ₗ[ℂ] (X → ℂ)) (he : Function.Injective e) :
    Function.Injective (tensorEval (A := A) e) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  by_contra hne
  obtain ⟨φ, hφ⟩ := exists_dual_lid_rTensor_ne_zero hne
  have h1 : e (TensorProduct.lid ℂ S (φ.rTensor S t)) ≠ 0 :=
    fun h => hφ (he (h.trans (map_zero e).symm))
  obtain ⟨x, hx⟩ := Function.ne_iff.mp h1
  apply hx
  rw [← tensorEval_dual, ht]
  simp

end TensorEvaluation

section FinTwo

variable {V : Fin 2 → Type uX} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- The binary splitting of a two-factor indexed tensor. -/
def finTwoTensorEquiv : PiTensorProduct ℂ V ≃ₗ[ℂ] V 0 ⊗[ℂ] V 1 :=
  (FiniteTensor.headTailLinearEquiv (r := 1) ℂ V).trans
    (TensorProduct.congr (LinearEquiv.refl ℂ (V 0))
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun j : Fin 1 => V j.succ) 0))

@[simp]
theorem finTwoTensorEquiv_tprod (v : ∀ i, V i) :
    finTwoTensorEquiv (PiTensorProduct.tprod ℂ v) = v 0 ⊗ₜ v 1 := by
  simp only [finTwoTensorEquiv, LinearEquiv.trans_apply,
    FiniteTensor.headTailLinearEquiv_tprod, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    PiTensorProduct.subsingletonEquiv_apply_tprod]
  rfl

variable {H : Fin 2 → Type uG} [∀ i, Group (H i)]

/-- The action of `H 0 × H 1` on functions `H 1 → V 0`: the first factor through `τ`,
the second by right translation. -/
def finTwoFunAction (τ : Representation ℂ (H 0) (V 0)) (m : ∀ i, H i) (F : H 1 → V 0) :
    H 1 → V 0 :=
  fun g => τ (m 0) (F (g * m 1))

/-- The evaluation of the two-factor tensor as a function on the second group. -/
def finTwoEval (e : V 1 →ₗ[ℂ] (H 1 → ℂ)) : PiTensorProduct ℂ V →ₗ[ℂ] (H 1 → V 0) :=
  (tensorEval e).comp finTwoTensorEquiv.toLinearMap

omit [∀ i, Group (H i)] in
theorem finTwoEval_injective (e : V 1 →ₗ[ℂ] (H 1 → ℂ)) (he : Function.Injective e) :
    Function.Injective (finTwoEval (V := V) e) :=
  (tensorEval_injective e he).comp finTwoTensorEquiv.injective

theorem finTwoEval_external (τ : ∀ i, Representation ℂ (H i) (V i))
    (e : V 1 →ₗ[ℂ] (H 1 → ℂ)) (he : ∀ (h : H 1) (s : V 1) (g : H 1), e (τ 1 h s) g = e s (g * h))
    (m : ∀ i, H i) (t : PiTensorProduct ℂ V) :
    finTwoEval e (FiniteTensor.external τ m t) = finTwoFunAction (τ 0) m (finTwoEval e t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    funext g
    simp only [map_smul, FiniteTensor.external_tprod, finTwoEval, LinearMap.comp_apply,
      LinearEquiv.coe_coe, finTwoTensorEquiv_tprod, finTwoFunAction, Pi.smul_apply,
      tensorEval_tmul, he]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    funext g
    simp [finTwoFunAction]

end FinTwo

section Key

variable {H : Fin 2 → Type uG} [∀ i, Group (H i)]
  {V : Fin 2 → Type uX} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {U : Type uU} [AddCommGroup U] [Module ℂ U]

theorem finTwo_mulSingle_one_mul (g : H 1) (m : ∀ i, H i) :
    MonoidHom.mulSingle H 1 g * m =
      MonoidHom.mulSingle H 0 (m 0) * MonoidHom.mulSingle H 1 (g * m 1) := by
  funext i
  fin_cases i
  · simp [MonoidHom.mulSingle_apply]
  · simp [MonoidHom.mulSingle_apply]

/-- The functions `g ↦ φ(g · w)` attached to a first-factor intertwiner `φ`. -/
def translateEval (W : Representation ℂ (∀ i, H i) U) (τ₀ : Representation ℂ (H 0) (V 0))
    (φ : Representation.IntertwiningMap (W.comp (MonoidHom.mulSingle H 0)) τ₀) :
    U →ₗ[ℂ] (H 1 → V 0) where
  toFun w g := φ (W (MonoidHom.mulSingle H 1 g) w)
  map_add' w w' := by funext g; simp
  map_smul' c w := by funext g; simp

theorem translateEval_apply (W : Representation ℂ (∀ i, H i) U)
    (τ₀ : Representation ℂ (H 0) (V 0))
    (φ : Representation.IntertwiningMap (W.comp (MonoidHom.mulSingle H 0)) τ₀) (w : U) (g : H 1) :
    translateEval W τ₀ φ w g = φ (W (MonoidHom.mulSingle H 1 g) w) := rfl

theorem translateEval_equivariant (W : Representation ℂ (∀ i, H i) U)
    (τ₀ : Representation ℂ (H 0) (V 0))
    (φ : Representation.IntertwiningMap (W.comp (MonoidHom.mulSingle H 0)) τ₀) (m : ∀ i, H i)
    (w : U) :
    translateEval W τ₀ φ (W m w) = finTwoFunAction τ₀ m (translateEval W τ₀ φ w) := by
  funext g
  simp only [translateEval_apply, finTwoFunAction]
  rw [← Module.End.mul_apply, ← map_mul, finTwo_mulSingle_one_mul, map_mul,
    Module.End.mul_apply]
  exact LinearMap.congr_fun (φ.isIntertwining' (m 0)) _

/-- An intertwiner into the two-factor external tensor, from functions which lie in the
image of an injective equivariant evaluation. -/
theorem exists_external_ne_zero (W : Representation ℂ (∀ i, H i) U)
    (τ : ∀ i, Representation ℂ (H i) (V i))
    (φ : Representation.IntertwiningMap (W.comp (MonoidHom.mulSingle H 0)) (τ 0)) (hφ : φ ≠ 0)
    (e : V 1 →ₗ[ℂ] (H 1 → ℂ)) (he : Function.Injective e)
    (heq : ∀ (h : H 1) (s : V 1) (g : H 1), e (τ 1 h s) g = e s (g * h))
    (hrange : ∀ w : U, translateEval W (τ 0) φ w ∈ LinearMap.range (finTwoEval (V := V) e)) :
    ∃ Φ : W.IntertwiningMap (FiniteTensor.external τ), Φ ≠ 0 := by
  let ι := finTwoEval (V := V) e
  have hι : Function.Injective ι := finTwoEval_injective e he
  let L := LinearEquiv.ofInjective ι hι
  let Φ₀ : U →ₗ[ℂ] PiTensorProduct ℂ V :=
    L.symm.toLinearMap ∘ₗ (translateEval W (τ 0) φ).codRestrict (LinearMap.range ι) hrange
  have hΦ₀ : ∀ w, ι (Φ₀ w) = translateEval W (τ 0) φ w := by
    intro w
    have := L.apply_symm_apply ⟨translateEval W (τ 0) φ w, hrange w⟩
    exact congrArg Subtype.val this
  refine ⟨{ toLinearMap := Φ₀, isIntertwining' := fun m => ?_ }, ?_⟩
  · ext w
    apply hι
    simp only [LinearMap.comp_apply]
    rw [hΦ₀, finTwoEval_external τ e heq, hΦ₀, translateEval_equivariant]
  · intro h0
    obtain ⟨w, hw⟩ : ∃ w, φ w ≠ 0 := by
      by_contra h
      push Not at h
      exact hφ (Representation.IntertwiningMap.ext (LinearMap.ext h))
    apply hw
    have h1 : translateEval W (τ 0) φ w = 0 := by
      rw [← hΦ₀]
      have : Φ₀ w = 0 := congrArg (fun f : W.IntertwiningMap (FiniteTensor.external τ) => f w) h0
      rw [this, map_zero]
    have h2 := congrFun h1 1
    simpa [translateEval_apply] using h2

end Key

section Range

variable {A : Type uA} {S : Type uS} [AddCommGroup A] [Module ℂ A] [AddCommGroup S] [Module ℂ S]
  {X : Type uX}

/-- A function with values in a finite-dimensional subspace lies in the image of the
tensor evaluation once its coordinate functions do. -/
theorem mem_range_tensorEval {D : Submodule ℂ A} [FiniteDimensional ℂ D]
    (e : S →ₗ[ℂ] (X → ℂ)) (F : X → A) (hD : ∀ x, F x ∈ D)
    (hcoord : ∀ ψ : Module.Dual ℂ D, ∃ s, e s = fun x => ψ ⟨F x, hD x⟩) :
    F ∈ LinearMap.range (tensorEval (A := A) e) := by
  classical
  let b := Module.finBasis ℂ D
  choose s hs using fun j => hcoord (b.coord j)
  refine ⟨∑ j, (b j : A) ⊗ₜ s j, ?_⟩
  funext x
  rw [map_sum, Finset.sum_apply]
  simp only [tensorEval_tmul, hs, Module.Basis.coord_apply]
  have h2 := congrArg Subtype.val (b.sum_repr ⟨F x, hD x⟩)
  rw [Submodule.coe_sum] at h2
  simp only [Submodule.coe_smul] at h2
  exact h2

end Range

section RightRegular

variable (H : Type uG) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The complex functions on `H` invariant under right translation by some open
subgroup. -/
def rightSmoothFunctions : Submodule ℂ (H → ℂ) where
  carrier := {f | ∃ K : OpenSubgroup H, ∀ (x k : H), k ∈ K → f (x * k) = f x}
  add_mem' := by
    rintro f f' ⟨K, hK⟩ ⟨K', hK'⟩
    refine ⟨K ⊓ K', fun x k hk => ?_⟩
    rw [OpenSubgroup.mem_inf] at hk
    simp [hK x k hk.1, hK' x k hk.2]
  zero_mem' := ⟨⊤, fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨K, hK⟩
    exact ⟨K, fun x k hk => by simp [hK x k hk]⟩

variable {H}

/-- The open subgroup `g K g⁻¹`. -/
def conjOpenSubgroup (g : H) (K : OpenSubgroup H) : OpenSubgroup H :=
  K.comap (MulAut.conj g⁻¹).toMonoidHom (by
    change Continuous fun x => g⁻¹ * x * g⁻¹⁻¹
    fun_prop)

theorem mem_conjOpenSubgroup (g : H) (K : OpenSubgroup H) (x : H) :
    x ∈ conjOpenSubgroup g K ↔ g⁻¹ * x * g ∈ K := by
  simp [conjOpenSubgroup, OpenSubgroup.mem_comap]

/-- Right translation by `g` on right-smooth functions. -/
def rightTranslate (g : H) : rightSmoothFunctions H →ₗ[ℂ] rightSmoothFunctions H where
  toFun f := ⟨fun x => f.1 (x * g), by
    obtain ⟨K, hK⟩ := f.2
    refine ⟨conjOpenSubgroup g K, fun x k hk => ?_⟩
    rw [mem_conjOpenSubgroup] at hk
    have : x * k * g = x * g * (g⁻¹ * k * g) := by group
    simp only [this, hK _ _ hk]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem rightTranslate_apply (g : H) (f : rightSmoothFunctions H) (x : H) :
    (rightTranslate g f).1 x = f.1 (x * g) := rfl

/-- The right regular representation on right-smooth functions. -/
def rightRegular : Representation ℂ H (rightSmoothFunctions H) where
  toFun := rightTranslate
  map_one' := LinearMap.ext fun f => Subtype.ext (funext fun x => by
    simp)
  map_mul' g g' := LinearMap.ext fun f => Subtype.ext (funext fun x => by
    change f.1 (x * (g * g')) = f.1 (x * g * g')
    rw [mul_assoc])

theorem rightRegular_isSmooth : IsSmooth (rightRegular (H := H)) := by
  intro f
  obtain ⟨K, hK⟩ := f.2
  refine ⟨K, ?_⟩
  rw [fixedVectors, Representation.mem_invariants]
  intro k
  exact Subtype.ext (funext fun x => hK x k k.2)

/-- The smooth right regular representation, with carrier raised to `Type (max uG uV)`. -/
def rightRegularRep : SmoothRep.{0, uG, max uG uV} ℂ H :=
  SmoothRep.of (universeLiftRepresentation.{max uG uV} (rightRegular (H := H)))
    ((isSmooth_universeLift_iff _).mpr rightRegular_isSmooth)

/-- Evaluation of a vector of the right regular representation as a function. -/
def rightRegularEval : rightRegularRep.{uV, uG} (H := H) →ₗ[ℂ] (H → ℂ) where
  toFun v := (ULift.down (α := rightSmoothFunctions H) v).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rightRegularEval_injective :
    Function.Injective (rightRegularEval.{uV, uG} (H := H)) := by
  intro v w h
  exact ULift.ext _ _ (Subtype.ext h)

theorem rightRegularEval_equivariant (h : H) (s : rightRegularRep.{uV, uG} (H := H)) (g : H) :
    rightRegularEval ((rightRegularRep.{uV, uG} (H := H)).representation h s) g =
      rightRegularEval s (g * h) := rfl

theorem exists_rightRegularEval_eq (f : H → ℂ) (K : OpenSubgroup H)
    (hf : ∀ x k, k ∈ K → f (x * k) = f x) :
    ∃ s : rightRegularRep.{uV, uG} (H := H), rightRegularEval s = f :=
  ⟨ULift.up ⟨f, K, hf⟩, rfl⟩

end RightRegular

section RangeCondition

variable {H : Fin 2 → Type uG} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  [∀ i, IsTopologicalGroup (H i)]
  {V : Fin 2 → Type uX} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {U : Type uU} [AddCommGroup U] [Module ℂ U]

omit [∀ i, IsTopologicalGroup (H i)] in
/-- For a smooth `W` and an admissible first factor, the translated functions `g ↦ φ(g · w)`
are finite sums of right-smooth coordinate functions. -/
theorem translateEval_mem_range (W : Representation ℂ (∀ i, H i) U) (hW : IsSmooth W)
    (τ : ∀ i, Representation ℂ (H i) (V i)) (hτ : IsAdmissible (τ 0))
    (φ : Representation.IntertwiningMap (W.comp (MonoidHom.mulSingle H 0)) (τ 0))
    (e : V 1 →ₗ[ℂ] (H 1 → ℂ))
    (hsurj : ∀ (f : H 1 → ℂ) (K : OpenSubgroup (H 1)), (∀ x k, k ∈ K → f (x * k) = f x) →
      ∃ s, e s = f)
    (w : U) : translateEval W (τ 0) φ w ∈ LinearMap.range (finTwoEval (V := V) e) := by
  obtain ⟨Uw, hUw⟩ := hW w
  have hfix : ∀ u ∈ Uw, W u w = w := by
    intro u hu
    rw [fixedVectors, Representation.mem_invariants] at hUw
    exact hUw ⟨u, hu⟩
  have hφ : ∀ h v, φ (W (MonoidHom.mulSingle H 0 h) v) = τ 0 h (φ v) :=
    fun h v => LinearMap.congr_fun (φ.isIntertwining' h) v
  let K₁ : OpenSubgroup (H 0) :=
    Uw.comap (MonoidHom.mulSingle H 0) (by exact continuous_mulSingle 0)
  let K₂ : OpenSubgroup (H 1) :=
    Uw.comap (MonoidHom.mulSingle H 1) (by exact continuous_mulSingle 1)
  let D := fixedVectors (τ 0) K₁.toSubgroup
  have : FiniteDimensional ℂ D := hτ.2 K₁
  set Fw := translateEval W (τ 0) φ w with hFw
  have hD : ∀ g, Fw g ∈ D := by
    intro g
    show Fw g ∈ fixedVectors (τ 0) K₁.toSubgroup
    rw [fixedVectors, Representation.mem_invariants]
    intro k
    have hk : MonoidHom.mulSingle H 0 (k : H 0) ∈ Uw := OpenSubgroup.mem_comap.mp k.2
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, hFw,
      translateEval_apply]
    have hc : MonoidHom.mulSingle H 0 (k : H 0) * MonoidHom.mulSingle H 1 g =
        MonoidHom.mulSingle H 1 g * MonoidHom.mulSingle H 0 (k : H 0) :=
      ((Pi.mulSingle_commute (by decide : (0 : Fin 2) ≠ 1)) (k : H 0) g).eq
    rw [← hφ, ← Module.End.mul_apply, ← map_mul, hc, map_mul,
      Module.End.mul_apply, hfix _ hk]
  have hK₂ : ∀ g k, k ∈ K₂ → Fw (g * k) = Fw g := by
    intro g k hk
    have hk' : MonoidHom.mulSingle H 1 k ∈ Uw := OpenSubgroup.mem_comap.mp hk
    simp only [hFw, translateEval_apply, map_mul, Module.End.mul_apply, hfix _ hk']
  obtain ⟨t, ht⟩ := mem_range_tensorEval e Fw hD (fun ψ => hsurj _ K₂ (fun x k hk => by
    have : (⟨Fw (x * k), hD (x * k)⟩ : D) = ⟨Fw x, hD x⟩ := Subtype.ext (hK₂ x k hk)
    simp only [this]))
  refine ⟨finTwoTensorEquiv.symm t, ?_⟩
  simp only [finTwoEval, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact ht

omit [∀ i, IsTopologicalGroup (H i)] in
/-- The key construction: a nonzero intertwiner from the first-factor restriction of a
smooth `W` to an admissible `τ 0` gives a nonzero intertwiner `W → τ 0 ⊗ τ 1`, when `τ 1`
evaluates injectively and equivariantly onto all right-smooth functions. -/
theorem exists_external_ne_zero_of_smooth (W : Representation ℂ (∀ i, H i) U) (hW : IsSmooth W)
    (τ : ∀ i, Representation ℂ (H i) (V i)) (hτ : IsAdmissible (τ 0))
    (φ : Representation.IntertwiningMap (W.comp (MonoidHom.mulSingle H 0)) (τ 0)) (hφ : φ ≠ 0)
    (e : V 1 →ₗ[ℂ] (H 1 → ℂ)) (he : Function.Injective e)
    (heq : ∀ (h : H 1) (s : V 1) (g : H 1), e (τ 1 h s) g = e s (g * h))
    (hsurj : ∀ (f : H 1 → ℂ) (K : OpenSubgroup (H 1)), (∀ x k, k ∈ K → f (x * k) = f x) →
      ∃ s, e s = f) :
    ∃ Φ : W.IntertwiningMap (FiniteTensor.external τ), Φ ≠ 0 :=
  exists_external_ne_zero W τ φ hφ e he heq (translateEval_mem_range W hW τ hτ φ e hsurj)

end RangeCondition

section FixedSlice

variable {H : Fin 2 → Type uG} [∀ i, Group (H i)]
  {U : Type uU} [AddCommGroup U] [Module ℂ U]

theorem mulSingle_zero_one_commute (a : H 0) (b : H 1) :
    MonoidHom.mulSingle H 0 a * MonoidHom.mulSingle H 1 b =
      MonoidHom.mulSingle H 1 b * MonoidHom.mulSingle H 0 a :=
  ((Pi.mulSingle_commute (by decide : (0 : Fin 2) ≠ 1)) a b).eq

theorem eq_mulSingle_zero_mul_one (m : ∀ i, H i) :
    m = MonoidHom.mulSingle H 0 (m 0) * MonoidHom.mulSingle H 1 (m 1) := by
  funext i
  fin_cases i
  · simp [MonoidHom.mulSingle_apply]
  · simp [MonoidHom.mulSingle_apply]

/-- The vectors fixed by `K` in the second factor, as a subrepresentation of the
first-factor restriction. -/
def secondFixedSlice (W : Representation ℂ (∀ i, H i) U) (K : Subgroup (H 1)) :
    Subrepresentation (W.comp (MonoidHom.mulSingle H 0)) where
  toSubmodule := fixedVectors (W.comp (MonoidHom.mulSingle H 1)) K
  apply_mem_toSubmodule h v hv := by
    change ∀ k : K, W (MonoidHom.mulSingle H 1 (k : H 1)) v = v at hv
    change ∀ k : K, W (MonoidHom.mulSingle H 1 (k : H 1))
      (W (MonoidHom.mulSingle H 0 h) v) = W (MonoidHom.mulSingle H 0 h) v
    intro k
    rw [← Module.End.mul_apply, ← map_mul, ← mulSingle_zero_one_commute, map_mul,
      Module.End.mul_apply, hv k]

theorem mem_secondFixedSlice (W : Representation ℂ (∀ i, H i) U) (K : Subgroup (H 1)) (v : U) :
    v ∈ (secondFixedSlice W K).toSubmodule ↔ ∀ k ∈ K, W (MonoidHom.mulSingle H 1 k) v = v :=
  ⟨fun hv k hk => hv ⟨k, hk⟩, fun hv k => hv k.1 k.2⟩

variable [∀ i, TopologicalSpace (H i)]

theorem isSmooth_secondFixedSlice (W : Representation ℂ (∀ i, H i) U) (hW : IsSmooth W)
    (K : Subgroup (H 1)) : IsSmooth (secondFixedSlice W K).toRepresentation := by
  intro v
  obtain ⟨O, hO⟩ := hW v.1
  refine ⟨O.comap (MonoidHom.mulSingle H 0) (by exact continuous_mulSingle 0), ?_⟩
  change ∀ g : O, W g v.1 = v.1 at hO
  intro k
  exact Subtype.ext (hO ⟨_, OpenSubgroup.mem_comap.mp k.2⟩)

theorem isAdmissible_secondFixedSlice (W : Representation ℂ (∀ i, H i) U) (hW : IsAdmissible W)
    (K : OpenSubgroup (H 1)) :
    IsAdmissible (secondFixedSlice W K.toSubgroup).toRepresentation := by
  refine ⟨isSmooth_secondFixedSlice W hW.1 _, fun K₁ => ?_⟩
  let O : OpenSubgroup (∀ i, H i) :=
    K₁.comap (Pi.evalMonoidHom H 0) (continuous_apply 0) ⊓
      K.comap (Pi.evalMonoidHom H 1) (continuous_apply 1)
  have hfin : Module.Finite ℂ (fixedVectors W O.toSubgroup) := hW.2 O
  let f : fixedVectors (secondFixedSlice W K.toSubgroup).toRepresentation K₁.toSubgroup →ₗ[ℂ]
      fixedVectors W O.toSubgroup :=
    { toFun := fun v => ⟨v.1.1, by
        change ∀ g : O, W g v.1.1 = v.1.1
        intro g
        have hg := OpenSubgroup.mem_inf.mp g.2
        have h0 : (g : ∀ i, H i) 0 ∈ K₁ := OpenSubgroup.mem_comap.mp hg.1
        have h1 : (g : ∀ i, H i) 1 ∈ K := OpenSubgroup.mem_comap.mp hg.2
        have hv0 : W (MonoidHom.mulSingle H 0 ((g : ∀ i, H i) 0)) v.1.1 = v.1.1 :=
          congrArg Subtype.val (v.2 ⟨_, h0⟩)
        have hv1 : W (MonoidHom.mulSingle H 1 ((g : ∀ i, H i) 1)) v.1.1 = v.1.1 :=
          (mem_secondFixedSlice W K.toSubgroup v.1.1).mp v.1.2 _ h1
        rw [eq_mulSingle_zero_mul_one (g : ∀ i, H i), map_mul, Module.End.mul_apply, hv1, hv0]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro v w h
    have h' : v.1.1 = w.1.1 := congrArg (fun x : fixedVectors W O.toSubgroup => (x : U)) h
    exact Subtype.ext (Subtype.ext h')
  exact Module.Finite.of_injective f hf

/-- An irreducible subquotient of the first-factor restriction of a smooth `W` is already a
subquotient of a slice of vectors fixed by a compact open subgroup of the second factor. -/
theorem exists_secondFixedSlice_isSubquotient (W : Representation ℂ (∀ i, H i) U)
    (hW : IsSmooth W)
    (hcpt : ∀ O : OpenSubgroup (H 1), ∃ K : OpenSubgroup (H 1),
      IsCompact (K : Set (H 1)) ∧ K ≤ O)
    {VX : Type uX} [AddCommGroup VX] [Module ℂ VX] (X : Representation ℂ (H 0) VX)
    (hX : X.IsIrreducible)
    (hocc : WeylBranchPieces.IsSubquotient (W.comp (MonoidHom.mulSingle H 0)) X) :
    ∃ K : OpenSubgroup (H 1), IsCompact (K : Set (H 1)) ∧
      WeylBranchPieces.IsSubquotient (secondFixedSlice W K.toSubgroup).toRepresentation X := by
  obtain ⟨S, q, hq⟩ := hocc
  have hnt : Nontrivial VX := by
    have : IsSimpleModule (MonoidAlgebra ℂ (H 0)) X.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule X).mp inferInstance
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (H 0)) X.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : VX)
  obtain ⟨u, hu⟩ := hq x
  obtain ⟨O, hO⟩ := hW u.1
  change ∀ g : O, W g u.1 = u.1 at hO
  obtain ⟨K, hKc, hKO⟩ :=
    hcpt (O.comap (MonoidHom.mulSingle H 1) (by exact continuous_mulSingle 1))
  refine ⟨K, hKc, ?_⟩
  have hufix : u.1 ∈ (secondFixedSlice W K.toSubgroup).toSubmodule :=
    (mem_secondFixedSlice W K.toSubgroup u.1).mpr fun k hk =>
      hO ⟨_, OpenSubgroup.mem_comap.mp (hKO hk)⟩
  let S₂ : Subrepresentation (secondFixedSlice W K.toSubgroup).toRepresentation :=
    { toSubmodule := S.toSubmodule.comap (secondFixedSlice W K.toSubgroup).toSubmodule.subtype
      apply_mem_toSubmodule := fun h _ hv => S.apply_mem_toSubmodule h hv }
  let ι : S₂.toSubmodule →ₗ[ℂ] S.toSubmodule :=
    LinearMap.codRestrict S.toSubmodule
      ((secondFixedSlice W K.toSubgroup).toSubmodule.subtype ∘ₗ S₂.toSubmodule.subtype)
      (fun v => v.2)
  let q₂ : S₂.toRepresentation.IntertwiningMap X :=
    { toLinearMap := q.toLinearMap ∘ₗ ι
      isIntertwining' := fun g => by
        ext v
        exact LinearMap.congr_fun (q.isIntertwining' g) (ι v) }
  have hq₂ : q₂ ≠ 0 := by
    intro h0
    apply hx
    rw [← hu]
    exact LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap h0)
      (⟨⟨u.1, hufix⟩, u.2⟩ : S₂.toSubmodule)
  exact ⟨S₂, q₂, (Representation.IsIrreducible.surjective_or_eq_zero q₂).resolve_right hq₂⟩

variable [∀ i, IsTopologicalGroup (H i)]

/-- A nonzero map from a compact-open fixed slice extends, through averaging over the
compact open subgroup, to a nonzero first-factor intertwiner. -/
theorem exists_ne_zero_of_secondFixedSlice (W : Representation ℂ (∀ i, H i) U)
    (hW : IsSmooth W) (K : OpenSubgroup (H 1)) (hK : IsCompact (K : Set (H 1)))
    {VX : Type uX} [AddCommGroup VX] [Module ℂ VX] (X : Representation ℂ (H 0) VX)
    (ψ : (secondFixedSlice W K.toSubgroup).toRepresentation.IntertwiningMap X) (hψ : ψ ≠ 0) :
    ∃ φ : Representation.IntertwiningMap (W.comp (MonoidHom.mulSingle H 0)) X, φ ≠ 0 := by
  have hW₁ : IsSmooth (W.comp (MonoidHom.mulSingle H 1)) :=
    isSmooth_comp _ (by exact continuous_mulSingle 1) hW
  let P := Compact.CharZero.fixedProjection (W.comp (MonoidHom.mulSingle H 1)) hW₁ K hK
  have hP : ∀ (h : H 0) (v : U),
      P (W (MonoidHom.mulSingle H 0 h) v) =
        (secondFixedSlice W K.toSubgroup).toRepresentation h (P v) := by
    intro h v
    let f : Representation.IntertwiningMap (W.comp (MonoidHom.mulSingle H 1))
        (W.comp (MonoidHom.mulSingle H 1)) :=
      { toLinearMap := W (MonoidHom.mulSingle H 0 h)
        isIntertwining' := fun g => by
          ext w
          change W (MonoidHom.mulSingle H 0 h) (W (MonoidHom.mulSingle H 1 g) w) =
            W (MonoidHom.mulSingle H 1 g) (W (MonoidHom.mulSingle H 0 h) w)
          rw [← Module.End.mul_apply, ← map_mul, mulSingle_zero_one_commute, map_mul,
            Module.End.mul_apply] }
    have hc := LinearMap.congr_fun
      (Compact.CharZero.averageMap_commute _ _ hW₁ hW₁ K hK f) v
    apply Subtype.ext
    exact hc.symm
  let φ : Representation.IntertwiningMap (W.comp (MonoidHom.mulSingle H 0)) X :=
    { toLinearMap := ψ.toLinearMap ∘ₗ P
      isIntertwining' := fun h => by
        ext v
        change ψ (P (W (MonoidHom.mulSingle H 0 h) v)) = X h (ψ (P v))
        rw [hP]
        exact LinearMap.congr_fun (ψ.isIntertwining' h) (P v) }
  refine ⟨φ, fun h0 => hψ ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have h1 : φ v.1 = 0 := by rw [h0]; rfl
  have h2 : P v.1 = v := Compact.CharZero.fixedProjection_fixed _ hW₁ K hK v
  change ψ (P v.1) = 0 at h1
  rw [h2] at h1
  exact h1

/-- Variant of `exists_ne_zero_of_secondFixedSlice` for a surjection onto a nonzero target. -/
theorem exists_ne_zero_of_secondFixedSlice_of_surjective (W : Representation ℂ (∀ i, H i) U)
    (hW : IsSmooth W) (K : OpenSubgroup (H 1)) (hK : IsCompact (K : Set (H 1)))
    {VX : Type uX} [AddCommGroup VX] [Module ℂ VX] [Nontrivial VX]
    (X : Representation ℂ (H 0) VX)
    (ψ : (secondFixedSlice W K.toSubgroup).toRepresentation.IntertwiningMap X)
    (hψ : Function.Surjective ψ) :
    ∃ φ : Representation.IntertwiningMap (W.comp (MonoidHom.mulSingle H 0)) X, φ ≠ 0 := by
  refine exists_ne_zero_of_secondFixedSlice W hW K hK X ψ fun h0 => ?_
  obtain ⟨a, ha⟩ := exists_ne (0 : VX)
  obtain ⟨v, rfl⟩ := hψ a
  apply ha
  rw [h0]
  rfl

end FixedSlice

end Langlands.Classification.LeftCuspidalDerivative
