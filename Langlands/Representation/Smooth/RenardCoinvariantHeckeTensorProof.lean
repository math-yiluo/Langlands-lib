import Langlands.Representation.Smooth.RenardCheckRightActionProof
import Langlands.Algebra.NondegenerateTensorScalars

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory MeasureTheory.Measure TensorProduct MulOpposite

namespace Langlands.Renard.Smooth

open Langlands.Hecke Langlands.Algebra Langlands.HarmonicAnalysis

universe u v w z

namespace CoinvariantTensor

section Operators

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable (μ : Measure G) [μ.IsHaarMeasure]
  (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- The check action of a left translate first applies the inverse group action. -/
theorem check_leftTranslate (a : G) (f : SchwartzBruhat G) (x : V) :
    CheckAction.operator μ ρ hρ (TestFunction.leftTranslate a f) x =
      CheckAction.operator μ ρ hρ f (ρ a⁻¹ x) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro L
  rw [map_sub, sub_eq_zero, CheckAction.dual, CheckAction.dual]
  rw [← integral_mul_left_eq_self
    (fun g => TestFunction.leftTranslate a f g * L (ρ g⁻¹ x)) a]
  simp only [TestFunction.leftTranslate_apply, inv_mul_cancel_left,
    mul_inv_rev, map_mul, Module.End.mul_apply]

/-- Compact-open normalized indicators fix a subgroup-fixed vector also on the right. -/
theorem check_normalizedIndicator_of_fixed (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) {x : V} (hx : x ∈ fixedVectors ρ K.toSubgroup) :
    CheckAction.operator μ ρ hρ (HeckeAlgebra.toTestFunction μ
      (HeckeAlgebra.normalizedIndicator μ K hK)) x = x := by
  have hinv : TestFunction.inversion (TestFunction.subgroupIndicator K hK) =
      TestFunction.subgroupIndicator K hK := by
    ext g
    by_cases hg : g ∈ K
    · have hgi : g⁻¹ ∈ K := K.inv_mem hg
      simp [TestFunction.subgroupIndicator_apply, hg, hgi]
    · have hgi : g⁻¹ ∉ K := fun h => hg (K.inv_mem_iff.mp h)
      simp [TestFunction.subgroupIndicator_apply, hg, hgi]
  have hmass : μ.inv (K : Set G) = μ (K : Set G) := by
    rw [Measure.inv_apply]
    congr 1
    ext g
    simp
  change integratedAction μ.inv ρ hρ
    (TestFunction.inversion (((μ.real (K : Set G) : ℂ)⁻¹) •
      TestFunction.subgroupIndicator K hK)) x = x
  rw [map_smul, hinv, map_smul, LinearMap.smul_apply,
    integratedAction_subgroupIndicator_of_fixed μ.inv ρ hρ K hK hx, hmass]
  change (μ.real (K : Set G) : ℂ)⁻¹ • ((μ.real (K : Set G) : ℂ) • x) = x
  rw [smul_smul, inv_mul_cancel₀ (HeckeAlgebra.compactOpen_complex_mass_ne_zero μ K hK),
    one_smul]

end Operators

section Bilinear

variable {G : Type u} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {V : Type v} {W : Type w} {Z : Type z}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Z] [Module ℂ Z]
variable (μ : Measure G) [μ.IsHaarMeasure]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
  (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
variable (M : NonUnitalModule (HeckeAlgebra μ)ᵐᵒᵖ V)
  (hM : IsCheckRightAction μ ρ hρ M)

include hρ hM

set_option linter.unusedSectionVars false in
/-- A diagonal-invariant bilinear map is balanced for the check and integrated actions. -/
theorem balanced_of_invariant (b : V →ₗ[ℂ] W →ₗ[ℂ] Z)
    (hb : ∀ g x y, b (ρ g x) (σ g y) = b x y) (f : HeckeAlgebra μ) (x : V) (y : W) :
    b (letI := M; op f • x) y = b x (heckeAction μ σ hσ f y) := by
  rw [hM f x]
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro L
  rw [map_sub, sub_eq_zero]
  have hleft := CheckAction.dual μ ρ hρ (HeckeAlgebra.toTestFunction μ f) x
    (L.comp (b.flip y))
  have hright := integratedAction_dual μ σ hσ (HeckeAlgebra.toTestFunction μ f) y
    (L.comp (b x))
  dsimp only [LinearMap.comp_apply, LinearMap.flip_apply] at hleft hright
  change L (b (CheckAction.operator μ ρ hρ (HeckeAlgebra.toTestFunction μ f) x) y) = _
  rw [hleft, show L (b x (heckeAction μ σ hσ f y)) = _ from hright]
  apply integral_congr_ae
  filter_upwards [] with g
  congr 1
  have h := hb g (ρ g⁻¹ x) y
  simpa only [ρ.self_inv_apply] using congrArg L h.symm

/-- Hecke balancing detects diagonal invariance by translated averaging operators. -/
theorem invariant_of_balanced
    (b : V →ₗ[ℂ] W →ₗ[ℂ] Z)
    (hb : ∀ (f : HeckeAlgebra μ) x y,
      b (letI := M; op f • x) y = b x (heckeAction μ σ hσ f y)) :
    ∀ g x y, b (ρ g x) (σ g y) = b x y := by
  intro g x y
  obtain ⟨U, hU⟩ := hρ x
  obtain ⟨J, hJ⟩ := hσ y
  obtain ⟨K, hK, hKU⟩ := compactOpenSubgroupBasis G (↑(U ⊓ J) : Set G)
    ((U ⊓ J).isOpen.mem_nhds (U ⊓ J).one_mem)
  have hx : x ∈ fixedVectors ρ K.toSubgroup :=
    fun k => hU ⟨k.val, (hKU k.property).1⟩
  have hy : y ∈ fixedVectors σ K.toSubgroup :=
    fun k => hJ ⟨k.val, (hKU k.property).2⟩
  let e := HeckeAlgebra.normalizedIndicator μ K hK
  let f := (HeckeAlgebra.toTestFunction μ).symm
    (TestFunction.leftTranslate g (HeckeAlgebra.toTestFunction μ e))
  have hright : heckeAction μ σ hσ f y = σ g y := by
    change integratedAction μ σ hσ (TestFunction.leftTranslate g
      (HeckeAlgebra.toTestFunction μ e)) y = _
    rw [integratedAction_leftTranslate]
    exact congrArg (σ g) (heckeAction_normalizedIndicator_of_fixed μ σ hσ K hK hy)
  have hleft : (letI := M; op f • ρ g x) = x := by
    rw [hM]
    change CheckAction.operator μ ρ hρ (TestFunction.leftTranslate g
      (HeckeAlgebra.toTestFunction μ e)) (ρ g x) = x
    rw [check_leftTranslate, ρ.inv_self_apply]
    exact check_normalizedIndicator_of_fixed μ ρ hρ K hK hx
  have h := hb f (ρ g x) y
  rw [hleft, hright] at h
  exact h.symm

end Bilinear

section Quotients

variable {G : Type u} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {V : Type v} {W : Type w}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable (μ : Measure G) [μ.IsHaarMeasure]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
  (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
variable [M : NonUnitalModule (HeckeAlgebra μ)ᵐᵒᵖ V]
  (hM : IsCheckRightAction μ ρ hρ M)

variable [L : NonUnitalModule (HeckeAlgebra μ) W]
  [SMulCommClass ℂ (HeckeAlgebra μ) W] [IsScalarTower ℂ (HeckeAlgebra μ) W]
  (hL : ∀ (f : HeckeAlgebra μ) (y : W), f • y = heckeAction μ σ hσ f y)

local instance tensorModule : Module ℂ (NonUnitalModuleTensor.Tensor (HeckeAlgebra μ) V W) :=
  NondegenerateTensorScalars.compatibleModule ℂ (HeckeAlgebra μ) V W

include hM

set_option linter.unusedSectionVars false in
/-- Compatibility of the specified check action with scalar multiplication in the algebra. -/
theorem right_scalar (c : ℂ) (f : HeckeAlgebra μ) (x : V) :
    op (c • f) • x = c • (op f • x) := by
  rw [hM, hM]
  change CheckAction.operator μ ρ hρ (c • HeckeAlgebra.toTestFunction μ f) x =
    c • CheckAction.operator μ ρ hρ (HeckeAlgebra.toTestFunction μ f) x
  exact congrArg (fun T : Module.End ℂ V => T x) ((CheckAction.operator μ ρ hρ).map_smul c _)

/-- A right local unit moves complex scalars between the original tensor factors. -/
theorem scalar_tmul (c : ℂ) (x : V) (y : W) :
    NonUnitalModuleTensor.tmul (HeckeAlgebra μ) V W (c • x) y =
      c • NonUnitalModuleTensor.tmul (HeckeAlgebra μ) V W x y := by
  obtain ⟨U, hU⟩ := hρ x
  obtain ⟨K, hK, hKU⟩ := compactOpenSubgroupBasis G (U : Set G)
    (U.isOpen.mem_nhds U.one_mem)
  let e := HeckeAlgebra.normalizedIndicator μ K hK
  have he : op e • x = x := (hM e x).trans
    (check_normalizedIndicator_of_fixed μ ρ hρ K hK (fun k => hU ⟨k.val, hKU k.property⟩))
  calc
    _ = NonUnitalModuleTensor.tmul (HeckeAlgebra μ) V W (op (c • e) • x) y := by
      rw [right_scalar μ ρ hρ hM, he]
    _ = NonUnitalModuleTensor.tmul (HeckeAlgebra μ) V W x ((c • e) • y) :=
      NonUnitalModuleTensor.tmul_balanced _ _ _ _ _ _
    _ = c • NonUnitalModuleTensor.tmul (HeckeAlgebra μ) V W x (e • y) := by
      rw [smul_assoc]
      rfl
    _ = c • NonUnitalModuleTensor.tmul (HeckeAlgebra μ) V W (op e • x) y := by
      rw [NonUnitalModuleTensor.tmul_balanced]
    _ = _ := by rw [he]

/-- The original pure tensor is complex bilinear for the compatible scalar structure. -/
def pureBilinear : V →ₗ[ℂ] W →ₗ[ℂ] NonUnitalModuleTensor.Tensor (HeckeAlgebra μ) V W :=
  LinearMap.mk₂ ℂ (NonUnitalModuleTensor.tmul (HeckeAlgebra μ) V W)
    (NonUnitalModuleTensor.add_tmul _ _ _) (scalar_tmul μ ρ hρ hM)
    (NonUnitalModuleTensor.tmul_add _ _ _) (fun _ _ _ => rfl)

/-- The complex tensor maps onto the original balanced tensor. -/
def tensorProjection : (V ⊗[ℂ] W) →ₗ[ℂ]
    NonUnitalModuleTensor.Tensor (HeckeAlgebra μ) V W :=
  TensorProduct.lift (pureBilinear μ ρ hρ hM)

include hL in
/-- Hecke balancing makes the complex tensor projection diagonal-invariant. -/
theorem tensorProjection_invariant (g : G) :
    (tensorProjection μ ρ hρ hM).comp (Representation.tprod ρ σ g) =
      tensorProjection μ ρ hρ hM := by
  ext x y
  exact invariant_of_balanced μ ρ σ hρ hσ M hM
    (pureBilinear μ ρ hρ hM) (by
      intro f x y
      change NonUnitalModuleTensor.tmul (HeckeAlgebra μ) V W (op f • x) y =
        NonUnitalModuleTensor.tmul (HeckeAlgebra μ) V W x (heckeAction μ σ hσ f y)
      rw [← hL]
      exact NonUnitalModuleTensor.tmul_balanced _ _ _ f x y) g x y

/-- The forward comparison descends the pure tensor map through diagonal coinvariants. -/
def fromCoinvariants : Representation.Coinvariants (Representation.tprod ρ σ) →ₗ[ℂ]
    NonUnitalModuleTensor.Tensor (HeckeAlgebra μ) V W :=
  Representation.Coinvariants.lift _ (tensorProjection μ ρ hρ hM)
    (tensorProjection_invariant μ ρ σ hρ hσ hM hL)

@[simp] theorem fromCoinvariants_tmul (x : V) (y : W) :
    fromCoinvariants μ ρ σ hρ hσ hM hL
      (Representation.Coinvariants.mk (Representation.tprod ρ σ) (x ⊗ₜ y)) =
      NonUnitalModuleTensor.tmul (HeckeAlgebra μ) V W x y := rfl

/-- The pure coinvariant class, as a bilinear map. -/
def classBilinear : V →ₗ[ℂ] W →ₗ[ℂ]
    Representation.Coinvariants (Representation.tprod ρ σ) :=
  (TensorProduct.mk ℂ V W).compr₂ (Representation.Coinvariants.mk (Representation.tprod ρ σ))

/-- The reverse comparison descends through the actual integer balancing quotient. -/
def toCoinvariants : NonUnitalModuleTensor.Tensor (HeckeAlgebra μ) V W →+
    Representation.Coinvariants (Representation.tprod ρ σ) :=
  NonUnitalModuleTensor.lift (HeckeAlgebra μ)
    (NondegenerateTensorScalars.toBiadditive (classBilinear ρ σ))
    (by
      intro f x y
      change classBilinear ρ σ (op f • x) y = classBilinear ρ σ x (f • y)
      rw [hL]
      exact balanced_of_invariant μ ρ σ hρ hσ M hM (classBilinear ρ σ) (by
        intro g x y
        exact Representation.Coinvariants.mk_self_apply (Representation.tprod ρ σ) g (x ⊗ₜ y))
        f x y)

omit [SMulCommClass ℂ (HeckeAlgebra μ) W] [IsScalarTower ℂ (HeckeAlgebra μ) W] in
@[simp] theorem toCoinvariants_tmul (x : V) (y : W) :
    toCoinvariants μ ρ σ hρ hσ hM hL (NonUnitalModuleTensor.tmul (HeckeAlgebra μ) V W x y) =
      Representation.Coinvariants.mk (Representation.tprod ρ σ) (x ⊗ₜ y) := rfl

/-- The actual coinvariant and original balanced tensor quotients are additively equivalent. -/
def equivalence : Representation.Coinvariants (Representation.tprod ρ σ) ≃+
    NonUnitalModuleTensor.Tensor (HeckeAlgebra μ) V W where
  toFun := fromCoinvariants μ ρ σ hρ hσ hM hL
  invFun := toCoinvariants μ ρ σ hρ hσ hM hL
  left_inv t := by
    obtain ⟨q, rfl⟩ := Representation.Coinvariants.mk_surjective (Representation.tprod ρ σ) t
    induction q using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add q r hq hr => simpa only [map_add] using congrArg₂ (· + ·) hq hr
  right_inv t := by
    have h : (fromCoinvariants μ ρ σ hρ hσ hM hL).toAddMonoidHom.comp
        (toCoinvariants μ ρ σ hρ hσ hM hL) =
        AddMonoidHom.id (NonUnitalModuleTensor.Tensor (HeckeAlgebra μ) V W) :=
      NonUnitalModuleTensor.hom_ext (HeckeAlgebra μ) (fun _ _ => rfl)
    exact DFunLike.congr_fun h t
  map_add' := (fromCoinvariants μ ρ σ hρ hσ hM hL).map_add

end Quotients

end CoinvariantTensor

/-- Renard III.1.15: diagonal coinvariants identify with the original Hecke tensor. -/
theorem coinvariantHeckeTensor : CoinvariantHeckeTensorStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ μ _ V W _ _ _ _ ρ σ hρ hσ M hM
  let _ := M
  let _ := heckeNonUnitalModule μ σ hσ
  let _ := NonUnitalModule.ofLinearEndHom_smulCommClass (heckeAction μ σ hσ)
  let _ := NonUnitalModule.ofLinearEndHom_isScalarTower (heckeAction μ σ hσ)
  exact ⟨CoinvariantTensor.equivalence μ ρ σ hρ hσ hM (fun _ _ => rfl), fun _ _ => rfl⟩

end Langlands.Renard.Smooth
