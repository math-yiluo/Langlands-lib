import Langlands.AllFieldBZ.Group.GL.MirabolicMixedProductSubgroups
import Langlands.AllFieldBZ.Representation.Induction.BinaryProduct
import Langlands.Representation.Mirabolic.MixedProducts

/-!
# All-field port of `Langlands.Representation.Mirabolic.MixedProducts`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Mirabolic.MixedProducts` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct
open scoped NNReal
namespace Langlands.AllFieldBZ
universe uF uR uG uH uK uV uW uX uY uZ uU

/-! ## Compact induction from a subgroup containing every element -/

namespace Induction
open Langlands.Induction
section TopHom
variable {G : Type uG} [Group G]

end TopHom
section TopEquiv
variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem _root_.Langlands.Induction.subsingleton_leftQuotient (P : Subgroup G) (hP : ∀ g, g ∈ P) :
    Subsingleton (LeftQuotient P) :=
  ⟨fun a b => Quotient.inductionOn₂ a b fun _ _ =>
    Quotient.sound (QuotientGroup.rightRel_apply.mpr (hP _))⟩

end TopEquiv
end Induction
/-! ## Binary external tensor products, pullbacks and carrier lifts -/

namespace MixedProductTensor
open Langlands.MixedProductTensor
section External
variable {G : Type uG} {H : Type uH} [Group G] [Group H]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
variable {V'' : Type uX} [AddCommGroup V''] [Module ℂ V'']
variable {W : Type uY} [AddCommGroup W] [Module ℂ W]
variable {W' : Type uZ} [AddCommGroup W'] [Module ℂ W']
variable {W'' : Type uU} [AddCommGroup W''] [Module ℂ W'']

section Smooth
variable [TopologicalSpace G] [TopologicalSpace H]

end Smooth
end External
section Pullback
variable {G : Type uG} [Group G] {K : Type uK} [Group K]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uW} [AddCommGroup V'] [Module ℂ V']

end Pullback
section Lift
variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uW} [AddCommGroup V'] [Module ℂ V']

end Lift
section Functors
variable {G : Type uG} {H : Type uH} {K : Type uK} [Group G] [Group H] [Group K]
variable [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K]

end Functors
end MixedProductTensor
/-! ## The representations being induced -/

namespace GeneralLinear.Mirabolic.MixedProduct
open Langlands.GeneralLinear.Mirabolic.MixedProduct
section Inducing
variable {R : Type uR} [CommRing R] {k r : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

variable [TopologicalSpace R]

end Inducing
/-! ### The case `k = 0`: both inducing subgroups are the whole group -/

section RankZero
variable {R : Type uR} [CommRing R] {r : ℕ}

variable [TopologicalSpace R]

end RankZero
end GeneralLinear.Mirabolic.MixedProduct
/-! ## Characters, products and their laws for a supplied p-adic realization -/

namespace LocalFieldPackage.TopologicalData
open Langlands.GeneralLinear hiding blockSum rankInclusion
open Langlands.GeneralLinear.Mirabolic.MixedProduct
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-! ### The explicit total characters -/

/-- Case (II): `χ_L(a, p) = ν_k(a)^((r+1)/2) · ν_(r+1)(p)^(-k/2)` on `GL_k × P_(r+1)`,
with `ν_n = |det|_F` the residue-normalized determinant norm. -/
def leftLeviCharacter (k r : ℕ) :
    GeneralLinear k F.Carrier × mirabolic r F.Carrier →* ℂˣ :=
  (realPowerCharacter (T.determinantNorm k) (((r + 1 : ℕ) : ℝ) / 2)).comp
      (MonoidHom.fst _ _) *
    (realPowerCharacter ((T.determinantNorm (r + 1)).comp (mirabolic r F.Carrier).subtype)
      (-((k : ℝ) / 2))).comp (MonoidHom.snd _ _)

theorem leftLeviCharacter_apply (k r : ℕ)
    (q : GeneralLinear k F.Carrier × mirabolic r F.Carrier) :
    (T.leftLeviCharacter k r q : ℂ) =
      ((((T.determinantNorm k q.1 : ℝ≥0) : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        ((((T.determinantNorm (r + 1) q.2.val : ℝ≥0) : ℝ) ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) :=
  rfl

/-- Case (III): `χ_R(p, a) = ν_r(d)^(k/2) · ν_k(a)^(-(r+1)/2)`, `d = projection p`. -/
def rightLeviCharacter (k r : ℕ) :
    mirabolic r F.Carrier × GeneralLinear k F.Carrier →* ℂˣ :=
  (realPowerCharacter ((T.determinantNorm r).comp Mirabolic.projection) ((k : ℝ) / 2)).comp
      (MonoidHom.fst _ _) *
    (realPowerCharacter (T.determinantNorm k) (-(((r + 1 : ℕ) : ℝ) / 2))).comp
      (MonoidHom.snd _ _)

theorem rightLeviCharacter_apply (k r : ℕ)
    (q : mirabolic r F.Carrier × GeneralLinear k F.Carrier) :
    (T.rightLeviCharacter k r q : ℂ) =
      ((((T.determinantNorm r (Mirabolic.projection q.1) : ℝ≥0) : ℝ) ^ ((k : ℝ) / 2) : ℝ) : ℂ) *
        ((((T.determinantNorm k q.2 : ℝ≥0) : ℝ) ^ (-(((r + 1 : ℕ) : ℝ) / 2)) : ℝ) : ℂ) :=
  rfl

private theorem determinantNorm_zero (g : GeneralLinear 0 F.Carrier) :
    T.determinantNorm 0 g = 1 := by
  rw [show g = 1 from Units.ext (Matrix.ext fun i => Fin.elim0 i), map_one]

/-- For `k = 0` the left character is trivial. -/
theorem leftLeviCharacter_zero_left (r : ℕ) : T.leftLeviCharacter 0 r = 1 := by
  ext q
  rw [leftLeviCharacter_apply, T.determinantNorm_zero]
  simp

/-- For `k = 0` the right character is trivial. -/
theorem rightLeviCharacter_zero_left (r : ℕ) : T.rightLeviCharacter 0 r = 1 := by
  ext q
  rw [rightLeviCharacter_apply, T.determinantNorm_zero]
  simp

/-- For `r = 0`, `χ_R(p, a) = ν_k(a)^(-1/2)`: only the retained twist survives. -/
theorem rightLeviCharacter_zero_right_apply (k : ℕ)
    (q : mirabolic 0 F.Carrier × GeneralLinear k F.Carrier) :
    (T.rightLeviCharacter k 0 q : ℂ) =
      ((((T.determinantNorm k q.2 : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [rightLeviCharacter_apply, T.determinantNorm_zero]
  simp

theorem isOpen_ker_leftLeviCharacter_comp (k r : ℕ) :
    letI := T.topology
    IsOpen (((T.leftLeviCharacter k r).comp leftProjection).ker :
      Set (leftSubgroup k r F.Carrier)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 1)
  let φ₁ : leftSubgroup k r F.Carrier →* ℝ≥0ˣ :=
    (T.determinantNorm k).comp ((MonoidHom.fst _ _).comp leftProjection)
  let φ₂ : leftSubgroup k r F.Carrier →* ℝ≥0ˣ :=
    ((T.determinantNorm (r + 1)).comp (mirabolic r F.Carrier).subtype).comp
      ((MonoidHom.snd _ _).comp leftProjection)
  have h₁ : IsOpen (φ₁.ker : Set (leftSubgroup k r F.Carrier)) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact (T.isOpen_ker_determinantNorm k).preimage
      (continuous_fst.comp continuous_leftProjection)
  have h₂ : IsOpen (φ₂.ker : Set (leftSubgroup k r F.Carrier)) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap, ← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact ((T.isOpen_ker_determinantNorm (r + 1)).preimage continuous_subtype_val).preimage
      (continuous_snd.comp continuous_leftProjection)
  refine Subgroup.isOpen_mono (H₁ := φ₁.ker ⊓ φ₂.ker) ?_ ?_
  · intro h hh
    obtain ⟨hh₁, hh₂⟩ := Subgroup.mem_inf.mp hh
    have e₁ : T.determinantNorm k (leftProjection h).1 = 1 := hh₁
    have e₂ : T.determinantNorm (r + 1) (leftProjection h).2.val = 1 := hh₂
    change T.leftLeviCharacter k r (leftProjection h) = 1
    simp [leftLeviCharacter, realPowerCharacter, e₁, e₂]
  · rw [Subgroup.coe_inf]
    exact h₁.inter h₂

theorem isOpen_ker_rightLeviCharacter_comp (k r : ℕ) :
    letI := T.topology
    IsOpen (((T.rightLeviCharacter k r).comp rightProjection).ker :
      Set (rightSubgroup k r F.Carrier)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 1)
  let φ₁ : rightSubgroup k r F.Carrier →* ℝ≥0ˣ :=
    (T.determinantNorm r).comp (Mirabolic.projection.comp
      ((MonoidHom.fst _ _).comp rightProjection))
  let φ₂ : rightSubgroup k r F.Carrier →* ℝ≥0ˣ :=
    (T.determinantNorm k).comp ((MonoidHom.snd _ _).comp rightProjection)
  have h₁ : IsOpen (φ₁.ker : Set (rightSubgroup k r F.Carrier)) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact (T.isOpen_ker_determinantNorm r).preimage
      (Mirabolic.continuous_projection.comp (continuous_fst.comp continuous_rightProjection))
  have h₂ : IsOpen (φ₂.ker : Set (rightSubgroup k r F.Carrier)) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact (T.isOpen_ker_determinantNorm k).preimage
      (continuous_snd.comp continuous_rightProjection)
  refine Subgroup.isOpen_mono (H₁ := φ₁.ker ⊓ φ₂.ker) ?_ ?_
  · intro h hh
    obtain ⟨hh₁, hh₂⟩ := Subgroup.mem_inf.mp hh
    have e₁ : T.determinantNorm r (Mirabolic.projection (rightProjection h).1) = 1 := hh₁
    have e₂ : T.determinantNorm k (rightProjection h).2 = 1 := hh₂
    change T.rightLeviCharacter k r (rightProjection h) = 1
    simp [rightLeviCharacter, realPowerCharacter, e₁, e₂]
  · rw [Subgroup.coe_inf]
    exact h₁.inter h₂

/-- The case (II) smooth character `h ↦ χ_L(leftProjection h)` on the inducing subgroup. -/
def leftCharacter (k r : ℕ) :
    letI := T.topology
    Induction.SmoothCharacter ℂ (leftSubgroup k r F.Carrier) :=
  letI := T.topology
  { toMonoidHom := (T.leftLeviCharacter k r).comp leftProjection
    isOpen_ker := T.isOpen_ker_leftLeviCharacter_comp k r }

/-- The case (III) smooth character `h ↦ χ_R(rightProjection h)` on the inducing subgroup. -/
def rightCharacter (k r : ℕ) :
    letI := T.topology
    Induction.SmoothCharacter ℂ (rightSubgroup k r F.Carrier) :=
  letI := T.topology
  { toMonoidHom := (T.rightLeviCharacter k r).comp rightProjection
    isOpen_ker := T.isOpen_ker_rightLeviCharacter_comp k r }

theorem leftCharacter_apply (k r : ℕ) (h : leftSubgroup k r F.Carrier) :
    letI := T.topology
    (T.leftCharacter k r).toMonoidHom h = T.leftLeviCharacter k r (leftProjection h) := rfl

theorem rightCharacter_apply (k r : ℕ) (h : rightSubgroup k r F.Carrier) :
    letI := T.topology
    (T.rightCharacter k r).toMonoidHom h = T.rightLeviCharacter k r (rightProjection h) := rfl

theorem leftCharacter_zero_left (r : ℕ) :
    letI := T.topology
    (T.leftCharacter 0 r).toMonoidHom = 1 := by
  change (T.leftLeviCharacter 0 r).comp leftProjection = 1
  rw [T.leftLeviCharacter_zero_left, MonoidHom.one_comp]

theorem rightCharacter_zero_left (r : ℕ) :
    letI := T.topology
    (T.rightCharacter 0 r).toMonoidHom = 1 := by
  change (T.rightLeviCharacter 0 r).comp rightProjection = 1
  rw [T.rightLeviCharacter_zero_left, MonoidHom.one_comp]

/-! ### The two products -/

/-- BZ77 §4.12(II): the product `A × B` of `A ∈ Rep(GL_k)` and `B ∈ Rep(P_(r+1))`,
a smooth representation of `P_(k+r+1)`. It is the published normalized compact
induction, from `leftSubgroup k r`, of `A ⊠ B` pulled back along `leftProjection`,
twisted by `χ_L`. -/
def leftMixedProductFunctor (k r : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + r) F.Carrier) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1)
  MixedProductTensor.externalFunctor ⋙
    MixedProductTensor.pullbackFunctor leftProjection continuous_leftProjection ⋙
      SmoothRep.toRep ⋙
        Induction.normalizedCompactInductionFunctor (leftSubgroup k r F.Carrier)
          (T.leftCharacter k r)

/-- BZ77 §4.12(III): the product `B × A` of `B ∈ Rep(P_(r+1))` and `A ∈ Rep(GL_k)`,
a smooth representation of `P_(k+r+1)`. It is the published normalized compact
induction, from `rightSubgroup k r`, of `B ⊠ A` pulled back along `rightProjection`,
twisted by `χ_R`. -/
def rightMixedProductFunctor (k r : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + r) F.Carrier) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1)
  MixedProductTensor.externalFunctor ⋙
    MixedProductTensor.pullbackFunctor rightProjection continuous_rightProjection ⋙
      SmoothRep.toRep ⋙
        Induction.normalizedCompactInductionFunctor (rightSubgroup k r F.Carrier)
          (T.rightCharacter k r)

variable {k r : ℕ}

/-! ### Evaluation, covariance, right translation and maps -/

/-- The value `f(x) ∈ A ⊗ B` at `x ∈ P_(k+r+1)` of a vector `f` of `A × B`. -/
def leftMixedEval
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (f : letI := T.topology; (T.leftMixedProductFunctor k r).obj X)
    (x : mirabolic (k + r) F.Carrier) : X.1 ⊗[ℂ] X.2 :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1)
  Induction.eval (leftSubgroup k r F.Carrier)
    (twist (T.leftCharacter k r).toMonoidHom
      (leftInducingRepresentation X.1.representation X.2.representation))
    (show Induction.CompactFunctions (leftSubgroup k r F.Carrier)
      (twist (T.leftCharacter k r).toMonoidHom
        (leftInducingRepresentation X.1.representation X.2.representation)) from f).1 x

/-- The value `f(x) ∈ B ⊗ A` at `x ∈ P_(k+r+1)` of a vector `f` of `B × A`. -/
def rightMixedEval
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (f : letI := T.topology; (T.rightMixedProductFunctor k r).obj X)
    (x : mirabolic (k + r) F.Carrier) : X.1 ⊗[ℂ] X.2 :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1)
  Induction.eval (rightSubgroup k r F.Carrier)
    (twist (T.rightCharacter k r).toMonoidHom
      (rightInducingRepresentation X.1.representation X.2.representation))
    (show Induction.CompactFunctions (rightSubgroup k r F.Carrier)
      (twist (T.rightCharacter k r).toMonoidHom
        (rightInducingRepresentation X.1.representation X.2.representation)) from f).1 x

/-- Vectors of `A × B` are determined by their values. -/
theorem leftMixedEval_injective
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)) :
    Function.Injective (T.leftMixedEval X) := by
  intro f f' h
  exact Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => congrFun h x)))

/-- Vectors of `B × A` are determined by their values. -/
theorem rightMixedEval_injective
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier)) :
    Function.Injective (T.rightMixedEval X) := by
  intro f f' h
  exact Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => congrFun h x)))

/-- Covariance `f(h x) = χ_L(h) • (A ⊠ B)(leftProjection h) (f x)`. -/
theorem leftMixedEval_covariant
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (f : letI := T.topology; (T.leftMixedProductFunctor k r).obj X)
    (h : leftSubgroup k r F.Carrier) (x : mirabolic (k + r) F.Carrier) :
    letI := T.topology
    T.leftMixedEval X f ((h : mirabolic (k + r) F.Carrier) * x) =
      (T.leftLeviCharacter k r (leftProjection h) : ℂ) •
        leftInducingRepresentation X.1.representation X.2.representation h
          (T.leftMixedEval X f x) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 1)
  exact (show Induction.CompactFunctions (leftSubgroup k r F.Carrier)
    (twist (T.leftCharacter k r).toMonoidHom
      (leftInducingRepresentation X.1.representation X.2.representation)) from f).1.1.2 h x

/-- The source formula `f([a Z; 0 p] x) = χ_L(a, p) • (A(a) ⊗ B(p)) (f x)`. -/
theorem leftMixedEval_leftMatrix_mul
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (f : letI := T.topology; (T.leftMixedProductFunctor k r).obj X)
    (a : GeneralLinear k F.Carrier) (q : mirabolic r F.Carrier)
    (Z : Matrix (Fin k) (Fin (r + 1)) F.Carrier) (x : mirabolic (k + r) F.Carrier) :
    letI := T.topology
    T.leftMixedEval X f ((leftMatrix a q Z : mirabolic (k + r) F.Carrier) * x) =
      (T.leftLeviCharacter k r (a, q) : ℂ) •
        TensorProduct.map (X.1.representation a) (X.2.representation q)
          (T.leftMixedEval X f x) := by
  rw [T.leftMixedEval_covariant, leftInducingRepresentation_leftMatrix, leftProjection_matrix]

/-- Left multiplication by the actual radical does not change values. -/
theorem leftMixedEval_of_mem_leftKernel_mul
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (f : letI := T.topology; (T.leftMixedProductFunctor k r).obj X)
    {h : leftSubgroup k r F.Carrier} (hh : h ∈ leftKernel k r F.Carrier)
    (x : mirabolic (k + r) F.Carrier) :
    letI := T.topology
    T.leftMixedEval X f ((h : mirabolic (k + r) F.Carrier) * x) = T.leftMixedEval X f x := by
  rw [T.leftMixedEval_covariant, leftInducingRepresentation_of_mem_leftKernel _ _ hh,
    show leftProjection h = 1 from hh, map_one, Units.val_one, one_smul,
    Module.End.one_apply]

/-- The action is right translation: `(g · f)(x) = f(x g)`. -/
theorem leftMixedProductFunctor_action
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (g : mirabolic (k + r) F.Carrier)
    (f : letI := T.topology; (T.leftMixedProductFunctor k r).obj X)
    (x : mirabolic (k + r) F.Carrier) :
    letI := T.topology
    T.leftMixedEval X (((T.leftMixedProductFunctor k r).obj X).representation g f) x =
      T.leftMixedEval X f (x * g) := rfl

/-- Each vector has a single open subgroup of right stabilizers. -/
theorem leftMixedEval_exists_openSubgroup
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (f : letI := T.topology; (T.leftMixedProductFunctor k r).obj X) :
    letI := T.topology
    ∃ K : OpenSubgroup (mirabolic (k + r) F.Carrier), ∀ (u : K) (x : mirabolic (k + r) F.Carrier),
      T.leftMixedEval X f (x * (u : mirabolic (k + r) F.Carrier)) = T.leftMixedEval X f x := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 1)
  obtain ⟨K, hK⟩ := (show Induction.CompactFunctions (leftSubgroup k r F.Carrier)
    (twist (T.leftCharacter k r).toMonoidHom
      (leftInducingRepresentation X.1.representation X.2.representation)) from f).1.2
  exact ⟨K, fun u x => congrArg (fun φ => φ.1 x) (hK u)⟩

/-- The nonzero support, projected to `H \ P_(k+r+1)`, is compact. -/
theorem rightMixedEval_isCompact_quotientSupport
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (f : letI := T.topology; (T.rightMixedProductFunctor k r).obj X) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1)
    IsCompact (Induction.quotientSupport (rightSubgroup k r F.Carrier)
      (T.rightMixedEval X f)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 1)
  exact (show Induction.CompactFunctions (rightSubgroup k r F.Carrier)
    (twist (T.rightCharacter k r).toMonoidHom
      (rightInducingRepresentation X.1.representation X.2.representation)) from f).2

/-- A vector of `A × B` from a covariant function with a single open subgroup of right
stabilizers and compact projected support. -/
def leftMixedMk
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (f : mirabolic (k + r) F.Carrier → X.1 ⊗[ℂ] X.2)
    (hcov : letI := T.topology
      ∀ (h : leftSubgroup k r F.Carrier) (x : mirabolic (k + r) F.Carrier),
        f ((h : mirabolic (k + r) F.Carrier) * x) =
          (T.leftLeviCharacter k r (leftProjection h) : ℂ) •
            leftInducingRepresentation X.1.representation X.2.representation h (f x))
    (K : letI := T.topology; OpenSubgroup (mirabolic (k + r) F.Carrier))
    (hK : letI := T.topology
      ∀ (u : K) (x : mirabolic (k + r) F.Carrier),
        f (x * (u : mirabolic (k + r) F.Carrier)) = f x)
    (hc : letI := T.topology
      letI := T.generalLinearTopologicalGroup (k + r + 1)
      IsCompact (Induction.quotientSupport (leftSubgroup k r F.Carrier) f)) :
    letI := T.topology
    (T.leftMixedProductFunctor k r).obj X :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1)
  Induction.compactFunctionOf (leftSubgroup k r F.Carrier)
    (twist (T.leftCharacter k r).toMonoidHom
      (leftInducingRepresentation X.1.representation X.2.representation)) f hcov K hK hc

/-! ### The unit -/

end LocalFieldPackage.TopologicalData
end Langlands.AllFieldBZ
