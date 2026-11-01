import Langlands.Global.AdelicParabolicInduction
import Langlands.Global.HeckeCharacter
import Langlands.Representation.Induction.BlockFactors

/-!
# Half-twisted adelic induction from actual block factors

The coefficient module is the published algebraic indexed tensor product.
Finite smoothness concerns a common stabilizer in the actual finite factor.
-/

noncomputable section

universe uF uV uW uX

namespace Langlands.Global.AdelicBlockFactorInduction

open NumberField IsDedekindDomain
open Langlands.GeneralLinear AdelicBlockParabolic
open scoped BigOperators

variable (F : Type uF) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable {V : Fin B.length → Type uV} {W : Fin B.length → Type uW}
  {X : Fin B.length → Type uX}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]

/-- Actual tensor-valued covariant functions for the positive half twist. -/
abbrev Sections
    (σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i)) :=
  AdelicParabolicInduction.Sections F B (B.blockTensor σ)

/-- Actual right translation on the tensor-valued covariant functions. -/
abbrev rightAction
    (σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i)) :
    Representation ℂ (AdelicGL F n) (Sections F B σ) :=
  AdelicParabolicInduction.rightAction F B (B.blockTensor σ)

theorem covariance
    (σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i))
    (f : Sections F B σ) (p : Full F B) (g : AdelicGL F n) :
    f.val (p.val * g) =
      (AdelicBlockDeterminantCharacter.leviHalfCharacter F B
        (B.leviProjection (Adeles F) p) : ℂ) •
        B.blockTensor σ (B.leviProjection (Adeles F) p) (f.val g) :=
  AdelicParabolicInduction.covariance F B (B.blockTensor σ) f p g

@[simp]
theorem evaluate_rightAction
    (σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i))
    (g x : AdelicGL F n) (f : Sections F B σ) :
    (rightAction F B σ g f).val x = f.val (x * g) := rfl

/-- Tensor-valued sections fixed by one open subgroup of the finite factor. -/
abbrev FiniteSmoothSections
    (σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i)) :=
  AdelicParabolicInduction.FiniteSmoothSections F B (B.blockTensor σ)

/-- The full adelic action on the actual finite-smooth block-factor sections. -/
def finiteSmoothInduced
    (σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i)) :
    Representation ℂ (AdelicGL F n) (FiniteSmoothSections F B σ) :=
  AdelicParabolicInduction.finiteSmoothInduced F B (B.blockTensor σ)

@[simp]
theorem evaluate_finiteSmoothInduced
    (σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i))
    (g x : AdelicGL F n) (f : FiniteSmoothSections F B σ) :
    (finiteSmoothInduced F B σ g f).val.val x = f.val.val (x * g) := rfl

/-- Restriction to the actual finite adelic group is smooth. -/
theorem finiteSmoothInduced_isSmooth
    (σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i)) :
    Langlands.IsSmooth (R := ℂ) (G := FiniteAdelicGL F n)
      (V := FiniteSmoothSections F B σ)
      ((finiteSmoothInduced F B σ).comp (AdelicGL.ofFinite F n).toMonoidHom) :=
  AdelicParabolicInduction.finiteSmoothInduced_isSmooth F B (B.blockTensor σ)

/-- Every finite slice is locally constant, with no topology on the tensor module. -/
theorem finiteSmoothSection_finiteLocallyConstant
    (σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i))
    (f : FiniteSmoothSections F B σ) (a : InfiniteAdelicGL F n) :
    IsLocallyConstant (fun b => f.val.val (AdelicGL.pair F n a b)) :=
  AdelicParabolicInduction.finiteSmoothSection_finiteLocallyConstant F B
    (B.blockTensor σ) f a

/-- Tensor the factor intertwiners and postcompose the actual sections. -/
def sectionMap
    {σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i)}
    {τ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (W i)}
    (T : ∀ i, (σ i).IntertwiningMap (τ i)) :
    (rightAction F B σ).IntertwiningMap (rightAction F B τ) :=
  AdelicParabolicInduction.sectionMap F B (FiniteTensor.externalMap T)

@[simp]
theorem sectionMap_apply
    {σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i)}
    {τ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (W i)}
    (T : ∀ i, (σ i).IntertwiningMap (τ i))
    (f : Sections F B σ) (x : AdelicGL F n) :
    (sectionMap F B T f).val x = FiniteTensor.externalMap T (f.val x) := rfl

@[simp]
theorem sectionMap_id
    (σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i)) :
    sectionMap F B (fun i => Representation.IntertwiningMap.id (σ i)) =
      Representation.IntertwiningMap.id (rightAction F B σ) := by
  ext f x
  change FiniteTensor.externalMap
    (fun i => Representation.IntertwiningMap.id (σ i)) (f.val x) = f.val x
  rw [FiniteTensor.externalMap_id]
  rfl

theorem sectionMap_comp
    {σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i)}
    {τ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (W i)}
    {υ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (X i)}
    (T : ∀ i, (σ i).IntertwiningMap (τ i))
    (S : ∀ i, (τ i).IntertwiningMap (υ i)) :
    sectionMap F B (fun i => (S i).comp (T i)) =
      (sectionMap F B S).comp (sectionMap F B T) := by
  ext f x
  change FiniteTensor.externalMap (fun i => (S i).comp (T i)) (f.val x) =
    FiniteTensor.externalMap S (FiniteTensor.externalMap T (f.val x))
  rw [FiniteTensor.externalMap_comp]
  rfl

/-- Actual tensor coefficient postcomposition preserves the common finite stabilizer. -/
def finiteSmoothInducedMap
    {σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i)}
    {τ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (W i)}
    (T : ∀ i, (σ i).IntertwiningMap (τ i)) :
    (finiteSmoothInduced F B σ).IntertwiningMap (finiteSmoothInduced F B τ) :=
  AdelicParabolicInduction.finiteSmoothInducedMap F B (FiniteTensor.externalMap T)

@[simp]
theorem finiteSmoothInducedMap_apply
    {σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i)}
    {τ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (W i)}
    (T : ∀ i, (σ i).IntertwiningMap (τ i))
    (f : FiniteSmoothSections F B σ) (x : AdelicGL F n) :
    (finiteSmoothInducedMap F B T f).val.val x =
      FiniteTensor.externalMap T (f.val.val x) := rfl

@[simp]
theorem finiteSmoothInducedMap_id
    (σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i)) :
    finiteSmoothInducedMap F B (fun i => Representation.IntertwiningMap.id (σ i)) =
      Representation.IntertwiningMap.id (finiteSmoothInduced F B σ) := by
  rw [finiteSmoothInducedMap, FiniteTensor.externalMap_id,
    AdelicParabolicInduction.finiteSmoothInducedMap_id]
  rfl

theorem finiteSmoothInducedMap_comp
    {σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i)}
    {τ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (W i)}
    {υ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (X i)}
    (T : ∀ i, (σ i).IntertwiningMap (τ i))
    (S : ∀ i, (τ i).IntertwiningMap (υ i)) :
    finiteSmoothInducedMap F B (fun i => (S i).comp (T i)) =
      (finiteSmoothInducedMap F B S).comp (finiteSmoothInducedMap F B T) := by
  rw [finiteSmoothInducedMap, FiniteTensor.externalMap_comp,
    AdelicParabolicInduction.finiteSmoothInducedMap_comp]
  rfl

/-- Product of the actual block central Hecke characters, with no rank weights. -/
def centralCharacter (c : Fin B.length → HeckeCharacter F) : HeckeCharacter F :=
  ∏ i, c i

@[simp]
theorem centralCharacter_onIdeles
    (c : Fin B.length → HeckeCharacter F) (z : Ideles F) :
    (centralCharacter F B c).onIdeles z = ∏ i, (c i).onIdeles z := by
  classical
  have heval (S : Finset (Fin B.length)) :
      (∏ i ∈ S, c i) (ideleClassMap F z) = ∏ i ∈ S, c i (ideleClassMap F z) := by
    induction S using Finset.induction_on with
    | empty => rfl
    | @insert i S hi hS =>
      simp only [Finset.prod_insert hi, ContinuousMonoidHom.mul_apply, hS]
  exact heval Finset.univ

/-- A common scalar acts on the actual tensor by the product central character. -/
theorem blockTensor_scalar
    (σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i))
    (c : Fin B.length → HeckeCharacter F)
    (hσ : ∀ i (z : Ideles F) (v : V i),
      σ i (AdelicGL.scalar F (B.size i) z) v = ((c i).onIdeles z : ℂ) • v)
    (z : Ideles F) (v : PiTensorProduct ℂ V) :
    B.blockTensor σ (AdelicBlockCenter.scalarLevi F B z) v =
      ((centralCharacter F B c).onIdeles z : ℂ) • v := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    rw [map_smul, BlockShape.blockTensor_tprod]
    simp_rw [AdelicBlockCenter.scalarLevi_apply, hσ]
    rw [(PiTensorProduct.tprod ℂ).map_smul_univ,
      centralCharacter_onIdeles, Units.coe_prod]
    exact smul_comm a _ _
  | add x y hx hy =>
    simp only [map_add, hx, hy, smul_add]

/-- All covariant sections inherit the product of the supplied block central characters. -/
theorem rightAction_scalar
    (σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i))
    (c : Fin B.length → HeckeCharacter F)
    (hσ : ∀ i (z : Ideles F) (v : V i),
      σ i (AdelicGL.scalar F (B.size i) z) v = ((c i).onIdeles z : ℂ) • v)
    (z : Ideles F) (f : Sections F B σ) :
    rightAction F B σ (AdelicGL.scalar F n z) f =
      ((centralCharacter F B c).onIdeles z : ℂ) • f :=
  AdelicParabolicInduction.rightAction_scalar F B (B.blockTensor σ)
    (centralCharacter F B c).onIdeles.toMonoidHom (blockTensor_scalar F B σ c hσ) z f

/-- The actual finite-smooth induced representation has that same central character. -/
theorem finiteSmoothInduced_scalar
    (σ : ∀ i, Representation ℂ (AdelicGL F (B.size i)) (V i))
    (c : Fin B.length → HeckeCharacter F)
    (hσ : ∀ i (z : Ideles F) (v : V i),
      σ i (AdelicGL.scalar F (B.size i) z) v = ((c i).onIdeles z : ℂ) • v)
    (z : Ideles F) (f : FiniteSmoothSections F B σ) :
    finiteSmoothInduced F B σ (AdelicGL.scalar F n z) f =
      ((centralCharacter F B c).onIdeles z : ℂ) • f :=
  AdelicParabolicInduction.finiteSmoothInduced_scalar F B (B.blockTensor σ)
    (centralCharacter F B c).onIdeles.toMonoidHom (blockTensor_scalar F B σ c hσ) z f

end Langlands.Global.AdelicBlockFactorInduction
