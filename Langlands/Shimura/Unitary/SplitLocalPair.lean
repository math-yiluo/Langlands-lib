import Langlands.Shimura.Unitary.SplitCompletionChart
import Langlands.Shimura.Unitary.UnitaryLocalProfileRealizationStatement
import Langlands.Shimura.Unitary.ComplexMatrixInvolution
import Langlands.ClassFieldTheory.Local.BrauerInvariantRepresentative
import Langlands.ClassFieldTheory.Local.BrauerLocalInvariant

/-! # A local pair with exchange involution at an actual split place -/

noncomputable section

universe u v

namespace Langlands.Shimura.AlgebraInvolution

/-- The exchange involution of a ring times its multiplicative opposite. -/
def exchangeOpposite (R B : Type*) [CommRing R] [Ring B] [Algebra R B] :
    AlgebraInvolution R (B × Bᵐᵒᵖ) where
  linear :=
    { toFun := fun a => (a.2.unop, MulOpposite.op a.1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one := rfl
  map_mul := fun _ _ => rfl
  involutive := fun _ => rfl

@[simp] theorem exchangeOpposite_apply (R B : Type*) [CommRing R] [Ring B] [Algebra R B]
    (a : B × Bᵐᵒᵖ) : exchangeOpposite R B a = (a.2.unop, MulOpposite.op a.1) := rfl

end Langlands.Shimura.AlgebraInvolution

namespace Langlands.Shimura.FiniteUnitary.SplitPlaceIdentification

open NumberField _root_.Algebra Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.ClassFieldTheory.Local Langlands.LocalField
open scoped FiniteExtension TensorProduct ValuativeRel

variable {E : Type u} {K : Type v}
  [Field E] [Field K] [NumberField K] [Algebra E K]
  {p : Langlands.Global.FinitePlace E}

local instance (r : Langlands.Global.FinitePlace K) :
    ValuativeRel (FiniteCompletion K r) := FiniteCompletion.valuativeRel r

local instance (r : Langlands.Global.FinitePlace K) :
    IsNonarchimedeanLocalField (FiniteCompletion K r) :=
  FiniteCompletion.isNonarchimedeanLocalField r

/-- A factor of the prescribed degree and invariant over an actual upper completion. -/
def invariantFactor (q : FinitePlacesAbove K p) {n : ℕ} (hn : 0 < n)
    (x : denominatorSubgroup n) : CSA.{v, v} (FiniteCompletion K q.val) :=
  csaOfInvariant (FiniteCompletion K q.val) hn x

theorem finrank_invariantFactor (q : FinitePlacesAbove K p) {n : ℕ} (hn : 0 < n)
    (x : denominatorSubgroup n) :
    Module.finrank (FiniteCompletion K q.val) (invariantFactor q hn x) = n * n :=
  finrank_csaOfInvariant _ hn x

theorem finiteBrauerInvariant_invariantFactor (q : FinitePlacesAbove K p)
    {n : ℕ} (hn : 0 < n) (x : denominatorSubgroup n) :
    finiteBrauerInvariant K q.val (Brauer.classOf (invariantFactor q hn x)) =
      (x : RationalModIntegers) :=
  localBrauerInvariant_csaOfInvariant _ hn x

variable [NumberField E]

/-- Use the scalar map of the actual upper completion on any of its CSA factors. -/
scoped instance factorAlgebra (r : Langlands.Global.FinitePlace K)
    [r.asIdeal.LiesOver p.asIdeal] (B : CSA.{v, v} (FiniteCompletion K r)) :
    Algebra (FiniteCompletion E p) B :=
  Algebra.compHom B (algebraMap (FiniteCompletion E p) (FiniteCompletion K r))

scoped instance factorTower (r : Langlands.Global.FinitePlace K)
    [r.asIdeal.LiesOver p.asIdeal] (B : CSA.{v, v} (FiniteCompletion K r)) :
    IsScalarTower (FiniteCompletion E p) (FiniteCompletion K r) B :=
  IsScalarTower.of_algebraMap_eq' rfl

variable [IsTotallyReal E] [IsTotallyComplex K] [IsQuadraticExtension E K]
  (h : SplitPlaceIdentification E K p) (q : FinitePlacesAbove K p)

local notation "F" => FiniteCompletion E p
local notation "K₁" => FiniteCompletion K q.val
local notation "K₂" => FiniteCompletion K (Subtype.val (otherPlace h q))

local instance : Algebra K₁ K₂ :=
  (h.completionEquivBetween q (h.otherPlace q)).toRingEquiv.toRingHom.toAlgebra

/-- The opposite factor over the other actual completion, using its canonical field chart. -/
def otherFactor (B : CSA.{v, v} (FiniteCompletion K q.val)) : CSA.{v, v} K₂ :=
  Brauer.baseChange (K := K₁) K₂ (Brauer.opposite (K := K₁) B)

variable (B : CSA.{v, v} (FiniteCompletion K q.val))

theorem finrank_otherFactor :
    Module.finrank K₂ (h.otherFactor q B) = Module.finrank K₁ B := by
  change Module.finrank K₂ (K₂ ⊗[K₁] Bᵐᵒᵖ) = _
  rw [Module.finrank_baseChange]
  exact (MulOpposite.opLinearEquiv K₁ : B ≃ₗ[K₁] Bᵐᵒᵖ).finrank_eq.symm

theorem finiteBrauerInvariant_otherFactor :
    finiteBrauerInvariant K (h.otherPlace q).val (Brauer.classOf (h.otherFactor q B)) =
      -finiteBrauerInvariant K q.val (Brauer.classOf B) := by
  have hv (a b : K₁) :
      h.completionEquivBetween q (h.otherPlace q) a ≤ᵥ
        h.completionEquivBetween q (h.otherPlace q) b ↔ a ≤ᵥ b := by
    rw [FiniteCompletion.valuativeRel_vle, FiniteCompletion.valuativeRel_vle,
      h.valuation_completionEquivBetween, h.valuation_completionEquivBetween]
  change localBrauerInvariant K₂ (Brauer.scalarExtension K₂
    (Brauer.classOf (Brauer.opposite (K := K₁) B))) = _
  rw [localBrauerInvariant_fieldEquiv K₁ K₂
    (h.completionEquivBetween q (h.otherPlace q)).toRingEquiv
    (h.continuous_completionEquivBetween q (h.otherPlace q)) hv,
    Brauer.classOf_opposite, map_neg]
  rfl

private def oppositeEquivOverFirst :
    Bᵐᵒᵖ ≃ₐ[K₁] (K₂ ⊗[K₁] Bᵐᵒᵖ) :=
  AlgEquiv.ofBijective Algebra.TensorProduct.includeRight
    (Algebra.TensorProduct.includeRight_bijective
      (h.completionEquivBetween q (h.otherPlace q)).bijective)

private theorem oppositeEquivOverFirst_algebraMap (x : K₁) :
    h.oppositeEquivOverFirst q B (algebraMap K₁ Bᵐᵒᵖ x) =
      algebraMap K₂ (h.otherFactor q B) (h.completionEquivBetween q (h.otherPlace q) x) := by
  rw [(h.oppositeEquivOverFirst q B).commutes]
  rfl

/-- Identify the opposite ring with the factor over the other place over the base completion. -/
def oppositeEquivOtherFactor : Bᵐᵒᵖ ≃ₐ[F] h.otherFactor q B :=
  AlgEquiv.ofRingEquiv (f := (h.oppositeEquivOverFirst q B).toRingEquiv) fun s => by
    change h.oppositeEquivOverFirst q B
      (algebraMap K₁ Bᵐᵒᵖ (algebraMap F K₁ s)) =
        algebraMap K₂ (h.otherFactor q B) (algebraMap F K₂ s)
    rw [oppositeEquivOverFirst_algebraMap, AlgEquiv.commutes]

theorem oppositeEquivOtherFactor_algebraMap (x : K₁) :
    h.oppositeEquivOtherFactor q B (algebraMap K₁ Bᵐᵒᵖ x) =
      algebraMap K₂ (h.otherFactor q B) (h.completionEquivBetween q (h.otherPlace q) x) :=
  h.oppositeEquivOverFirst_algebraMap q B x

/-- The local center acts through evaluation at each actual upper completion. -/
def splitPairCenterMap : LocalCenter E K p →ₐ[F] (B × h.otherFactor q B) :=
  ((IsScalarTower.toAlgHom F K₁ B).comp (completedCenterMap E K p q.val)).prod
    ((IsScalarTower.toAlgHom F K₂ (h.otherFactor q B)).comp
      (completedCenterMap E K p (h.otherPlace q).val))

@[simp] theorem splitPairCenterMap_fst (z : LocalCenter E K p) :
    (h.splitPairCenterMap q B z).1 = algebraMap K₁ B (completedCenterMap E K p q.val z) := rfl

@[simp] theorem splitPairCenterMap_snd (z : LocalCenter E K p) :
    (h.splitPairCenterMap q B z).2 =
      algebraMap K₂ (h.otherFactor q B) (completedCenterMap E K p (h.otherPlace q).val z) := rfl

private def splitPairTransport :
    (B × Bᵐᵒᵖ) ≃ₐ[F] (B × h.otherFactor q B) :=
  AlgEquiv.prodCongr (AlgEquiv.refl : B ≃ₐ[F] B) (h.oppositeEquivOtherFactor q B)

/-- The exchange involution on the two factors over the actual completions. -/
def splitPairInvolution : AlgebraInvolution F (B × h.otherFactor q B) :=
  (AlgebraInvolution.exchangeOpposite F B).transport (h.splitPairTransport q B)

theorem splitPairInvolution_center (z : LocalCenter E K p) :
    h.splitPairInvolution q B (h.splitPairCenterMap q B z) =
      h.splitPairCenterMap q B (localConjugation E K p z) := by
  let e := (h.oriented q).equiv
  have hcenter (z' : LocalCenter E K p) : h.splitPairCenterMap q B z' =
      h.splitPairTransport q B
        (algebraMap K₁ B (h.completionEquiv q (e z').1),
          algebraMap K₁ Bᵐᵒᵖ (h.completionEquiv q (e z').2)) := by
    refine Prod.ext ?_ ?_
    · change _ = algebraMap K₁ B (h.completionEquiv q (e z').1)
      simp only [e, splitPairCenterMap_fst, oriented_fst, AlgEquiv.apply_symm_apply]
    · change _ = h.oppositeEquivOtherFactor q B
        (algebraMap K₁ Bᵐᵒᵖ (h.completionEquiv q (e z').2))
      rw [splitPairCenterMap_snd, oppositeEquivOtherFactor_algebraMap]
      simp only [e, oriented_snd, completionEquivBetween, AlgEquiv.trans_apply,
        AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply]
  rw [hcenter z, hcenter (localConjugation E K p z)]
  dsimp only [e]
  rw [(h.oriented q).conjugation_eq, splitPairInvolution, AlgebraInvolution.transport_equiv]
  rfl

end Langlands.Shimura.FiniteUnitary.SplitPlaceIdentification
