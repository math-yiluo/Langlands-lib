import Langlands.Algebra.NonUnitalTensorHomAdjunctionStatements
import Langlands.Algebra.NonUnitalTensorAssociativityStatements
import Langlands.Algebra.CompatibleUnitizationTensor
import Langlands.Algebra.NondegenerateModuleHomScalars
import Langlands.Algebra.NondegenerateTensorScalars
import Langlands.Algebra.NondegenerateTensorFunctor
import Langlands.Algebra.NonUnitalBimoduleHomScalars

/-!
# Coefficient-linear forms of the tensor–Hom and associativity isomorphisms

Renard (9 July 2026), I.2.2, printed pp. 15–16 / PDF pp. 21–22: the Theorem
(I.2.2.1)–(I.2.2.4) over the unitizations and the Corollary (I.2.2.5)–(I.2.2.7) for
nondegenerate modules over idempotented algebras, with their coefficient structures.
The additive isomorphisms are the published canonical ones; the coefficient modules are
named constructions on the published carriers. All conclusions are Prop-valued targets.

The Corollary clauses add the published compatibility predicate on the bimodule `Y`
(`RightSourceCompatible` or `SourceCompatible`). This is a correction of the source, not a
consequence of its hypotheses: under the bare bimodule convention of printed p.6 / PDF p.12
the canonical maps can fail to be linear for the recovered coefficients (counterexample in
the paired Markdown).
-/

set_option autoImplicit false

namespace Langlands.Algebra.TensorHomLinear

open MulOpposite
open NonUnitalModuleTensor (Tensor tmul)

universe uK uA uB uM uN uR uS uX uY uZ

/-! ### Pointwise coefficients on original Hom groups -/

section Pointwise

variable (k : Type uK) {A : Type uA} {M : Type uM} {N : Type uN}
  [CommSemiring k] [NonUnitalRing A] [AddCommGroup M] [AddCommGroup N]
  [NonUnitalModule A M] [NonUnitalModule A N] [Module k N] [SMulCommClass k A N]

/-- `(c • f)(m) = c • f(m)`, for given coefficients on the target commuting with `A`. -/
def pointwiseSMul (c : k) (f : NonUnitalModuleHom A M N) : NonUnitalModuleHom A M N where
  toAddMonoidHom := c • f.toAddMonoidHom
  map_smul' a m := by
    change c • f (a • m) = a • (c • f m)
    rw [f.map_smul, smul_comm c a]

@[simp] theorem pointwiseSMul_apply (c : k) (f : NonUnitalModuleHom A M N) (m : M) :
    pointwiseSMul k c f m = c • f m := rfl

/-- The pointwise coefficient module on the published additive Hom group. -/
abbrev pointwiseModule : Module k (NonUnitalModuleHom A M N) where
  smul := pointwiseSMul k
  one_smul f := by ext m; exact one_smul k (f m)
  mul_smul c d f := by ext m; exact mul_smul c d (f m)
  smul_zero c := by ext m; exact smul_zero c
  smul_add c f g := by ext m; exact smul_add c (f m) (g m)
  add_smul c d f := by ext m; exact add_smul c d (f m)
  zero_smul f := by ext m; exact zero_smul k (f m)

theorem pointwise_smul_apply (c : k) (f : NonUnitalModuleHom A M N) (m : M) :
    letI := pointwiseModule k (A := A) (M := M) (N := N)
    (c • f) m = c • f m := rfl

end Pointwise

section PointwiseSource

variable (k : Type uK) {R : Type uR} {S : Type uS} {Y : Type uY} {Z : Type uZ}
  [CommSemiring k] [NonUnitalRing R] [NonUnitalRing S]
  [AddCommGroup Y] [AddCommGroup Z]

/-- Pointwise coefficients commute with the published right source action. -/
theorem rightSource_smulCommClass
    [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    [Module k Z] [SMulCommClass k Sᵐᵒᵖ Z] (hY : ActionsCommute R S Y) :
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    letI := pointwiseModule k (A := Sᵐᵒᵖ) (M := Y) (N := Z)
    SMulCommClass k Rᵐᵒᵖ (NonUnitalModuleHom Sᵐᵒᵖ Y Z) := by
  let := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  let := pointwiseModule k (A := Sᵐᵒᵖ) (M := Y) (N := Z)
  exact ⟨fun _ _ _ => by ext y; rfl⟩

/-- Pointwise coefficients commute with the published left source action. -/
theorem source_smulCommClass
    [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    [Module k Z] [SMulCommClass k S Z] (hY : ActionsCommute S R Y) :
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hY
    letI := pointwiseModule k (A := S) (M := Y) (N := Z)
    SMulCommClass k R (NonUnitalModuleHom S Y Z) := by
  let := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hY
  let := pointwiseModule k (A := S) (M := Y) (N := Z)
  exact ⟨fun _ _ _ => by ext y; rfl⟩

end PointwiseSource

/-! ### Unitized actions -/

section UnitizedCommute

variable (k : Type uK) (A : Type uA) (B : Type uB) (Y : Type uY)
  [CommRing k]
  [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [NonUnitalRing B] [Module k B] [IsScalarTower k B B] [SMulCommClass k B B]
  [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y] [IsScalarTower k A Y]
  [SMulCommClass k A Y] [NonUnitalModule Bᵐᵒᵖ Y] [IsScalarTower k Bᵐᵒᵖ Y]
  [SMulCommClass k Bᵐᵒᵖ Y]

/-- The unitized left `Ã`- and right `B̃`-actions of an `A`-`B` bimodule commute. -/
theorem unitizedActionsCommute (hY : ActionsCommute A B Y) :
    @ActionsCommute (Unitization k A) (Unitization k B) Y _ _ _
      (CompatibleUnitizationTensor.leftNonUnitalModule k A Y)
      (CompatibleUnitizationTensor.rightNonUnitalModule k B Y) := by
  intro u v y
  change u.fst • (v.fst • y + op v.snd • y) + u.snd • (v.fst • y + op v.snd • y) =
    v.fst • (u.fst • y + u.snd • y) + op v.snd • (u.fst • y + u.snd • y)
  rw [smul_add, smul_add, smul_add, smul_add, smul_comm u.fst v.fst y,
    smul_comm u.fst (op v.snd) y, (smul_comm v.fst u.snd y).symm, hY u.snd v.snd y]
  abel

end UnitizedCommute

section UnitizedTargets

variable (k : Type uK) (A : Type uA) (Z : Type uZ)
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup Z] [Module k Z]

/-- The given coefficients commute with the unitized left action. -/
theorem unitizedLeft_smulCommClass [NonUnitalModule A Z] [IsScalarTower k A Z]
    [SMulCommClass k A Z] :
    letI := CompatibleUnitizationTensor.leftNonUnitalModule k A Z
    SMulCommClass k (Unitization k A) Z :=
  letI := CompatibleUnitizationTensor.leftNonUnitalModule k A Z
  ⟨fun c u z => (CompatibleUnitizationTensor.left_smulCommClass k A Z).smul_comm c u z⟩

/-- The given coefficients commute with the unitized right action. -/
theorem unitizedRight_smulCommClass [NonUnitalModule Aᵐᵒᵖ Z] [IsScalarTower k Aᵐᵒᵖ Z]
    [SMulCommClass k Aᵐᵒᵖ Z] :
    letI := CompatibleUnitizationTensor.rightNonUnitalModule k A Z
    SMulCommClass k (Unitization k A)ᵐᵒᵖ Z :=
  letI := CompatibleUnitizationTensor.rightNonUnitalModule k A Z
  ⟨fun c w z => (CompatibleUnitizationTensor.right_smulCommClass k A Z).smul_comm c w z⟩

end UnitizedTargets

/-! ### Right-factor coefficients on a tensor with a residual left action -/

section ResidualTensor

variable (k : Type uK) {A : Type uA} {B : Type uB} {Y : Type uY} {Z : Type uZ}
  [CommSemiring k] [NonUnitalRing A] [NonUnitalRing B]
  [AddCommGroup Y] [NonUnitalModule A Y] [NonUnitalModule Bᵐᵒᵖ Y]
  [AddCommGroup Z] [NonUnitalModule B Z] [Module k Z] [SMulCommClass k B Z]

/-- On `Y ⊗_B Z`, the coefficients `c • (y ⊗ z) = y ⊗ (c • z)` commute with the published
residual left action `a • (y ⊗ z) = (a • y) ⊗ z`. -/
theorem residual_smulCommClass (hY : ActionsCommute A B Y) :
    letI := NonUnitalBimoduleTensor.leftModule hY Z
    letI := NondegenerateTensorScalars.compatibleModule k B Y Z
    SMulCommClass k A (Tensor B Y Z) := by
  let := NonUnitalBimoduleTensor.leftModule hY Z
  let := NondegenerateTensorScalars.compatibleModule k B Y Z
  refine ⟨fun c a t => ?_⟩
  have h : (NondegenerateTensorScalars.compatibleScalarEnd k B Y Z c).comp
        (NonUnitalBimoduleTensor.leftScalar hY Z a) =
      (NonUnitalBimoduleTensor.leftScalar hY Z a).comp
        (NondegenerateTensorScalars.compatibleScalarEnd k B Y Z c) :=
    NonUnitalModuleTensor.hom_ext B fun _ _ => rfl
  exact DFunLike.congr_fun h t

end ResidualTensor

/-! ### The Theorem: (I.2.2.1)–(I.2.2.2) over the unitizations -/

namespace UnitizedRight

open NonUnitalTensorHomAdjunction.Right

variable (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [CommRing k]
  [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
  [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
  [AddCommGroup X] [Module k X] [NonUnitalModule Rᵐᵒᵖ X]
  [IsScalarTower k Rᵐᵒᵖ X] [SMulCommClass k Rᵐᵒᵖ X]
  [AddCommGroup Y] [Module k Y] [NonUnitalModule R Y] [IsScalarTower k R Y]
  [SMulCommClass k R Y] [NonUnitalModule Sᵐᵒᵖ Y] [IsScalarTower k Sᵐᵒᵖ Y]
  [SMulCommClass k Sᵐᵒᵖ Y]
  [AddCommGroup Z] [Module k Z] [NonUnitalModule Sᵐᵒᵖ Z]
  [IsScalarTower k Sᵐᵒᵖ Z] [SMulCommClass k Sᵐᵒᵖ Z]
  (hY : ActionsCommute R S Y)

attribute [local instance] CompatibleUnitizationTensor.rightNonUnitalModule
  CompatibleUnitizationTensor.leftNonUnitalModule

/-- Pointwise given coefficients on `Hom_S̃(X ⊗_R̃ Y, Z)`. -/
noncomputable abbrev tensorHomModule :
    Module k (TensorHom (Unitization k R) (Unitization k S) X Y Z
      (unitizedActionsCommute k R S Y hY)) :=
  letI := NonUnitalBimoduleTensor.rightModule X (unitizedActionsCommute k R S Y hY)
  letI := unitizedRight_smulCommClass k S Z
  pointwiseModule k

/-- Pointwise given coefficients on `Hom_S̃(Y, Z)`. -/
noncomputable abbrev innerHomModule :
    Module k (NonUnitalModuleHom (Unitization k S)ᵐᵒᵖ Y Z) :=
  letI := unitizedRight_smulCommClass k S Z
  pointwiseModule k

/-- Pointwise coefficients on `Hom_R̃(X, Hom_S̃(Y, Z))`, through those of `Hom_S̃(Y, Z)`. -/
noncomputable abbrev curriedHomModule :
    Module k (CurriedHom (Unitization k R) (Unitization k S) X Y Z
      (unitizedActionsCommute k R S Y hY)) :=
  letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z)
    (unitizedActionsCommute k R S Y hY)
  letI := innerHomModule k S Y Z
  letI := unitizedRight_smulCommClass k S Z
  letI := rightSource_smulCommClass k (Z := Z) (unitizedActionsCommute k R S Y hY)
  pointwiseModule k

/-- (I.2.2.1)–(I.2.2.2): the canonical equivalence `φ ↦ ψ`, `ψ(x)(y) = φ(x ⊗ y)`, is
`k`-linear for the pointwise given coefficients. -/
def ExistsLinearCanonical : Prop :=
  letI := tensorHomModule k R S X Y Z hY
  letI := curriedHomModule k R S X Y Z hY
  ∃ E : TensorHom (Unitization k R) (Unitization k S) X Y Z (unitizedActionsCommute k R S Y hY)
      ≃ₗ[k] CurriedHom (Unitization k R) (Unitization k S) X Y Z
        (unitizedActionsCommute k R S Y hY),
    Canonical (Unitization k R) (Unitization k S) X Y Z (unitizedActionsCommute k R S Y hY)
      E.toAddEquiv

end UnitizedRight

/-! ### The Theorem: (I.2.2.3) over the unitizations -/

namespace UnitizedLeft

open NonUnitalTensorHomAdjunction.Left

variable (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [CommRing k]
  [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
  [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
  [AddCommGroup X] [Module k X] [NonUnitalModule R X]
  [IsScalarTower k R X] [SMulCommClass k R X]
  [AddCommGroup Y] [Module k Y] [NonUnitalModule S Y] [IsScalarTower k S Y]
  [SMulCommClass k S Y] [NonUnitalModule Rᵐᵒᵖ Y] [IsScalarTower k Rᵐᵒᵖ Y]
  [SMulCommClass k Rᵐᵒᵖ Y]
  [AddCommGroup Z] [Module k Z] [NonUnitalModule S Z]
  [IsScalarTower k S Z] [SMulCommClass k S Z]
  (hY : ActionsCommute S R Y)

attribute [local instance] CompatibleUnitizationTensor.rightNonUnitalModule
  CompatibleUnitizationTensor.leftNonUnitalModule

/-- Pointwise given coefficients on `Hom_S̃(Y ⊗_R̃ X, Z)`. -/
noncomputable abbrev tensorHomModule :
    Module k (TensorHom (Unitization k R) (Unitization k S) X Y Z
      (unitizedActionsCommute k S R Y hY)) :=
  letI := NonUnitalBimoduleTensor.leftModule (unitizedActionsCommute k S R Y hY) X
  letI := unitizedLeft_smulCommClass k S Z
  pointwiseModule k

/-- Pointwise given coefficients on `Hom_S̃(Y, Z)`. -/
noncomputable abbrev innerHomModule :
    Module k (NonUnitalModuleHom (Unitization k S) Y Z) :=
  letI := unitizedLeft_smulCommClass k S Z
  pointwiseModule k

/-- Pointwise coefficients on `Hom_R̃(X, Hom_S̃(Y, Z))`, through those of `Hom_S̃(Y, Z)`. -/
noncomputable abbrev curriedHomModule :
    Module k (CurriedHom (Unitization k R) (Unitization k S) X Y Z
      (unitizedActionsCommute k S R Y hY)) :=
  letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z)
    (unitizedActionsCommute k S R Y hY)
  letI := innerHomModule k S Y Z
  letI := unitizedLeft_smulCommClass k S Z
  letI := source_smulCommClass k (Z := Z) (unitizedActionsCommute k S R Y hY)
  pointwiseModule k

/-- (I.2.2.3): the canonical equivalence `φ ↦ ψ`, `ψ(x)(y) = φ(y ⊗ x)`, is `k`-linear for
the pointwise given coefficients. -/
def ExistsLinearCanonical : Prop :=
  letI := tensorHomModule k R S X Y Z hY
  letI := curriedHomModule k R S X Y Z hY
  ∃ E : TensorHom (Unitization k R) (Unitization k S) X Y Z (unitizedActionsCommute k S R Y hY)
      ≃ₗ[k] CurriedHom (Unitization k R) (Unitization k S) X Y Z
        (unitizedActionsCommute k S R Y hY),
    Canonical (Unitization k R) (Unitization k S) X Y Z (unitizedActionsCommute k S R Y hY)
      E.toAddEquiv

end UnitizedLeft

/-! ### The Theorem: (I.2.2.4) over the unitizations -/

namespace UnitizedAssoc

open NonUnitalTensorAssociativity

variable (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [CommRing k]
  [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
  [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
  [AddCommGroup X] [Module k X] [NonUnitalModule Rᵐᵒᵖ X]
  [IsScalarTower k Rᵐᵒᵖ X] [SMulCommClass k Rᵐᵒᵖ X]
  [AddCommGroup Y] [Module k Y] [NonUnitalModule R Y] [IsScalarTower k R Y]
  [SMulCommClass k R Y] [NonUnitalModule Sᵐᵒᵖ Y] [IsScalarTower k Sᵐᵒᵖ Y]
  [SMulCommClass k Sᵐᵒᵖ Y]
  [AddCommGroup Z] [Module k Z] [NonUnitalModule S Z]
  [IsScalarTower k S Z] [SMulCommClass k S Z]
  (hY : ActionsCommute R S Y)

attribute [local instance] CompatibleUnitizationTensor.rightNonUnitalModule
  CompatibleUnitizationTensor.leftNonUnitalModule

/-- Given coefficients on `(X ⊗_R̃ Y) ⊗_S̃ Z`, through those of `Z`. -/
noncomputable abbrev leftTensorModule :
    Module k (LeftTensor (Unitization k R) (Unitization k S) X Y Z
      (unitizedActionsCommute k R S Y hY)) :=
  letI := NonUnitalBimoduleTensor.rightModule X (unitizedActionsCommute k R S Y hY)
  letI := unitizedLeft_smulCommClass k S Z
  NondegenerateTensorScalars.compatibleModule k (Unitization k S)
    (Tensor (Unitization k R) X Y) Z

/-- Given coefficients on `X ⊗_R̃ (Y ⊗_S̃ Z)`, through those of `Y ⊗_S̃ Z`, which are
through those of `Z`. -/
noncomputable abbrev rightTensorModule :
    Module k (RightTensor (Unitization k R) (Unitization k S) X Y Z
      (unitizedActionsCommute k R S Y hY)) :=
  letI := NonUnitalBimoduleTensor.leftModule (unitizedActionsCommute k R S Y hY) Z
  letI := unitizedLeft_smulCommClass k S Z
  letI := NondegenerateTensorScalars.compatibleModule k (Unitization k S) Y Z
  letI := residual_smulCommClass k (Z := Z) (unitizedActionsCommute k R S Y hY)
  NondegenerateTensorScalars.compatibleModule k (Unitization k R) X
    (Tensor (Unitization k S) Y Z)

/-- (I.2.2.4): the canonical associativity equivalence
`(x ⊗ y) ⊗ z ↦ x ⊗ (y ⊗ z)` is `k`-linear for the given coefficients. -/
def ExistsLinearCanonical : Prop :=
  letI := leftTensorModule k R S X Y Z hY
  letI := rightTensorModule k R S X Y Z hY
  ∃ E : LeftTensor (Unitization k R) (Unitization k S) X Y Z
        (unitizedActionsCommute k R S Y hY)
      ≃ₗ[k] RightTensor (Unitization k R) (Unitization k S) X Y Z
        (unitizedActionsCommute k R S Y hY),
    Canonical (Unitization k R) (Unitization k S) X Y Z (unitizedActionsCommute k R S Y hY)
      E.toAddEquiv

end UnitizedAssoc

/-! ### The Corollary: (I.2.2.5) for nondegenerate modules -/

attribute [local instance] NondegenerateTensorScalars.opIsScalarTower
  NondegenerateTensorScalars.opSMulCommClass

namespace NondegenerateRight

open NonUnitalTensorHomAdjunction.Right

variable (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [CommRing k]
  [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
  [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
  [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
  [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y]
  [AddCommGroup Z] [NonUnitalModule Sᵐᵒᵖ Z]
  (hY : ActionsCommute R S Y) (hR : IsIdempotented R) (hS : IsIdempotented S)
  (hSZ : IsNondegenerate Sᵐᵒᵖ Z)

/-- The published pointwise I.2.1 coefficients on `Hom_S(X ⊗_R Y, Z)`, recovered on `Z`. -/
noncomputable abbrev tensorHomModule : Module k (TensorHom R S X Y Z hY) :=
  letI := NonUnitalBimoduleTensor.rightModule X hY
  NondegenerateModuleHomScalars.homModule k hS.op hSZ

/-- The published I.2.1 coefficients on `Hom_R(X, Hom_S(Y, Z)_R)`, recovered on the
nondegenerate right `R`-module `Hom_S(Y, Z)_R`. -/
noncomputable abbrev refinedHomModule : Module k (RefinedHom R S X Y Z hY hR) :=
  letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  NondegenerateModuleHomScalars.homModule k hR.op
    (nondegeneratePart_isNondegenerate (M := NonUnitalModuleHom Sᵐᵒᵖ Y Z) hR.op)

/-- (I.2.2.5): the refined canonical equivalence `Hom_S(X ⊗_R Y, Z) ≃ Hom_R(X, Hom_S(Y, Z)_R)`
is `k`-linear, compatibly with the ambient canonical additive equivalence. -/
def ExistsLinearRefinedCanonical : Prop :=
  letI := tensorHomModule k R S X Y Z hY hS hSZ
  letI := refinedHomModule k R S X Y Z hY hR
  ∃ (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY)
    (End : TensorHom R S X Y Z hY ≃ₗ[k] RefinedHom R S X Y Z hY hR),
    RefinedCanonical R S X Y Z hY hR E End.toAddEquiv

end NondegenerateRight

/-! ### The Corollary: (I.2.2.6) for nondegenerate modules -/

namespace NondegenerateLeft

open NonUnitalTensorHomAdjunction.Left

variable (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [CommRing k]
  [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
  [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
  [AddCommGroup X] [NonUnitalModule R X]
  [AddCommGroup Y] [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y]
  [AddCommGroup Z] [NonUnitalModule S Z]
  (hY : ActionsCommute S R Y) (hR : IsIdempotented R) (hS : IsIdempotented S)
  (hSZ : IsNondegenerate S Z)

/-- The published pointwise I.2.1 coefficients on `Hom_S(Y ⊗_R X, Z)`, recovered on `Z`. -/
noncomputable abbrev tensorHomModule : Module k (TensorHom R S X Y Z hY) :=
  letI := NonUnitalBimoduleTensor.leftModule hY X
  NondegenerateModuleHomScalars.homModule k hS hSZ

/-- The published I.2.1 coefficients on `Hom_R(X, Hom_S(Y, Z)_R)`, recovered on the
nondegenerate left `R`-module `Hom_S(Y, Z)_R`. -/
noncomputable abbrev refinedHomModule : Module k (RefinedHom R S X Y Z hY hR) :=
  letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hY
  NondegenerateModuleHomScalars.homModule k hR
    (nondegeneratePart_isNondegenerate (M := NonUnitalModuleHom S Y Z) hR)

/-- (I.2.2.6): the refined canonical equivalence `Hom_S(Y ⊗_R X, Z) ≃ Hom_R(X, Hom_S(Y, Z)_R)`
is `k`-linear, compatibly with the ambient canonical additive equivalence. -/
def ExistsLinearRefinedCanonical : Prop :=
  letI := tensorHomModule k R S X Y Z hY hS hSZ
  letI := refinedHomModule k R S X Y Z hY hR
  ∃ (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY)
    (End : TensorHom R S X Y Z hY ≃ₗ[k] RefinedHom R S X Y Z hY hR),
    RefinedCanonical R S X Y Z hY hR E End.toAddEquiv

end NondegenerateLeft

/-! ### The Corollary: (I.2.2.7) for nondegenerate modules -/

namespace NondegenerateAssoc

open NonUnitalTensorAssociativity

variable (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [CommRing k]
  [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
  [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
  [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
  [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y]
  [AddCommGroup Z] [NonUnitalModule S Z]
  (hY : ActionsCommute R S Y) (hR : IsIdempotented R) (hS : IsIdempotented S)
  (hRY : IsNondegenerate R Y) (hSZ : IsNondegenerate S Z)

/-- The published I.2.1 tensor coefficients on `(X ⊗_R Y) ⊗_S Z`, recovered on `Z`. -/
noncomputable abbrev leftTensorModule : Module k (LeftTensor R S X Y Z hY) :=
  letI := NonUnitalBimoduleTensor.rightModule X hY
  NondegenerateTensorScalars.module k S (Tensor R X Y) Z hS hSZ

/-- The published I.2.1 tensor coefficients on `X ⊗_R (Y ⊗_S Z)`, recovered on the
nondegenerate left `R`-module `Y ⊗_S Z`. -/
noncomputable abbrev rightTensorModule : Module k (RightTensor R S X Y Z hY) :=
  letI := NonUnitalBimoduleTensor.leftModule hY Z
  NondegenerateTensorScalars.module k R X (Tensor S Y Z) hR
    (NondegenerateTensorFunctor.isNondegenerate hR hY hRY Z)

/-- (I.2.2.7): the canonical associativity equivalence is `k`-linear. -/
def ExistsLinearCanonical : Prop :=
  letI := leftTensorModule k R S X Y Z hY hS hSZ
  letI := rightTensorModule k R S X Y Z hY hR hRY
  ∃ E : LeftTensor R S X Y Z hY ≃ₗ[k] RightTensor R S X Y Z hY,
    Canonical R S X Y Z hY E.toAddEquiv

end NondegenerateAssoc

end Langlands.Algebra.TensorHomLinear

namespace Langlands.Algebra

open MulOpposite TensorHomLinear

universe uK uR uS uX uY uZ

/-- Closed target for Renard's Theorem I.2.2 with coefficients: (I.2.2.1)–(I.2.2.4) over the
unitizations, for given coefficient modules compatible with the original actions. -/
def UnitizedTensorHomLinearTheorem : Prop :=
  (∀ (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [CommRing k]
    [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
    [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
    [AddCommGroup X] [Module k X] [NonUnitalModule Rᵐᵒᵖ X]
    [IsScalarTower k Rᵐᵒᵖ X] [SMulCommClass k Rᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule R Y] [IsScalarTower k R Y]
    [SMulCommClass k R Y] [NonUnitalModule Sᵐᵒᵖ Y] [IsScalarTower k Sᵐᵒᵖ Y]
    [SMulCommClass k Sᵐᵒᵖ Y]
    [AddCommGroup Z] [Module k Z] [NonUnitalModule Sᵐᵒᵖ Z]
    [IsScalarTower k Sᵐᵒᵖ Z] [SMulCommClass k Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y),
    UnitizedRight.ExistsLinearCanonical k R S X Y Z hY) ∧
  (∀ (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [CommRing k]
    [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
    [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
    [AddCommGroup X] [Module k X] [NonUnitalModule R X]
    [IsScalarTower k R X] [SMulCommClass k R X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule S Y] [IsScalarTower k S Y]
    [SMulCommClass k S Y] [NonUnitalModule Rᵐᵒᵖ Y] [IsScalarTower k Rᵐᵒᵖ Y]
    [SMulCommClass k Rᵐᵒᵖ Y]
    [AddCommGroup Z] [Module k Z] [NonUnitalModule S Z]
    [IsScalarTower k S Z] [SMulCommClass k S Z]
    (hY : ActionsCommute S R Y),
    UnitizedLeft.ExistsLinearCanonical k R S X Y Z hY) ∧
  (∀ (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [CommRing k]
    [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
    [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
    [AddCommGroup X] [Module k X] [NonUnitalModule Rᵐᵒᵖ X]
    [IsScalarTower k Rᵐᵒᵖ X] [SMulCommClass k Rᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule R Y] [IsScalarTower k R Y]
    [SMulCommClass k R Y] [NonUnitalModule Sᵐᵒᵖ Y] [IsScalarTower k Sᵐᵒᵖ Y]
    [SMulCommClass k Sᵐᵒᵖ Y]
    [AddCommGroup Z] [Module k Z] [NonUnitalModule S Z]
    [IsScalarTower k S Z] [SMulCommClass k S Z]
    (hY : ActionsCommute R S Y),
    UnitizedAssoc.ExistsLinearCanonical k R S X Y Z hY)

/-- Closed target for Renard's Corollary I.2.2 with coefficients: (I.2.2.5)–(I.2.2.7) for
nondegenerate modules over idempotented algebras, with the published recovered I.2.1
coefficients. Each clause adds the published compatibility predicate: the coefficients that
`S` recovers on the bimodule `Y` are compatible with the `R`-action. This is a correction of
the printed hypotheses, which do not imply it; see the paired Markdown. -/
def NondegenerateTensorHomLinearTheorem : Prop :=
  (∀ (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [CommRing k]
    [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
    [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
    [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y]
    [AddCommGroup Z] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y) (hR : IsIdempotented R) (hS : IsIdempotented S)
    (_hX : IsNondegenerate Rᵐᵒᵖ X) (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (_hc : NonUnitalBimoduleHomScalars.RightSourceCompatible k hS hSY (R := R))
    (hSZ : IsNondegenerate Sᵐᵒᵖ Z),
    NondegenerateRight.ExistsLinearRefinedCanonical k R S X Y Z hY hR hS hSZ) ∧
  (∀ (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [CommRing k]
    [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
    [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
    [AddCommGroup X] [NonUnitalModule R X]
    [AddCommGroup Y] [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y]
    [AddCommGroup Z] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y) (hR : IsIdempotented R) (hS : IsIdempotented S)
    (_hX : IsNondegenerate R X) (hSY : IsNondegenerate S Y)
    (_hc : NonUnitalBimoduleHomScalars.SourceCompatible k hS hSY (S := R))
    (hSZ : IsNondegenerate S Z),
    NondegenerateLeft.ExistsLinearRefinedCanonical k R S X Y Z hY hR hS hSZ) ∧
  (∀ (k : Type uK) (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [CommRing k]
    [NonUnitalRing R] [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
    [NonUnitalRing S] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
    [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y]
    [AddCommGroup Z] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y) (hR : IsIdempotented R) (hS : IsIdempotented S)
    (hRY : IsNondegenerate R Y) (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (_hc : NonUnitalBimoduleHomScalars.RightSourceCompatible k hS hSY (R := R))
    (hSZ : IsNondegenerate S Z),
    NondegenerateAssoc.ExistsLinearCanonical k R S X Y Z hY hR hS hRY hSZ)

/-- Closed target for Renard I.2.2 with coefficients: the Theorem over the unitizations and
the Corollary for nondegenerate modules. -/
def TensorHomLinearTheorem : Prop :=
  UnitizedTensorHomLinearTheorem.{uK, uR, uS, uX, uY, uZ} ∧
    NondegenerateTensorHomLinearTheorem.{uK, uR, uS, uX, uY, uZ}

end Langlands.Algebra
