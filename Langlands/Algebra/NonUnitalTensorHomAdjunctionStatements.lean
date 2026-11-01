import Langlands.Algebra.NonUnitalBimoduleTensor
import Langlands.Algebra.NonUnitalBimoduleHomNaturality

/-!
# Original-action additive tensor-Hom equivalence targets

Internal generalizations of the additive cores of Renard I.2.2.1–.3 and .5–.6.
Helpers implement evaluation pairings, balancing, published-map packaging and
landing in the actual nondegenerate part. The equivalence and naturality
conclusions remain Prop-valued targets.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalTensorHomAdjunction

open MulOpposite
open NonUnitalModuleTensor (Tensor tmul lift IsBalanced)
open NonUnitalBimoduleTensor (rightModule leftModule rightMap leftMap)
open NonUnitalBimoduleHomActions
  (rightSourceAction sourceAction rightSourceMap sourceMap mapAddHom postcomposeAddHom)

universe uR uS uX uY uZ uX' uY' uZ'

/-- Both inverse identities on whole additive Hom groups. -/
def InverseIdentities {A : Type uX} {B : Type uY} [AddCommGroup A] [AddCommGroup B]
    (E : A ≃+ B) : Prop :=
  E.symm.toAddMonoidHom.comp E.toAddMonoidHom = AddMonoidHom.id A ∧
  E.toAddMonoidHom.comp E.symm.toAddMonoidHom = AddMonoidHom.id B

namespace Right

section Triple

variable (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [NonUnitalRing R] [NonUnitalRing S]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
  [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
  (hY : ActionsCommute R S Y)

/-- The original tensor Hom with exactly the published residual tensor action. -/
abbrev TensorHom : Type (max uX uY uZ) :=
  letI := rightModule X hY
  NonUnitalModuleHom Sᵐᵒᵖ (Tensor R X Y) Z

instance tensorHomGroup : AddCommGroup (TensorHom R S X Y Z hY) :=
  letI := rightModule X hY
  NonUnitalModuleHom.instAddCommGroup

/-- Original intertwiners into the actual Hom with its published source action. -/
abbrev CurriedHom : Type (max uX uY uZ) :=
  letI := rightSourceAction (Z := Z) hY
  NonUnitalModuleHom Rᵐᵒᵖ X (NonUnitalModuleHom Sᵐᵒᵖ Y Z)

instance curriedHomGroup : AddCommGroup (CurriedHom R S X Y Z hY) :=
  letI := rightSourceAction (Z := Z) hY
  NonUnitalModuleHom.instAddCommGroup

/-- The actual evaluation pairing of an original intertwiner. -/
def evaluationPairing (ψ : CurriedHom R S X Y Z hY) : X →+ Y →+ Z := by
  let := rightSourceAction (Z := Z) hY
  exact {
    toFun x := (ψ x).toAddMonoidHom
    map_zero' := by
      ext y
      change (ψ 0) y = 0
      rw [ψ.toAddMonoidHom.map_zero]
      rfl
    map_add' x x' := by
      ext y
      change (ψ (x + x')) y = (ψ x) y + (ψ x') y
      rw [ψ.toAddMonoidHom.map_add]
      rfl
  }

/-- Balancing follows from the supplied original linearity and source action. -/
theorem evaluationPairing_balanced (ψ : CurriedHom R S X Y Z hY) :
    IsBalanced R (evaluationPairing R S X Y Z hY ψ) := by
  let := rightSourceAction (Z := Z) hY
  intro r x y
  change (ψ (op r • x)) y = (ψ x) (r • y)
  rw [ψ.map_smul]
  rfl

/-- Canonical evaluation, whole published inverse lift, pure inverse and whole inverses. -/
def Canonical (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY) : Prop :=
  letI := rightModule X hY
  (∀ (φ : TensorHom R S X Y Z hY) (x : X) (y : Y),
    (E φ x) y = φ (tmul R X Y x y)) ∧
  (∀ ψ : CurriedHom R S X Y Z hY,
    (E.symm ψ).toAddMonoidHom =
      lift R (evaluationPairing R S X Y Z hY ψ)
        (evaluationPairing_balanced R S X Y Z hY ψ)) ∧
  (∀ (ψ : CurriedHom R S X Y Z hY) (x : X) (y : Y),
    E.symm ψ (tmul R X Y x y) = (ψ x) y) ∧
  InverseIdentities E

/-- Existence is a conclusion; no curry map or equivalence is a premise. -/
def ExistsCanonical : Prop :=
  ∃ E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY,
    Canonical R S X Y Z hY E

/-- Exactly the original nondegenerate part of the residual-action Hom. -/
abbrev HomPart (hR : IsIdempotented R) :=
  letI := rightSourceAction (Z := Z) hY
  nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)

/-- The original Hom into that actual part, with its inherited group and action. -/
abbrev RefinedHom (hR : IsIdempotented R) : Type (max uX uY uZ) :=
  NonUnitalModuleHom Rᵐᵒᵖ X (HomPart R S Y Z hY hR)

instance refinedHomGroup (hR : IsIdempotented R) :
    AddCommGroup (RefinedHom R S X Y Z hY hR) :=
  NonUnitalModuleHom.instAddCommGroup

/-- `J` is postcomposition with the original submodule inclusion. -/
def inclusionMap (hR : IsIdempotented R) :
    RefinedHom R S X Y Z hY hR →+ CurriedHom R S X Y Z hY :=
  letI := rightSourceAction (Z := Z) hY
  postcomposeAddHom (HomPart R S Y Z hY hR).subtype

/-- Every original map from nondegenerate `X` lands in this actual part. -/
theorem map_mem_part (hR : IsIdempotented R) (hX : IsNondegenerate Rᵐᵒᵖ X)
    (ψ : CurriedHom R S X Y Z hY) (x : X) :
    ψ x ∈ HomPart R S Y Z hY hR := by
  let := rightSourceAction (Z := Z) hY
  obtain ⟨e, he⟩ := hX x
  exact ⟨e, (ψ.map_smul (e : Rᵐᵒᵖ) x).symm.trans (congrArg ψ he)⟩

/-- The refined equivalence and its complete comparisons to the ambient one. -/
def RefinedCanonical (hR : IsIdempotented R)
    (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY)
    (End : TensorHom R S X Y Z hY ≃+ RefinedHom R S X Y Z hY hR) : Prop :=
  Canonical R S X Y Z hY E ∧
  (∀ (φ : TensorHom R S X Y Z hY) (x : X) (y : Y),
    ((End φ x).val) y = φ (tmul R X Y x y)) ∧
  (inclusionMap R S X Y Z hY hR).comp End.toAddMonoidHom = E.toAddMonoidHom ∧
  End.symm.toAddMonoidHom = E.symm.toAddMonoidHom.comp (inclusionMap R S X Y Z hY hR)

/-- Both compatible equivalences are conclusions of the refined existence target. -/
def ExistsRefinedCanonical (hR : IsIdempotented R) : Prop :=
  ∃ (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY)
    (End : TensorHom R S X Y Z hY ≃+ RefinedHom R S X Y Z hY hR),
    RefinedCanonical R S X Y Z hY hR E End

section Maps

variable {X' : Type uX'} {Y' : Type uY'} {Z' : Type uZ'}
  [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
  [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
  [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule Sᵐᵒᵖ Z']
  (hY' : ActionsCommute R S Y')
  (f : NonUnitalModuleHom Rᵐᵒᵖ X' X)
  (g : NonUnitalBimoduleHom R S Y' Y)
  (k : NonUnitalModuleHom Sᵐᵒᵖ Z Z')

/-- `P(φ) = k ∘ φ ∘ tensorMap(f,g)`, using the published one-sided tensor map. -/
def tensorHomMap : TensorHom R S X Y Z hY →+ TensorHom R S X' Y' Z' hY' :=
  letI := rightModule X hY
  letI := rightModule X' hY'
  mapAddHom (rightMap hY' hY f g) k

/-- `Q` uses the published one-sided original-linear Hom natural map. -/
def curriedHomMap : CurriedHom R S X Y Z hY →+ CurriedHom R S X' Y' Z' hY' :=
  letI := rightSourceAction (Z := Z) hY
  letI := rightSourceAction (Z := Z') hY'
  mapAddHom f (rightSourceMap hY hY' g k)

/-- Both directions of naturality, as equalities of complete additive maps. -/
def Naturality
    (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY)
    (E' : TensorHom R S X' Y' Z' hY' ≃+ CurriedHom R S X' Y' Z' hY') : Prop :=
  E'.toAddMonoidHom.comp (tensorHomMap R S X Y Z hY hY' f g k) =
    (curriedHomMap R S X Y Z hY hY' f g k).comp E.toAddMonoidHom ∧
  E'.symm.toAddMonoidHom.comp (curriedHomMap R S X Y Z hY hY' f g k) =
    (tensorHomMap R S X Y Z hY hY' f g k).comp E.symm.toAddMonoidHom

/-- Refined `Q` uses exactly the published restriction of the original Hom map. -/
def refinedHomMap (hR : IsIdempotented R) :
    RefinedHom R S X Y Z hY hR →+ RefinedHom R S X' Y' Z' hY' hR :=
  letI := rightSourceAction (Z := Z) hY
  letI := rightSourceAction (Z := Z') hY'
  mapAddHom f ((rightSourceMap hY hY' g k).restrictNondegeneratePart hR.op)

/-- Naturality through the actual nondegenerate parts, in both directions. -/
def RefinedNaturality (hR : IsIdempotented R)
    (End : TensorHom R S X Y Z hY ≃+ RefinedHom R S X Y Z hY hR)
    (End' : TensorHom R S X' Y' Z' hY' ≃+ RefinedHom R S X' Y' Z' hY' hR) : Prop :=
  End'.toAddMonoidHom.comp (tensorHomMap R S X Y Z hY hY' f g k) =
    (refinedHomMap R S X Y Z hY hY' f g k hR).comp End.toAddMonoidHom ∧
  End'.symm.toAddMonoidHom.comp (refinedHomMap R S X Y Z hY hY' f g k hR) =
    (tensorHomMap R S X Y Z hY hY' f g k).comp End.symm.toAddMonoidHom

end Maps
end Triple

/-- Closed unconditional existence target for every triple of original actions. -/
def ExistenceTheorem : Prop :=
  ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y),
    ExistsCanonical R S X Y Z hY

/-- Closed whole-map naturality target at six independent carrier universes. -/
def NaturalityTheorem : Prop :=
  ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    (X' : Type uX') (Y' : Type uY') (Z' : Type uZ')
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
    [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule Sᵐᵒᵖ Z']
    (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y')
    (f : NonUnitalModuleHom Rᵐᵒᵖ X' X) (g : NonUnitalBimoduleHom R S Y' Y)
    (k : NonUnitalModuleHom Sᵐᵒᵖ Z Z')
    (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY)
    (E' : TensorHom R S X' Y' Z' hY' ≃+ CurriedHom R S X' Y' Z' hY'),
    Canonical R S X Y Z hY E → Canonical R S X' Y' Z' hY' E' →
      Naturality R S X Y Z hY hY' f g k E E'

/-- Closed refined existence: only `R` is idempotented and only `X` nondegenerate. -/
def RefinedExistenceTheorem : Prop :=
  ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y) (hR : IsIdempotented R),
    IsNondegenerate Rᵐᵒᵖ X → ExistsRefinedCanonical R S X Y Z hY hR

/-- Closed naturality target for compatible refined witnesses at nondegenerate sources. -/
def RefinedNaturalityTheorem : Prop :=
  ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    (X' : Type uX') (Y' : Type uY') (Z' : Type uZ')
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
    [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule Sᵐᵒᵖ Z']
    (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y')
    (hR : IsIdempotented R)
    (f : NonUnitalModuleHom Rᵐᵒᵖ X' X) (g : NonUnitalBimoduleHom R S Y' Y)
    (k : NonUnitalModuleHom Sᵐᵒᵖ Z Z')
    (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY)
    (E' : TensorHom R S X' Y' Z' hY' ≃+ CurriedHom R S X' Y' Z' hY')
    (End : TensorHom R S X Y Z hY ≃+ RefinedHom R S X Y Z hY hR)
    (End' : TensorHom R S X' Y' Z' hY' ≃+ RefinedHom R S X' Y' Z' hY' hR),
    IsNondegenerate Rᵐᵒᵖ X → IsNondegenerate Rᵐᵒᵖ X' →
      RefinedCanonical R S X Y Z hY hR E End →
      RefinedCanonical R S X' Y' Z' hY' hR E' End' →
      RefinedNaturality R S X Y Z hY hY' f g k hR End End'

end Right

namespace Left

section Triple

variable (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [NonUnitalRing R] [NonUnitalRing S]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule R X] [NonUnitalModule S Y]
  [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
  (hY : ActionsCommute S R Y)

/-- The original tensor Hom with exactly the published residual tensor action. -/
abbrev TensorHom : Type (max uX uY uZ) :=
  letI := leftModule hY X
  NonUnitalModuleHom S (Tensor R Y X) Z

instance tensorHomGroup : AddCommGroup (TensorHom R S X Y Z hY) :=
  letI := leftModule hY X
  NonUnitalModuleHom.instAddCommGroup

/-- Original intertwiners into the actual Hom with its published source action. -/
abbrev CurriedHom : Type (max uX uY uZ) :=
  letI := sourceAction (Z := Z) hY
  NonUnitalModuleHom R X (NonUnitalModuleHom S Y Z)

instance curriedHomGroup : AddCommGroup (CurriedHom R S X Y Z hY) :=
  letI := sourceAction (Z := Z) hY
  NonUnitalModuleHom.instAddCommGroup

/-- The actual evaluation pairing of an original intertwiner. -/
def evaluationPairing (ψ : CurriedHom R S X Y Z hY) : Y →+ X →+ Z := by
  let := sourceAction (Z := Z) hY
  exact {
    toFun y :=
      { toFun x := (ψ x) y
        map_zero' := by
          change (ψ 0) y = 0
          rw [ψ.toAddMonoidHom.map_zero]
          rfl
        map_add' x x' := by
          change (ψ (x + x')) y = (ψ x) y + (ψ x') y
          rw [ψ.toAddMonoidHom.map_add]
          rfl }
    map_zero' := by ext x; exact (ψ x).map_zero
    map_add' y y' := by ext x; exact (ψ x).map_add y y' 
  }

/-- Balancing follows from the supplied original linearity and source action. -/
theorem evaluationPairing_balanced (ψ : CurriedHom R S X Y Z hY) :
    IsBalanced R (evaluationPairing R S X Y Z hY ψ) := by
  let := sourceAction (Z := Z) hY
  intro r y x
  change (ψ x) (op r • y) = (ψ (r • x)) y
  rw [ψ.map_smul]
  rfl

/-- Canonical evaluation, whole published inverse lift, pure inverse and whole inverses. -/
def Canonical (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY) : Prop :=
  letI := leftModule hY X
  (∀ (φ : TensorHom R S X Y Z hY) (x : X) (y : Y),
    (E φ x) y = φ (tmul R Y X y x)) ∧
  (∀ ψ : CurriedHom R S X Y Z hY,
    (E.symm ψ).toAddMonoidHom =
      lift R (evaluationPairing R S X Y Z hY ψ)
        (evaluationPairing_balanced R S X Y Z hY ψ)) ∧
  (∀ (ψ : CurriedHom R S X Y Z hY) (x : X) (y : Y),
    E.symm ψ (tmul R Y X y x) = (ψ x) y) ∧
  InverseIdentities E

/-- Existence is a conclusion; no curry map or equivalence is a premise. -/
def ExistsCanonical : Prop :=
  ∃ E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY,
    Canonical R S X Y Z hY E

/-- Exactly the original nondegenerate part of the residual-action Hom. -/
abbrev HomPart (hR : IsIdempotented R) :=
  letI := sourceAction (Z := Z) hY
  nondegeneratePart hR (NonUnitalModuleHom S Y Z)

/-- The original Hom into that actual part, with its inherited group and action. -/
abbrev RefinedHom (hR : IsIdempotented R) : Type (max uX uY uZ) :=
  NonUnitalModuleHom R X (HomPart R S Y Z hY hR)

instance refinedHomGroup (hR : IsIdempotented R) :
    AddCommGroup (RefinedHom R S X Y Z hY hR) :=
  NonUnitalModuleHom.instAddCommGroup

/-- `J` is postcomposition with the original submodule inclusion. -/
def inclusionMap (hR : IsIdempotented R) :
    RefinedHom R S X Y Z hY hR →+ CurriedHom R S X Y Z hY :=
  letI := sourceAction (Z := Z) hY
  postcomposeAddHom (HomPart R S Y Z hY hR).subtype

/-- Every original map from nondegenerate `X` lands in this actual part. -/
theorem map_mem_part (hR : IsIdempotented R) (hX : IsNondegenerate R X)
    (ψ : CurriedHom R S X Y Z hY) (x : X) :
    ψ x ∈ HomPart R S Y Z hY hR := by
  let := sourceAction (Z := Z) hY
  obtain ⟨e, he⟩ := hX x
  exact ⟨e, (ψ.map_smul (e : R) x).symm.trans (congrArg ψ he)⟩

/-- The refined equivalence and its complete comparisons to the ambient one. -/
def RefinedCanonical (hR : IsIdempotented R)
    (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY)
    (End : TensorHom R S X Y Z hY ≃+ RefinedHom R S X Y Z hY hR) : Prop :=
  Canonical R S X Y Z hY E ∧
  (∀ (φ : TensorHom R S X Y Z hY) (x : X) (y : Y),
    ((End φ x).val) y = φ (tmul R Y X y x)) ∧
  (inclusionMap R S X Y Z hY hR).comp End.toAddMonoidHom = E.toAddMonoidHom ∧
  End.symm.toAddMonoidHom = E.symm.toAddMonoidHom.comp (inclusionMap R S X Y Z hY hR)

/-- Both compatible equivalences are conclusions of the refined existence target. -/
def ExistsRefinedCanonical (hR : IsIdempotented R) : Prop :=
  ∃ (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY)
    (End : TensorHom R S X Y Z hY ≃+ RefinedHom R S X Y Z hY hR),
    RefinedCanonical R S X Y Z hY hR E End

section Maps

variable {X' : Type uX'} {Y' : Type uY'} {Z' : Type uZ'}
  [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
  [NonUnitalModule R X'] [NonUnitalModule S Y']
  [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z']
  (hY' : ActionsCommute S R Y')
  (f : NonUnitalModuleHom R X' X)
  (g : NonUnitalBimoduleHom S R Y' Y)
  (k : NonUnitalModuleHom S Z Z')

/-- `P(φ) = k ∘ φ ∘ tensorMap(f,g)`, using the published one-sided tensor map. -/
def tensorHomMap : TensorHom R S X Y Z hY →+ TensorHom R S X' Y' Z' hY' :=
  letI := leftModule hY X
  letI := leftModule hY' X'
  mapAddHom (leftMap hY' hY g f) k

/-- `Q` uses the published one-sided original-linear Hom natural map. -/
def curriedHomMap : CurriedHom R S X Y Z hY →+ CurriedHom R S X' Y' Z' hY' :=
  letI := sourceAction (Z := Z) hY
  letI := sourceAction (Z := Z') hY'
  mapAddHom f (sourceMap hY hY' g k)

/-- Both directions of naturality, as equalities of complete additive maps. -/
def Naturality
    (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY)
    (E' : TensorHom R S X' Y' Z' hY' ≃+ CurriedHom R S X' Y' Z' hY') : Prop :=
  E'.toAddMonoidHom.comp (tensorHomMap R S X Y Z hY hY' f g k) =
    (curriedHomMap R S X Y Z hY hY' f g k).comp E.toAddMonoidHom ∧
  E'.symm.toAddMonoidHom.comp (curriedHomMap R S X Y Z hY hY' f g k) =
    (tensorHomMap R S X Y Z hY hY' f g k).comp E.symm.toAddMonoidHom

/-- Refined `Q` uses exactly the published restriction of the original Hom map. -/
def refinedHomMap (hR : IsIdempotented R) :
    RefinedHom R S X Y Z hY hR →+ RefinedHom R S X' Y' Z' hY' hR :=
  letI := sourceAction (Z := Z) hY
  letI := sourceAction (Z := Z') hY'
  mapAddHom f ((sourceMap hY hY' g k).restrictNondegeneratePart hR)

/-- Naturality through the actual nondegenerate parts, in both directions. -/
def RefinedNaturality (hR : IsIdempotented R)
    (End : TensorHom R S X Y Z hY ≃+ RefinedHom R S X Y Z hY hR)
    (End' : TensorHom R S X' Y' Z' hY' ≃+ RefinedHom R S X' Y' Z' hY' hR) : Prop :=
  End'.toAddMonoidHom.comp (tensorHomMap R S X Y Z hY hY' f g k) =
    (refinedHomMap R S X Y Z hY hY' f g k hR).comp End.toAddMonoidHom ∧
  End'.symm.toAddMonoidHom.comp (refinedHomMap R S X Y Z hY hY' f g k hR) =
    (tensorHomMap R S X Y Z hY hY' f g k).comp End.symm.toAddMonoidHom

end Maps
end Triple

/-- Closed unconditional existence target for every triple of original actions. -/
def ExistenceTheorem : Prop :=
  ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y),
    ExistsCanonical R S X Y Z hY

/-- Closed whole-map naturality target at six independent carrier universes. -/
def NaturalityTheorem : Prop :=
  ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    (X' : Type uX') (Y' : Type uY') (Z' : Type uZ')
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    [NonUnitalModule R X'] [NonUnitalModule S Y']
    [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z']
    (hY : ActionsCommute S R Y) (hY' : ActionsCommute S R Y')
    (f : NonUnitalModuleHom R X' X) (g : NonUnitalBimoduleHom S R Y' Y)
    (k : NonUnitalModuleHom S Z Z')
    (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY)
    (E' : TensorHom R S X' Y' Z' hY' ≃+ CurriedHom R S X' Y' Z' hY'),
    Canonical R S X Y Z hY E → Canonical R S X' Y' Z' hY' E' →
      Naturality R S X Y Z hY hY' f g k E E'

/-- Closed refined existence: only `R` is idempotented and only `X` nondegenerate. -/
def RefinedExistenceTheorem : Prop :=
  ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y) (hR : IsIdempotented R),
    IsNondegenerate R X → ExistsRefinedCanonical R S X Y Z hY hR

/-- Closed naturality target for compatible refined witnesses at nondegenerate sources. -/
def RefinedNaturalityTheorem : Prop :=
  ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    (X' : Type uX') (Y' : Type uY') (Z' : Type uZ')
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    [NonUnitalModule R X'] [NonUnitalModule S Y']
    [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z']
    (hY : ActionsCommute S R Y) (hY' : ActionsCommute S R Y')
    (hR : IsIdempotented R)
    (f : NonUnitalModuleHom R X' X) (g : NonUnitalBimoduleHom S R Y' Y)
    (k : NonUnitalModuleHom S Z Z')
    (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY)
    (E' : TensorHom R S X' Y' Z' hY' ≃+ CurriedHom R S X' Y' Z' hY')
    (End : TensorHom R S X Y Z hY ≃+ RefinedHom R S X Y Z hY hR)
    (End' : TensorHom R S X' Y' Z' hY' ≃+ RefinedHom R S X' Y' Z' hY' hR),
    IsNondegenerate R X → IsNondegenerate R X' →
      RefinedCanonical R S X Y Z hY hR E End →
      RefinedCanonical R S X' Y' Z' hY' hR E' End' →
      RefinedNaturality R S X Y Z hY hY' f g k hR End End'

end Left

end Langlands.Algebra.NonUnitalTensorHomAdjunction

namespace Langlands.Algebra

open NonUnitalTensorHomAdjunction

universe uR uS uX uY uZ uX' uY' uZ'

/-- Closed original-action additive cores, naturality and actual-part refinements.
This is a statement target, not a proof of the tensor-Hom equivalences. -/
def NonUnitalTensorHomAdjunctionTheorem : Prop :=
  Right.ExistenceTheorem.{uR, uS, uX, uY, uZ} ∧
  Left.ExistenceTheorem.{uR, uS, uX, uY, uZ} ∧
  Right.NaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} ∧
  Left.NaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} ∧
  Right.RefinedExistenceTheorem.{uR, uS, uX, uY, uZ} ∧
  Left.RefinedExistenceTheorem.{uR, uS, uX, uY, uZ} ∧
  Right.RefinedNaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} ∧
  Left.RefinedNaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'}

end Langlands.Algebra
