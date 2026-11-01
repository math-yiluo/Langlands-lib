import Langlands.Algebra.RenardHomFunctors

set_option autoImplicit false
-- Private interface abbreviations intentionally have maximum universe sorts.
set_option linter.checkUnivs false

open CategoryTheory MulOpposite

namespace Langlands.Algebra.NondegenerateHomFunctorChecks

open NonUnitalBimoduleHomActions NondegenerateHomFunctor RenardHomFunctors

universe uS uR uY uM uN uP

/-! Complete unapplied types, tested generically and at complementary unequal universes. -/

private abbrev AmbientInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  (hY : @ActionsCommute S R Y s r y sy ry) →
  NonUnitalModuleCat.{uS, uM} S ⥤ NonUnitalModuleCat.{uR, max uY uM} R

example : AmbientInterface.{uS, uR, uY, uM} := @ambientFunctor.{uS, uR, uY, uM}
example : AmbientInterface.{0, 1, 0, 1} := @ambientFunctor.{0, 1, 0, 1}
example : AmbientInterface.{1, 0, 1, 0} := @ambientFunctor.{1, 0, 1, 0}

private abbrev ActionInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} → {M : Type uM} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] →
  [y : AddCommGroup Y] → [_m : AddCommGroup M] →
  [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  [_sm : NonUnitalModule S M] →
  (hY : @ActionsCommute S R Y s r y sy ry) →
  NonUnitalModule R (@NonUnitalModuleHom S Y M s y _m sy _sm)

example : ActionInterface.{uS, uR, uY, uM} := @sourceAction.{uS, uR, uY, uM}
example : ActionInterface.{0, 1, 0, 1} := @sourceAction.{0, 1, 0, 1}
example : ActionInterface.{1, 0, 1, 0} := @sourceAction.{1, 0, 1, 0}

private abbrev MapInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  (hY : @ActionsCommute S R Y s r y sy ry) →
  {M : Type uM} → {N : Type uN} →
  [_m : AddCommGroup M] → [_n : AddCommGroup N] →
  [_sm : NonUnitalModule S M] → [_sn : NonUnitalModule S N] →
  NonUnitalModuleHom S M N →
  NonUnitalModuleHom R (sourceHom hY M) (sourceHom hY N)

example : MapInterface.{uS, uR, uY, uM, uN} := @ambientMap.{uS, uR, uY, uM, uN}
example : MapInterface.{0, 1, 0, 1, 0} := @ambientMap.{0, 1, 0, 1, 0}
example : MapInterface.{1, 0, 1, 0, 1} := @ambientMap.{1, 0, 1, 0, 1}

private abbrev CompositeInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  (hY : @ActionsCommute S R Y s r y sy ry) →
  IsIdempotented R →
  NonUnitalModuleCat.{uS, uM} S ⥤ NondegenerateModuleCat.{uR, max uY uM} R

example : CompositeInterface.{uS, uR, uY, uM} := @nondegenerateFunctor.{uS, uR, uY, uM}
example : CompositeInterface.{0, 1, 0, 1} := @nondegenerateFunctor.{0, 1, 0, 1}
example : CompositeInterface.{1, 0, 1, 0} := @nondegenerateFunctor.{1, 0, 1, 0}

private abbrev RestrictionInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  (hY : @ActionsCommute S R Y s r y sy ry) →
  IsIdempotented R →
  NondegenerateModuleCat.{uS, uM} S ⥤ NondegenerateModuleCat.{uR, max uY uM} R

example : RestrictionInterface.{uS, uR, uY, uM} := @restrictedFunctor.{uS, uR, uY, uM}
example : RestrictionInterface.{0, 1, 0, 1} := @restrictedFunctor.{0, 1, 0, 1}
example : RestrictionInterface.{1, 0, 1, 0} := @restrictedFunctor.{1, 0, 1, 0}

private abbrev InclusionInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  (hY : @ActionsCommute S R Y s r y sy ry) →
  (hR : IsIdempotented R) →
  nondegenerateFunctor.{uS, uR, uY, uM} hY hR ⋙ nondegenerateInclusion R ⟶
    ambientFunctor hY

example : InclusionInterface.{uS, uR, uY, uM} := @inclusion.{uS, uR, uY, uM}
example : InclusionInterface.{0, 1, 0, 1} := @inclusion.{0, 1, 0, 1}
example : InclusionInterface.{1, 0, 1, 0} := @inclusion.{1, 0, 1, 0}

private abbrev RestrictedInclusionInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  (hY : @ActionsCommute S R Y s r y sy ry) →
  (hR : IsIdempotented R) →
  restrictedFunctor.{uS, uR, uY, uM} hY hR ⋙ nondegenerateInclusion R ⟶
    nondegenerateInclusion S ⋙ ambientFunctor hY

example : RestrictedInclusionInterface.{uS, uR, uY, uM} := @restrictedInclusion.{uS, uR, uY, uM}
example : RestrictedInclusionInterface.{0, 1, 0, 1} := @restrictedInclusion.{0, 1, 0, 1}
example : RestrictedInclusionInterface.{1, 0, 1, 0} := @restrictedInclusion.{1, 0, 1, 0}

private abbrev PartMapInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  (hY : @ActionsCommute S R Y s r y sy ry) →
  (hR : IsIdempotented R) →
  {M : Type uM} → {N : Type uN} →
  [_m : AddCommGroup M] → [_n : AddCommGroup N] →
  [_sm : NonUnitalModule S M] → [_sn : NonUnitalModule S N] →
  NonUnitalModuleHom S M N →
  NonUnitalModuleHom R (homPart hY hR M) (homPart hY hR N)

example : PartMapInterface.{uS, uR, uY, uM, uN} := @partMap.{uS, uR, uY, uM, uN}
example : PartMapInterface.{0, 1, 0, 1, 0} := @partMap.{0, 1, 0, 1, 0}
example : PartMapInterface.{1, 0, 1, 0, 1} := @partMap.{1, 0, 1, 0, 1}

private abbrev CompositionInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  (hY : @ActionsCommute S R Y s r y sy ry) →
  {M : Type uM} → {N : Type uN} → {P : Type uP} →
  [_m : AddCommGroup M] → [_n : AddCommGroup N] → [_p : AddCommGroup P] →
  [_sm : NonUnitalModule S M] → [_sn : NonUnitalModule S N] → [_sp : NonUnitalModule S P] →
  (g : NonUnitalModuleHom S N P) → (f : NonUnitalModuleHom S M N) →
  ambientMap hY (g.comp f) = (ambientMap hY g).comp (ambientMap hY f)

example : CompositionInterface.{uS, uR, uY, uM, uN, uP} := @ambientMap_comp.{uS, uR, uY, uM, uN, uP}
example : CompositionInterface.{0, 1, 0, 1, 0, 1} := @ambientMap_comp.{0, 1, 0, 1, 0, 1}
example : CompositionInterface.{1, 0, 1, 0, 1, 0} := @ambientMap_comp.{1, 0, 1, 0, 1, 0}

private abbrev PseudoInterface :=
  {A : Type uS} → {B : Type uR} →
  [a : NonUnitalRing A] → [b : NonUnitalRing B] →
  [right : NonUnitalModule Aᵐᵒᵖ B] →
  (hBA : @ActionsCommute B A B b a _ (NonUnitalModule.regular B) right) →
  (hA : IsIdempotented A) →
  NondegenerateModuleCat.{uR, uM} B ⥤ NondegenerateModuleCat.{uS, max uR uM} A

example : PseudoInterface.{uS, uR, uM} := @pseudoF.{uS, uR, uM}
example : PseudoInterface.{0, 1, 0} := @pseudoF.{0, 1, 0}
example : PseudoInterface.{1, 0, 1} := @pseudoF.{1, 0, 1}

private abbrev InductionInterface :=
  {A : Type uS} → {B : Type uR} →
  [a : NonUnitalRing A] → [b : NonUnitalRing B] →
  [left : NonUnitalModule A B] →
  (hAB : @ActionsCommute A B B a b _ left (NonUnitalModule.rightRegular B)) →
  (hB : IsIdempotented B) →
  NondegenerateModuleCat.{uS, uM} A ⥤ NondegenerateModuleCat.{uR, max uR uM} B

example : InductionInterface.{uS, uR, uM} := @I.{uS, uR, uM}
example : InductionInterface.{0, 1, 0} := @I.{0, 1, 0}
example : InductionInterface.{1, 0, 1} := @I.{1, 0, 1}

private abbrev PseudoAdapterInterface :=
  {A : Type uS} → {B : Type uR} →
  [a : NonUnitalRing A] → [b : NonUnitalRing B] →
  [right : NonUnitalModule Aᵐᵒᵖ B] →
  (hBA : @ActionsCommute B A B b a _ (NonUnitalModule.regular B) right) →
  (hA : IsIdempotented A) →
  @IsNondegenerateBimodule B A B b a _ (NonUnitalModule.regular B) right →
  NondegenerateModuleCat.{uR, uM} B ⥤ NondegenerateModuleCat.{uS, max uR uM} A

example : PseudoAdapterInterface.{uS, uR, uM} := @pseudoFOfNondegenerate.{uS, uR, uM}
example : PseudoAdapterInterface.{0, 1, 0} := @pseudoFOfNondegenerate.{0, 1, 0}
example : PseudoAdapterInterface.{1, 0, 1} := @pseudoFOfNondegenerate.{1, 0, 1}

private abbrev InductionAdapterInterface :=
  {A : Type uS} → {B : Type uR} →
  [a : NonUnitalRing A] → [b : NonUnitalRing B] →
  [left : NonUnitalModule A B] →
  (hAB : @ActionsCommute A B B a b _ left (NonUnitalModule.rightRegular B)) →
  (hB : IsIdempotented B) →
  @IsNondegenerateBimodule A B B a b _ left (NonUnitalModule.rightRegular B) →
  NondegenerateModuleCat.{uS, uM} A ⥤ NondegenerateModuleCat.{uR, max uR uM} B

example : InductionAdapterInterface.{uS, uR, uM} := @IOfNondegenerate.{uS, uR, uM}
example : InductionAdapterInterface.{0, 1, 0} := @IOfNondegenerate.{0, 1, 0}
example : InductionAdapterInterface.{1, 0, 1} := @IOfNondegenerate.{1, 0, 1}

private abbrev PseudoInclusionInterface :=
  {A : Type uS} → {B : Type uR} →
  [a : NonUnitalRing A] → [b : NonUnitalRing B] →
  [right : NonUnitalModule Aᵐᵒᵖ B] →
  (hBA : @ActionsCommute B A B b a _ (NonUnitalModule.regular B) right) →
  (hA : IsIdempotented A) →
  pseudoF.{uS, uR, uM} hBA hA ⋙ nondegenerateInclusion A ⟶
    nondegenerateInclusion B ⋙ @ambientFunctor B A B b a _ (NonUnitalModule.regular B) right hBA

example : PseudoInclusionInterface.{uS, uR, uM} := @pseudoInclusion.{uS, uR, uM}
example : PseudoInclusionInterface.{0, 1, 0} := @pseudoInclusion.{0, 1, 0}
example : PseudoInclusionInterface.{1, 0, 1} := @pseudoInclusion.{1, 0, 1}

private abbrev InductionInclusionInterface :=
  {A : Type uS} → {B : Type uR} →
  [a : NonUnitalRing A] → [b : NonUnitalRing B] →
  [left : NonUnitalModule A B] →
  (hAB : @ActionsCommute A B B a b _ left (NonUnitalModule.rightRegular B)) →
  (hB : IsIdempotented B) →
  I.{uS, uR, uM} hAB hB ⋙ nondegenerateInclusion B ⟶
    nondegenerateInclusion A ⋙ @ambientFunctor A B B a b _ left (NonUnitalModule.rightRegular B) hAB

example : InductionInclusionInterface.{uS, uR, uM} := @inductionInclusion.{uS, uR, uM}
example : InductionInclusionInterface.{0, 1, 0} := @inductionInclusion.{0, 1, 0}
example : InductionInclusionInterface.{1, 0, 1} := @inductionInclusion.{1, 0, 1}

section Competing

variable {S : Type uS} {R : Type uR} {Y : Type uY} {M : Type uM}
  [s₁ : NonUnitalRing S] [s₂ : NonUnitalRing S]
  [r₁ : NonUnitalRing R] [r₂ : NonUnitalRing R]
  [y₁ : AddCommGroup Y] [y₂ : AddCommGroup Y]
  [m₁ : AddCommGroup M] [m₂ : AddCommGroup M]
  (sy : @NonUnitalModule S Y s₁ y₁)
  (ry : @NonUnitalModule Rᵐᵒᵖ Y (@MulOpposite.instNonUnitalRing R r₁) y₁)
  (sm : @NonUnitalModule S M s₁ m₁)
  (hY : @ActionsCommute S R Y s₁ r₁ y₁ sy ry)
  [syOther : @NonUnitalModule S Y s₁ y₁]
  [ryOther : @NonUnitalModule Rᵐᵒᵖ Y (@MulOpposite.instNonUnitalRing R r₁) y₁]
  [smOther : @NonUnitalModule S M s₁ m₁]
  [homOther : @NonUnitalModule R (@NonUnitalModuleHom S Y M s₁ y₁ m₁ sy sm) r₁
    (@NonUnitalModuleHom.instAddCommGroup S Y M s₁ y₁ m₁ sy sm)]

set_option linter.overlappingInstances false in
example :
    let H := @ambientFunctor.{uS, uR, uY, uM} S R Y s₁ r₁ y₁ sy ry hY
    let X := @NonUnitalModuleCat.of S s₁ M m₁ sm
    @NonUnitalModuleCat.carrier R r₁ (H.obj X) = @NonUnitalModuleHom S Y M s₁ y₁ m₁ sy sm ∧
    @NonUnitalModuleCat.isAddCommGroup R r₁ (H.obj X) =
      @NonUnitalModuleHom.instAddCommGroup S Y M s₁ y₁ m₁ sy sm ∧
    @NonUnitalModuleCat.isModule R r₁ (H.obj X) =
      @sourceAction S R Y M s₁ r₁ y₁ m₁ sy ry sm hY :=
  ⟨rfl, rfl, rfl⟩

set_option linter.overlappingInstances false in
example (hR : @IsIdempotented R r₁) :
    let H := @nondegenerateFunctor.{uS, uR, uY, uM} S R Y s₁ r₁ y₁ sy ry hY hR
    let X := @NonUnitalModuleCat.of S s₁ M m₁ sm
    @NonUnitalModuleCat.carrier R r₁ (H.obj X).obj =
      @nondegeneratePart R r₁ hR (@NonUnitalModuleHom S Y M s₁ y₁ m₁ sy sm)
        (@NonUnitalModuleHom.instAddCommGroup S Y M s₁ y₁ m₁ sy sm)
        (@sourceAction S R Y M s₁ r₁ y₁ m₁ sy ry sm hY) := rfl

set_option linter.overlappingInstances false in
example (f : @NonUnitalModuleHom S M M s₁ m₁ m₁ sm sm) :
    let H := @NonUnitalModuleHom S Y M s₁ y₁ m₁ sy sm
    let G := @NonUnitalModuleHom.instAddCommGroup S Y M s₁ y₁ m₁ sy sm
    let action := @sourceAction S R Y M s₁ r₁ y₁ m₁ sy ry sm hY
    @NonUnitalModuleHom.toAddMonoidHom R H H r₁ G G action action
      (@ambientMap S R Y s₁ r₁ y₁ sy ry hY M M m₁ m₁ sm sm f) =
      @postcomposeAddHom S s₁ Y M M y₁ m₁ m₁ sy sm sm f := rfl

end Competing

section Coincident

variable {A : Type uS} [a₁ : NonUnitalRing A] [a₂ : NonUnitalRing A]
  [g₁ : AddCommGroup A] [g₂ : AddCommGroup A]
  (left : @NonUnitalModule A A a₁ g₁)
  (right : @NonUnitalModule Aᵐᵒᵖ A (@MulOpposite.instNonUnitalRing A a₁) g₁)
  (h : @ActionsCommute A A A a₁ a₁ g₁ left right)
  [leftOther : @NonUnitalModule A A a₁ g₁]
  [rightOther : @NonUnitalModule Aᵐᵒᵖ A (@MulOpposite.instNonUnitalRing A a₁) g₁]
  [homOther : @NonUnitalModule A (@NonUnitalModuleHom A A A a₁ g₁ g₁ left left) a₁
    (@NonUnitalModuleHom.instAddCommGroup A A A a₁ g₁ g₁ left left)]

set_option linter.overlappingInstances false in
example :
    let H := @ambientFunctor.{uS, uS, uS, uS} A A A a₁ a₁ g₁ left right h
    let X := @NonUnitalModuleCat.of A a₁ A g₁ left
    @NonUnitalModuleCat.isModule A a₁ (H.obj X) =
      @sourceAction A A A A a₁ a₁ g₁ g₁ left right left h ∧
    @NonUnitalModuleCat.isAddCommGroup A a₁ (H.obj X) =
      @NonUnitalModuleHom.instAddCommGroup A A A a₁ g₁ g₁ left left :=
  ⟨rfl, rfl⟩

end Coincident

section SpecializedCompeting

variable {A : Type uS} {B : Type uR}
  [a₁ : NonUnitalRing A] [a₂ : NonUnitalRing A]
  [b₁ : NonUnitalRing B] [b₂ : NonUnitalRing B]
  [otherGroup : AddCommGroup B]
  (right : @NonUnitalModule Aᵐᵒᵖ B (@MulOpposite.instNonUnitalRing A a₁)
    (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₁)))
  (left : @NonUnitalModule A B a₁
    (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₁)))
  (hBA : @ActionsCommute B A B b₁ a₁ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₁)) (@NonUnitalModule.regular B b₁) right)
  (hAB : @ActionsCommute A B B a₁ b₁ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₁)) left (@NonUnitalModule.rightRegular B b₁))

set_option linter.overlappingInstances false in
example (hA : @IsIdempotented A a₁) :
    @pseudoF.{uS, uR, uM} A B a₁ b₁ right hBA hA =
      @restrictedFunctor B A B b₁ a₁ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₁)) (@NonUnitalModule.regular B b₁) right hBA hA := rfl

set_option linter.overlappingInstances false in
example (hB : @IsIdempotented B b₁) :
    @I.{uS, uR, uM} A B a₁ b₁ left hAB hB =
      @restrictedFunctor A B B a₁ b₁ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₁)) left (@NonUnitalModule.rightRegular B b₁) hAB hB := rfl

end SpecializedCompeting

section TrivialCarriers

variable {S : Type uS} {R : Type uR} {Y : Type uY} {M : Type uM}
  [NonUnitalRing S] [NonUnitalRing R] [AddCommGroup Y] [AddCommGroup M]
  [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S M]
  (hY : ActionsCommute S R Y) (hR : IsIdempotented R)

example [Subsingleton M] : Subsingleton (sourceHom hY M) := hom_subsingleton
example [Subsingleton Y] : Subsingleton (sourceHom hY M) := hom_subsingleton_of_source

example [Subsingleton M] : Subsingleton (homPart hY hR M) := by
  have : Subsingleton (sourceHom hY M) := hom_subsingleton
  exact inferInstance

example [Subsingleton Y] : Subsingleton (homPart hY hR M) := by
  have : Subsingleton (sourceHom hY M) := hom_subsingleton_of_source
  exact inferInstance

end TrivialCarriers

section IntegerZero

local instance intZero : NonUnitalModule ℤ ℤ := NonUnitalModule.zero
local instance intRightZero : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.zero

private theorem zeroCommute : ActionsCommute ℤ ℤ ℤ := actionsCommute_zero_left

private abbrev zeroHom := sourceHom zeroCommute ℤ
private abbrev zeroPart := homPart zeroCommute (IsIdempotented.of_ring ℤ) ℤ

/-- Both carriers are nonzero, and the identity additive map is a nonzero actual Hom. -/
example : (NonUnitalModuleHom.id ℤ ℤ : zeroHom) ≠ 0 := by
  intro he
  have bad : (1 : ℤ) = 0 :=
    congrArg (fun f : NonUnitalModuleHom ℤ ℤ ℤ => f 1) he
  exact one_ne_zero bad

/-- The induced action is zero on that entire nonzero Hom. -/
private theorem zeroEnd (r : ℤ) : NonUnitalModule.toEndHom zeroHom.isModule r = 0 :=
  sourceAction_toEndHom_eq_zero zeroCommute (fun _ _ => rfl) r

/-- Idempotent fixation under the actual residual action forces the Hom to be zero. -/
private theorem zeroPart_mem (φ : NonUnitalModuleHom ℤ ℤ ℤ) :
    φ ∈ zeroPart ↔ φ = 0 := by
  constructor
  · rintro ⟨e, he⟩
    change NonUnitalModule.toEndHom zeroHom.isModule (e : ℤ) φ = φ at he
    rw [zeroEnd] at he
    exact he.symm
  · rintro rfl
    exact zeroPart.zero_mem

example : (NonUnitalModuleHom.id ℤ ℤ : zeroHom) ∉ zeroPart := by
  intro he
  have bad : (1 : ℤ) = 0 :=
    congrArg (fun f : NonUnitalModuleHom ℤ ℤ ℤ => f 1) ((zeroPart_mem _).mp he)
  exact one_ne_zero bad

/-- The constructed subtype is trivial although the ambient Hom is nonzero. -/
example : Subsingleton zeroPart :=
  ⟨fun φ ψ => Subtype.ext (((zeroPart_mem _).mp φ.property).trans
    ((zeroPart_mem _).mp ψ.property).symm)⟩

example (φ : zeroPart) :
    zeroPart.subtype φ = φ.val ∧ φ.val = 0 :=
  ⟨rfl, (zeroPart_mem _).mp φ.property⟩

example (φ : zeroPart) :
    (show NonUnitalModuleHom ℤ zeroPart zeroHom from
      (inclusion zeroCommute (IsIdempotented.of_ring ℤ)).app
        (NonUnitalModuleCat.of ℤ ℤ)) φ = φ.val := rfl

example (φ : zeroPart) :
    (partMap zeroCommute (IsIdempotented.of_ring ℤ) (NonUnitalModuleHom.id ℤ ℤ) φ).val =
      φ.val := rfl

end IntegerZero

section IntegerRegular

local instance intRegular : NonUnitalModule ℤ ℤ := NonUnitalModule.regular ℤ
local instance intRightRegular : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.rightRegular ℤ

private theorem regularCommute : ActionsCommute ℤ ℤ ℤ :=
  NonUnitalModule.regular_actionsCommute ℤ

private def regularInteger : NondegenerateModuleCat ℤ :=
  ⟨NonUnitalModuleCat.of ℤ ℤ,
    fun n => ⟨⟨1, IsIdempotentElem.one⟩, one_mul n⟩⟩

example (a b : ℤ) :
    NonUnitalModule.toEndHom (pseudoAction regularCommute) a
      (NonUnitalModuleHom.id ℤ ℤ) b = b * a := rfl

example (b b' : ℤ) :
    NonUnitalModule.toEndHom (inductionAction regularCommute) b
      (NonUnitalModuleHom.id ℤ ℤ) b' = b' * b := rfl

private def regularIdPart : homPart regularCommute (IsIdempotented.of_ring ℤ) ℤ :=
  ⟨NonUnitalModuleHom.id ℤ ℤ, ⟨⟨1, IsIdempotentElem.one⟩,
    NonUnitalModuleHom.ext fun n => mul_one n⟩⟩

example (b b' : ℤ) :
    (show NonUnitalModuleHom ℤ ℤ regularInteger.obj from
      (b • (show ((I regularCommute (IsIdempotented.of_ring ℤ)).obj regularInteger).obj from
        regularIdPart)).val) b' = b' * b := rfl

example :
    ((pseudoF regularCommute (IsIdempotented.of_ring ℤ)).obj regularInteger).obj.carrier =
      homPart regularCommute (IsIdempotented.of_ring ℤ) ℤ := rfl

example :
    (inductionInclusion regularCommute (IsIdempotented.of_ring ℤ)).app regularInteger =
      (homPart regularCommute (IsIdempotented.of_ring ℤ) ℤ).subtype := rfl

end IntegerRegular

end Langlands.Algebra.NondegenerateHomFunctorChecks
