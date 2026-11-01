import Langlands.Algebra.NondegenerateRightHomFunctor

set_option autoImplicit false
-- Private interface abbreviations intentionally have maximum universe sorts.
set_option linter.checkUnivs false

open CategoryTheory MulOpposite

namespace Langlands.Algebra.NondegenerateRightHomFunctorChecks

open NonUnitalBimoduleHomActions NondegenerateRightHomFunctor

universe uS uR uY uM uN uP

/-! Complete unapplied types, tested generically and at complementary unequal universes. -/

private abbrev AmbientInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [ry : NonUnitalModule R Y] → [sy : NonUnitalModule Sᵐᵒᵖ Y] →
  (hY : @ActionsCommute R S Y r s y ry sy) →
  NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ ⥤ NonUnitalModuleCat.{uR, max uY uM} Rᵐᵒᵖ

example : AmbientInterface.{uS, uR, uY, uM} := @ambientFunctor.{uS, uR, uY, uM}
example : AmbientInterface.{0, 1, 0, 1} := @ambientFunctor.{0, 1, 0, 1}
example : AmbientInterface.{1, 0, 1, 0} := @ambientFunctor.{1, 0, 1, 0}

private abbrev MapInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [ry : NonUnitalModule R Y] → [sy : NonUnitalModule Sᵐᵒᵖ Y] →
  (hY : @ActionsCommute R S Y r s y ry sy) →
  {M : Type uM} → {N : Type uN} →
  [_m : AddCommGroup M] → [_n : AddCommGroup N] →
  [_sm : NonUnitalModule Sᵐᵒᵖ M] → [_sn : NonUnitalModule Sᵐᵒᵖ N] →
  NonUnitalModuleHom Sᵐᵒᵖ M N →
  NonUnitalModuleHom Rᵐᵒᵖ (rightSourceHom hY M) (rightSourceHom hY N)

example : MapInterface.{uS, uR, uY, uM, uN} := @ambientMap.{uS, uR, uY, uM, uN}
example : MapInterface.{0, 1, 0, 1, 0} := @ambientMap.{0, 1, 0, 1, 0}
example : MapInterface.{1, 0, 1, 0, 1} := @ambientMap.{1, 0, 1, 0, 1}

private abbrev CompositeInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [ry : NonUnitalModule R Y] → [sy : NonUnitalModule Sᵐᵒᵖ Y] →
  (hY : @ActionsCommute R S Y r s y ry sy) →
  IsIdempotented R →
  NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ ⥤ NondegenerateModuleCat.{uR, max uY uM} Rᵐᵒᵖ

example : CompositeInterface.{uS, uR, uY, uM} := @nondegenerateFunctor.{uS, uR, uY, uM}
example : CompositeInterface.{0, 1, 0, 1} := @nondegenerateFunctor.{0, 1, 0, 1}
example : CompositeInterface.{1, 0, 1, 0} := @nondegenerateFunctor.{1, 0, 1, 0}

private abbrev RestrictionInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [ry : NonUnitalModule R Y] → [sy : NonUnitalModule Sᵐᵒᵖ Y] →
  (hY : @ActionsCommute R S Y r s y ry sy) →
  IsIdempotented R →
  NondegenerateModuleCat.{uS, uM} Sᵐᵒᵖ ⥤ NondegenerateModuleCat.{uR, max uY uM} Rᵐᵒᵖ

example : RestrictionInterface.{uS, uR, uY, uM} := @restrictedFunctor.{uS, uR, uY, uM}
example : RestrictionInterface.{0, 1, 0, 1} := @restrictedFunctor.{0, 1, 0, 1}
example : RestrictionInterface.{1, 0, 1, 0} := @restrictedFunctor.{1, 0, 1, 0}

private abbrev InclusionInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [ry : NonUnitalModule R Y] → [sy : NonUnitalModule Sᵐᵒᵖ Y] →
  (hY : @ActionsCommute R S Y r s y ry sy) →
  (hR : IsIdempotented R) →
  nondegenerateFunctor.{uS, uR, uY, uM} hY hR ⋙ nondegenerateInclusion Rᵐᵒᵖ ⟶
    ambientFunctor hY

example : InclusionInterface.{uS, uR, uY, uM} := @inclusion.{uS, uR, uY, uM}
example : InclusionInterface.{0, 1, 0, 1} := @inclusion.{0, 1, 0, 1}
example : InclusionInterface.{1, 0, 1, 0} := @inclusion.{1, 0, 1, 0}

private abbrev RestrictedInclusionInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [ry : NonUnitalModule R Y] → [sy : NonUnitalModule Sᵐᵒᵖ Y] →
  (hY : @ActionsCommute R S Y r s y ry sy) →
  (hR : IsIdempotented R) →
  restrictedFunctor.{uS, uR, uY, uM} hY hR ⋙ nondegenerateInclusion Rᵐᵒᵖ ⟶
    nondegenerateInclusion Sᵐᵒᵖ ⋙ ambientFunctor hY

example : RestrictedInclusionInterface.{uS, uR, uY, uM} := @restrictedInclusion.{uS, uR, uY, uM}
example : RestrictedInclusionInterface.{0, 1, 0, 1} := @restrictedInclusion.{0, 1, 0, 1}
example : RestrictedInclusionInterface.{1, 0, 1, 0} := @restrictedInclusion.{1, 0, 1, 0}

private abbrev PartMapInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [ry : NonUnitalModule R Y] → [sy : NonUnitalModule Sᵐᵒᵖ Y] →
  (hY : @ActionsCommute R S Y r s y ry sy) →
  (hR : IsIdempotented R) →
  {M : Type uM} → {N : Type uN} →
  [_m : AddCommGroup M] → [_n : AddCommGroup N] →
  [_sm : NonUnitalModule Sᵐᵒᵖ M] → [_sn : NonUnitalModule Sᵐᵒᵖ N] →
  NonUnitalModuleHom Sᵐᵒᵖ M N →
  NonUnitalModuleHom Rᵐᵒᵖ (homPart hY hR M) (homPart hY hR N)

example : PartMapInterface.{uS, uR, uY, uM, uN} := @partMap.{uS, uR, uY, uM, uN}
example : PartMapInterface.{0, 1, 0, 1, 0} := @partMap.{0, 1, 0, 1, 0}
example : PartMapInterface.{1, 0, 1, 0, 1} := @partMap.{1, 0, 1, 0, 1}

private abbrev CompositionInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [ry : NonUnitalModule R Y] → [sy : NonUnitalModule Sᵐᵒᵖ Y] →
  (hY : @ActionsCommute R S Y r s y ry sy) →
  {M : Type uM} → {N : Type uN} → {P : Type uP} →
  [_m : AddCommGroup M] → [_n : AddCommGroup N] → [_p : AddCommGroup P] →
  [_sm : NonUnitalModule Sᵐᵒᵖ M] → [_sn : NonUnitalModule Sᵐᵒᵖ N] → [_sp : NonUnitalModule Sᵐᵒᵖ P] →
  (g : NonUnitalModuleHom Sᵐᵒᵖ N P) → (f : NonUnitalModuleHom Sᵐᵒᵖ M N) →
  ambientMap hY (g.comp f) = (ambientMap hY g).comp (ambientMap hY f)

example : CompositionInterface.{uS, uR, uY, uM, uN, uP} := @ambientMap_comp.{uS, uR, uY, uM, uN, uP}
example : CompositionInterface.{0, 1, 0, 1, 0, 1} := @ambientMap_comp.{0, 1, 0, 1, 0, 1}
example : CompositionInterface.{1, 0, 1, 0, 1, 0} := @ambientMap_comp.{1, 0, 1, 0, 1, 0}

private abbrev ActionInterface :=
  {R : Type uR} → {S : Type uS} → {Y : Type uY} → {M : Type uM} →
  [r : NonUnitalRing R] → [s : NonUnitalRing S] →
  [y : AddCommGroup Y] → [m : AddCommGroup M] →
  [ry : NonUnitalModule R Y] → [sy : NonUnitalModule Sᵐᵒᵖ Y] →
  [sm : NonUnitalModule Sᵐᵒᵖ M] →
  (hY : @ActionsCommute R S Y r s y ry sy) →
  NonUnitalModule Rᵐᵒᵖ (@NonUnitalModuleHom Sᵐᵒᵖ Y M _ y m sy sm)

example : ActionInterface.{uS, uR, uY, uM} := @rightSourceAction.{uS, uR, uY, uM}
example : ActionInterface.{0, 1, 0, 1} := @rightSourceAction.{0, 1, 0, 1}
example : ActionInterface.{1, 0, 1, 0} := @rightSourceAction.{1, 0, 1, 0}

private abbrev PartInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [ry : NonUnitalModule R Y] → [sy : NonUnitalModule Sᵐᵒᵖ Y] →
  (hY : @ActionsCommute R S Y r s y ry sy) →
  (hR : IsIdempotented R) →
  (M : Type uM) → [_m : AddCommGroup M] → [_sm : NonUnitalModule Sᵐᵒᵖ M] →
  NonUnitalSubmodule Rᵐᵒᵖ (rightSourceHom hY M)

example : PartInterface.{uS, uR, uY, uM} := @homPart.{uS, uR, uY, uM}
example : PartInterface.{0, 1, 0, 1} := @homPart.{0, 1, 0, 1}
example : PartInterface.{1, 0, 1, 0} := @homPart.{1, 0, 1, 0}

private abbrev CompositeEqualityInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [ry : NonUnitalModule R Y] → [sy : NonUnitalModule Sᵐᵒᵖ Y] →
  (hY : @ActionsCommute R S Y r s y ry sy) → (hR : IsIdempotented R) →
  nondegenerateFunctor.{uS, uR, uY, uM} hY hR =
    ambientFunctor hY ⋙ nondegeneratePartFunctor hR.op

example : CompositeEqualityInterface.{uS, uR, uY, uM} := @nondegenerateFunctor_eq.{uS, uR, uY, uM}
example : CompositeEqualityInterface.{0, 1, 0, 1} := @nondegenerateFunctor_eq.{0, 1, 0, 1}
example : CompositeEqualityInterface.{1, 0, 1, 0} := @nondegenerateFunctor_eq.{1, 0, 1, 0}

private abbrev RestrictionEqualityInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [ry : NonUnitalModule R Y] → [sy : NonUnitalModule Sᵐᵒᵖ Y] →
  (hY : @ActionsCommute R S Y r s y ry sy) → (hR : IsIdempotented R) →
  restrictedFunctor.{uS, uR, uY, uM} hY hR =
    nondegenerateInclusion Sᵐᵒᵖ ⋙ (ambientFunctor hY ⋙ nondegeneratePartFunctor hR.op)

example : RestrictionEqualityInterface.{uS, uR, uY, uM} := @restrictedFunctor_eq.{uS, uR, uY, uM}
example : RestrictionEqualityInterface.{0, 1, 0, 1} := @restrictedFunctor_eq.{0, 1, 0, 1}
example : RestrictionEqualityInterface.{1, 0, 1, 0} := @restrictedFunctor_eq.{1, 0, 1, 0}

private abbrev NaturalityInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [y : AddCommGroup Y] →
  [ry : NonUnitalModule R Y] → [sy : NonUnitalModule Sᵐᵒᵖ Y] →
  (hY : @ActionsCommute R S Y r s y ry sy) → (hR : IsIdempotented R) →
  {M : Type uM} → {N : Type uN} →
  [_m : AddCommGroup M] → [_n : AddCommGroup N] →
  [_sm : NonUnitalModule Sᵐᵒᵖ M] → [_sn : NonUnitalModule Sᵐᵒᵖ N] →
  (f : NonUnitalModuleHom Sᵐᵒᵖ M N) →
  (ambientMap hY f).comp (homPart hY hR M).subtype =
    (homPart hY hR N).subtype.comp (partMap hY hR f)

example : NaturalityInterface.{uS, uR, uY, uM, uN} := @inclusion_naturality.{uS, uR, uY, uM, uN}
example : NaturalityInterface.{0, 1, 0, 1, 0} := @inclusion_naturality.{0, 1, 0, 1, 0}
example : NaturalityInterface.{1, 0, 1, 0, 1} := @inclusion_naturality.{1, 0, 1, 0, 1}

section Competing

variable {S : Type uS} {R : Type uR} {Y : Type uY} {M : Type uM}
  [s₁ : NonUnitalRing S] [s₂ : NonUnitalRing S]
  [r₁ : NonUnitalRing R] [r₂ : NonUnitalRing R]
  [y₁ : AddCommGroup Y] [y₂ : AddCommGroup Y]
  [m₁ : AddCommGroup M] [m₂ : AddCommGroup M]
  (sy : @NonUnitalModule Sᵐᵒᵖ Y (@MulOpposite.instNonUnitalRing S s₁) y₁)
  (ry : @NonUnitalModule R Y r₁ y₁)
  (sm : @NonUnitalModule Sᵐᵒᵖ M (@MulOpposite.instNonUnitalRing S s₁) m₁)
  (hY : @ActionsCommute R S Y r₁ s₁ y₁ ry sy)
  [syOther : @NonUnitalModule Sᵐᵒᵖ Y (@MulOpposite.instNonUnitalRing S s₁) y₁]
  [ryOther : @NonUnitalModule R Y r₁ y₁]
  [smOther : @NonUnitalModule Sᵐᵒᵖ M (@MulOpposite.instNonUnitalRing S s₁) m₁]
  [homOther : @NonUnitalModule Rᵐᵒᵖ
    (@NonUnitalModuleHom Sᵐᵒᵖ Y M (@MulOpposite.instNonUnitalRing S s₁) y₁ m₁ sy sm)
    (@MulOpposite.instNonUnitalRing R r₁)
    (@NonUnitalModuleHom.instAddCommGroup Sᵐᵒᵖ Y M (@MulOpposite.instNonUnitalRing S s₁) y₁ m₁ sy sm)]

set_option linter.overlappingInstances false in
example :
    let H := @ambientFunctor.{uS, uR, uY, uM} S R Y s₁ r₁ y₁ ry sy hY
    let X := @NonUnitalModuleCat.of Sᵐᵒᵖ (@MulOpposite.instNonUnitalRing S s₁) M m₁ sm
    @NonUnitalModuleCat.carrier Rᵐᵒᵖ (@MulOpposite.instNonUnitalRing R r₁) (H.obj X) =
      @NonUnitalModuleHom Sᵐᵒᵖ Y M (@MulOpposite.instNonUnitalRing S s₁) y₁ m₁ sy sm ∧
    @NonUnitalModuleCat.isAddCommGroup Rᵐᵒᵖ (@MulOpposite.instNonUnitalRing R r₁) (H.obj X) =
      @NonUnitalModuleHom.instAddCommGroup Sᵐᵒᵖ Y M (@MulOpposite.instNonUnitalRing S s₁) y₁ m₁ sy sm ∧
    @NonUnitalModuleCat.isModule Rᵐᵒᵖ (@MulOpposite.instNonUnitalRing R r₁) (H.obj X) =
      @rightSourceAction R S Y M r₁ s₁ y₁ m₁ ry sy sm hY :=
  ⟨rfl, rfl, rfl⟩

set_option linter.overlappingInstances false in
example (hR : @IsIdempotented R r₁) :
    let H := @nondegenerateFunctor.{uS, uR, uY, uM} S R Y s₁ r₁ y₁ ry sy hY hR
    let X := @NonUnitalModuleCat.of Sᵐᵒᵖ (@MulOpposite.instNonUnitalRing S s₁) M m₁ sm
    @NonUnitalModuleCat.carrier Rᵐᵒᵖ (@MulOpposite.instNonUnitalRing R r₁) (H.obj X).obj =
      @nondegeneratePart Rᵐᵒᵖ (@MulOpposite.instNonUnitalRing R r₁) (@IsIdempotented.op R r₁ hR)
        (@NonUnitalModuleHom Sᵐᵒᵖ Y M (@MulOpposite.instNonUnitalRing S s₁) y₁ m₁ sy sm)
        (@NonUnitalModuleHom.instAddCommGroup Sᵐᵒᵖ Y M (@MulOpposite.instNonUnitalRing S s₁) y₁ m₁ sy sm)
        (@rightSourceAction R S Y M r₁ s₁ y₁ m₁ ry sy sm hY) := rfl

set_option linter.overlappingInstances false in
example (f : @NonUnitalModuleHom Sᵐᵒᵖ M M (@MulOpposite.instNonUnitalRing S s₁) m₁ m₁ sm sm) :
    let H := @NonUnitalModuleHom Sᵐᵒᵖ Y M (@MulOpposite.instNonUnitalRing S s₁) y₁ m₁ sy sm
    let G := @NonUnitalModuleHom.instAddCommGroup Sᵐᵒᵖ Y M (@MulOpposite.instNonUnitalRing S s₁) y₁ m₁ sy sm
    let action := @rightSourceAction R S Y M r₁ s₁ y₁ m₁ ry sy sm hY
    @NonUnitalModuleHom.toAddMonoidHom Rᵐᵒᵖ H H (@MulOpposite.instNonUnitalRing R r₁) G G action action
      (@ambientMap S R Y s₁ r₁ y₁ ry sy hY M M m₁ m₁ sm sm f) =
      @postcomposeAddHom Sᵐᵒᵖ (@MulOpposite.instNonUnitalRing S s₁) Y M M y₁ m₁ m₁ sy sm sm f := rfl

set_option linter.overlappingInstances false in
example (hR : @IsIdempotented R r₁) :
    let H := @nondegenerateFunctor.{uS, uR, uY, uM} S R Y s₁ r₁ y₁ ry sy hY hR
    let X := @NonUnitalModuleCat.of Sᵐᵒᵖ (@MulOpposite.instNonUnitalRing S s₁) M m₁ sm
    let Q := @homPart S R Y s₁ r₁ y₁ ry sy hY hR M m₁ sm
    @NonUnitalModuleCat.isAddCommGroup Rᵐᵒᵖ (@MulOpposite.instNonUnitalRing R r₁) (H.obj X).obj =
      (@NonUnitalSubmodule.toAddSubgroup Rᵐᵒᵖ
        (@NonUnitalModuleHom Sᵐᵒᵖ Y M (@MulOpposite.instNonUnitalRing S s₁) y₁ m₁ sy sm)
        (@MulOpposite.instNonUnitalRing R r₁)
        (@NonUnitalModuleHom.instAddCommGroup Sᵐᵒᵖ Y M (@MulOpposite.instNonUnitalRing S s₁) y₁ m₁ sy sm)
        (@rightSourceAction R S Y M r₁ s₁ y₁ m₁ ry sy sm hY) Q).toAddCommGroup ∧
    @NonUnitalModuleCat.isModule Rᵐᵒᵖ (@MulOpposite.instNonUnitalRing R r₁) (H.obj X).obj =
      @NonUnitalSubmodule.instNonUnitalModuleSubtypeMem Rᵐᵒᵖ
        (@NonUnitalModuleHom Sᵐᵒᵖ Y M (@MulOpposite.instNonUnitalRing S s₁) y₁ m₁ sy sm)
        (@MulOpposite.instNonUnitalRing R r₁)
        (@NonUnitalModuleHom.instAddCommGroup Sᵐᵒᵖ Y M (@MulOpposite.instNonUnitalRing S s₁) y₁ m₁ sy sm)
        (@rightSourceAction R S Y M r₁ s₁ y₁ m₁ ry sy sm hY) Q :=
  ⟨rfl, rfl⟩

end Competing

section Coincident

variable {A : Type uS} [a₁ : NonUnitalRing A] [a₂ : NonUnitalRing A]
  [g₁ : AddCommGroup A] [g₂ : AddCommGroup A]
  (left : @NonUnitalModule A A a₁ g₁)
  (right : @NonUnitalModule Aᵐᵒᵖ A (@MulOpposite.instNonUnitalRing A a₁) g₁)
  (h : @ActionsCommute A A A a₁ a₁ g₁ left right)
  [leftOther : @NonUnitalModule A A a₁ g₁]
  [rightOther : @NonUnitalModule Aᵐᵒᵖ A (@MulOpposite.instNonUnitalRing A a₁) g₁]
  [homOther : @NonUnitalModule Aᵐᵒᵖ
    (@NonUnitalModuleHom Aᵐᵒᵖ A A (@MulOpposite.instNonUnitalRing A a₁) g₁ g₁ right right)
    (@MulOpposite.instNonUnitalRing A a₁)
    (@NonUnitalModuleHom.instAddCommGroup Aᵐᵒᵖ A A (@MulOpposite.instNonUnitalRing A a₁) g₁ g₁ right right)]

set_option linter.overlappingInstances false in
example :
    let H := @ambientFunctor.{uS, uS, uS, uS} A A A a₁ a₁ g₁ left right h
    let X := @NonUnitalModuleCat.of Aᵐᵒᵖ (@MulOpposite.instNonUnitalRing A a₁) A g₁ right
    @NonUnitalModuleCat.isModule Aᵐᵒᵖ (@MulOpposite.instNonUnitalRing A a₁) (H.obj X) =
      @rightSourceAction A A A A a₁ a₁ g₁ g₁ left right right h ∧
    @NonUnitalModuleCat.isAddCommGroup Aᵐᵒᵖ (@MulOpposite.instNonUnitalRing A a₁) (H.obj X) =
      @NonUnitalModuleHom.instAddCommGroup Aᵐᵒᵖ A A (@MulOpposite.instNonUnitalRing A a₁) g₁ g₁ right right :=
  ⟨rfl, rfl⟩

end Coincident

section TrivialCarriers

variable {S : Type uS} {R : Type uR} {Y : Type uY} {M : Type uM}
  [NonUnitalRing S] [NonUnitalRing R] [AddCommGroup Y] [AddCommGroup M]
  [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ M]
  (hY : ActionsCommute R S Y) (hR : IsIdempotented R)

example [Subsingleton M] : Subsingleton (rightSourceHom hY M) := hom_subsingleton
example [Subsingleton Y] : Subsingleton (rightSourceHom hY M) := hom_subsingleton_of_source

example [Subsingleton M] : Subsingleton (homPart hY hR M) := by
  have : Subsingleton (rightSourceHom hY M) := hom_subsingleton
  exact inferInstance

example [Subsingleton Y] : Subsingleton (homPart hY hR M) := by
  have : Subsingleton (rightSourceHom hY M) := hom_subsingleton_of_source
  exact inferInstance

end TrivialCarriers

section IntegerZero

local instance intZero : NonUnitalModule ℤ ℤ := NonUnitalModule.zero
local instance intRightZero : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.zero

private theorem zeroCommute : ActionsCommute ℤ ℤ ℤ := actionsCommute_zero_left

private abbrev zeroHom := rightSourceHom zeroCommute ℤ
private abbrev zeroPart := homPart zeroCommute (IsIdempotented.of_ring ℤ) ℤ

/-- The identity of a nonzero integer carrier is a nonzero actual right-linear Hom. -/
private theorem zeroId_ne_zero : (NonUnitalModuleHom.id ℤᵐᵒᵖ ℤ : zeroHom) ≠ 0 := by
  intro he
  have bad : (1 : ℤ) = 0 :=
    congrArg (fun f : NonUnitalModuleHom ℤᵐᵒᵖ ℤ ℤ => f 1) he
  exact one_ne_zero bad

/-- The entire named residual scalar endomorphism is zero. -/
private theorem zeroEnd (r : ℤᵐᵒᵖ) : NonUnitalModule.toEndHom zeroHom.isModule r = 0 := by
  apply AddMonoidHom.ext
  intro h
  apply NonUnitalModuleHom.ext
  intro y
  change (show NonUnitalModuleHom ℤᵐᵒᵖ ℤ ℤ from h) 0 = 0
  exact (show NonUnitalModuleHom ℤᵐᵒᵖ ℤ ℤ from h).map_zero

private theorem zeroPart_mem (φ : NonUnitalModuleHom ℤᵐᵒᵖ ℤ ℤ) :
    φ ∈ zeroPart ↔ φ = 0 := by
  constructor
  · rintro ⟨e, he⟩
    change NonUnitalModule.toEndHom zeroHom.isModule (e : ℤᵐᵒᵖ) φ = φ at he
    rw [zeroEnd] at he
    exact he.symm
  · rintro rfl
    exact zeroPart.zero_mem

example : (NonUnitalModuleHom.id ℤᵐᵒᵖ ℤ : zeroHom) ∉ zeroPart :=
  fun he => zeroId_ne_zero ((zeroPart_mem _).mp he)

example : Subsingleton zeroPart :=
  ⟨fun φ ψ => Subtype.ext (((zeroPart_mem _).mp φ.property).trans
    ((zeroPart_mem _).mp ψ.property).symm)⟩

example (φ : zeroPart) : zeroPart.subtype φ = φ.val ∧ φ.val = 0 :=
  ⟨rfl, (zeroPart_mem _).mp φ.property⟩

example (φ : zeroPart) :
    (show NonUnitalModuleHom ℤᵐᵒᵖ zeroPart zeroHom from
      (inclusion zeroCommute (IsIdempotented.of_ring ℤ)).app
        (NonUnitalModuleCat.of ℤᵐᵒᵖ ℤ)) φ = φ.val := rfl

example (φ : zeroPart) :
    (partMap zeroCommute (IsIdempotented.of_ring ℤ) (NonUnitalModuleHom.id ℤᵐᵒᵖ ℤ) φ).val =
      φ.val := rfl

end IntegerZero

section IntegerRegular

local instance intRegular : NonUnitalModule ℤ ℤ := NonUnitalModule.regular ℤ
local instance intRightRegular : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.rightRegular ℤ

private theorem regularCommute : ActionsCommute ℤ ℤ ℤ :=
  NonUnitalModule.regular_actionsCommute ℤ

private def regularInteger : NondegenerateModuleCat ℤᵐᵒᵖ :=
  ⟨NonUnitalModuleCat.of ℤᵐᵒᵖ ℤ,
    fun n => ⟨⟨op 1, by exact congrArg op IsIdempotentElem.one.eq⟩, mul_one n⟩⟩

example (a b : ℤ) :
    NonUnitalModule.toEndHom (rightSourceAction regularCommute) (op a)
      (NonUnitalModuleHom.id ℤᵐᵒᵖ ℤ) b = a * b := rfl

private def regularIdPart : homPart regularCommute (IsIdempotented.of_ring ℤ) ℤ :=
  ⟨NonUnitalModuleHom.id ℤᵐᵒᵖ ℤ,
    (mem_homPart_iff regularCommute (IsIdempotented.of_ring ℤ) _).mpr
      ⟨⟨1, IsIdempotentElem.one⟩, fun n => one_mul n⟩⟩

example (a b : ℤ) :
    (show NonUnitalModuleHom ℤᵐᵒᵖ ℤ ℤ from
      (op a • regularIdPart).val) b = a * b := rfl

example :
    ((restrictedFunctor regularCommute (IsIdempotented.of_ring ℤ)).obj regularInteger).obj.carrier =
      homPart regularCommute (IsIdempotented.of_ring ℤ) ℤ := rfl

example :
    (restrictedInclusion regularCommute (IsIdempotented.of_ring ℤ)).app regularInteger =
      (homPart regularCommute (IsIdempotented.of_ring ℤ) ℤ).subtype := rfl

end IntegerRegular

end Langlands.Algebra.NondegenerateRightHomFunctorChecks
