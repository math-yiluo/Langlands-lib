import Langlands.Algebra.NondegenerateModuleNaturalEndEvaluation

/-!
# Statements of the actual forgetful natural-endomorphism classification

Renard I.1.6, printed pp.11–12/PDF17–18. These are proposition definitions,
not proofs. The actual regular object is available at carrier universe
`max uA uM`; no transfer to an arbitrarily smaller universe is asserted.
-/

set_option autoImplicit false

namespace Langlands.Algebra
namespace NondegenerateModuleNaturalEndClassificationStatement

universe uA uM

variable {A : Type uA} [NonUnitalRing A]

/-- Evaluation after the published family action is the entire identity ring map. -/
def FamilyCompositeIdentity (hA : IsIdempotented A) : Prop :=
  letI := IdempotentedRingRightLimit.ring hA
  letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
  (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA).comp
      (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA) =
    RingHom.id (IdempotentedRingRightLimit A)

/-- The family action after evaluation is the entire identity ring map. -/
def NaturalEndCompositeIdentity (hA : IsIdempotented A) : Prop :=
  letI := IdempotentedRingRightLimit.ring hA
  letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
  (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA).comp
      (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA) =
    RingHom.id (NondegenerateModuleNaturalEnd.{uA, max uA uM} A)

/-- Every actual compatible right family is recovered by the two specified maps. -/
def FamilyRecovery (hA : IsIdempotented A) : Prop :=
  ∀ x : IdempotentedRingRightLimit A,
    NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA
      (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA x) = x

/-- Every actual forgetful natural transformation is recovered by the two maps. -/
def NaturalEndRecovery (hA : IsIdempotented A) : Prop :=
  ∀ θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A,
    IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA
      (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA θ) = θ

/-- Reconstruction retains equality of the entire original additive component. -/
def ComponentRecovery (hA : IsIdempotented A) : Prop :=
  ∀ (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A),
    ((IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA
      (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA θ)).app M).hom =
      (θ.app M).hom

/-- The component reconstruction evaluated at every original module element. -/
def ComponentPointRecovery (hA : IsIdempotented A) : Prop :=
  ∀ (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) (m : M.obj),
    (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA
      (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA θ)).app M m =
      θ.app M m

/-- Evaluation recovers every coordinate at an actual original idempotent. -/
def CoordinateRecovery (hA : IsIdempotented A) : Prop :=
  ∀ (x : IdempotentedRingRightLimit A) (e : Idempotent A),
    (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA
      (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA x)).val e = x.val e

/-- An actual ring equivalence with both entire functions fixed to the two maps. -/
def SpecifiedRingEquivalence (hA : IsIdempotented A) : Prop :=
  letI := IdempotentedRingRightLimit.ring hA
  letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
  ∃ E : IdempotentedRingRightLimit A ≃+*
      NondegenerateModuleNaturalEnd.{uA, max uA uM} A,
    (E : IdempotentedRingRightLimit A → NondegenerateModuleNaturalEnd.{uA, max uA uM} A) =
      (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA :
        IdempotentedRingRightLimit A → NondegenerateModuleNaturalEnd.{uA, max uA uM} A) ∧
    (E.symm : NondegenerateModuleNaturalEnd.{uA, max uA uM} A → IdempotentedRingRightLimit A) =
      (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA :
        NondegenerateModuleNaturalEnd.{uA, max uA uM} A → IdempotentedRingRightLimit A)

/-- All classification assertions for every original idempotented nonunital ring. -/
def Classification : Prop :=
  ∀ (A : Type uA) (originalRing : NonUnitalRing A)
    (hA : @IsIdempotented A originalRing),
    @FamilyCompositeIdentity.{uA, uM} A originalRing hA ∧
    @NaturalEndCompositeIdentity.{uA, uM} A originalRing hA ∧
    @FamilyRecovery.{uA, uM} A originalRing hA ∧
    @NaturalEndRecovery.{uA, uM} A originalRing hA ∧
    @ComponentRecovery.{uA, uM} A originalRing hA ∧
    @ComponentPointRecovery.{uA, uM} A originalRing hA ∧
    @CoordinateRecovery.{uA, uM} A originalRing hA ∧
    @SpecifiedRingEquivalence.{uA, uM} A originalRing hA

/-! Complete unapplied declaration telescopes at independent universes. -/

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @FamilyCompositeIdentity.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @NaturalEndCompositeIdentity.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @FamilyRecovery.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @NaturalEndRecovery.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @ComponentRecovery.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @ComponentPointRecovery.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @CoordinateRecovery.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @SpecifiedRingEquivalence.{uA, uM}

example : Prop := Classification.{uA, uM}

/-! The ring universe may be smaller than the lifting universe. -/

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @FamilyCompositeIdentity.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @NaturalEndCompositeIdentity.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @FamilyRecovery.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @NaturalEndRecovery.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @ComponentRecovery.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @ComponentPointRecovery.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @CoordinateRecovery.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @SpecifiedRingEquivalence.{0, 1}

example : Prop := Classification.{0, 1}

/-! The ring universe may be larger; the actual carrier universe is still 1. -/

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @FamilyCompositeIdentity.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @NaturalEndCompositeIdentity.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @FamilyRecovery.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @NaturalEndRecovery.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @ComponentRecovery.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @ComponentPointRecovery.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @CoordinateRecovery.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @SpecifiedRingEquivalence.{1, 0}

example : Prop := Classification.{1, 0}

/-! A competing scalar ring cannot change the chosen original statements. -/
section CompetingOriginalRings

variable {A : Type uA} (originalRing : NonUnitalRing A)
  [competingOriginalRing : NonUnitalRing A]

example : @FamilyCompositeIdentity.{uA, uM} A originalRing =
    (fun hA : @IsIdempotented A originalRing =>
      letI := originalRing
      letI := IdempotentedRingRightLimit.ring hA
      letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
      (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA).comp
          (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA) =
        RingHom.id (IdempotentedRingRightLimit A)) := rfl

example : @NaturalEndCompositeIdentity.{uA, uM} A originalRing =
    (fun hA : @IsIdempotented A originalRing =>
      letI := originalRing
      letI := IdempotentedRingRightLimit.ring hA
      letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
      (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA).comp
          (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA) =
        RingHom.id (NondegenerateModuleNaturalEnd.{uA, max uA uM} A)) := rfl

example : @FamilyRecovery.{uA, uM} A originalRing =
    (fun hA : @IsIdempotented A originalRing =>
      letI := originalRing
      ∀ x : IdempotentedRingRightLimit A,
        NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA
          (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA x) = x) := rfl

example : @NaturalEndRecovery.{uA, uM} A originalRing =
    (fun hA : @IsIdempotented A originalRing =>
      letI := originalRing
      ∀ θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A,
        IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA
          (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA θ) = θ) := rfl

example : @ComponentRecovery.{uA, uM} A originalRing =
    (fun hA : @IsIdempotented A originalRing =>
      letI := originalRing
      ∀ (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A)
        (M : NondegenerateModuleCat.{uA, max uA uM} A),
        ((IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA
          (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA θ)).app M).hom =
          (θ.app M).hom) := rfl

example : @ComponentPointRecovery.{uA, uM} A originalRing =
    (fun hA : @IsIdempotented A originalRing =>
      letI := originalRing
      ∀ (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A)
        (M : NondegenerateModuleCat.{uA, max uA uM} A) (m : M.obj),
        (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA
          (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA θ)).app M m =
          θ.app M m) := rfl

example : @CoordinateRecovery.{uA, uM} A originalRing =
    (fun hA : @IsIdempotented A originalRing =>
      letI := originalRing
      ∀ (x : IdempotentedRingRightLimit A) (e : Idempotent A),
        (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA
          (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA x)).val e =
          x.val e) := rfl

example : @SpecifiedRingEquivalence.{uA, uM} A originalRing =
    (fun hA : @IsIdempotented A originalRing =>
      letI := originalRing
      letI := IdempotentedRingRightLimit.ring hA
      letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
      ∃ E : IdempotentedRingRightLimit A ≃+*
          NondegenerateModuleNaturalEnd.{uA, max uA uM} A,
        (E : IdempotentedRingRightLimit A → NondegenerateModuleNaturalEnd.{uA, max uA uM} A) =
          (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA :
            IdempotentedRingRightLimit A → NondegenerateModuleNaturalEnd.{uA, max uA uM} A) ∧
        (E.symm : NondegenerateModuleNaturalEnd.{uA, max uA uM} A →
            IdempotentedRingRightLimit A) =
          (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA :
            NondegenerateModuleNaturalEnd.{uA, max uA uM} A → IdempotentedRingRightLimit A)) :=
  rfl

end CompetingOriginalRings

/-! Competing source and target rings cannot alter either ring-map identity. -/
section CompetingEndAndFamilyRings

variable {A : Type uA} [NonUnitalRing A]
  [competingEndRing : Ring (NondegenerateModuleNaturalEnd.{uA, max uA uM} A)]
  [competingFamilyRing : Ring (IdempotentedRingRightLimit A)]

example (hA : IsIdempotented A) :
    FamilyCompositeIdentity.{uA, uM} hA =
      (letI := IdempotentedRingRightLimit.ring hA
       letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
       (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA).comp
           (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA) =
         RingHom.id (IdempotentedRingRightLimit A)) := rfl

example (hA : IsIdempotented A) :
    NaturalEndCompositeIdentity.{uA, uM} hA =
      (letI := IdempotentedRingRightLimit.ring hA
       letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
       (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA).comp
           (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA) =
         RingHom.id (NondegenerateModuleNaturalEnd.{uA, max uA uM} A)) := rfl

example (hA : IsIdempotented A) :
    SpecifiedRingEquivalence.{uA, uM} hA =
      (letI := IdempotentedRingRightLimit.ring hA
       letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
       ∃ E : IdempotentedRingRightLimit A ≃+*
           NondegenerateModuleNaturalEnd.{uA, max uA uM} A,
         (E : IdempotentedRingRightLimit A → NondegenerateModuleNaturalEnd.{uA, max uA uM} A) =
           (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA :
             IdempotentedRingRightLimit A → NondegenerateModuleNaturalEnd.{uA, max uA uM} A) ∧
         (E.symm : NondegenerateModuleNaturalEnd.{uA, max uA uM} A →
             IdempotentedRingRightLimit A) =
           (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA :
             NondegenerateModuleNaturalEnd.{uA, max uA uM} A → IdempotentedRingRightLimit A)) :=
  rfl

/-! The expected types below supply the named operations explicitly. The global
categorical endomorphism semiring may win instance search; it is definitionally
the projection of the named inherited ring, so these check that exact interface. -/

noncomputable example (hA : IsIdempotented A) :
    @RingHom (IdempotentedRingRightLimit A)
      (NondegenerateModuleNaturalEnd.{uA, max uA uM} A)
      (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring
      (NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A).toNonAssocSemiring :=
  IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA

noncomputable example (hA : IsIdempotented A) :
    @RingHom (NondegenerateModuleNaturalEnd.{uA, max uA uM} A)
      (IdempotentedRingRightLimit A)
      (NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A).toNonAssocSemiring
      (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring :=
  NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA

example (hA : IsIdempotented A) :
    FamilyCompositeIdentity.{uA, uM} hA =
      (let r := (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring
       let t := (NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A).toNonAssocSemiring
       @RingHom.comp _ _ _ r t r
           (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA)
           (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA) =
         @RingHom.id (IdempotentedRingRightLimit A) r) := rfl

example (hA : IsIdempotented A) :
    NaturalEndCompositeIdentity.{uA, uM} hA =
      (let r := (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring
       let t := (NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A).toNonAssocSemiring
       @RingHom.comp _ _ _ t r t
           (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA)
           (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA) =
         @RingHom.id (NondegenerateModuleNaturalEnd.{uA, max uA uM} A) t) := rfl

example (hA : IsIdempotented A) :
    FamilyRecovery.{uA, uM} hA =
      (let r := (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring
       let t := (NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A).toNonAssocSemiring
       ∀ x : IdempotentedRingRightLimit A,
         @DFunLike.coe _ _ _ (@RingHom.instFunLike _ _ t r)
             (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA)
             (@DFunLike.coe _ _ _ (@RingHom.instFunLike _ _ r t)
               (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA) x) =
           x) := rfl

example (hA : IsIdempotented A) :
    NaturalEndRecovery.{uA, uM} hA =
      (let r := (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring
       let t := (NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A).toNonAssocSemiring
       ∀ θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A,
         @DFunLike.coe _ _ _ (@RingHom.instFunLike _ _ r t)
             (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA)
             (@DFunLike.coe _ _ _ (@RingHom.instFunLike _ _ t r)
               (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA) θ) =
           θ) := rfl

example (hA : IsIdempotented A) :
    SpecifiedRingEquivalence.{uA, uM} hA =
      (letI := IdempotentedRingRightLimit.ring hA
       letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
       ∃ E : @RingEquiv (IdempotentedRingRightLimit A)
          (NondegenerateModuleNaturalEnd.{uA, max uA uM} A)
          (IdempotentedRingRightLimit.ring hA).toMul
          (NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A).toMul
          (IdempotentedRingRightLimit.ring hA).toAdd
          (NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A).toAdd,
        E.toFun = (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA).toFun ∧
        E.invFun = (NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA).toFun) :=
  rfl

end CompetingEndAndFamilyRings

/-! Zero rings stay within the aggregate, which specializes to the ambient ring. -/
section ZeroRings

variable {A : Type uA} [NonUnitalRing A] [Subsingleton A]

example (h : Classification.{uA, uM}) (hA : IsIdempotented A) :
    FamilyCompositeIdentity.{uA, uM} hA ∧ NaturalEndCompositeIdentity.{uA, uM} hA ∧
      FamilyRecovery.{uA, uM} hA ∧ NaturalEndRecovery.{uA, uM} hA ∧
      ComponentRecovery.{uA, uM} hA ∧ ComponentPointRecovery.{uA, uM} hA ∧
      CoordinateRecovery.{uA, uM} hA ∧ SpecifiedRingEquivalence.{uA, uM} hA :=
  h A inferInstance hA

end ZeroRings

end NondegenerateModuleNaturalEndClassificationStatement
end Langlands.Algebra
