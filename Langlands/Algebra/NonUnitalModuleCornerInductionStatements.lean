import Langlands.Algebra.NonUnitalModuleCornerInduction
import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Statements for the actual fixed-part induction isomorphism

Renard (9 July 2026), I.3.2, formula (I.3.2.1), printed p.20/PDF26.
The closed targets below are unproved arbitrary-ring additive statements.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalModuleCornerInduction

open CategoryTheory

universe uA uZ uZ'

variable {A : Type uA} [NonUnitalRing A]

/-- The actual corner element with ambient value `e * a * e`. -/
def sandwichCorner (e : Idempotent A) (a : A) : Idempotent.Corner e :=
  ⟨(e : A) * a * e, (Idempotent.mem_corner_iff_exists e _).mpr ⟨a, rfl⟩⟩

theorem sandwichCorner_val (e : Idempotent A) (a : A) :
    (sandwichCorner e a).val = (e : A) * a * e := rfl

/-- The published fixed subtype of the actual ambient induced object. -/
abbrev InducedFixedPart (e : Idempotent A) (Z : Type uZ) [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z] :=
  NonUnitalModuleCorner.FixedPart e (ambientObject e Z)

/-- The specified pure tensor, including its intrinsic fixed-subtype membership. -/
def fixedPartPureTensor (e : Idempotent A) {Z : Type uZ} [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z] (z : Z) : InducedFixedPart e Z :=
  ⟨tmul e (e : A) z, by
    change (tensorModule e Z).toDistribSMul.toSMul.smul (e : A) (tmul e (e : A) z) =
      tmul e (e : A) z
    rw [tensorModule_smul_tmul, e.property.eq]⟩

theorem fixedPartPureTensor_val (e : Idempotent A) {Z : Type uZ} [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z] (z : Z) :
    (fixedPartPureTensor e z).val = tmul e (e : A) z := rfl

/-- Canonicality specifies whole functions, tensor evaluations and whole-map inverse laws. -/
def CanonicalFixedPartEquivalence (e : Idempotent A) (Z : Type uZ) [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z]
    (E : Z ≃ₗ[Idempotent.Corner e] InducedFixedPart e Z) : Prop :=
  (⇑E = fixedPartPureTensor e) ∧
  (∀ z : Z, (E z).val = tmul e (e : A) z) ∧
  (∀ (a : A) (z : Z),
    E.symm (NonUnitalModuleCorner.projection
      (M := Tensor e Z) (hM := tensorModule e Z) e (tmul e a z)) =
        sandwichCorner e a • z) ∧
  E.symm.toLinearMap.comp E.toLinearMap = LinearMap.id ∧
  E.toLinearMap.comp E.symm.toLinearMap = LinearMap.id

/-- Restriction of the entire original `id ⊗ f`, with both named residual actions. -/
def restrictedInducedMap (e : Idempotent A) {Z : Type uZ} {Z' : Type uZ'}
    [AddCommGroup Z] [AddCommGroup Z']
    [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z']
    (f : Z →ₗ[Idempotent.Corner e] Z') :
    InducedFixedPart e Z →ₗ[Idempotent.Corner e] InducedFixedPart e Z' :=
  NonUnitalModuleCorner.restrict
    (M := Tensor e Z) (N := Tensor e Z')
    (hM := tensorModule e Z) (hN := tensorModule e Z') e (inducedMap e f)

/-- Both naturality directions are equalities of entire corner-linear maps. -/
def FixedPartEquivalenceNaturality (e : Idempotent A) {Z : Type uZ} {Z' : Type uZ'}
    [AddCommGroup Z] [AddCommGroup Z']
    [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z']
    (f : Z →ₗ[Idempotent.Corner e] Z')
    (E : Z ≃ₗ[Idempotent.Corner e] InducedFixedPart e Z)
    (E' : Z' ≃ₗ[Idempotent.Corner e] InducedFixedPart e Z') : Prop :=
  E'.toLinearMap.comp f = (restrictedInducedMap e f).comp E.toLinearMap ∧
  E'.symm.toLinearMap.comp (restrictedInducedMap e f) = f.comp E.symm.toLinearMap

/-- Unconditional canonical existence for independent ring and module universes. -/
def CornerInductionFixedPartEquivalenceTheorem : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    ∃ E : Z ≃ₗ[Idempotent.Corner e] InducedFixedPart e Z,
      CanonicalFixedPartEquivalence e Z E

/-- Closed whole-map naturality for independently sized source and target carriers. -/
def CornerInductionFixedPartNaturalityTheorem : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (e : Idempotent A)
    (Z : Type uZ) (Z' : Type uZ') [AddCommGroup Z] [AddCommGroup Z']
    [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z']
    (f : Z →ₗ[Idempotent.Corner e] Z')
    (E : Z ≃ₗ[Idempotent.Corner e] InducedFixedPart e Z)
    (E' : Z' ≃ₗ[Idempotent.Corner e] InducedFixedPart e Z'),
    CanonicalFixedPartEquivalence e Z E →
    CanonicalFixedPartEquivalence e Z' E' →
    FixedPartEquivalenceNaturality e f E E'

/-- The transparent actual induction followed by the published ambient fixed-part functor. -/
abbrev fixedPartInductionFunctor (e : Idempotent A) :
    ModuleCat.{uZ} (Idempotent.Corner e) ⥤
      ModuleCat.{max uA uZ} (Idempotent.Corner e) :=
  ambientFunctor e ⋙ NonUnitalModuleCorner.functor e

/-- Canonical actual components, in both directions, of the universe-correct natural iso. -/
def CanonicalFixedPartNaturalIso (e : Idempotent A)
    (iso : ModuleCat.uliftFunctor.{uA, uZ} (Idempotent.Corner e) ≅
      fixedPartInductionFunctor.{uA, uZ} e) : Prop :=
  ∀ Z : ModuleCat.{uZ} (Idempotent.Corner e),
    ∃ E : Z ≃ₗ[Idempotent.Corner e] InducedFixedPart e Z,
      CanonicalFixedPartEquivalence e Z E ∧
      (iso.hom.app Z).hom = E.toLinearMap.comp
        (ULift.moduleEquiv : ULift.{uA, uZ} Z ≃ₗ[Idempotent.Corner e] Z).toLinearMap ∧
      (iso.inv.app Z).hom =
        (ULift.moduleEquiv : ULift.{uA, uZ} Z ≃ₗ[Idempotent.Corner e] Z).symm.toLinearMap.comp
          E.symm.toLinearMap ∧
      ∀ z : Z, ((iso.hom.app Z).hom (ULift.up z)).val = tmul e (e : A) z

/-- Existence of the actual canonical natural iso is a conclusion. -/
def CornerInductionFixedPartNaturalIsoTheorem : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (e : Idempotent A),
    ∃ iso : ModuleCat.uliftFunctor.{uA, uZ} (Idempotent.Corner e) ≅
      fixedPartInductionFunctor.{uA, uZ} e,
      CanonicalFixedPartNaturalIso e iso

/-- The source's actual composite through the nondegenerate category. -/
abbrev nondegenerateFixedPartInductionFunctor (hA : IsIdempotented A) (e : Idempotent A) :
    ModuleCat.{uZ} (Idempotent.Corner e) ⥤
      ModuleCat.{max uA uZ} (Idempotent.Corner e) :=
  nondegenerateFunctor hA e ⋙ NonUnitalModuleCorner.nondegenerateFunctor e

/-- Equality of the entire functors, retaining all original objects, actions and maps. -/
theorem nondegenerateFixedPartInductionFunctor_eq (hA : IsIdempotented A)
    (e : Idempotent A) :
    nondegenerateFixedPartInductionFunctor.{uA, uZ} hA e =
      fixedPartInductionFunctor.{uA, uZ} e := rfl

/-- The source-category adapter has the identical canonical component conditions. -/
def NondegenerateCornerInductionFixedPartNaturalIsoTheorem : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A),
    ∃ iso : ModuleCat.uliftFunctor.{uA, uZ} (Idempotent.Corner e) ≅
      nondegenerateFixedPartInductionFunctor.{uA, uZ} hA e,
      CanonicalFixedPartNaturalIso e iso

/-- The single exact proof-successor target bundles all four closed assertions. -/
def CornerInductionFixedPartTheorem : Prop :=
  CornerInductionFixedPartEquivalenceTheorem.{uA, uZ} ∧
  CornerInductionFixedPartNaturalityTheorem.{uA, uZ, uZ'} ∧
  CornerInductionFixedPartNaturalIsoTheorem.{uA, uZ} ∧
  NondegenerateCornerInductionFixedPartNaturalIsoTheorem.{uA, uZ}

end Langlands.Algebra.NonUnitalModuleCornerInduction
