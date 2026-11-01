import Langlands.Algebra.NonUnitalModuleCornerInductionStatements

/-!
# The actual fixed-part induction isomorphism and naturality

An additive proof of Renard (9 July 2026), I.3.2, formula (I.3.2.1).
The inverse descends the balanced sandwich pairing through the original quotient.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalModuleCornerInduction

open CategoryTheory

universe uA uZ uZ'

variable {A : Type uA} [NonUnitalRing A]

attribute [local instance] rightCornerModule cornerModule tensorModule

private theorem sandwich_zero (e : Idempotent A) : sandwichCorner e 0 = 0 := by
  apply Subtype.ext
  change (e : A) * 0 * e = 0
  rw [mul_zero, zero_mul]

private theorem sandwich_add (e : Idempotent A) (a b : A) :
    sandwichCorner e (a + b) = sandwichCorner e a + sandwichCorner e b := by
  apply Subtype.ext
  change (e : A) * (a + b) * e = e * a * e + e * b * e
  rw [mul_add, add_mul]

private theorem sandwich_self (e : Idempotent A) : sandwichCorner e (e : A) = 1 := by
  apply Subtype.ext
  change (e : A) * e * e = e
  rw [e.property.eq, e.property.eq]

private theorem sandwich_left (e : Idempotent A) (a : A) :
    sandwichCorner e ((e : A) * a) = sandwichCorner e a := by
  apply Subtype.ext
  change (e : A) * (e * a) * e = e * a * e
  rw [← mul_assoc, e.property.eq]

private theorem sandwich_right_corner (e : Idempotent A) (a : A)
    (c : Idempotent.Corner e) :
    sandwichCorner e (a * Idempotent.Corner.toAmbient e c) = sandwichCorner e a * c := by
  apply Subtype.ext
  change (e : A) * (a * c.val) * e = (e * a * e) * c.val
  have hc := (Idempotent.mem_corner_iff e c.val).mp c.property
  simp only [mul_assoc, hc.1, hc.2]

section Pointwise

variable (e : Idempotent A) (Z : Type uZ) [AddCommGroup Z]
  [Module (Idempotent.Corner e) Z]

/-- The biadditive sandwich pairing on the original additive groups. -/
def sandwichPairing : A →+ Z →+ Z where
  toFun a :=
    { toFun := fun z => sandwichCorner e a • z
      map_zero' := smul_zero _
      map_add' := smul_add _ }
  map_zero' := by
    ext z
    change sandwichCorner e 0 • z = 0
    rw [sandwich_zero, zero_smul]
  map_add' a b := by
    ext z
    change sandwichCorner e (a + b) • z = sandwichCorner e a • z + sandwichCorner e b • z
    rw [sandwich_add, add_smul]

/-- Balancing uses the original right corner multiplication, without a unit law on `A`. -/
theorem sandwichPairing_balanced :
    NonUnitalModuleTensor.IsBalanced (Idempotent.Corner e) (sandwichPairing e Z) := by
  intro c a z
  change sandwichCorner e (a * Idempotent.Corner.toAmbient e c) • z =
    sandwichCorner e a • (c • z)
  rw [sandwich_right_corner, mul_smul]

/-- The actual additive descent through the published balanced quotient. -/
def sandwichLift : Tensor e Z →+ Z :=
  NonUnitalModuleTensor.lift (Idempotent.Corner e)
    (sandwichPairing e Z) (sandwichPairing_balanced e Z)

@[simp] theorem sandwichLift_tmul (a : A) (z : Z) :
    sandwichLift e Z (tmul e a z) = sandwichCorner e a • z := rfl

/-- The canonical pure-tensor map with the published fixed-part corner action. -/
def fixedPartLinearMap : Z →ₗ[Idempotent.Corner e] InducedFixedPart e Z where
  toFun := fixedPartPureTensor e
  map_add' z w := by
    apply Subtype.ext
    exact NonUnitalModuleTensor.tmul_add (Idempotent.Corner e) A Z (e : A) z w
  map_smul' c z := by
    apply Subtype.ext
    change tmul e (e : A) (c • z) =
      (tensorModule e Z).toDistribSMul.toSMul.smul c.val (tmul e (e : A) z)
    rw [tensorModule_smul_tmul, ← tmul_balanced]
    have hc := (Idempotent.mem_corner_iff e c.val).mp c.property
    change tmul e ((e : A) * c.val) z = tmul e (c.val * e) z
    rw [hc.1, hc.2]

/-- The first inverse law is the unit law in the ordinary corner module. -/
theorem sandwichLift_fixedPartLinearMap (z : Z) :
    sandwichLift e Z (fixedPartLinearMap e Z z).val = z := by
  change sandwichLift e Z (tmul e (e : A) z) = z
  rw [sandwichLift_tmul, sandwich_self, one_smul]

/-- Equality of entire additive maps; balancing proves the other inverse on every tensor. -/
theorem fixedPartLinearMap_comp_sandwichLift :
    (fixedPartLinearMap e Z).toAddMonoidHom.comp (sandwichLift e Z) =
      NonUnitalModuleCorner.projection
        (M := Tensor e Z) (hM := tensorModule e Z) e := by
  apply NonUnitalModuleTensor.hom_ext (Idempotent.Corner e)
  intro a z
  apply Subtype.ext
  change tmul e (e : A) (sandwichCorner e a • z) =
    (tensorModule e Z).toDistribSMul.toSMul.smul (e : A) (tmul e a z)
  rw [tensorModule_smul_tmul, ← tmul_balanced]
  change tmul e ((e : A) * (e * a * e)) z = tmul e ((e : A) * a) z
  rw [← mul_assoc (e : A) ((e : A) * a) (e : A),
    ← mul_assoc (e : A) (e : A) a, e.property.eq]
  exact (tmul_balanced e (1 : Idempotent.Corner e) ((e : A) * a) z).trans
    (by rw [one_smul])

/-- The explicit equivalence on the actual quotient's fixed subtype. -/
def fixedPartEquivalence : Z ≃ₗ[Idempotent.Corner e] InducedFixedPart e Z :=
  { fixedPartLinearMap e Z with
    invFun := fun x => sandwichLift e Z x.val
    left_inv := sandwichLift_fixedPartLinearMap e Z
    right_inv := by
      intro x
      have h := DFunLike.congr_fun (fixedPartLinearMap_comp_sandwichLift e Z) x.val
      exact h.trans (Subtype.ext x.property) }

/-- The explicit equivalence meets all the published canonicality conditions. -/
theorem fixedPartEquivalence_canonical :
    CanonicalFixedPartEquivalence e Z (fixedPartEquivalence e Z) := by
  refine ⟨rfl, fun _ => rfl, ?_, ?_, ?_⟩
  · intro a z
    change sandwichLift e Z
      ((tensorModule e Z).toDistribSMul.toSMul.smul (e : A) (tmul e a z)) = _
    rw [tensorModule_smul_tmul, sandwichLift_tmul, sandwich_left]
  · ext z
    exact (fixedPartEquivalence e Z).symm_apply_apply z
  · ext x
    exact (fixedPartEquivalence e Z).apply_symm_apply x

end Pointwise

/-- Closed pointwise existence, without any local-unit hypothesis. -/
theorem cornerInductionFixedPartEquivalence :
    CornerInductionFixedPartEquivalenceTheorem.{uA, uZ} := by
  intro A _ e Z _ _
  exact ⟨fixedPartEquivalence e Z, fixedPartEquivalence_canonical e Z⟩

/-- Both whole-map naturality laws hold for any two canonical witnesses. -/
theorem cornerInductionFixedPartNaturality :
    CornerInductionFixedPartNaturalityTheorem.{uA, uZ, uZ'} := by
  intro A _ e Z Z' _ _ _ _ f E E' hE hE'
  have hf : E'.toLinearMap.comp f = (restrictedInducedMap e f).comp E.toLinearMap := by
    ext z
    apply Subtype.ext
    change (E' (f z)).val = inducedMap e f (E z).val
    rw [hE'.2.1, hE.2.1, inducedMap_tmul]
  refine ⟨hf, ?_⟩
  ext x
  apply E'.injective
  change E' (E'.symm (restrictedInducedMap e f x)) = E' (f (E.symm x))
  rw [E'.apply_symm_apply]
  have h := LinearMap.congr_fun hf (E.symm x)
  change E' (f (E.symm x)) = restrictedInducedMap e f (E (E.symm x)) at h
  rw [E.apply_symm_apply] at h
  exact h.symm

/-- The universe-correct canonical comparison, using Mathlib's actual lift functor. -/
def fixedPartNaturalIso (e : Idempotent A) :
    ModuleCat.uliftFunctor.{uA, uZ} (Idempotent.Corner e) ≅
      fixedPartInductionFunctor.{uA, uZ} e :=
  NatIso.ofComponents (fun Z =>
    ((ULift.moduleEquiv : ULift.{uA, uZ} Z ≃ₗ[Idempotent.Corner e] Z).trans
      (fixedPartEquivalence e Z)).toModuleIso) (by
    intro Z Z' f
    ext z
    apply Subtype.ext
    change tmul e (e : A) (f.hom z.down) = inducedMap e f.hom (tmul e (e : A) z.down)
    rw [inducedMap_tmul])

/-- The entire components in both directions are the specified canonical maps. -/
theorem fixedPartNaturalIso_canonical (e : Idempotent A) :
    CanonicalFixedPartNaturalIso e (fixedPartNaturalIso.{uA, uZ} e) := by
  intro Z
  exact ⟨fixedPartEquivalence e Z, fixedPartEquivalence_canonical e Z,
    rfl, rfl, fun _ => rfl⟩

/-- Closed ambient natural-isomorphism existence over any associative nonunital ring. -/
theorem cornerInductionFixedPartNaturalIso :
    CornerInductionFixedPartNaturalIsoTheorem.{uA, uZ} := by
  intro A _ e
  exact ⟨fixedPartNaturalIso e, fixedPartNaturalIso_canonical e⟩

/-- The identical components give the published nondegenerate-category adapter. -/
theorem nondegenerateCornerInductionFixedPartNaturalIso :
    NondegenerateCornerInductionFixedPartNaturalIsoTheorem.{uA, uZ} := by
  intro A _ hA e
  exact ⟨fixedPartNaturalIso e, fixedPartNaturalIso_canonical e⟩

/-- Renard I.3.2.1 on the actual balanced quotient, with all four closed conclusions. -/
theorem cornerInductionFixedPart : CornerInductionFixedPartTheorem.{uA, uZ, uZ'} :=
  ⟨cornerInductionFixedPartEquivalence, cornerInductionFixedPartNaturality,
    cornerInductionFixedPartNaturalIso, nondegenerateCornerInductionFixedPartNaturalIso⟩

end Langlands.Algebra.NonUnitalModuleCornerInduction
