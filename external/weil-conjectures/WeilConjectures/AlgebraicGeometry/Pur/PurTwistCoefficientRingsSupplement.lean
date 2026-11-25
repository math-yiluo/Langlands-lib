/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Functor.EpiMono
public import WeilConjectures.AlgebraicGeometry.PurTwistCoefficientRings

/-! # Coefficient rings of the integral Tate twist

The constant and completed coefficient rings, their quotient projections, and the
canonical comparison form the coefficient data used before constructing the Tate line.

## References

* Stacks Tag 03PK
* Stacks Tag 03CO
* Stacks Tag 03EK
-/

@[expose] public section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
variable (S : Scheme.{t}) (l : ℕ) [Fact l.Prime]

/-- The constant discrete `Z_l` ring sheaf. -/
noncomputable abbrev purTwistZlConstantOfUniverses :=
  (constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{max u (t + 1)} ℤ_[l]))

/-- Reduction of constant finite coefficient rings. -/
noncomputable def purTwistFiniteTransitionOfUniverses (n : ℕ) :
    purTwistFiniteRingOfUniverses S l (n + 1) ⟶ purTwistFiniteRingOfUniverses S l n :=
  (constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1))) (ZMod (l ^ (n + 1)))).comp
        ULift.ringEquiv.toRingHom)))

/-- The positive finite coefficient inverse system. It is reducible, so unfolding the
tied-universe name `purTwistZlTower` still exposes `Functor.ofOpSequence` to `simp`. -/
noncomputable abbrev purTwistZlTowerOfUniverses :=
  Functor.ofOpSequence (purTwistFiniteTransitionOfUniverses S l)

/-- The completed `Z_l` coefficient sheaf, as the specified inverse limit. -/
noncomputable def purTwistZlCompletionOfUniverses := limit (purTwistZlTowerOfUniverses S l)

/-- The coefficient projection to exponent `n + 1`. -/
noncomputable def purTwistZlProjectionOfUniverses (n : ℕ) :
    purTwistZlCompletionOfUniverses S l ⟶ purTwistFiniteRingOfUniverses S l n :=
  limit.π (purTwistZlTowerOfUniverses S l) (op n)

/-- Constant p-adic reduction. -/
noncomputable def purTwistZlReductionOfUniverses (n : ℕ) :
    purTwistZlConstantOfUniverses S l ⟶ purTwistFiniteRingOfUniverses S l n :=
  (constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((PadicInt.toZModPow (n + 1)).comp ULift.ringEquiv.toRingHom)))

/-- The completion map is uniquely fixed by all finite reductions. -/
theorem purTwistZlCompletionMap_existsUniqueOfUniverses :
    ∃! a : purTwistZlConstantOfUniverses S l ⟶ purTwistZlCompletionOfUniverses S l,
      ∀ n : ℕ, a ≫ purTwistZlProjectionOfUniverses S l n =
        purTwistZlReductionOfUniverses S l n := by
  let c : Cone (purTwistZlTowerOfUniverses S l) :=
    { pt := purTwistZlConstantOfUniverses S l
      π := NatTrans.ofOpSequence (purTwistZlReductionOfUniverses S l) (by
        intro n
        change 𝟙 _ ≫ _ = _
        rw [Category.id_comp]
        simp only [purTwistZlTowerOfUniverses,
          Functor.ofOpSequence_map_homOfLE_succ]
        dsimp [purTwistZlReductionOfUniverses, purTwistFiniteTransitionOfUniverses]
        rw [← Functor.map_comp]
        congr 1
        ext z
        exact DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow
          (n + 1) (n + 1 + 1) (Nat.le_succ _)).symm z.down) }
  refine ⟨limit.lift _ c, ?_, ?_⟩
  · intro n
    exact limit.lift_π c (op n)
  · intro a ha
    apply limit.hom_ext
    intro n
    exact (ha n.unop).trans (limit.lift_π c n).symm

/-- The actual constant-to-completed coefficient map, fixed by its residue projections. -/
noncomputable def purTwistZlCompletionMapOfUniverses :=
  (purTwistZlCompletionMap_existsUniqueOfUniverses S l).exists.choose

/-- The constant discrete `Z_l` ring sheaf. -/
noncomputable abbrev purTwistZlConstant :=
  purTwistZlConstantOfUniverses.{t, t} S l

/-- Reduction of constant finite coefficient rings. -/
noncomputable abbrev purTwistFiniteTransition (n : ℕ) :
    purTwistFiniteRing S l (n + 1) ⟶ purTwistFiniteRing S l n :=
  purTwistFiniteTransitionOfUniverses.{t, t} S l n

/-- The positive finite coefficient inverse system. -/
noncomputable abbrev purTwistZlTower :=
  purTwistZlTowerOfUniverses.{t, t} S l

/-- The completed `Z_l` coefficient sheaf, as the specified inverse limit. -/
noncomputable abbrev purTwistZlCompletion :=
  purTwistZlCompletionOfUniverses.{t, t} S l

/-- The coefficient projection to exponent `n + 1`. -/
noncomputable abbrev purTwistZlProjection (n : ℕ) :
    purTwistZlCompletion S l ⟶ purTwistFiniteRing S l n :=
  purTwistZlProjectionOfUniverses.{t, t} S l n

/-- Constant p-adic reduction. -/
noncomputable abbrev purTwistZlReduction (n : ℕ) :
    purTwistZlConstant S l ⟶ purTwistFiniteRing S l n :=
  purTwistZlReductionOfUniverses.{t, t} S l n

/-- The completion map is uniquely fixed by all finite reductions. -/
theorem purTwistZlCompletionMap_existsUnique :
    ∃! a : purTwistZlConstant S l ⟶ purTwistZlCompletion S l,
      ∀ n : ℕ, a ≫ purTwistZlProjection S l n = purTwistZlReduction S l n := by
  exact purTwistZlCompletionMap_existsUniqueOfUniverses.{t, t} S l

/-- The actual constant-to-completed coefficient map, fixed by its residue projections. -/
noncomputable abbrev purTwistZlCompletionMap :=
  purTwistZlCompletionMapOfUniverses.{t, t} S l

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical `Z_l` inclusion into the extension's valuation ring is fixed in the field. -/
theorem purTwistIntegersMap_existsUnique :
    ∃! i : ℤ_[l] →+* Padic.coefficientExtensionIntegers l E,
      ∀ z : ℤ_[l], (i z : E) = algebraMap ℚ_[l] E (z : ℚ_[l]) := by
  have hO := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec.1
  let i : ℤ_[l] →+* Padic.coefficientExtensionIntegers l E :=
    ((algebraMap ℚ_[l] E).comp (algebraMap ℤ_[l] ℚ_[l])).codRestrict _ (by
      intro z
      apply (hO _).2
      change spectralNorm ℚ_[l] E (algebraMap ℚ_[l] E (z : ℚ_[l])) ≤ 1
      rw [spectralNorm_extends]
      exact z.property)
  refine ⟨i, fun z ↦ rfl, ?_⟩
  intro j hj
  ext z
  exact (hj z).trans rfl

/-- The canonical inclusion, chosen from its equality in the coefficient field. -/
noncomputable def purTwistIntegersMap := (purTwistIntegersMap_existsUnique l E).exists.choose

/-- The constant valuation-ring sheaf. -/
noncomputable abbrev purTwistIntegralConstant :=
  (constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))

/-- The constant scalar-extension map induced by the field inclusion. -/
noncomputable def purTwistConstantIntegersMap :
    purTwistZlConstantOfUniverses S l ⟶ purTwistIntegralConstant S l E :=
  (constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((purTwistIntegersMap l E).comp ULift.ringEquiv.toRingHom)))

/-- The canonical quotient of the discrete valuation-ring sheaf. -/
noncomputable def purTwistIntegralQuotient (n : ℕ) :
    purTwistIntegralConstant S l E ⟶
      WeilConjectures.integralCoefficientCommRingSheaf l E S n :=
  (constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
        ULift.ringEquiv.toRingHom)))

/-- The constant valuation ring maps canonically into its completion. -/
theorem purTwistIntegralCompletionMap_existsUnique :
    ∃! a : purTwistIntegralConstant S l E ⟶
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S,
      ∀ n : ℕ, a ≫ WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n =
        purTwistIntegralQuotient S l E n := by
  let F := sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let c : Cone (WeilConjectures.integralCoefficientSheafSystem l E S) :=
    { pt := F.obj (purTwistIntegralConstant S l E)
      π := NatTrans.ofOpSequence
        (fun n ↦ F.map (purTwistIntegralQuotient S l E n)) (by
          intro n
          change 𝟙 _ ≫ _ = _
          rw [Category.id_comp]
          simp only [WeilConjectures.integralCoefficientSheafSystem,
            Functor.ofOpSequence_map_homOfLE_succ]
          dsimp [F, purTwistIntegralQuotient,
            WeilConjectures.integralCoefficientSheafTransition]
          rw [← Functor.map_comp, ← Functor.map_comp]
          congr 1) }
  let a : purTwistIntegralConstant S l E ⟶
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S :=
    F.preimage (limit.lift _ c)
  have ha : ∀ n : ℕ,
      a ≫ WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n =
        purTwistIntegralQuotient S l E n := by
    intro n
    apply F.map_injective
    rw [Functor.map_comp]
    dsimp only [a]
    rw [Functor.map_preimage]
    exact limit.lift_π c (op n)
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply F.map_injective
  apply limit.hom_ext
  intro n
  exact (F.map_comp _ _).symm.trans
    ((congrArg F.map ((hb n.unop).trans (ha n.unop).symm)).trans (F.map_comp _ _))

/-- The actual constant-to-completed valuation-ring map. -/
noncomputable def purTwistIntegralCompletionMap :=
  (purTwistIntegralCompletionMap_existsUnique S l E).exists.choose

/-- A completed scalar map is canonical when each finite projection factors through a
finite p-adic quotient with the specified constant residues. The index is allowed to depend
on the target quotient, as required for ramified extensions. -/
def IsPurTwistCompletedScalarMap
    (a : purTwistZlCompletionOfUniverses S l ⟶
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S) : Prop :=
  ∀ n : ℕ, ∃ (k : ℕ) (q : ZMod (l ^ (k + 1)) →+* Padic.coefficientExtensionRing l E (n + 1)),
    (∀ z : ℤ_[l], q (PadicInt.toZModPow (k + 1) z) =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
        (purTwistIntegersMap l E z)) ∧
    a ≫ WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n =
      purTwistZlProjectionOfUniverses S l k ≫
        (constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).map
          (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
            (q.comp ULift.ringEquiv.toRingHom)))

private theorem purTwistZlReduction_epi (n : ℕ) :
    Epi (purTwistZlReductionOfUniverses.{t, u} S l n) := by
  let q : CommRingCat.of (ULift.{max u (t + 1)} ℤ_[l]) ⟶
      CommRingCat.of (ULift.{max u (t + 1)} (ZMod (l ^ (n + 1)))) :=
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((PadicInt.toZModPow (n + 1)).comp ULift.ringEquiv.toRingHom))
  have : Epi q := ConcreteCategory.epi_of_surjective q (by
    intro x
    obtain ⟨z, hz⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow (n + 1)) x.down
    exact ⟨ULift.up z, congrArg ULift.up hz⟩)
  change Epi ((constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).map q)
  let := (constantSheafAdj (ProEt.topology S) CommRingCat.{max u (t + 1)}
    (MorphismProperty.Over.mkIdTerminal _ _)).isLeftAdjoint
  infer_instance

private theorem purTwistZlFiniteFactor_ext
    {B : Sheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}} (k m : ℕ)
    (f : purTwistFiniteRingOfUniverses S l k ⟶ B) (g : purTwistFiniteRingOfUniverses S l m ⟶ B)
    (h : purTwistZlReductionOfUniverses S l k ≫ f = purTwistZlReductionOfUniverses S l m ≫ g) :
    purTwistZlProjectionOfUniverses S l k ≫ f = purTwistZlProjectionOfUniverses S l m ≫ g := by
  let t := max k m
  let p (i : ℕ) (hi : i ≤ t) := (purTwistZlTowerOfUniverses S l).map (homOfLE hi).op
  have hp (i : ℕ) (hi : i ≤ t) :
      purTwistZlProjectionOfUniverses S l t ≫ p i hi = purTwistZlProjectionOfUniverses S l i :=
    limit.w (purTwistZlTowerOfUniverses S l) (homOfLE hi).op
  have hr (i : ℕ) (hi : i ≤ t) :
      purTwistZlReductionOfUniverses S l t ≫ p i hi = purTwistZlReductionOfUniverses S l i := by
    have hz (j : ℕ) := (purTwistZlCompletionMap_existsUniqueOfUniverses S l).exists.choose_spec j
    change ∀ j, purTwistZlCompletionMapOfUniverses S l ≫ purTwistZlProjectionOfUniverses S l j =
      purTwistZlReductionOfUniverses S l j at hz
    rw [← hz t, Category.assoc, hp, hz i]
  have : Epi (purTwistZlReductionOfUniverses S l t) := purTwistZlReduction_epi S l t
  have he : p k (le_max_left k m) ≫ f = p m (le_max_right k m) ≫ g := by
    apply (cancel_epi (purTwistZlReductionOfUniverses S l t)).mp
    simpa only [← Category.assoc, hr] using h
  rw [← hp k (le_max_left k m), ← hp m (le_max_right k m),
    Category.assoc, Category.assoc, he]

/-- The completed scalar map is uniquely determined by its finite quotient formulas. -/
theorem purTwistCompletedScalarMap_existsUnique :
    ∃! a : purTwistZlCompletionOfUniverses S l ⟶
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S,
      IsPurTwistCompletedScalarMap S l E a := by
  classical
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    apply (h.2.1 _).2
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E), spectralNorm_extends]
    exact Padic.norm_p_lt_one
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hq (n : ℕ) : ∃ q : ZMod (l ^ (n + 1)) →+*
      Padic.coefficientExtensionRing l E (n + 1),
      ∀ z : ℤ_[l], q (PadicInt.toZModPow (n + 1) z) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
          (purTwistIntegersMap l E z) := by
    let g := (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
      (purTwistIntegersMap l E)
    have hker : RingHom.ker (PadicInt.toZModPow (n + 1)) ≤ RingHom.ker g := by
      rw [PadicInt.ker_toZModPow, Ideal.span_le, Set.singleton_subset_iff]
      change Ideal.Quotient.mk _ ((purTwistIntegersMap l E) ((l : ℤ_[l]) ^ (n + 1))) = 0
      rw [map_pow, map_natCast, Ideal.Quotient.eq_zero_iff_mem]
      change (l : Padic.coefficientExtensionIntegers l E) ^ (n + 1) ∈
        Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
          Set (Padic.coefficientExtensionIntegers l E)) ^ (n + 1)
      rw [hgen]
      exact Ideal.pow_mem_pow hm (n + 1)
    exact ⟨(PadicInt.toZModPow (n + 1)).liftOfSurjective
      (ZMod.ringHom_surjective _) ⟨g, hker⟩,
      fun z ↦ RingHom.liftOfSurjective_comp_apply _ _ _ z⟩
  choose q hq using hq
  let C (n : ℕ) : purTwistFiniteRingOfUniverses S l n ⟶
      WeilConjectures.integralCoefficientCommRingSheaf l E S n :=
    (constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).map
      (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((q n).comp ULift.ringEquiv.toRingHom)))
  let T (n : ℕ) : WeilConjectures.integralCoefficientCommRingSheaf l E S (n + 1) ⟶
      WeilConjectures.integralCoefficientCommRingSheaf l E S n :=
    (constantSheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}).map
      (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp ULift.ringEquiv.toRingHom)))
  have hconst (n : ℕ) : purTwistZlReductionOfUniverses S l n ≫ C n =
      purTwistConstantIntegersMap S l E ≫ purTwistIntegralQuotient S l E n := by
    dsimp [C, purTwistZlReductionOfUniverses, purTwistConstantIntegersMap, purTwistIntegralQuotient]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext z
    exact hq n z.down
  have hquo (n : ℕ) : purTwistIntegralQuotient S l E (n + 1) ≫ T n =
      purTwistIntegralQuotient S l E n := by
    dsimp [T, purTwistIntegralQuotient]
    rw [← Functor.map_comp]
    congr 1
  let b (n : ℕ) := purTwistZlProjectionOfUniverses S l n ≫ C n
  have hb (n : ℕ) : b (n + 1) ≫ T n = b n := by
    dsimp only [b]
    rw [Category.assoc]
    apply purTwistZlFiniteFactor_ext
    rw [← Category.assoc, hconst, Category.assoc, hquo, hconst]
  let F := sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let c : Cone (WeilConjectures.integralCoefficientSheafSystem l E S) :=
    { pt := F.obj (purTwistZlCompletionOfUniverses S l)
      π := NatTrans.ofOpSequence (fun n ↦ F.map (b n)) (by
        intro n
        change 𝟙 _ ≫ _ = _
        rw [Category.id_comp]
        simp only [WeilConjectures.integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ]
        change F.map (b n) = F.map (b (n + 1)) ≫ F.map (T n)
        rw [← Functor.map_comp, hb]) }
  let a : purTwistZlCompletionOfUniverses S l ⟶
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S :=
    F.preimage (limit.lift _ c)
  have ha (n : ℕ) :
      a ≫ WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n = b n := by
    apply F.map_injective
    rw [Functor.map_comp]
    dsimp only [a]
    rw [Functor.map_preimage]
    exact limit.lift_π c (op n)
  refine ⟨a, fun n ↦ ⟨n, q n, hq n, ha n⟩, ?_⟩
  intro a' ha'
  apply F.map_injective
  apply limit.hom_ext
  intro n
  have he : a' ≫ WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n.unop =
      a ≫ WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n.unop := by
    obtain ⟨k, q', hq', hc'⟩ := ha' n.unop
    rw [hc', ha]
    apply purTwistZlFiniteFactor_ext
    dsimp [C, purTwistZlReductionOfUniverses]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext z
    exact (hq' z.down).trans (hq n.unop z.down).symm
  exact (F.map_comp _ _).symm.trans ((congrArg F.map he).trans (F.map_comp _ _))

/-- The canonical completed scalar map, with its finite quotient characterization. -/
noncomputable def purTwistCompletedScalarMap :=
  (purTwistCompletedScalarMap_existsUnique S l E).exists.choose

/-- The two inclusions of the discrete p-adic ring agree. -/
theorem purTwistCoefficientSquare :
    purTwistZlCompletionMapOfUniverses S l ≫ purTwistCompletedScalarMap S l E =
      purTwistConstantIntegersMap S l E ≫ purTwistIntegralCompletionMap S l E := by
  have hproj (n : ℕ) :
      (purTwistZlCompletionMapOfUniverses S l ≫ purTwistCompletedScalarMap S l E) ≫
          WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n =
        (purTwistConstantIntegersMap S l E ≫ purTwistIntegralCompletionMap S l E) ≫
          WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n := by
    obtain ⟨k, q, hq, hcomp⟩ :=
      (purTwistCompletedScalarMap_existsUnique S l E).exists.choose_spec n
    change purTwistCompletedScalarMap S l E ≫ _ = _ at hcomp
    have hzl := (purTwistZlCompletionMap_existsUniqueOfUniverses S l).exists.choose_spec k
    change purTwistZlCompletionMapOfUniverses S l ≫ _ = _ at hzl
    have hint := (purTwistIntegralCompletionMap_existsUnique S l E).exists.choose_spec n
    change purTwistIntegralCompletionMap S l E ≫ _ = _ at hint
    rw [Category.assoc, hcomp, ← Category.assoc, hzl, Category.assoc, hint]
    dsimp [purTwistZlReductionOfUniverses, purTwistConstantIntegersMap, purTwistIntegralQuotient]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext z
    exact hq z.down
  let F := sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  apply F.map_injective
  apply limit.hom_ext
  intro n
  exact (F.map_comp _ _).symm.trans ((congrArg F.map (hproj n.unop)).trans
    (F.map_comp _ _))

/-- The coefficient comparison is the canonical map from the ring-sheaf tensor (pushout). -/
noncomputable def purTwistCoefficientComparison :=
  pushout.desc (purTwistCompletedScalarMap S l E) (purTwistIntegralCompletionMap S l E)
    (purTwistCoefficientSquare S l E)

end AlgebraicGeometry.Scheme
