import Langlands.Algebra.NondegenerateModuleForgetful
import Mathlib.CategoryTheory.Center.Basic
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# The actual categorical centre and original-image commutant action

Renard I.1.7, printed pp.12–13/PDF18–19. This module constructs the
forward commutant action, without assuming any classification result.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open CategoryTheory

universe uA uM

/-- The actual centre, with original module intertwiners as components. -/
abbrev NondegenerateModuleCenter (A : Type uA) [NonUnitalRing A] :=
  CatCenter (NondegenerateModuleCat.{uA, uM} A)

namespace NondegenerateModuleCenter

variable {A : Type uA} [NonUnitalRing A]

/-- The named ring is the inherited ring on identity natural transformations. -/
@[instance_reducible]
def ring (A : Type uA) [NonUnitalRing A] :
    Ring (NondegenerateModuleCenter.{uA, uM} A) :=
  inferInstanceAs (Ring (CatCenter (NondegenerateModuleCat.{uA, uM} A)))

theorem carrier_eq (A : Type uA) [NonUnitalRing A] :
    NondegenerateModuleCenter.{uA, uM} A =
      CatCenter (NondegenerateModuleCat.{uA, uM} A) := rfl

/-- The named product applies the right factor first, then the left factor. -/
theorem mul_app_toAddMonoidHom (z w : NondegenerateModuleCenter.{uA, uM} A)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    ((@HMul.hMul _ _ _ (@instHMul _ (ring.{uA, uM} A).toMul) z w).app M).hom.toAddMonoidHom =
      (z.app M).hom.toAddMonoidHom.comp (w.app M).hom.toAddMonoidHom := rfl

/-- Apply the actual forgetful functor to every original component. -/
def forget (z : NondegenerateModuleCenter.{uA, uM} A) :
    NondegenerateModuleNaturalEnd.{uA, uM} A where
  app M := (nondegenerateModuleForgetful A).map (z.app M)
  naturality M N f := by
    simpa only [Functor.map_comp] using
      congrArg (fun g : M ⟶ N => (nondegenerateModuleForgetful A).map g) (z.naturality f)

@[simp] theorem forget_app_hom (z : NondegenerateModuleCenter.{uA, uM} A)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    ((forget z).app M).hom = (z.app M).hom.toAddMonoidHom := rfl

theorem forget_app_coe (z : NondegenerateModuleCenter.{uA, uM} A)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    (fun m : M.obj => (forget z).app M m) =
      ((z.app M).hom.toAddMonoidHom : M.obj → M.obj) := rfl

@[simp] theorem forget_app_apply (z : NondegenerateModuleCenter.{uA, uM} A)
    (M : NondegenerateModuleCat.{uA, uM} A) (m : M.obj) :
    (forget z).app M m = (z.app M).hom.toAddMonoidHom m := rfl

/-- Forgetting the original scalar-linearity preserves all inherited ring operations.
Both ring structures in the type are the named ones, given explicitly. -/
def forgetRingHom :
    @RingHom (NondegenerateModuleCenter.{uA, uM} A) (NondegenerateModuleNaturalEnd.{uA, uM} A)
      (ring.{uA, uM} A).toNonAssocSemiring
      (NondegenerateModuleNaturalEnd.ring.{uA, uM} A).toNonAssocSemiring where
  toFun := forget
  map_zero' := by apply NatTrans.ext; funext M; rfl
  map_one' := by apply NatTrans.ext; funext M; rfl
  map_add' := by intro z w; apply NatTrans.ext; funext M; rfl
  map_mul' := by intro z w; apply NatTrans.ext; funext M; rfl

theorem forgetRingHom_coe :
    (forgetRingHom.{uA, uM} (A := A) : NondegenerateModuleCenter.{uA, uM} A →
      NondegenerateModuleNaturalEnd.{uA, uM} A) = forget := rfl

/-- Faithfulness uses original morphism extensionality and needs no regular object. -/
theorem forgetRingHom_injective :
    Function.Injective (forgetRingHom.{uA, uM} (A := A)) := by
  intro z w h
  apply CatCenter.ext
  intro M
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  intro m
  exact congrArg (fun θ : NondegenerateModuleNaturalEnd.{uA, uM} A => θ.app M m) h

/-- The actual centralizer of the canonical original-ring image. -/
def commutantSubring (hA : IsIdempotented A) :
    letI := IdempotentedRingRightLimit.ring hA
    Subring (IdempotentedRingRightLimit A) := by
  letI := IdempotentedRingRightLimit.ring hA
  exact Subring.centralizer (Set.range (IdempotentedRingRightLimit.canonicalRingHom hA))

/-- The actual subtype of commuting compatible right families. -/
abbrev Commutant (hA : IsIdempotented A) := ↥(commutantSubring hA)

/-- The named ring on the actual centralizer subtype. -/
@[instance_reducible]
def commutantRing (hA : IsIdempotented A) : Ring (Commutant hA) := by
  letI := IdempotentedRingRightLimit.ring hA
  exact inferInstanceAs (Ring ↥(commutantSubring hA))

/-- The actual subring inclusion. Both ring structures in the type are the named ones,
given explicitly. -/
def commutantInclusion (hA : IsIdempotented A) :
    @RingHom (Commutant hA) (IdempotentedRingRightLimit A)
      (commutantRing hA).toNonAssocSemiring
      (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring := by
  letI := IdempotentedRingRightLimit.ring hA
  exact (commutantSubring hA).subtype

theorem commutantInclusion_coe (hA : IsIdempotented A) :
    (commutantInclusion hA : Commutant hA → IdempotentedRingRightLimit A) =
      Subtype.val := rfl

theorem commutantSubring_eq (hA : IsIdempotented A) :
    letI := IdempotentedRingRightLimit.ring hA
    commutantSubring hA =
      Subring.centralizer (Set.range (IdempotentedRingRightLimit.canonicalRingHom hA)) := rfl

theorem mem_commutantSubring_iff (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) :
    letI := IdempotentedRingRightLimit.ring hA
    x ∈ commutantSubring hA ↔
      ∀ a : A, IdempotentedRingRightLimit.canonical a * x =
        x * IdempotentedRingRightLimit.canonical a := by
  constructor
  · intro hx a
    exact hx _ ⟨a, rfl⟩
  · intro hx y hy
    obtain ⟨a, rfl⟩ := hy
    exact hx a

theorem commutes (hA : IsIdempotented A) (x : Commutant hA) (a : A) :
    IdempotentedRingRightLimit.product hA (IdempotentedRingRightLimit.canonical a) x.val =
      IdempotentedRingRightLimit.product hA x.val (IdempotentedRingRightLimit.canonical a) :=
  (mem_commutantSubring_iff hA x.val).mp x.property a

/-- Original-linearity follows by acting with the entire commutation equality. -/
theorem action_smul (hA : IsIdempotented A) (x : Commutant hA)
    (M : NondegenerateModuleCat.{uA, uM} A) (a : A) (m : M.obj) :
    IdempotentedRingRightLimit.actionAddHom hA M.property x.val (a • m) =
      a • IdempotentedRingRightLimit.actionAddHom hA M.property x.val m := by
  have h := congrArg
    (fun y => IdempotentedRingRightLimitAction.act M.property y m) (commutes hA x a)
  change IdempotentedRingRightLimitAction.act M.property x.val (a • m) =
    a • IdempotentedRingRightLimitAction.act M.property x.val m
  rw [IdempotentedRingRightLimitAction.product_act hA M.property,
    IdempotentedRingRightLimitAction.product_act hA M.property,
    IdempotentedRingRightLimitAction.canonical_act hA M.property,
    IdempotentedRingRightLimitAction.canonical_act hA M.property] at h
  exact h.symm

/-- The published entire additive action bundled as an original module morphism. -/
def component (hA : IsIdempotented A) (x : Commutant hA)
    (M : NondegenerateModuleCat.{uA, uM} A) : NonUnitalModuleHom A M.obj M.obj where
  toAddMonoidHom := IdempotentedRingRightLimit.actionAddHom hA M.property x.val
  map_smul' := action_smul hA x M

@[simp] theorem component_toAddMonoidHom (hA : IsIdempotented A) (x : Commutant hA)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    (component hA x M).toAddMonoidHom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x.val := rfl

theorem component_coe (hA : IsIdempotented A) (x : Commutant hA)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    (component hA x M : M.obj → M.obj) =
      IdempotentedRingRightLimitAction.act M.property x.val := rfl

@[simp] theorem component_apply (hA : IsIdempotented A) (x : Commutant hA)
    (M : NondegenerateModuleCat.{uA, uM} A) (m : M.obj) :
    component hA x M m = IdempotentedRingRightLimitAction.act M.property x.val m := rfl

theorem component_eq (hA : IsIdempotented A) (x : Commutant hA)
    (M : NondegenerateModuleCat.{uA, uM} A) (m : M.obj) (e : Idempotent A)
    (he : (e : A) • m = m) : component hA x M m = x.val.val e • m :=
  IdempotentedRingRightLimit.actionAddHom_eq hA M.property x.val m e he

/-- The source lemma formula holds for every family, before imposing centrality. -/
theorem action_original_smul (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (M : NondegenerateModuleCat.{uA, uM} A)
    (a : A) (m : M.obj) :
    IdempotentedRingRightLimit.actionAddHom hA M.property x (a • m) =
      IdempotentedRingRightLimit.applyOriginal hA x a • m := by
  classical
  obtain ⟨e, he⟩ := (IsIdempotented.iff_two_sided_local_units.mp hA) {a}
  have hea : (e : A) * a = a := (he a (by simp)).1
  have hem : (e : A) • (a • m) = a • m := by rw [← mul_smul, hea]
  rw [IdempotentedRingRightLimit.actionAddHom_eq hA M.property x (a • m) e hem,
    IdempotentedRingRightLimit.applyOriginal_eq hA x a e hea, mul_smul]

theorem component_original_smul (hA : IsIdempotented A) (x : Commutant hA)
    (M : NondegenerateModuleCat.{uA, uM} A) (a : A) (m : M.obj) :
    component hA x M (a • m) =
      IdempotentedRingRightLimit.applyOriginal hA x.val a • m :=
  action_original_smul hA x.val M a m

/-- The actual identity natural transformation from the original commutant action. -/
def commutantCenter (hA : IsIdempotented A) (x : Commutant hA) :
    NondegenerateModuleCenter.{uA, uM} A where
  app M := ObjectProperty.homMk (component hA x M)
  naturality M N f := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    exact congrArg (fun g : M.obj →+ N.obj => g m)
      (IdempotentedRingRightLimit.actionAddHom_naturality hA M.property N.property f.hom x.val).symm

@[simp] theorem commutantCenter_app_hom (hA : IsIdempotented A) (x : Commutant hA)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    ((commutantCenter hA x).app M).hom = component hA x M := rfl

theorem forget_commutantCenter (hA : IsIdempotented A) (x : Commutant hA) :
    forget (commutantCenter.{uA, uM} hA x) =
      IdempotentedRingRightLimit.familyNaturalEnd hA x.val := rfl

/-- The commutant acts by actual central endomorphisms, preserving all ring operations.
Both ring structures in the type are the named ones, given explicitly. -/
def fromCommutantRingHom (hA : IsIdempotented A) :
    @RingHom (Commutant hA) (NondegenerateModuleCenter.{uA, uM} A)
      (commutantRing hA).toNonAssocSemiring (ring.{uA, uM} A).toNonAssocSemiring where
  toFun := commutantCenter hA
  map_zero' := by
    apply forgetRingHom_injective
    exact IdempotentedRingRightLimit.familyNaturalEnd_zero hA
  map_one' := by
    apply forgetRingHom_injective
    exact IdempotentedRingRightLimit.familyNaturalEnd_unit hA
  map_add' := by
    intro x y
    apply forgetRingHom_injective
    exact IdempotentedRingRightLimit.familyNaturalEnd_add hA x.val y.val
  map_mul' := by
    intro x y
    apply forgetRingHom_injective
    exact IdempotentedRingRightLimit.familyNaturalEnd_product hA x.val y.val

theorem fromCommutantRingHom_coe (hA : IsIdempotented A) :
    (fromCommutantRingHom.{uA, uM} hA : Commutant hA → NondegenerateModuleCenter.{uA, uM} A) =
      commutantCenter hA := rfl

@[simp] theorem fromCommutantRingHom_app_toAddMonoidHom
    (hA : IsIdempotented A) (x : Commutant hA) (M : NondegenerateModuleCat.{uA, uM} A) :
    (((fromCommutantRingHom.{uA, uM} hA x).app M).hom).toAddMonoidHom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x.val := rfl

theorem fromCommutantRingHom_app_coe
    (hA : IsIdempotented A) (x : Commutant hA) (M : NondegenerateModuleCat.{uA, uM} A) :
    ((((fromCommutantRingHom.{uA, uM} hA x).app M).hom).toAddMonoidHom :
      M.obj → M.obj) = IdempotentedRingRightLimitAction.act M.property x.val := rfl

@[simp] theorem fromCommutantRingHom_app_apply
    (hA : IsIdempotented A) (x : Commutant hA) (M : NondegenerateModuleCat.{uA, uM} A)
    (m : M.obj) :
    (((fromCommutantRingHom.{uA, uM} hA x).app M).hom).toAddMonoidHom m =
      IdempotentedRingRightLimitAction.act M.property x.val m := rfl

theorem fromCommutantRingHom_app_eq
    (hA : IsIdempotented A) (x : Commutant hA) (M : NondegenerateModuleCat.{uA, uM} A)
    (m : M.obj) (e : Idempotent A) (he : (e : A) • m = m) :
    (((fromCommutantRingHom.{uA, uM} hA x).app M).hom).toAddMonoidHom m =
      x.val.val e • m := component_eq hA x M m e he

theorem fromCommutantRingHom_app_original_smul
    (hA : IsIdempotented A) (x : Commutant hA) (M : NondegenerateModuleCat.{uA, uM} A)
    (a : A) (m : M.obj) :
    (((fromCommutantRingHom.{uA, uM} hA x).app M).hom).toAddMonoidHom (a • m) =
      IdempotentedRingRightLimit.applyOriginal hA x.val a • m :=
  component_original_smul hA x M a m

/-- The commutant product acts by the right factor first, then the left factor. -/
theorem fromCommutantRingHom_mul_app_toAddMonoidHom (hA : IsIdempotented A)
    (x y : Commutant hA) (M : NondegenerateModuleCat.{uA, uM} A) :
    (((fromCommutantRingHom.{uA, uM} hA
        (@HMul.hMul _ _ _ (@instHMul _ (commutantRing hA).toMul) x y)).app M).hom).toAddMonoidHom =
      (IdempotentedRingRightLimit.actionAddHom hA M.property x.val).comp
        (IdempotentedRingRightLimit.actionAddHom hA M.property y.val) := by
  apply AddMonoidHom.ext
  intro m
  exact IdempotentedRingRightLimitAction.product_act hA M.property x.val y.val m

/-- The entire bundled forgetful composite is the published family map restricted to the subring.
All four ring structures are the named ones, given explicitly. -/
theorem forgetRingHom_comp_fromCommutantRingHom (hA : IsIdempotented A) :
    @RingHom.comp (Commutant hA) (NondegenerateModuleCenter.{uA, uM} A)
        (NondegenerateModuleNaturalEnd.{uA, uM} A)
        (commutantRing hA).toNonAssocSemiring (ring.{uA, uM} A).toNonAssocSemiring
        (NondegenerateModuleNaturalEnd.ring.{uA, uM} A).toNonAssocSemiring
        (forgetRingHom.{uA, uM} (A := A)) (fromCommutantRingHom.{uA, uM} hA) =
      @RingHom.comp (Commutant hA) (IdempotentedRingRightLimit A)
        (NondegenerateModuleNaturalEnd.{uA, uM} A)
        (commutantRing hA).toNonAssocSemiring
        (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring
        (NondegenerateModuleNaturalEnd.ring.{uA, uM} A).toNonAssocSemiring
        (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, uM} hA) (commutantInclusion hA) :=
  rfl

/-- The whole composite at every component, with the published family action. -/
theorem forget_fromCommutantRingHom_app_hom (hA : IsIdempotented A) (x : Commutant hA)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    ((forgetRingHom.{uA, uM} (A := A) (fromCommutantRingHom.{uA, uM} hA x)).app M).hom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x.val := rfl

/-- The same component, through the published family map and the actual inclusion. -/
theorem forget_fromCommutantRingHom_app_hom_eq_family (hA : IsIdempotented A)
    (x : Commutant hA) (M : NondegenerateModuleCat.{uA, uM} A) :
    ((forgetRingHom.{uA, uM} (A := A) (fromCommutantRingHom.{uA, uM} hA x)).app M).hom =
      ((IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, uM} hA
        (commutantInclusion hA x)).app M).hom := rfl

/-- The component of a named commutant product, right factor first. -/
theorem component_mul_toAddMonoidHom (hA : IsIdempotented A) (x y : Commutant hA)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    (component hA (@HMul.hMul _ _ _ (@instHMul _ (commutantRing hA).toMul) x y)
        M).toAddMonoidHom =
      (component hA x M).toAddMonoidHom.comp (component hA y M).toAddMonoidHom :=
  IdempotentedRingRightLimit.actionAddHom_product hA M.property x.val y.val

/-! Definitional compatibility of the named rings with the inherited instances. These checks
compare structures by `rfl` and make no claim about which typeclass-search route is chosen. -/

example (A : Type uA) [NonUnitalRing A] :
    ring.{uA, uM} A = (inferInstance : Ring (CatCenter (NondegenerateModuleCat.{uA, uM} A))) :=
  rfl

example (A : Type uA) [NonUnitalRing A] :
    ring.{uA, uM} A = (inferInstance : Ring (End (𝟭 (NondegenerateModuleCat.{uA, uM} A)))) :=
  rfl

example (hA : IsIdempotented A) :
    commutantRing hA =
      @Subring.toRing (IdempotentedRingRightLimit A) (IdempotentedRingRightLimit.ring hA)
        (commutantSubring hA) := rfl

example (hA : IsIdempotented A) :
    commutantRing hA =
      (letI := IdempotentedRingRightLimit.ring hA
       (inferInstance : Ring ↥(commutantSubring hA))) := rfl

example (hA : IsIdempotented A) :
    (commutantInclusion hA : Commutant hA → IdempotentedRingRightLimit A) =
      (letI := IdempotentedRingRightLimit.ring hA
       ((commutantSubring hA).subtype : Commutant hA → IdempotentedRingRightLimit A)) := rfl

/-- Mathlib's inherited instance makes the actual centre commutative. -/
example (A : Type uA) [NonUnitalRing A] :
    IsMulCommutative (NondegenerateModuleCenter.{uA, uM} A) := inferInstance

example (z w : NondegenerateModuleCenter.{uA, uM} A) :
    @HMul.hMul _ _ _ (@instHMul _ (ring.{uA, uM} A).toMul) z w = w ≫ z := rfl

example (z w : NondegenerateModuleCenter.{uA, uM} A) :
    @HAdd.hAdd _ _ _ (@instHAdd _ (ring.{uA, uM} A).toAdd) z w = z + w := rfl

example : @OfNat.ofNat (NondegenerateModuleCenter.{uA, uM} A) 1
      (@One.toOfNat1 _ (ring.{uA, uM} A).toOne) = 𝟙 (𝟭 (NondegenerateModuleCat.{uA, uM} A)) :=
  rfl

example : @OfNat.ofNat (NondegenerateModuleCenter.{uA, uM} A) 0
      (@Zero.toOfNat0 _ (ring.{uA, uM} A).toZero) = 0 := rfl


/-! Complete unapplied interfaces at independent universes. -/

example : (A : Type uA) → [NonUnitalRing A] → Type (max uA (uM + 1)) :=
  @NondegenerateModuleCenter.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    NondegenerateModuleCenter.{uA, uM} A = CatCenter (NondegenerateModuleCat.{uA, uM} A) :=
  @carrier_eq.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] → Ring (NondegenerateModuleCenter.{uA, uM} A) :=
  @ring.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    NondegenerateModuleCenter.{uA, uM} A → NondegenerateModuleNaturalEnd.{uA, uM} A :=
  @forget.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    @RingHom (NondegenerateModuleCenter.{uA, uM} A) (NondegenerateModuleNaturalEnd.{uA, uM} A)
      (ring.{uA, uM} A).toNonAssocSemiring
      (NondegenerateModuleNaturalEnd.ring.{uA, uM} A).toNonAssocSemiring :=
  @forgetRingHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    (forgetRingHom.{uA, uM} (A := A) : NondegenerateModuleCenter.{uA, uM} A →
      NondegenerateModuleNaturalEnd.{uA, uM} A) = forget :=
  @forgetRingHom_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    (z : NondegenerateModuleCenter.{uA, uM} A) → (M : NondegenerateModuleCat.{uA, uM} A) →
    ((forget z).app M).hom = (z.app M).hom.toAddMonoidHom :=
  @forget_app_hom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    (z : NondegenerateModuleCenter.{uA, uM} A) → (M : NondegenerateModuleCat.{uA, uM} A) →
    (fun m : M.obj => (forget z).app M m) =
      ((z.app M).hom.toAddMonoidHom : M.obj → M.obj) :=
  @forget_app_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    Function.Injective (forgetRingHom.{uA, uM} (A := A)) :=
  @forgetRingHom_injective.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := IdempotentedRingRightLimit.ring hA
    Subring (IdempotentedRingRightLimit A) :=
  @commutantSubring.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A → Type uA :=
  @Commutant.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    Ring (Commutant hA) :=
  @commutantRing.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    @RingHom (Commutant hA) (IdempotentedRingRightLimit A)
      (commutantRing hA).toNonAssocSemiring
      (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring :=
  @commutantInclusion.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (commutantInclusion hA : Commutant hA → IdempotentedRingRightLimit A) = Subtype.val :=
  @commutantInclusion_coe.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := IdempotentedRingRightLimit.ring hA
    commutantSubring hA =
      Subring.centralizer (Set.range (IdempotentedRingRightLimit.canonicalRingHom hA)) :=
  @commutantSubring_eq.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) →
    letI := IdempotentedRingRightLimit.ring hA
    x ∈ commutantSubring hA ↔
      ∀ a : A, IdempotentedRingRightLimit.canonical a * x =
        x * IdempotentedRingRightLimit.canonical a :=
  @mem_commutantSubring_iff.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) →
    NonUnitalModuleHom A M.obj M.obj :=
  @component.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) →
    (component hA x M).toAddMonoidHom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x.val :=
  @component_toAddMonoidHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) →
    (component hA x M : M.obj → M.obj) =
      IdempotentedRingRightLimitAction.act M.property x.val :=
  @component_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) →
    (m : M.obj) → (e : Idempotent A) → (e : A) • m = m →
    component hA x M m = x.val.val e • m :=
  @component_eq.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) → (M : NondegenerateModuleCat.{uA, uM} A) →
    (a : A) → (m : M.obj) →
    IdempotentedRingRightLimit.actionAddHom hA M.property x (a • m) =
      IdempotentedRingRightLimit.applyOriginal hA x a • m :=
  @action_original_smul.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    Commutant hA → NondegenerateModuleCenter.{uA, uM} A :=
  @commutantCenter.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    @RingHom (Commutant hA) (NondegenerateModuleCenter.{uA, uM} A)
      (commutantRing hA).toNonAssocSemiring (ring.{uA, uM} A).toNonAssocSemiring :=
  @fromCommutantRingHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (fromCommutantRingHom.{uA, uM} hA : Commutant hA → NondegenerateModuleCenter.{uA, uM} A) =
      commutantCenter hA :=
  @fromCommutantRingHom_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) →
    (((fromCommutantRingHom.{uA, uM} hA x).app M).hom).toAddMonoidHom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x.val :=
  @fromCommutantRingHom_app_toAddMonoidHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) →
    ((((fromCommutantRingHom.{uA, uM} hA x).app M).hom).toAddMonoidHom : M.obj → M.obj) =
      IdempotentedRingRightLimitAction.act M.property x.val :=
  @fromCommutantRingHom_app_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) → (m : M.obj) →
    (((fromCommutantRingHom.{uA, uM} hA x).app M).hom).toAddMonoidHom m =
      IdempotentedRingRightLimitAction.act M.property x.val m :=
  @fromCommutantRingHom_app_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) →
    (m : M.obj) → (e : Idempotent A) → (e : A) • m = m →
    (((fromCommutantRingHom.{uA, uM} hA x).app M).hom).toAddMonoidHom m = x.val.val e • m :=
  @fromCommutantRingHom_app_eq.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) → (a : A) → (m : M.obj) →
    (((fromCommutantRingHom.{uA, uM} hA x).app M).hom).toAddMonoidHom (a • m) =
      IdempotentedRingRightLimit.applyOriginal hA x.val a • m :=
  @fromCommutantRingHom_app_original_smul.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    @RingHom.comp (Commutant hA) (NondegenerateModuleCenter.{uA, uM} A)
        (NondegenerateModuleNaturalEnd.{uA, uM} A)
        (commutantRing hA).toNonAssocSemiring (ring.{uA, uM} A).toNonAssocSemiring
        (NondegenerateModuleNaturalEnd.ring.{uA, uM} A).toNonAssocSemiring
        (forgetRingHom.{uA, uM} (A := A)) (fromCommutantRingHom.{uA, uM} hA) =
      @RingHom.comp (Commutant hA) (IdempotentedRingRightLimit A)
        (NondegenerateModuleNaturalEnd.{uA, uM} A)
        (commutantRing hA).toNonAssocSemiring
        (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring
        (NondegenerateModuleNaturalEnd.ring.{uA, uM} A).toNonAssocSemiring
        (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, uM} hA) (commutantInclusion hA) :=
  @forgetRingHom_comp_fromCommutantRingHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x y : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) →
    (((fromCommutantRingHom.{uA, uM} hA
        (@HMul.hMul _ _ _ (@instHMul _ (commutantRing hA).toMul) x y)).app M).hom).toAddMonoidHom =
      (IdempotentedRingRightLimit.actionAddHom hA M.property x.val).comp
        (IdempotentedRingRightLimit.actionAddHom hA M.property y.val) :=
  @fromCommutantRingHom_mul_app_toAddMonoidHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) →
    ((forgetRingHom.{uA, uM} (A := A) (fromCommutantRingHom.{uA, uM} hA x)).app M).hom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x.val :=
  @forget_fromCommutantRingHom_app_hom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    (z w : NondegenerateModuleCenter.{uA, uM} A) → (M : NondegenerateModuleCat.{uA, uM} A) →
    ((@HMul.hMul _ _ _ (@instHMul _ (ring.{uA, uM} A).toMul) z w).app M).hom.toAddMonoidHom =
      (z.app M).hom.toAddMonoidHom.comp (w.app M).hom.toAddMonoidHom :=
  @mul_app_toAddMonoidHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    (z : NondegenerateModuleCenter.{uA, uM} A) → (M : NondegenerateModuleCat.{uA, uM} A) →
    (m : M.obj) → (forget z).app M m = (z.app M).hom.toAddMonoidHom m :=
  @forget_app_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (a : A) →
    IdempotentedRingRightLimit.product hA (IdempotentedRingRightLimit.canonical a) x.val =
      IdempotentedRingRightLimit.product hA x.val (IdempotentedRingRightLimit.canonical a) :=
  @commutes.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) → (a : A) → (m : M.obj) →
    IdempotentedRingRightLimit.actionAddHom hA M.property x.val (a • m) =
      a • IdempotentedRingRightLimit.actionAddHom hA M.property x.val m :=
  @action_smul.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) → (m : M.obj) →
    component hA x M m = IdempotentedRingRightLimitAction.act M.property x.val m :=
  @component_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) → (a : A) → (m : M.obj) →
    component hA x M (a • m) = IdempotentedRingRightLimit.applyOriginal hA x.val a • m :=
  @component_original_smul.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x y : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) →
    (component hA (@HMul.hMul _ _ _ (@instHMul _ (commutantRing hA).toMul) x y)
        M).toAddMonoidHom =
      (component hA x M).toAddMonoidHom.comp (component hA y M).toAddMonoidHom :=
  @component_mul_toAddMonoidHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) →
    ((commutantCenter.{uA, uM} hA x).app M).hom = component hA x M :=
  @commutantCenter_app_hom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) →
    forget (commutantCenter.{uA, uM} hA x) = IdempotentedRingRightLimit.familyNaturalEnd hA x.val :=
  @forget_commutantCenter.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) →
    ((forgetRingHom.{uA, uM} (A := A) (fromCommutantRingHom.{uA, uM} hA x)).app M).hom =
      ((IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, uM} hA
        (commutantInclusion hA x)).app M).hom :=
  @forget_fromCommutantRingHom_app_hom_eq_family.{uA, uM}

/-! The scalar universe is smaller than the module-carrier universe. -/

example : (A : Type 0) → [NonUnitalRing A] → Type (max 0 (1 + 1)) :=
  @NondegenerateModuleCenter.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] →
    NondegenerateModuleCenter.{0, 1} A = CatCenter (NondegenerateModuleCat.{0, 1} A) :=
  @carrier_eq.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] → Ring (NondegenerateModuleCenter.{0, 1} A) :=
  @ring.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    NondegenerateModuleCenter.{0, 1} A → NondegenerateModuleNaturalEnd.{0, 1} A :=
  @forget.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    @RingHom (NondegenerateModuleCenter.{0, 1} A) (NondegenerateModuleNaturalEnd.{0, 1} A)
      (ring.{0, 1} A).toNonAssocSemiring
      (NondegenerateModuleNaturalEnd.ring.{0, 1} A).toNonAssocSemiring :=
  @forgetRingHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    (forgetRingHom.{0, 1} (A := A) : NondegenerateModuleCenter.{0, 1} A →
      NondegenerateModuleNaturalEnd.{0, 1} A) = forget :=
  @forgetRingHom_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    (z : NondegenerateModuleCenter.{0, 1} A) → (M : NondegenerateModuleCat.{0, 1} A) →
    ((forget z).app M).hom = (z.app M).hom.toAddMonoidHom :=
  @forget_app_hom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    (z : NondegenerateModuleCenter.{0, 1} A) → (M : NondegenerateModuleCat.{0, 1} A) →
    (fun m : M.obj => (forget z).app M m) =
      ((z.app M).hom.toAddMonoidHom : M.obj → M.obj) :=
  @forget_app_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    Function.Injective (forgetRingHom.{0, 1} (A := A)) :=
  @forgetRingHom_injective.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := IdempotentedRingRightLimit.ring hA
    Subring (IdempotentedRingRightLimit A) :=
  @commutantSubring.{0}

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A → Type 0 :=
  @Commutant.{0}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    Ring (Commutant hA) :=
  @commutantRing.{0}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    @RingHom (Commutant hA) (IdempotentedRingRightLimit A)
      (commutantRing hA).toNonAssocSemiring
      (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring :=
  @commutantInclusion.{0}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (commutantInclusion hA : Commutant hA → IdempotentedRingRightLimit A) = Subtype.val :=
  @commutantInclusion_coe.{0}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := IdempotentedRingRightLimit.ring hA
    commutantSubring hA =
      Subring.centralizer (Set.range (IdempotentedRingRightLimit.canonicalRingHom hA)) :=
  @commutantSubring_eq.{0}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) →
    letI := IdempotentedRingRightLimit.ring hA
    x ∈ commutantSubring hA ↔
      ∀ a : A, IdempotentedRingRightLimit.canonical a * x =
        x * IdempotentedRingRightLimit.canonical a :=
  @mem_commutantSubring_iff.{0}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{0, 1} A) →
    NonUnitalModuleHom A M.obj M.obj :=
  @component.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{0, 1} A) →
    (component hA x M).toAddMonoidHom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x.val :=
  @component_toAddMonoidHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{0, 1} A) →
    (component hA x M : M.obj → M.obj) =
      IdempotentedRingRightLimitAction.act M.property x.val :=
  @component_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{0, 1} A) →
    (m : M.obj) → (e : Idempotent A) → (e : A) • m = m →
    component hA x M m = x.val.val e • m :=
  @component_eq.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) → (M : NondegenerateModuleCat.{0, 1} A) →
    (a : A) → (m : M.obj) →
    IdempotentedRingRightLimit.actionAddHom hA M.property x (a • m) =
      IdempotentedRingRightLimit.applyOriginal hA x a • m :=
  @action_original_smul.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    Commutant hA → NondegenerateModuleCenter.{0, 1} A :=
  @commutantCenter.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    @RingHom (Commutant hA) (NondegenerateModuleCenter.{0, 1} A)
      (commutantRing hA).toNonAssocSemiring (ring.{0, 1} A).toNonAssocSemiring :=
  @fromCommutantRingHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (fromCommutantRingHom.{0, 1} hA : Commutant hA → NondegenerateModuleCenter.{0, 1} A) =
      commutantCenter hA :=
  @fromCommutantRingHom_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{0, 1} A) →
    (((fromCommutantRingHom.{0, 1} hA x).app M).hom).toAddMonoidHom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x.val :=
  @fromCommutantRingHom_app_toAddMonoidHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{0, 1} A) →
    ((((fromCommutantRingHom.{0, 1} hA x).app M).hom).toAddMonoidHom : M.obj → M.obj) =
      IdempotentedRingRightLimitAction.act M.property x.val :=
  @fromCommutantRingHom_app_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{0, 1} A) → (m : M.obj) →
    (((fromCommutantRingHom.{0, 1} hA x).app M).hom).toAddMonoidHom m =
      IdempotentedRingRightLimitAction.act M.property x.val m :=
  @fromCommutantRingHom_app_apply.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{0, 1} A) →
    (m : M.obj) → (e : Idempotent A) → (e : A) • m = m →
    (((fromCommutantRingHom.{0, 1} hA x).app M).hom).toAddMonoidHom m = x.val.val e • m :=
  @fromCommutantRingHom_app_eq.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{0, 1} A) → (a : A) → (m : M.obj) →
    (((fromCommutantRingHom.{0, 1} hA x).app M).hom).toAddMonoidHom (a • m) =
      IdempotentedRingRightLimit.applyOriginal hA x.val a • m :=
  @fromCommutantRingHom_app_original_smul.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    @RingHom.comp (Commutant hA) (NondegenerateModuleCenter.{0, 1} A)
        (NondegenerateModuleNaturalEnd.{0, 1} A)
        (commutantRing hA).toNonAssocSemiring (ring.{0, 1} A).toNonAssocSemiring
        (NondegenerateModuleNaturalEnd.ring.{0, 1} A).toNonAssocSemiring
        (forgetRingHom.{0, 1} (A := A)) (fromCommutantRingHom.{0, 1} hA) =
      @RingHom.comp (Commutant hA) (IdempotentedRingRightLimit A)
        (NondegenerateModuleNaturalEnd.{0, 1} A)
        (commutantRing hA).toNonAssocSemiring
        (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring
        (NondegenerateModuleNaturalEnd.ring.{0, 1} A).toNonAssocSemiring
        (IdempotentedRingRightLimit.toNaturalEndRingHom.{0, 1} hA) (commutantInclusion hA) :=
  @forgetRingHom_comp_fromCommutantRingHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x y : Commutant hA) → (M : NondegenerateModuleCat.{0, 1} A) →
    (((fromCommutantRingHom.{0, 1} hA
        (@HMul.hMul _ _ _ (@instHMul _ (commutantRing hA).toMul) x y)).app M).hom).toAddMonoidHom =
      (IdempotentedRingRightLimit.actionAddHom hA M.property x.val).comp
        (IdempotentedRingRightLimit.actionAddHom hA M.property y.val) :=
  @fromCommutantRingHom_mul_app_toAddMonoidHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{0, 1} A) →
    ((forgetRingHom.{0, 1} (A := A) (fromCommutantRingHom.{0, 1} hA x)).app M).hom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x.val :=
  @forget_fromCommutantRingHom_app_hom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    (z w : NondegenerateModuleCenter.{0, 1} A) → (M : NondegenerateModuleCat.{0, 1} A) →
    ((@HMul.hMul _ _ _ (@instHMul _ (ring.{0, 1} A).toMul) z w).app M).hom.toAddMonoidHom =
      (z.app M).hom.toAddMonoidHom.comp (w.app M).hom.toAddMonoidHom :=
  @mul_app_toAddMonoidHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    (z : NondegenerateModuleCenter.{0, 1} A) → (M : NondegenerateModuleCat.{0, 1} A) →
    (m : M.obj) → (forget z).app M m = (z.app M).hom.toAddMonoidHom m :=
  @forget_app_apply.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (a : A) →
    IdempotentedRingRightLimit.product hA (IdempotentedRingRightLimit.canonical a) x.val =
      IdempotentedRingRightLimit.product hA x.val (IdempotentedRingRightLimit.canonical a) :=
  @commutes.{0}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{0, 1} A) → (a : A) → (m : M.obj) →
    IdempotentedRingRightLimit.actionAddHom hA M.property x.val (a • m) =
      a • IdempotentedRingRightLimit.actionAddHom hA M.property x.val m :=
  @action_smul.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{0, 1} A) → (m : M.obj) →
    component hA x M m = IdempotentedRingRightLimitAction.act M.property x.val m :=
  @component_apply.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{0, 1} A) → (a : A) → (m : M.obj) →
    component hA x M (a • m) = IdempotentedRingRightLimit.applyOriginal hA x.val a • m :=
  @component_original_smul.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x y : Commutant hA) → (M : NondegenerateModuleCat.{0, 1} A) →
    (component hA (@HMul.hMul _ _ _ (@instHMul _ (commutantRing hA).toMul) x y)
        M).toAddMonoidHom =
      (component hA x M).toAddMonoidHom.comp (component hA y M).toAddMonoidHom :=
  @component_mul_toAddMonoidHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{0, 1} A) →
    ((commutantCenter.{0, 1} hA x).app M).hom = component hA x M :=
  @commutantCenter_app_hom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) →
    forget (commutantCenter.{0, 1} hA x) = IdempotentedRingRightLimit.familyNaturalEnd hA x.val :=
  @forget_commutantCenter.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{0, 1} A) →
    ((forgetRingHom.{0, 1} (A := A) (fromCommutantRingHom.{0, 1} hA x)).app M).hom =
      ((IdempotentedRingRightLimit.toNaturalEndRingHom.{0, 1} hA
        (commutantInclusion hA x)).app M).hom :=
  @forget_fromCommutantRingHom_app_hom_eq_family.{0, 1}

/-! The scalar universe is larger than the module-carrier universe. -/

example : (A : Type 1) → [NonUnitalRing A] → Type (max 1 (0 + 1)) :=
  @NondegenerateModuleCenter.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    NondegenerateModuleCenter.{1, 0} A = CatCenter (NondegenerateModuleCat.{1, 0} A) :=
  @carrier_eq.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] → Ring (NondegenerateModuleCenter.{1, 0} A) :=
  @ring.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    NondegenerateModuleCenter.{1, 0} A → NondegenerateModuleNaturalEnd.{1, 0} A :=
  @forget.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    @RingHom (NondegenerateModuleCenter.{1, 0} A) (NondegenerateModuleNaturalEnd.{1, 0} A)
      (ring.{1, 0} A).toNonAssocSemiring
      (NondegenerateModuleNaturalEnd.ring.{1, 0} A).toNonAssocSemiring :=
  @forgetRingHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    (forgetRingHom.{1, 0} (A := A) : NondegenerateModuleCenter.{1, 0} A →
      NondegenerateModuleNaturalEnd.{1, 0} A) = forget :=
  @forgetRingHom_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    (z : NondegenerateModuleCenter.{1, 0} A) → (M : NondegenerateModuleCat.{1, 0} A) →
    ((forget z).app M).hom = (z.app M).hom.toAddMonoidHom :=
  @forget_app_hom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    (z : NondegenerateModuleCenter.{1, 0} A) → (M : NondegenerateModuleCat.{1, 0} A) →
    (fun m : M.obj => (forget z).app M m) =
      ((z.app M).hom.toAddMonoidHom : M.obj → M.obj) :=
  @forget_app_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    Function.Injective (forgetRingHom.{1, 0} (A := A)) :=
  @forgetRingHom_injective.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := IdempotentedRingRightLimit.ring hA
    Subring (IdempotentedRingRightLimit A) :=
  @commutantSubring.{1}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A → Type 1 :=
  @Commutant.{1}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    Ring (Commutant hA) :=
  @commutantRing.{1}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    @RingHom (Commutant hA) (IdempotentedRingRightLimit A)
      (commutantRing hA).toNonAssocSemiring
      (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring :=
  @commutantInclusion.{1}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (commutantInclusion hA : Commutant hA → IdempotentedRingRightLimit A) = Subtype.val :=
  @commutantInclusion_coe.{1}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := IdempotentedRingRightLimit.ring hA
    commutantSubring hA =
      Subring.centralizer (Set.range (IdempotentedRingRightLimit.canonicalRingHom hA)) :=
  @commutantSubring_eq.{1}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) →
    letI := IdempotentedRingRightLimit.ring hA
    x ∈ commutantSubring hA ↔
      ∀ a : A, IdempotentedRingRightLimit.canonical a * x =
        x * IdempotentedRingRightLimit.canonical a :=
  @mem_commutantSubring_iff.{1}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{1, 0} A) →
    NonUnitalModuleHom A M.obj M.obj :=
  @component.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{1, 0} A) →
    (component hA x M).toAddMonoidHom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x.val :=
  @component_toAddMonoidHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{1, 0} A) →
    (component hA x M : M.obj → M.obj) =
      IdempotentedRingRightLimitAction.act M.property x.val :=
  @component_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{1, 0} A) →
    (m : M.obj) → (e : Idempotent A) → (e : A) • m = m →
    component hA x M m = x.val.val e • m :=
  @component_eq.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) → (M : NondegenerateModuleCat.{1, 0} A) →
    (a : A) → (m : M.obj) →
    IdempotentedRingRightLimit.actionAddHom hA M.property x (a • m) =
      IdempotentedRingRightLimit.applyOriginal hA x a • m :=
  @action_original_smul.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    Commutant hA → NondegenerateModuleCenter.{1, 0} A :=
  @commutantCenter.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    @RingHom (Commutant hA) (NondegenerateModuleCenter.{1, 0} A)
      (commutantRing hA).toNonAssocSemiring (ring.{1, 0} A).toNonAssocSemiring :=
  @fromCommutantRingHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (fromCommutantRingHom.{1, 0} hA : Commutant hA → NondegenerateModuleCenter.{1, 0} A) =
      commutantCenter hA :=
  @fromCommutantRingHom_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{1, 0} A) →
    (((fromCommutantRingHom.{1, 0} hA x).app M).hom).toAddMonoidHom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x.val :=
  @fromCommutantRingHom_app_toAddMonoidHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{1, 0} A) →
    ((((fromCommutantRingHom.{1, 0} hA x).app M).hom).toAddMonoidHom : M.obj → M.obj) =
      IdempotentedRingRightLimitAction.act M.property x.val :=
  @fromCommutantRingHom_app_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{1, 0} A) → (m : M.obj) →
    (((fromCommutantRingHom.{1, 0} hA x).app M).hom).toAddMonoidHom m =
      IdempotentedRingRightLimitAction.act M.property x.val m :=
  @fromCommutantRingHom_app_apply.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{1, 0} A) →
    (m : M.obj) → (e : Idempotent A) → (e : A) • m = m →
    (((fromCommutantRingHom.{1, 0} hA x).app M).hom).toAddMonoidHom m = x.val.val e • m :=
  @fromCommutantRingHom_app_eq.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{1, 0} A) → (a : A) → (m : M.obj) →
    (((fromCommutantRingHom.{1, 0} hA x).app M).hom).toAddMonoidHom (a • m) =
      IdempotentedRingRightLimit.applyOriginal hA x.val a • m :=
  @fromCommutantRingHom_app_original_smul.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    @RingHom.comp (Commutant hA) (NondegenerateModuleCenter.{1, 0} A)
        (NondegenerateModuleNaturalEnd.{1, 0} A)
        (commutantRing hA).toNonAssocSemiring (ring.{1, 0} A).toNonAssocSemiring
        (NondegenerateModuleNaturalEnd.ring.{1, 0} A).toNonAssocSemiring
        (forgetRingHom.{1, 0} (A := A)) (fromCommutantRingHom.{1, 0} hA) =
      @RingHom.comp (Commutant hA) (IdempotentedRingRightLimit A)
        (NondegenerateModuleNaturalEnd.{1, 0} A)
        (commutantRing hA).toNonAssocSemiring
        (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring
        (NondegenerateModuleNaturalEnd.ring.{1, 0} A).toNonAssocSemiring
        (IdempotentedRingRightLimit.toNaturalEndRingHom.{1, 0} hA) (commutantInclusion hA) :=
  @forgetRingHom_comp_fromCommutantRingHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x y : Commutant hA) → (M : NondegenerateModuleCat.{1, 0} A) →
    (((fromCommutantRingHom.{1, 0} hA
        (@HMul.hMul _ _ _ (@instHMul _ (commutantRing hA).toMul) x y)).app M).hom).toAddMonoidHom =
      (IdempotentedRingRightLimit.actionAddHom hA M.property x.val).comp
        (IdempotentedRingRightLimit.actionAddHom hA M.property y.val) :=
  @fromCommutantRingHom_mul_app_toAddMonoidHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{1, 0} A) →
    ((forgetRingHom.{1, 0} (A := A) (fromCommutantRingHom.{1, 0} hA x)).app M).hom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x.val :=
  @forget_fromCommutantRingHom_app_hom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    (z w : NondegenerateModuleCenter.{1, 0} A) → (M : NondegenerateModuleCat.{1, 0} A) →
    ((@HMul.hMul _ _ _ (@instHMul _ (ring.{1, 0} A).toMul) z w).app M).hom.toAddMonoidHom =
      (z.app M).hom.toAddMonoidHom.comp (w.app M).hom.toAddMonoidHom :=
  @mul_app_toAddMonoidHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    (z : NondegenerateModuleCenter.{1, 0} A) → (M : NondegenerateModuleCat.{1, 0} A) →
    (m : M.obj) → (forget z).app M m = (z.app M).hom.toAddMonoidHom m :=
  @forget_app_apply.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (a : A) →
    IdempotentedRingRightLimit.product hA (IdempotentedRingRightLimit.canonical a) x.val =
      IdempotentedRingRightLimit.product hA x.val (IdempotentedRingRightLimit.canonical a) :=
  @commutes.{1}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{1, 0} A) → (a : A) → (m : M.obj) →
    IdempotentedRingRightLimit.actionAddHom hA M.property x.val (a • m) =
      a • IdempotentedRingRightLimit.actionAddHom hA M.property x.val m :=
  @action_smul.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{1, 0} A) → (m : M.obj) →
    component hA x M m = IdempotentedRingRightLimitAction.act M.property x.val m :=
  @component_apply.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{1, 0} A) → (a : A) → (m : M.obj) →
    component hA x M (a • m) = IdempotentedRingRightLimit.applyOriginal hA x.val a • m :=
  @component_original_smul.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x y : Commutant hA) → (M : NondegenerateModuleCat.{1, 0} A) →
    (component hA (@HMul.hMul _ _ _ (@instHMul _ (commutantRing hA).toMul) x y)
        M).toAddMonoidHom =
      (component hA x M).toAddMonoidHom.comp (component hA y M).toAddMonoidHom :=
  @component_mul_toAddMonoidHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{1, 0} A) →
    ((commutantCenter.{1, 0} hA x).app M).hom = component hA x M :=
  @commutantCenter_app_hom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) →
    forget (commutantCenter.{1, 0} hA x) = IdempotentedRingRightLimit.familyNaturalEnd hA x.val :=
  @forget_commutantCenter.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : Commutant hA) → (M : NondegenerateModuleCat.{1, 0} A) →
    ((forgetRingHom.{1, 0} (A := A) (fromCommutantRingHom.{1, 0} hA x)).app M).hom =
      ((IdempotentedRingRightLimit.toNaturalEndRingHom.{1, 0} hA
        (commutantInclusion hA x)).app M).hom :=
  @forget_fromCommutantRingHom_app_hom_eq_family.{1, 0}

/-! The original scalar-ring argument remains explicit under competition. -/
section CompetingOriginalRings

variable {A : Type uA} (originalRing : NonUnitalRing A) [competingRing : NonUnitalRing A]

example : @NondegenerateModuleCenter.{uA, uM} A originalRing =
    CatCenter (@NondegenerateModuleCat.{uA, uM} A originalRing) := rfl

example : (letI := originalRing; Ring (NondegenerateModuleCenter.{uA, uM} A)) :=
  @ring.{uA, uM} A originalRing

example : @RingHom (@NondegenerateModuleCenter.{uA, uM} A originalRing)
    (@NondegenerateModuleNaturalEnd.{uA, uM} A originalRing)
    (@ring.{uA, uM} A originalRing).toNonAssocSemiring
    (@NondegenerateModuleNaturalEnd.ring.{uA, uM} A originalRing).toNonAssocSemiring :=
  @forgetRingHom.{uA, uM} A originalRing

example : (hA : @IsIdempotented A originalRing) →
    letI := originalRing
    letI := IdempotentedRingRightLimit.ring hA
    Subring (IdempotentedRingRightLimit A) :=
  @commutantSubring A originalRing

example : (hA : @IsIdempotented A originalRing) →
    letI := originalRing
    (x : Commutant hA) → (M : NondegenerateModuleCat.{uA, uM} A) →
    NonUnitalModuleHom A M.obj M.obj :=
  @component.{uA, uM} A originalRing

example : (hA : @IsIdempotented A originalRing) →
    @RingHom (@Commutant A originalRing hA) (@NondegenerateModuleCenter.{uA, uM} A originalRing)
      (@commutantRing A originalRing hA).toNonAssocSemiring
      (@ring.{uA, uM} A originalRing).toNonAssocSemiring :=
  @fromCommutantRingHom.{uA, uM} A originalRing

end CompetingOriginalRings

/-! Explicit named expected operations determine each full ring-map interface.
The inherited categorical endomorphism instance is definitionally compatible;
these checks do not prescribe a typeclass-search route. -/
section CompetingRings

variable {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
  [competingFamilyRing : Ring (IdempotentedRingRightLimit A)]
  [competingCommutantRing : Ring (Commutant hA)]
  [competingCenterRing : Ring (NondegenerateModuleCenter.{uA, uM} A)]
  [competingEndRing : Ring (NondegenerateModuleNaturalEnd.{uA, uM} A)]

example : @RingHom (NondegenerateModuleCenter.{uA, uM} A)
    (NondegenerateModuleNaturalEnd.{uA, uM} A)
    (ring.{uA, uM} A).toNonAssocSemiring
    (NondegenerateModuleNaturalEnd.ring.{uA, uM} A).toNonAssocSemiring :=
  forgetRingHom.{uA, uM} (A := A)

example : @RingHom (Commutant hA) (IdempotentedRingRightLimit A)
    (commutantRing hA).toNonAssocSemiring
    (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring :=
  commutantInclusion hA

example : @RingHom (Commutant hA) (NondegenerateModuleCenter.{uA, uM} A)
    (commutantRing hA).toNonAssocSemiring (ring.{uA, uM} A).toNonAssocSemiring :=
  fromCommutantRingHom.{uA, uM} hA

example : @RingHom.comp _ _ _
      (commutantRing hA).toNonAssocSemiring
      (ring.{uA, uM} A).toNonAssocSemiring
      (NondegenerateModuleNaturalEnd.ring.{uA, uM} A).toNonAssocSemiring
      (forgetRingHom.{uA, uM} (A := A)) (fromCommutantRingHom.{uA, uM} hA) =
    @RingHom.comp _ _ _
      (commutantRing hA).toNonAssocSemiring
      (IdempotentedRingRightLimit.ring hA).toNonAssocSemiring
      (NondegenerateModuleNaturalEnd.ring.{uA, uM} A).toNonAssocSemiring
      (IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, uM} hA) (commutantInclusion hA) :=
  forgetRingHom_comp_fromCommutantRingHom hA

example : @commutantSubring A _ hA =
    @Subring.centralizer (IdempotentedRingRightLimit A) (IdempotentedRingRightLimit.ring hA)
      (Set.range (IdempotentedRingRightLimit.canonicalRingHom hA)) := rfl

example : (z w : NondegenerateModuleCenter.{uA, uM} A) →
    (M : NondegenerateModuleCat.{uA, uM} A) →
    ((@HMul.hMul _ _ _ (@instHMul _ (ring.{uA, uM} A).toMul) z w).app M).hom.toAddMonoidHom =
      (z.app M).hom.toAddMonoidHom.comp (w.app M).hom.toAddMonoidHom :=
  @mul_app_toAddMonoidHom.{uA, uM} A _

end CompetingRings

/-! An unrelated action on the same carrier cannot replace the original object action. -/
section CompetingActions

variable {A : Type uA} [NonUnitalRing A] {M : Type uM} [AddCommGroup M]
  (originalAction : NonUnitalModule A M) [competingAction : NonUnitalModule A M]

example (hA : IsIdempotented A) (hM : @IsNondegenerate A M _ _ originalAction)
    (x : Commutant hA) :
    @NonUnitalModuleHom A M M _ _ _ originalAction originalAction :=
  component hA x ⟨@NonUnitalModuleCat.of A _ M _ originalAction, hM⟩

example (hA : IsIdempotented A) (hM : @IsNondegenerate A M _ _ originalAction)
    (x : Commutant hA) :
    @NonUnitalModuleHom.toAddMonoidHom A M M _ _ _ originalAction originalAction
      (component hA x ⟨@NonUnitalModuleCat.of A _ M _ originalAction, hM⟩) =
      @IdempotentedRingRightLimit.actionAddHom A _ M _ originalAction hA hM x.val := rfl

example (hA : IsIdempotented A) (hM : @IsNondegenerate A M _ _ originalAction)
    (x : Commutant hA) (m : M) (e : Idempotent A)
    (he : @SMul.smul A M originalAction.toDistribSMul.toSMul (e : A) m = m) :
    component hA x ⟨@NonUnitalModuleCat.of A _ M _ originalAction, hM⟩ m =
      @SMul.smul A M originalAction.toDistribSMul.toSMul (x.val.val e) m :=
  component_eq hA x ⟨@NonUnitalModuleCat.of A _ M _ originalAction, hM⟩ m e he

example (hA : IsIdempotented A) (hM : @IsNondegenerate A M _ _ originalAction)
    (x : Commutant hA) :
    @NonUnitalModuleHom.toAddMonoidHom A M M _ _ _ originalAction originalAction
      (((fromCommutantRingHom.{uA, uM} hA x).app
        ⟨@NonUnitalModuleCat.of A _ M _ originalAction, hM⟩).hom) =
      @IdempotentedRingRightLimit.actionAddHom A _ M _ originalAction hA hM x.val := rfl

end CompetingActions

/-! Zero rings are retained, with no nontriviality assumption. -/
section ZeroRing

variable {A : Type uA} [NonUnitalRing A] [Subsingleton A]

example : ∃ hA : IsIdempotented A, ∀ (x : Commutant hA) (M : NondegenerateModuleCat.{uA, uM} A),
    (component hA x M).toAddMonoidHom = 0 := by
  have hA : IsIdempotented A := by
    intro s
    refine ⟨⟨0, zero_mul 0⟩, ?_⟩
    intro a _ha
    exact Subsingleton.elim _ _
  refine ⟨hA, ?_⟩
  intro x M
  apply AddMonoidHom.ext
  intro m
  obtain ⟨e, he⟩ := M.property m
  rw [show (component hA x M).toAddMonoidHom m = x.val.val e • m from
    component_eq hA x M m e he]
  have hx : x.val.val e = 0 := Subsingleton.elim _ _
  rw [hx]
  exact @NonUnitalModule.zero_smul A M.obj _ _ M.obj.isModule m

example (hA : IsIdempotented A) (x : Commutant hA)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    ((fromCommutantRingHom.{uA, uM} hA x).app M).hom.toAddMonoidHom = 0 := by
  apply AddMonoidHom.ext
  intro m
  obtain ⟨e, he⟩ := M.property m
  rw [fromCommutantRingHom_app_eq hA x M m e he]
  have hx : x.val.val e = 0 := Subsingleton.elim _ _
  rw [hx]
  exact @NonUnitalModule.zero_smul A M.obj _ _ M.obj.isModule m

end ZeroRing

end NondegenerateModuleCenter
end Langlands.Algebra
