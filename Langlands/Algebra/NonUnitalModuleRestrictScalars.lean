import Langlands.Algebra.NonUnitalModuleAdditive
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Restriction of original nonunital actions along a scalar homomorphism

Internal general prerequisites for Renard 2026 I.2.3, printed pp.16–18/PDF22–24.
An ambient action has no unit law. Nondegenerate restriction needs the explicit
left-local-unit condition below, even when both scalar rings are idempotented.
-/

set_option autoImplicit false

namespace Langlands.Algebra

open CategoryTheory

universe uA uB uC uM uN uP

namespace NonUnitalModuleRestrictScalars

variable {A : Type uA} {B : Type uB} {C : Type uC}
  [NonUnitalRing A] [NonUnitalRing B] [NonUnitalRing C]
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

/-- Pull back exactly the specified original action, without adjoining a unit. -/
@[instance_reducible]
def module (φ : A →ₙ+* B) (hM : NonUnitalModule B M) : NonUnitalModule A M :=
  NonUnitalModule.ofEndHom ((NonUnitalModule.toEndHom hM).comp φ)

/-- The complete original endomorphism representation is composed with φ. -/
@[simp] theorem toEndHom_module (φ : A →ₙ+* B) (hM : NonUnitalModule B M) :
    NonUnitalModule.toEndHom (module φ hM) =
      (NonUnitalModule.toEndHom hM).comp φ := by
  ext a m
  rfl

/-- The formula is pinned to both specified structures, also on equal carrier types. -/
@[simp] theorem module_action (φ : A →ₙ+* B) (hM : NonUnitalModule B M)
    (a : A) (m : M) :
    NonUnitalModule.toEndHom (module φ hM) a m =
      NonUnitalModule.toEndHom hM (φ a) m := rfl

/-- The same formula for the actual scalar actions, with both structures explicit. -/
theorem module_smul (φ : A →ₙ+* B) (hM : NonUnitalModule B M) (a : A) (m : M) :
    @HSMul.hSMul A M M (@instHSMul A M (@NonUnitalModule.actionSMul A M _ _ (module φ hM)))
        a m =
      @HSMul.hSMul B M M (@instHSMul B M (@NonUnitalModule.actionSMul B M _ _ hM)) (φ a) m :=
  rfl

@[simp] theorem module_id (hM : NonUnitalModule A M) :
    module (NonUnitalRingHom.id A) hM = hM := by
  cases hM
  rfl

@[simp] theorem module_comp (φ : A →ₙ+* B) (ψ : B →ₙ+* C)
    (hM : NonUnitalModule C M) :
    module φ (module ψ hM) = module (ψ.comp φ) hM := rfl

@[simp] theorem module_zero (φ : A →ₙ+* B) :
    module φ (NonUnitalModule.zero : NonUnitalModule B M) = NonUnitalModule.zero := rfl

@[simp] theorem module_zeroHom (hM : NonUnitalModule B M) :
    module (0 : A →ₙ+* B) hM = NonUnitalModule.zero := by
  apply (NonUnitalModule.equivEndHom (A := A) (M := M)).injective
  ext a m
  exact hM.zero_smul m

section Maps

variable [hM : NonUnitalModule B M] [hN : NonUnitalModule B N]
  [hP : NonUnitalModule B P]

/-- Restriction keeps the entire additive map of an original intertwiner. -/
def map (φ : A →ₙ+* B) (f : NonUnitalModuleHom B M N) :
    letI := module φ hM
    letI := module φ hN
    NonUnitalModuleHom A M N := by
  let _ := module φ hM
  let _ := module φ hN
  exact
    { toAddMonoidHom := f.toAddMonoidHom
      map_smul' a m := f.map_smul (φ a) m }

@[simp] theorem map_toAddMonoidHom (φ : A →ₙ+* B)
    (f : NonUnitalModuleHom B M N) :
    letI := module φ hM
    letI := module φ hN
    (map φ f).toAddMonoidHom = f.toAddMonoidHom := rfl

@[simp] theorem map_apply (φ : A →ₙ+* B) (f : NonUnitalModuleHom B M N) (m : M) :
    map φ f m = f m := rfl

/-- Equality of whole functions, with no pointwise argument left implicit. -/
theorem coe_map (φ : A →ₙ+* B) (f : NonUnitalModuleHom B M N) :
    ⇑(map φ f) = ⇑f := rfl

@[simp] theorem map_id (φ : A →ₙ+* B) :
    letI := module φ hM
    map φ (NonUnitalModuleHom.id B M) = NonUnitalModuleHom.id A M := by
  let _ := module φ hM
  apply NonUnitalModuleHom.ext
  intro m
  rfl

@[simp] theorem map_comp (φ : A →ₙ+* B)
    (g : NonUnitalModuleHom B N P) (f : NonUnitalModuleHom B M N) :
    letI := module φ hM
    letI := module φ hN
    letI := module φ hP
    map φ (g.comp f) = (map φ g).comp (map φ f) := by
  let _ := module φ hM
  let _ := module φ hN
  let _ := module φ hP
  apply NonUnitalModuleHom.ext
  intro m
  rfl

@[simp] theorem map_zero (φ : A →ₙ+* B) :
    letI := module φ hM
    letI := module φ hN
    map φ (0 : NonUnitalModuleHom B M N) = 0 := by
  let _ := module φ hM
  let _ := module φ hN
  apply NonUnitalModuleHom.ext
  intro m
  rfl

@[simp] theorem map_add (φ : A →ₙ+* B) (f g : NonUnitalModuleHom B M N) :
    letI := module φ hM
    letI := module φ hN
    map φ (f + g) = map φ f + map φ g := by
  let _ := module φ hM
  let _ := module φ hN
  apply NonUnitalModuleHom.ext
  intro m
  rfl

@[simp] theorem map_neg (φ : A →ₙ+* B) (f : NonUnitalModuleHom B M N) :
    letI := module φ hM
    letI := module φ hN
    map φ (-f) = -map φ f := by
  let _ := module φ hM
  let _ := module φ hN
  apply NonUnitalModuleHom.ext
  intro m
  rfl

/-- The actual Hom operation is additive for the published pointwise groups. -/
def mapAddHom (φ : A →ₙ+* B) :
    letI := module φ hM
    letI := module φ hN
    NonUnitalModuleHom B M N →+ NonUnitalModuleHom A M N where
  toFun := map φ
  map_zero' := map_zero φ
  map_add' := map_add φ

@[simp] theorem mapAddHom_apply (φ : A →ₙ+* B) (f : NonUnitalModuleHom B M N) :
    mapAddHom φ f = map φ f := rfl

/-- The bundled Hom function is exactly the named original restriction. -/
theorem coe_mapAddHom (φ : A →ₙ+* B) :
    ⇑(mapAddHom (M := M) (N := N) φ) =
      (fun f : NonUnitalModuleHom B M N => map φ f) := rfl

end Maps

/-- The actual ambient restriction functor, keeping each additive carrier. -/
def functor (φ : A →ₙ+* B) :
    NonUnitalModuleCat.{uB, uM} B ⥤ NonUnitalModuleCat.{uA, uM} A where
  obj M := @NonUnitalModuleCat.of A _ M M.isAddCommGroup (module φ M.isModule)
  map f := map φ f
  map_id _ := map_id φ
  map_comp f g := map_comp φ g f

/-- The carrier equality is definitional, including the original additive structure. -/
@[simp] theorem functor_obj_carrier (φ : A →ₙ+* B) (M : NonUnitalModuleCat.{uB, uM} B) :
    ((functor φ).obj M : Type uM) = M := rfl

@[simp] theorem functor_obj_module (φ : A →ₙ+* B)
    (M : NonUnitalModuleCat.{uB, uM} B) :
    ((functor φ).obj M).isModule = module φ M.isModule := rfl

@[simp] theorem functor_obj_addCommGroup (φ : A →ₙ+* B)
    (M : NonUnitalModuleCat.{uB, uM} B) :
    ((functor φ).obj M).isAddCommGroup = M.isAddCommGroup := rfl

/-- The categorical Hom map keeps the entire original additive map. -/
@[simp] theorem functor_map_toAddMonoidHom (φ : A →ₙ+* B)
    {M N : NonUnitalModuleCat.{uB, uM} B} (f : M ⟶ N) :
    ((functor φ).map f).toAddMonoidHom = f.toAddMonoidHom := rfl

instance functor_additive (φ : A →ₙ+* B) : (functor.{uA, uB, uM} φ).Additive where
  map_add := by
    intro M N f g
    exact map_add φ f g

/-- Nondegeneracy of the pulled-back LEFT regular action on B, in actual elements. -/
def HasLeftLocalUnits (φ : A →ₙ+* B) : Prop :=
  ∀ b : B, ∃ e : Idempotent A, φ (e : A) * b = b

/-- The explicit two-sided finite-family condition of Renard I.2.3, PDF24. -/
def HasTwoSidedLocalUnits (φ : A →ₙ+* B) : Prop :=
  ∀ s : Finset B, ∃ e : Idempotent A,
    ∀ b ∈ s, φ (e : A) * b = b ∧ b * φ (e : A) = b

/-- The source's two-sided condition supplies the weaker input used here. -/
theorem HasTwoSidedLocalUnits.hasLeftLocalUnits (φ : A →ₙ+* B)
    (hφ : HasTwoSidedLocalUnits φ) : HasLeftLocalUnits φ := by
  classical
  intro b
  obtain ⟨e, he⟩ := hφ {b}
  exact ⟨e, (he b (by simp)).1⟩

/-- A unital scalar homomorphism satisfies the sufficient condition using 1. -/
theorem hasLeftLocalUnits_of_ringHom {R : Type uA} {S : Type uB}
    [Ring R] [Ring S] (φ : R →+* S) : HasLeftLocalUnits φ.toNonUnitalRingHom := by
  intro b
  refine ⟨⟨1, IsIdempotentElem.one⟩, ?_⟩
  change φ 1 * b = b
  rw [φ.map_one, one_mul]

/-- The small preservation lemma needed to define restriction on the full subcategories. -/
theorem isNondegenerate (φ : A →ₙ+* B) (hφ : HasLeftLocalUnits φ)
    [hM : NonUnitalModule B M] (hnd : IsNondegenerate B M) :
    letI := module φ hM
    IsNondegenerate A M := by
  intro m
  obtain ⟨b, hb⟩ := hnd m
  obtain ⟨e, he⟩ := hφ (b : B)
  refine ⟨e, ?_⟩
  change φ (e : A) • m = m
  calc
    φ (e : A) • m = φ (e : A) • ((b : B) • m) :=
      congrArg (φ (e : A) • ·) hb.symm
    _ = m := by rw [← mul_smul, he, hb]

/-- Actual restriction on the nondegenerate full categories, with the necessary input exposed. -/
def nondegenerateFunctor (φ : A →ₙ+* B) (hφ : HasLeftLocalUnits φ) :
    NondegenerateModuleCat.{uB, uM} B ⥤ NondegenerateModuleCat.{uA, uM} A where
  obj M := ⟨(functor φ).obj M.obj, isNondegenerate (M := M.obj) φ hφ M.property⟩
  map {M N} f := ObjectProperty.homMk (map (M := M.obj) (N := N.obj) φ f.hom)
  map_id M := by
    apply ObjectProperty.hom_ext
    exact map_id φ
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact map_comp φ g.hom f.hom

@[simp] theorem nondegenerateFunctor_obj (φ : A →ₙ+* B) (hφ : HasLeftLocalUnits φ)
    (M : NondegenerateModuleCat.{uB, uM} B) :
    ((nondegenerateFunctor φ hφ).obj M).obj = (functor φ).obj M.obj := rfl

@[simp] theorem nondegenerateFunctor_map_hom (φ : A →ₙ+* B) (hφ : HasLeftLocalUnits φ)
    {M N : NondegenerateModuleCat.{uB, uM} B} (f : M ⟶ N) :
    ((nondegenerateFunctor φ hφ).map f).hom = map φ f.hom := rfl

/-- The nondegenerate restriction keeps the entire original additive map. -/
@[simp] theorem nondegenerateFunctor_map_toAddMonoidHom (φ : A →ₙ+* B)
    (hφ : HasLeftLocalUnits φ) {M N : NondegenerateModuleCat.{uB, uM} B} (f : M ⟶ N) :
    ((nondegenerateFunctor φ hφ).map f).hom.toAddMonoidHom = f.hom.toAddMonoidHom := rfl

instance nondegenerateFunctor_additive (φ : A →ₙ+* B) (hφ : HasLeftLocalUnits φ) :
    (nondegenerateFunctor.{uA, uB, uM} φ hφ).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    exact map_add φ f.hom g.hom

/-- Compatibility of the complete functors with the actual inclusions. -/
theorem nondegenerateFunctor_comp_inclusion (φ : A →ₙ+* B) (hφ : HasLeftLocalUnits φ) :
    nondegenerateFunctor.{uA, uB, uM} φ hφ ⋙ nondegenerateInclusion A =
      nondegenerateInclusion B ⋙ functor φ := rfl

/-! Complete unapplied interfaces: no inferred equality of ring or carrier universes. -/

example : {A : Type uA} → {B : Type uB} →
    [NonUnitalRing A] → [NonUnitalRing B] → {M : Type uM} → [AddCommGroup M] →
    (A →ₙ+* B) → NonUnitalModule B M → NonUnitalModule A M :=
  @module.{uA, uB, uM}

example : {A : Type uA} → {B : Type uB} →
    [NonUnitalRing A] → [NonUnitalRing B] → {M : Type uM} → {N : Type uN} →
    [AddCommGroup M] → [AddCommGroup N] →
    [hM : NonUnitalModule B M] → [hN : NonUnitalModule B N] →
    (φ : A →ₙ+* B) → NonUnitalModuleHom B M N →
    letI := module φ hM
    letI := module φ hN
    NonUnitalModuleHom A M N := @map.{uA, uB, uM, uN}

example : {A : Type uA} → {B : Type uB} →
    [NonUnitalRing A] → [NonUnitalRing B] → {M : Type uM} → {N : Type uN} →
    [AddCommGroup M] → [AddCommGroup N] →
    [hM : NonUnitalModule B M] → [hN : NonUnitalModule B N] →
    (φ : A →ₙ+* B) →
    letI := module φ hM
    letI := module φ hN
    NonUnitalModuleHom B M N →+ NonUnitalModuleHom A M N :=
  @mapAddHom.{uA, uB, uM, uN}

example : {A : Type uA} → {B : Type uB} →
    [NonUnitalRing A] → [NonUnitalRing B] → (A →ₙ+* B) →
    NonUnitalModuleCat.{uB, uM} B ⥤ NonUnitalModuleCat.{uA, uM} A :=
  @functor.{uA, uB, uM}

example : {A : Type uA} → {B : Type uB} →
    [NonUnitalRing A] → [NonUnitalRing B] → (φ : A →ₙ+* B) →
    HasLeftLocalUnits φ →
    NondegenerateModuleCat.{uB, uM} B ⥤ NondegenerateModuleCat.{uA, uM} A :=
  @nondegenerateFunctor.{uA, uB, uM}

example : {A : Type uA} → {B : Type uB} →
    [NonUnitalRing A] → [NonUnitalRing B] →
    (φ : A →ₙ+* B) → (functor.{uA, uB, uM} φ).Additive :=
  @functor_additive.{uA, uB, uM}

example : {A : Type uA} → {B : Type uB} →
    [NonUnitalRing A] → [NonUnitalRing B] →
    (φ : A →ₙ+* B) → (hφ : HasLeftLocalUnits φ) →
    (nondegenerateFunctor.{uA, uB, uM} φ hφ).Additive :=
  @nondegenerateFunctor_additive.{uA, uB, uM}

example : {A : Type} → {B : Type 1} →
    [NonUnitalRing A] → [NonUnitalRing B] → {M : Type 2} → [AddCommGroup M] →
    (A →ₙ+* B) → NonUnitalModule B M → NonUnitalModule A M :=
  @module.{0, 1, 2}

example : {A : Type 2} → {B : Type 1} →
    [NonUnitalRing A] → [NonUnitalRing B] → {M : Type} → [AddCommGroup M] →
    (A →ₙ+* B) → NonUnitalModule B M → NonUnitalModule A M :=
  @module.{2, 1, 0}

example : {A : Type} → {B : Type 1} →
    [NonUnitalRing A] → [NonUnitalRing B] → {M : Type 2} → {N : Type 3} →
    [AddCommGroup M] → [AddCommGroup N] →
    [hM : NonUnitalModule B M] → [hN : NonUnitalModule B N] →
    (φ : A →ₙ+* B) → NonUnitalModuleHom B M N →
    letI := module φ hM
    letI := module φ hN
    NonUnitalModuleHom A M N := @map.{0, 1, 2, 3}

example : {A : Type 3} → {B : Type 2} →
    [NonUnitalRing A] → [NonUnitalRing B] → {M : Type 1} → {N : Type} →
    [AddCommGroup M] → [AddCommGroup N] →
    [hM : NonUnitalModule B M] → [hN : NonUnitalModule B N] →
    (φ : A →ₙ+* B) → NonUnitalModuleHom B M N →
    letI := module φ hM
    letI := module φ hN
    NonUnitalModuleHom A M N := @map.{3, 2, 1, 0}

example : {A : Type} → {B : Type 1} →
    [NonUnitalRing A] → [NonUnitalRing B] → {M : Type 2} → {N : Type 3} →
    [AddCommGroup M] → [AddCommGroup N] →
    [hM : NonUnitalModule B M] → [hN : NonUnitalModule B N] →
    (φ : A →ₙ+* B) →
    letI := module φ hM
    letI := module φ hN
    NonUnitalModuleHom B M N →+ NonUnitalModuleHom A M N := @mapAddHom.{0, 1, 2, 3}

example : {A : Type 3} → {B : Type 2} →
    [NonUnitalRing A] → [NonUnitalRing B] → {M : Type 1} → {N : Type} →
    [AddCommGroup M] → [AddCommGroup N] →
    [hM : NonUnitalModule B M] → [hN : NonUnitalModule B N] →
    (φ : A →ₙ+* B) →
    letI := module φ hM
    letI := module φ hN
    NonUnitalModuleHom B M N →+ NonUnitalModuleHom A M N := @mapAddHom.{3, 2, 1, 0}

example : {A : Type} → {B : Type 1} →
    [NonUnitalRing A] → [NonUnitalRing B] → (A →ₙ+* B) →
    NonUnitalModuleCat.{1, 2} B ⥤ NonUnitalModuleCat.{0, 2} A := @functor.{0, 1, 2}

example : {A : Type 2} → {B : Type 1} →
    [NonUnitalRing A] → [NonUnitalRing B] → (A →ₙ+* B) →
    NonUnitalModuleCat.{1, 0} B ⥤ NonUnitalModuleCat.{2, 0} A := @functor.{2, 1, 0}

example : {A : Type} → {B : Type 1} →
    [NonUnitalRing A] → [NonUnitalRing B] → (φ : A →ₙ+* B) →
    HasLeftLocalUnits φ →
    NondegenerateModuleCat.{1, 2} B ⥤ NondegenerateModuleCat.{0, 2} A :=
  @nondegenerateFunctor.{0, 1, 2}

example : {A : Type 2} → {B : Type 1} →
    [NonUnitalRing A] → [NonUnitalRing B] → (φ : A →ₙ+* B) →
    HasLeftLocalUnits φ →
    NondegenerateModuleCat.{1, 0} B ⥤ NondegenerateModuleCat.{2, 0} A :=
  @nondegenerateFunctor.{2, 1, 0}

example : {A : Type uA} → {B : Type uB} →
    [NonUnitalRing A] → [NonUnitalRing B] → (A →ₙ+* B) → Prop :=
  @HasLeftLocalUnits.{uA, uB}

example : {A : Type uA} → {B : Type uB} →
    [NonUnitalRing A] → [NonUnitalRing B] → (A →ₙ+* B) → Prop :=
  @HasTwoSidedLocalUnits.{uA, uB}

/-! Checked adapters from the source's two-sided condition and from unital homomorphisms. -/

example (φ : A →ₙ+* B) (hφ : HasTwoSidedLocalUnits φ) :
    NondegenerateModuleCat.{uB, uM} B ⥤ NondegenerateModuleCat.{uA, uM} A :=
  nondegenerateFunctor φ (HasTwoSidedLocalUnits.hasLeftLocalUnits φ hφ)

example {R : Type uA} {S : Type uB} [Ring R] [Ring S] (φ : R →+* S) :
    NondegenerateModuleCat.{uB, uM} S ⥤ NondegenerateModuleCat.{uA, uM} R :=
  nondegenerateFunctor φ.toNonUnitalRingHom (hasLeftLocalUnits_of_ringHom φ)

/-! Explicit choices take precedence over unrelated same-carrier actions. -/

example [_competingA : NonUnitalModule A M] [_competingB : NonUnitalModule B M]
    (φ : A →ₙ+* B) (chosenB : NonUnitalModule B M) (a : A) (m : M) :
    NonUnitalModule.toEndHom (module φ chosenB) a m =
      NonUnitalModule.toEndHom chosenB (φ a) m := module_action φ chosenB a m

example [_competingA : NonUnitalModule A M] [_competingB : NonUnitalModule B M]
    (φ : A →ₙ+* B) (chosenB : NonUnitalModule B M) (a : A) (m : M) :
    @HSMul.hSMul A M M (@instHSMul A M (@NonUnitalModule.actionSMul A M _ _ (module φ chosenB)))
        a m =
      @HSMul.hSMul B M M (@instHSMul B M (@NonUnitalModule.actionSMul B M _ _ chosenB))
        (φ a) m :=
  module_smul φ chosenB a m

example [_competingA : NonUnitalModule A M] [_competingB : NonUnitalModule B M]
    (φ : A →ₙ+* B) (chosenB : NonUnitalModule B M) :
    ((functor.{uA, uB, uM} φ).obj (@NonUnitalModuleCat.of B _ M _ chosenB)).isModule =
      module φ chosenB := rfl

example [_competing : NonUnitalModule A A]
    (chosen : NonUnitalModule A A) (a m : A) :
    NonUnitalModule.toEndHom (module (NonUnitalRingHom.id A) chosen) a m =
      NonUnitalModule.toEndHom chosen a m := rfl

example [_competingA : NonUnitalModule A M] [_competingB : NonUnitalModule B M]
    (φ : A →ₙ+* B) (chosenM chosenN : NonUnitalModule B M)
    (f : @NonUnitalModuleHom B M M _ _ _ chosenM chosenN) :
    @NonUnitalModuleHom.toAddMonoidHom A M M _ _ _
        (module φ chosenM) (module φ chosenN)
        (@map A B _ _ M M _ _ chosenM chosenN φ f) =
      @NonUnitalModuleHom.toAddMonoidHom B M M _ _ _ chosenM chosenN f := rfl

example [_competing : NonUnitalModule A A]
    (φ : A →ₙ+* A) (chosenM chosenN : NonUnitalModule A A) :
    @NonUnitalModuleHom A A A _ _ _ chosenM chosenN →
      @NonUnitalModuleHom A A A _ _ _ (module φ chosenM) (module φ chosenN) :=
  @map A A _ _ A A _ _ chosenM chosenN φ

example [_competing : NonUnitalModule A A]
    (φ : A →ₙ+* A) (chosenM chosenN : NonUnitalModule A A) :
    @NonUnitalModuleHom A A A _ _ _ chosenM chosenN →+
      @NonUnitalModuleHom A A A _ _ _ (module φ chosenM) (module φ chosenN) :=
  @mapAddHom A A _ _ A A _ _ chosenM chosenN φ

example (φ : A →ₙ+* B) :
    @NonUnitalModuleHom A M M _ _ _ (module φ NonUnitalModule.zero)
      (module φ NonUnitalModule.zero) := by
  let _ : NonUnitalModule B M := NonUnitalModule.zero
  exact map φ (NonUnitalModuleHom.id B M)

example [_competing : NonUnitalModule ℤ ℤ] :
    NonUnitalModule.toEndHom
      (module (NonUnitalRingHom.id ℤ) (NonUnitalModule.zero : NonUnitalModule ℤ ℤ)) 1 1 =
      0 := rfl

example :
    NonUnitalModule.toEndHom
      ((functor.{0, 0, 0} (NonUnitalRingHom.id ℤ)).obj
        (@NonUnitalModuleCat.of ℤ _ ℤ _ NonUnitalModule.zero)).isModule (1 : ℤ) (1 : ℤ) =
      (0 : ℤ) := rfl

/-! An actual usual nondegenerate module whose restriction by the zero hom degenerates. -/

example :
    letI := NonUnitalModule.ofModule ℤ ℤ
    IsNondegenerate ℤ ℤ ∧
      (letI := module (0 : ℤ →ₙ+* ℤ) (NonUnitalModule.ofModule ℤ ℤ)
       ¬ IsNondegenerate ℤ ℤ) := by
  let _ := NonUnitalModule.ofModule ℤ ℤ
  constructor
  · intro m
    exact ⟨⟨1, IsIdempotentElem.one⟩, one_smul ℤ m⟩
  · intro h
    obtain ⟨e, he⟩ := h 1
    change (0 : ℤ) • (1 : ℤ) = 1 at he
    rw [NonUnitalModule.zero_smul] at he
    exact zero_ne_one he

example : ¬ HasLeftLocalUnits (0 : ℤ →ₙ+* ℤ) := by
  intro h
  obtain ⟨e, he⟩ := h 1
  change (0 : ℤ) * 1 = 1 at he
  exact zero_ne_one ((zero_mul (1 : ℤ)).symm.trans he)

/-! Zero rings and trivial carriers remain admitted. -/

example [Subsingleton B] (φ : A →ₙ+* B) : HasLeftLocalUnits φ := by
  intro b
  exact ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩

example [Subsingleton M] (φ : A →ₙ+* B) (hM : NonUnitalModule B M) :
    letI := module φ hM
    IsNondegenerate A M := by
  intro m
  exact ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩

end NonUnitalModuleRestrictScalars

end Langlands.Algebra
