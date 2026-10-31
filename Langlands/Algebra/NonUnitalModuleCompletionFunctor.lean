import Langlands.Algebra.NonUnitalModuleLeftLimitAction
import Langlands.Algebra.NondegenerateModuleAdditive

/-!
# The actual coordinatewise completion functor

Renard I.1.5, printed p.10/PDF16. The coordinate map is defined on all
original ambient modules; the source's functor is its nondegenerate restriction.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open CategoryTheory

universe uA uM uN uP

namespace NonUnitalModuleLeftLimit

variable {A : Type uA} [NonUnitalRing A]
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [hM : NonUnitalModule A M] [hN : NonUnitalModule A N]
  [hP : NonUnitalModule A P]

/-- Apply the original intertwiner to every actual coordinate. -/
def mapAddHom (f : NonUnitalModuleHom A M N) :
    NonUnitalModuleLeftLimit A M →+ NonUnitalModuleLeftLimit A N where
  toFun x := ⟨fun e => f (x.val e), by
    constructor
    · intro e
      rw [← f.map_smul, x.property.1 e]
    · intro e d hed
      rw [← f.map_smul, x.property.2 e d hed]⟩
  map_zero' := by
    apply Subtype.ext
    funext e
    exact f.map_zero
  map_add' x y := by
    apply Subtype.ext
    funext e
    exact f.map_add (x.val e) (y.val e)

@[simp] theorem mapAddHom_val (f : NonUnitalModuleHom A M N)
    (x : NonUnitalModuleLeftLimit A M) (e : Idempotent A) :
    (mapAddHom f x).val e = f (x.val e) := rfl

/-- The image coordinate is fixed by its original idempotent action. -/
theorem mapAddHom_fixed (f : NonUnitalModuleHom A M N)
    (x : NonUnitalModuleLeftLimit A M) (e : Idempotent A) :
    (e : A) • (mapAddHom f x).val e = (mapAddHom f x).val e :=
  (mapAddHom f x).property.1 e

/-- The image family satisfies the original left transition equations. -/
theorem mapAddHom_coherent (f : NonUnitalModuleHom A M N)
    (x : NonUnitalModuleLeftLimit A M) (e d : Idempotent A) (hed : e ≤ d) :
    (e : A) • (mapAddHom f x).val d = (mapAddHom f x).val e :=
  (mapAddHom f x).property.2 e d hed

@[simp] theorem mapAddHom_id :
    mapAddHom (NonUnitalModuleHom.id A M) =
      AddMonoidHom.id (NonUnitalModuleLeftLimit A M) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem mapAddHom_comp (g : NonUnitalModuleHom A N P)
    (f : NonUnitalModuleHom A M N) :
    mapAddHom (g.comp f) = (mapAddHom g).comp (mapAddHom f) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem mapAddHom_zero :
    mapAddHom (0 : NonUnitalModuleHom A M N) = 0 := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem mapAddHom_add (f g : NonUnitalModuleHom A M N) :
    mapAddHom (f + g) = mapAddHom f + mapAddHom g := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem mapAddHom_neg (f : NonUnitalModuleHom A M N) :
    mapAddHom (-f) = -mapAddHom f := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  rfl

/-- Coordinatewise extension is additive on the original intertwiner group. -/
def mapAddHomAddHom :
    NonUnitalModuleHom A M N →+
      (NonUnitalModuleLeftLimit A M →+ NonUnitalModuleLeftLimit A N) where
  toFun := mapAddHom
  map_zero' := mapAddHom_zero
  map_add' := mapAddHom_add

@[simp] theorem mapAddHomAddHom_apply (f : NonUnitalModuleHom A M N) :
    mapAddHomAddHom f = mapAddHom f := rfl

/-- The original canonical family commutes with every original intertwiner. -/
theorem mapAddHom_canonical (f : NonUnitalModuleHom A M N) (m : M) :
    mapAddHom f (canonical (A := A) m) = canonical (f m) := by
  apply Subtype.ext
  funext e
  exact f.map_smul (e : A) m

/-- Naturality as an equality of entire additive maps, without local units. -/
theorem mapAddHom_comp_canonical (f : NonUnitalModuleHom A M N) :
    (mapAddHom f).comp canonical = canonical.comp f.toAddMonoidHom := by
  apply AddMonoidHom.ext
  exact mapAddHom_canonical f

/-- A shared right local unit proves equivariance for the actual family actions. -/
theorem mapAddHom_scalarAction (hA : IsIdempotented A)
    (f : NonUnitalModuleHom A M N) (a : A) (x : NonUnitalModuleLeftLimit A M) :
    mapAddHom f (scalarAction hA a x) = scalarAction hA a (mapAddHom f x) := by
  apply Subtype.ext
  funext e
  classical
  obtain ⟨d, hd⟩ := (IsIdempotented.iff_two_sided_local_units.mp hA) {(e : A) * a}
  have hed : ((e : A) * a) * (d : A) = (e : A) * a :=
    (hd ((e : A) * a) (by simp)).2
  change f ((scalarAction hA a x).val e) = _
  rw [scalarAction_val hA a x e d hed,
    scalarAction_val hA a (mapAddHom f x) e d hed]
  exact f.map_smul ((e : A) * a) (x.val d)

/-- The full coordinate additive map, equipped with its actual intertwining law. -/
def mapHom (hA : IsIdempotented A) (f : NonUnitalModuleHom A M N) :
    @NonUnitalModuleHom A (NonUnitalModuleLeftLimit A M) (NonUnitalModuleLeftLimit A N)
      _ _ _ (nonUnitalModule hA) (nonUnitalModule hA) := by
  letI := nonUnitalModule (M := M) hA
  letI := nonUnitalModule (M := N) hA
  exact
    { toAddMonoidHom := mapAddHom f
      map_smul' := mapAddHom_scalarAction hA f }

@[simp] theorem mapHom_toAddMonoidHom (hA : IsIdempotented A)
    (f : NonUnitalModuleHom A M N) :
    letI := nonUnitalModule (M := M) hA
    letI := nonUnitalModule (M := N) hA
    (mapHom hA f).toAddMonoidHom = mapAddHom f := rfl

@[simp] theorem mapHom_val (hA : IsIdempotented A) (f : NonUnitalModuleHom A M N)
    (x : NonUnitalModuleLeftLimit A M) (e : Idempotent A) :
    letI := nonUnitalModule (M := M) hA
    letI := nonUnitalModule (M := N) hA
    (mapHom hA f x).val e = f (x.val e) := rfl

@[simp] theorem mapHom_id (hA : IsIdempotented A) :
    let _ := nonUnitalModule (M := M) hA
    mapHom hA (NonUnitalModuleHom.id A M) =
      NonUnitalModuleHom.id A (NonUnitalModuleLeftLimit A M) := by
  let _ := nonUnitalModule (M := M) hA
  apply NonUnitalModuleHom.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem mapHom_comp (hA : IsIdempotented A)
    (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N) :
    let _ := nonUnitalModule (M := M) hA
    let _ := nonUnitalModule (M := N) hA
    let _ := nonUnitalModule (M := P) hA
    mapHom hA (g.comp f) = (mapHom hA g).comp (mapHom hA f) := by
  let _ := nonUnitalModule (M := M) hA
  let _ := nonUnitalModule (M := N) hA
  let _ := nonUnitalModule (M := P) hA
  apply NonUnitalModuleHom.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem mapHom_zero (hA : IsIdempotented A) :
    let _ := nonUnitalModule (M := M) hA
    let _ := nonUnitalModule (M := N) hA
    mapHom hA (0 : NonUnitalModuleHom A M N) = 0 := by
  let _ := nonUnitalModule (M := M) hA
  let _ := nonUnitalModule (M := N) hA
  apply NonUnitalModuleHom.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem mapHom_add (hA : IsIdempotented A) (f g : NonUnitalModuleHom A M N) :
    let _ := nonUnitalModule (M := M) hA
    let _ := nonUnitalModule (M := N) hA
    mapHom hA (f + g) = mapHom hA f + mapHom hA g := by
  let _ := nonUnitalModule (M := M) hA
  let _ := nonUnitalModule (M := N) hA
  apply NonUnitalModuleHom.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem mapHom_neg (hA : IsIdempotented A) (f : NonUnitalModuleHom A M N) :
    let _ := nonUnitalModule (M := M) hA
    let _ := nonUnitalModule (M := N) hA
    mapHom hA (-f) = -mapHom hA f := by
  let _ := nonUnitalModule (M := M) hA
  let _ := nonUnitalModule (M := N) hA
  apply NonUnitalModuleHom.ext
  intro x
  apply Subtype.ext
  rfl

/-- Extension is an additive map on the actual original intertwiner groups. -/
def mapHomAddHom (hA : IsIdempotented A) :
    letI := nonUnitalModule (M := M) hA
    letI := nonUnitalModule (M := N) hA
    NonUnitalModuleHom A M N →+
      NonUnitalModuleHom A (NonUnitalModuleLeftLimit A M) (NonUnitalModuleLeftLimit A N) := by
  letI := nonUnitalModule (M := M) hA
  letI := nonUnitalModule (M := N) hA
  exact
    { toFun := mapHom hA
      map_zero' := mapHom_zero hA
      map_add' := mapHom_add hA }

@[simp] theorem mapHomAddHom_apply (hA : IsIdempotented A)
    (f : NonUnitalModuleHom A M N) :
    letI := nonUnitalModule (M := M) hA
    letI := nonUnitalModule (M := N) hA
    mapHomAddHom hA f = mapHom hA f := rfl

/-- Naturality retains the complete actual intertwiners and original actions. -/
theorem mapHom_comp_canonicalHom (hA : IsIdempotented A)
    (f : NonUnitalModuleHom A M N) :
    let _ := nonUnitalModule (M := M) hA
    let _ := nonUnitalModule (M := N) hA
    (mapHom hA f).comp (canonicalHom hA) = (canonicalHom hA).comp f := by
  let _ := nonUnitalModule (M := M) hA
  let _ := nonUnitalModule (M := N) hA
  apply NonUnitalModuleHom.ext
  exact mapAddHom_canonical f

end NonUnitalModuleLeftLimit

variable {A : Type uA} [NonUnitalRing A]

/-- Ambient completion, with the actual family carrier in `Type (max uA uM)`. -/
def nonUnitalModuleCompletionFunctor (hA : IsIdempotented A) :
    NonUnitalModuleCat.{uA, uM} A ⥤ NonUnitalModuleCat.{uA, max uA uM} A where
  obj M := by
    letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
    exact NonUnitalModuleCat.of A (NonUnitalModuleLeftLimit A M)
  map f := NonUnitalModuleLeftLimit.mapHom hA f
  map_id _ := NonUnitalModuleLeftLimit.mapHom_id hA
  map_comp f g := NonUnitalModuleLeftLimit.mapHom_comp hA g f

@[simp] theorem nonUnitalModuleCompletionFunctor_obj (hA : IsIdempotented A)
    (M : NonUnitalModuleCat.{uA, uM} A) :
    ((nonUnitalModuleCompletionFunctor hA).obj M : Type (max uA uM)) =
      NonUnitalModuleLeftLimit A M := rfl

@[simp] theorem nonUnitalModuleCompletionFunctor_obj_action (hA : IsIdempotented A)
    (M : NonUnitalModuleCat.{uA, uM} A) :
    ((nonUnitalModuleCompletionFunctor hA).obj M).isModule =
      NonUnitalModuleLeftLimit.nonUnitalModule hA := rfl

@[simp] theorem nonUnitalModuleCompletionFunctor_map (hA : IsIdempotented A)
    {M N : NonUnitalModuleCat.{uA, uM} A} (f : M ⟶ N) :
    (nonUnitalModuleCompletionFunctor hA).map f =
      NonUnitalModuleLeftLimit.mapHom hA f := rfl

@[simp] theorem nonUnitalModuleCompletionFunctor_map_toAddMonoidHom (hA : IsIdempotented A)
    {M N : NonUnitalModuleCat.{uA, uM} A} (f : M ⟶ N) :
    ((nonUnitalModuleCompletionFunctor hA).map f).toAddMonoidHom =
      NonUnitalModuleLeftLimit.mapAddHom f := rfl

@[simp] theorem nonUnitalModuleCompletionFunctor_map_val (hA : IsIdempotented A)
    {M N : NonUnitalModuleCat.{uA, uM} A} (f : M ⟶ N)
    (x : NonUnitalModuleLeftLimit A M) (e : Idempotent A) :
    (((nonUnitalModuleCompletionFunctor hA).map f).toAddMonoidHom x).val e =
      f.toAddMonoidHom (x.val e) := rfl

/-- Ambient completion preserves the published pointwise Hom addition. -/
instance nonUnitalModuleCompletionFunctor_additive (hA : IsIdempotented A) :
    (nonUnitalModuleCompletionFunctor.{uA, uM} hA).Additive where
  map_add := by
    intro M N f g
    exact NonUnitalModuleLeftLimit.mapHom_add hA f g

/-- Renard's actual completion functor, with nondegenerate source objects. -/
def nondegenerateModuleCompletionFunctor (hA : IsIdempotented A) :
    NondegenerateModuleCat.{uA, uM} A ⥤ NonUnitalModuleCat.{uA, max uA uM} A :=
  nondegenerateInclusion A ⋙ nonUnitalModuleCompletionFunctor hA

@[simp] theorem nondegenerateModuleCompletionFunctor_obj (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    ((nondegenerateModuleCompletionFunctor hA).obj M : Type (max uA uM)) =
      NonUnitalModuleLeftLimit A M.obj := rfl

@[simp] theorem nondegenerateModuleCompletionFunctor_obj_action (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    ((nondegenerateModuleCompletionFunctor hA).obj M).isModule =
      NonUnitalModuleLeftLimit.nonUnitalModule (M := M.obj) hA := rfl

@[simp] theorem nondegenerateModuleCompletionFunctor_map (hA : IsIdempotented A)
    {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) :
    (nondegenerateModuleCompletionFunctor hA).map f =
      NonUnitalModuleLeftLimit.mapHom hA f.hom := rfl

@[simp] theorem nondegenerateModuleCompletionFunctor_map_toAddMonoidHom
    (hA : IsIdempotented A) {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) :
    ((nondegenerateModuleCompletionFunctor hA).map f).toAddMonoidHom =
      NonUnitalModuleLeftLimit.mapAddHom f.hom := rfl

@[simp] theorem nondegenerateModuleCompletionFunctor_map_val (hA : IsIdempotented A)
    {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N)
    (x : NonUnitalModuleLeftLimit A M.obj) (e : Idempotent A) :
    (((nondegenerateModuleCompletionFunctor hA).map f).toAddMonoidHom x).val e =
      f.hom.toAddMonoidHom (x.val e) := rfl

/-- The source restriction is additive for the inherited original Hom groups. -/
instance nondegenerateModuleCompletionFunctor_additive (hA : IsIdempotented A) :
    (nondegenerateModuleCompletionFunctor.{uA, uM} hA).Additive := by
  dsimp only [nondegenerateModuleCompletionFunctor]
  infer_instance

/-- At the saturated universe the actual canonical maps form a natural transformation. -/
def nonUnitalModuleCompletionCanonical (hA : IsIdempotented A) :
    𝟭 (NonUnitalModuleCat.{uA, max uA uM} A) ⟶
      nonUnitalModuleCompletionFunctor.{uA, max uA uM} hA where
  app M := NonUnitalModuleLeftLimit.canonicalHom hA
  naturality := by
    intro M N f
    exact (NonUnitalModuleLeftLimit.mapHom_comp_canonicalHom hA f).symm

@[simp] theorem nonUnitalModuleCompletionCanonical_app (hA : IsIdempotented A)
    (M : NonUnitalModuleCat.{uA, max uA uM} A) :
    (nonUnitalModuleCompletionCanonical hA).app M =
      NonUnitalModuleLeftLimit.canonicalHom (M := M) hA := rfl

@[simp] theorem nonUnitalModuleCompletionCanonical_app_toAddMonoidHom
    (hA : IsIdempotented A) (M : NonUnitalModuleCat.{uA, max uA uM} A) :
    ((nonUnitalModuleCompletionCanonical hA).app M).toAddMonoidHom =
      NonUnitalModuleLeftLimit.canonical := rfl

@[simp] theorem nonUnitalModuleCompletionCanonical_app_val
    (hA : IsIdempotented A) (M : NonUnitalModuleCat.{uA, max uA uM} A)
    (m : M) (e : Idempotent A) :
    (((nonUnitalModuleCompletionCanonical hA).app M).toAddMonoidHom m).val e = (e : A) • m := rfl

/-! Complete unapplied interfaces keep independent scalar and vector universes. -/

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → {N : Type uN} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    NonUnitalModuleHom A M N →
      (NonUnitalModuleLeftLimit A M →+ NonUnitalModuleLeftLimit A N) :=
  @NonUnitalModuleLeftLimit.mapAddHom.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → {N : Type uN} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (f : NonUnitalModuleHom A M N) → (x : NonUnitalModuleLeftLimit A M) →
    (e : Idempotent A) → (NonUnitalModuleLeftLimit.mapAddHom f x).val e = f (x.val e) :=
  @NonUnitalModuleLeftLimit.mapAddHom_val.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → {N : Type uN} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → (f : NonUnitalModuleHom A M N) →
    @NonUnitalModuleHom A (NonUnitalModuleLeftLimit A M) (NonUnitalModuleLeftLimit A N)
      _ _ _ (NonUnitalModuleLeftLimit.nonUnitalModule hA)
      (NonUnitalModuleLeftLimit.nonUnitalModule hA) :=
  @NonUnitalModuleLeftLimit.mapHom.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → {N : Type uN} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → (f : NonUnitalModuleHom A M N) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
     letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := N) hA
     (NonUnitalModuleLeftLimit.mapHom hA f).toAddMonoidHom =
       NonUnitalModuleLeftLimit.mapAddHom f) :=
  @NonUnitalModuleLeftLimit.mapHom_toAddMonoidHom.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → {N : Type uN} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → (f : NonUnitalModuleHom A M N) →
    (x : NonUnitalModuleLeftLimit A M) → (e : Idempotent A) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
     letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := N) hA
     (NonUnitalModuleLeftLimit.mapHom hA f x).val e = f (x.val e)) :=
  @NonUnitalModuleLeftLimit.mapHom_val.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → {N : Type uN} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → (f : NonUnitalModuleHom A M N) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
     letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := N) hA
     (NonUnitalModuleLeftLimit.mapHom hA f).comp
         (NonUnitalModuleLeftLimit.canonicalHom hA) =
       (NonUnitalModuleLeftLimit.canonicalHom hA).comp f) :=
  @NonUnitalModuleLeftLimit.mapHom_comp_canonicalHom.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    NonUnitalModuleCat.{uA, uM} A ⥤ NonUnitalModuleCat.{uA, max uA uM} A :=
  @nonUnitalModuleCompletionFunctor.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nonUnitalModuleCompletionFunctor.{uA, uM} hA).Additive :=
  @nonUnitalModuleCompletionFunctor_additive.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    NondegenerateModuleCat.{uA, uM} A ⥤ NonUnitalModuleCat.{uA, max uA uM} A :=
  @nondegenerateModuleCompletionFunctor.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegenerateModuleCompletionFunctor.{uA, uM} hA).Additive :=
  @nondegenerateModuleCompletionFunctor_additive.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NonUnitalModuleCat.{uA, uM} A) →
    ((nonUnitalModuleCompletionFunctor hA).obj M : Type (max uA uM)) =
      NonUnitalModuleLeftLimit A M :=
  @nonUnitalModuleCompletionFunctor_obj.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NonUnitalModuleCat.{uA, uM} A} → (f : M ⟶ N) →
    ((nonUnitalModuleCompletionFunctor hA).map f).toAddMonoidHom =
      NonUnitalModuleLeftLimit.mapAddHom f :=
  @nonUnitalModuleCompletionFunctor_map_toAddMonoidHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    𝟭 (NonUnitalModuleCat.{uA, max uA uM} A) ⟶
      nonUnitalModuleCompletionFunctor.{uA, max uA uM} hA :=
  @nonUnitalModuleCompletionCanonical.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NonUnitalModuleCat.{uA, max uA uM} A) →
    (nonUnitalModuleCompletionCanonical hA).app M =
      NonUnitalModuleLeftLimit.canonicalHom (M := M) hA :=
  @nonUnitalModuleCompletionCanonical_app.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NonUnitalModuleCat.{uA, max uA uM} A) →
    ((nonUnitalModuleCompletionCanonical hA).app M).toAddMonoidHom =
      NonUnitalModuleLeftLimit.canonical :=
  @nonUnitalModuleCompletionCanonical_app_toAddMonoidHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NonUnitalModuleCat.{uA, max uA uM} A) → (m : M) → (e : Idempotent A) →
    (((nonUnitalModuleCompletionCanonical hA).app M).toAddMonoidHom m).val e =
      (e : A) • m :=
  @nonUnitalModuleCompletionCanonical_app_val.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NonUnitalModuleCat.{uA, uM} A) →
    ((nonUnitalModuleCompletionFunctor hA).obj M).isModule =
      NonUnitalModuleLeftLimit.nonUnitalModule hA :=
  @nonUnitalModuleCompletionFunctor_obj_action.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NonUnitalModuleCat.{uA, uM} A} → (f : M ⟶ N) →
    (nonUnitalModuleCompletionFunctor hA).map f =
      NonUnitalModuleLeftLimit.mapHom hA f :=
  @nonUnitalModuleCompletionFunctor_map.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NonUnitalModuleCat.{uA, uM} A} → (f : M ⟶ N) →
    (x : NonUnitalModuleLeftLimit A M) → (e : Idempotent A) →
    (((nonUnitalModuleCompletionFunctor hA).map f).toAddMonoidHom x).val e =
      f.toAddMonoidHom (x.val e) :=
  @nonUnitalModuleCompletionFunctor_map_val.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NondegenerateModuleCat.{uA, uM} A) →
    ((nondegenerateModuleCompletionFunctor hA).obj M : Type (max uA uM)) =
      NonUnitalModuleLeftLimit A M.obj :=
  @nondegenerateModuleCompletionFunctor_obj.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NondegenerateModuleCat.{uA, uM} A) →
    ((nondegenerateModuleCompletionFunctor hA).obj M).isModule =
      NonUnitalModuleLeftLimit.nonUnitalModule (M := M.obj) hA :=
  @nondegenerateModuleCompletionFunctor_obj_action.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NondegenerateModuleCat.{uA, uM} A} → (f : M ⟶ N) →
    (nondegenerateModuleCompletionFunctor hA).map f =
      NonUnitalModuleLeftLimit.mapHom hA f.hom :=
  @nondegenerateModuleCompletionFunctor_map.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NondegenerateModuleCat.{uA, uM} A} → (f : M ⟶ N) →
    ((nondegenerateModuleCompletionFunctor hA).map f).toAddMonoidHom =
      NonUnitalModuleLeftLimit.mapAddHom f.hom :=
  @nondegenerateModuleCompletionFunctor_map_toAddMonoidHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NondegenerateModuleCat.{uA, uM} A} → (f : M ⟶ N) →
    (x : NonUnitalModuleLeftLimit A M.obj) → (e : Idempotent A) →
    (((nondegenerateModuleCompletionFunctor hA).map f).toAddMonoidHom x).val e =
      f.hom.toAddMonoidHom (x.val e) :=
  @nondegenerateModuleCompletionFunctor_map_val.{uA, uM}

/-! Unequal universe assignment (0, 1). -/

example : {A : Type 0} → [NonUnitalRing A] →
    {M : Type 1} → {N : Type 1} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    NonUnitalModuleHom A M N →
      (NonUnitalModuleLeftLimit A M →+ NonUnitalModuleLeftLimit A N) :=
  @NonUnitalModuleLeftLimit.mapAddHom.{0, 1, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    {M : Type 1} → {N : Type 1} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (f : NonUnitalModuleHom A M N) → (x : NonUnitalModuleLeftLimit A M) →
    (e : Idempotent A) → (NonUnitalModuleLeftLimit.mapAddHom f x).val e = f (x.val e) :=
  @NonUnitalModuleLeftLimit.mapAddHom_val.{0, 1, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    {M : Type 1} → {N : Type 1} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → (f : NonUnitalModuleHom A M N) →
    @NonUnitalModuleHom A (NonUnitalModuleLeftLimit A M) (NonUnitalModuleLeftLimit A N)
      _ _ _ (NonUnitalModuleLeftLimit.nonUnitalModule hA)
      (NonUnitalModuleLeftLimit.nonUnitalModule hA) :=
  @NonUnitalModuleLeftLimit.mapHom.{0, 1, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    {M : Type 1} → {N : Type 1} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → (f : NonUnitalModuleHom A M N) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
     letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := N) hA
     (NonUnitalModuleLeftLimit.mapHom hA f).toAddMonoidHom =
       NonUnitalModuleLeftLimit.mapAddHom f) :=
  @NonUnitalModuleLeftLimit.mapHom_toAddMonoidHom.{0, 1, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    {M : Type 1} → {N : Type 1} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → (f : NonUnitalModuleHom A M N) →
    (x : NonUnitalModuleLeftLimit A M) → (e : Idempotent A) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
     letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := N) hA
     (NonUnitalModuleLeftLimit.mapHom hA f x).val e = f (x.val e)) :=
  @NonUnitalModuleLeftLimit.mapHom_val.{0, 1, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    {M : Type 1} → {N : Type 1} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → (f : NonUnitalModuleHom A M N) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
     letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := N) hA
     (NonUnitalModuleLeftLimit.mapHom hA f).comp
         (NonUnitalModuleLeftLimit.canonicalHom hA) =
       (NonUnitalModuleLeftLimit.canonicalHom hA).comp f) :=
  @NonUnitalModuleLeftLimit.mapHom_comp_canonicalHom.{0, 1, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    NonUnitalModuleCat.{0, 1} A ⥤ NonUnitalModuleCat.{0, max 0 1} A :=
  @nonUnitalModuleCompletionFunctor.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nonUnitalModuleCompletionFunctor.{0, 1} hA).Additive :=
  @nonUnitalModuleCompletionFunctor_additive.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    NondegenerateModuleCat.{0, 1} A ⥤ NonUnitalModuleCat.{0, max 0 1} A :=
  @nondegenerateModuleCompletionFunctor.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegenerateModuleCompletionFunctor.{0, 1} hA).Additive :=
  @nondegenerateModuleCompletionFunctor_additive.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NonUnitalModuleCat.{0, 1} A) →
    ((nonUnitalModuleCompletionFunctor hA).obj M : Type (max 0 1)) =
      NonUnitalModuleLeftLimit A M :=
  @nonUnitalModuleCompletionFunctor_obj.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NonUnitalModuleCat.{0, 1} A} → (f : M ⟶ N) →
    ((nonUnitalModuleCompletionFunctor hA).map f).toAddMonoidHom =
      NonUnitalModuleLeftLimit.mapAddHom f :=
  @nonUnitalModuleCompletionFunctor_map_toAddMonoidHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    𝟭 (NonUnitalModuleCat.{0, max 0 1} A) ⟶
      nonUnitalModuleCompletionFunctor.{0, max 0 1} hA :=
  @nonUnitalModuleCompletionCanonical.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NonUnitalModuleCat.{0, max 0 1} A) →
    (nonUnitalModuleCompletionCanonical.{0, 1} hA).app M =
      NonUnitalModuleLeftLimit.canonicalHom (M := M) hA :=
  @nonUnitalModuleCompletionCanonical_app.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NonUnitalModuleCat.{0, max 0 1} A) →
    ((nonUnitalModuleCompletionCanonical.{0, 1} hA).app M).toAddMonoidHom =
      NonUnitalModuleLeftLimit.canonical :=
  @nonUnitalModuleCompletionCanonical_app_toAddMonoidHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NonUnitalModuleCat.{0, max 0 1} A) → (m : M) → (e : Idempotent A) →
    (((nonUnitalModuleCompletionCanonical.{0, 1} hA).app M).toAddMonoidHom m).val e =
      (e : A) • m :=
  @nonUnitalModuleCompletionCanonical_app_val.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NonUnitalModuleCat.{0, 1} A) →
    ((nonUnitalModuleCompletionFunctor hA).obj M).isModule =
      NonUnitalModuleLeftLimit.nonUnitalModule hA :=
  @nonUnitalModuleCompletionFunctor_obj_action.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NonUnitalModuleCat.{0, 1} A} → (f : M ⟶ N) →
    (nonUnitalModuleCompletionFunctor hA).map f =
      NonUnitalModuleLeftLimit.mapHom hA f :=
  @nonUnitalModuleCompletionFunctor_map.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NonUnitalModuleCat.{0, 1} A} → (f : M ⟶ N) →
    (x : NonUnitalModuleLeftLimit A M) → (e : Idempotent A) →
    (((nonUnitalModuleCompletionFunctor hA).map f).toAddMonoidHom x).val e =
      f.toAddMonoidHom (x.val e) :=
  @nonUnitalModuleCompletionFunctor_map_val.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NondegenerateModuleCat.{0, 1} A) →
    ((nondegenerateModuleCompletionFunctor hA).obj M : Type (max 0 1)) =
      NonUnitalModuleLeftLimit A M.obj :=
  @nondegenerateModuleCompletionFunctor_obj.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NondegenerateModuleCat.{0, 1} A) →
    ((nondegenerateModuleCompletionFunctor hA).obj M).isModule =
      NonUnitalModuleLeftLimit.nonUnitalModule (M := M.obj) hA :=
  @nondegenerateModuleCompletionFunctor_obj_action.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NondegenerateModuleCat.{0, 1} A} → (f : M ⟶ N) →
    (nondegenerateModuleCompletionFunctor hA).map f =
      NonUnitalModuleLeftLimit.mapHom hA f.hom :=
  @nondegenerateModuleCompletionFunctor_map.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NondegenerateModuleCat.{0, 1} A} → (f : M ⟶ N) →
    ((nondegenerateModuleCompletionFunctor hA).map f).toAddMonoidHom =
      NonUnitalModuleLeftLimit.mapAddHom f.hom :=
  @nondegenerateModuleCompletionFunctor_map_toAddMonoidHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NondegenerateModuleCat.{0, 1} A} → (f : M ⟶ N) →
    (x : NonUnitalModuleLeftLimit A M.obj) → (e : Idempotent A) →
    (((nondegenerateModuleCompletionFunctor hA).map f).toAddMonoidHom x).val e =
      f.hom.toAddMonoidHom (x.val e) :=
  @nondegenerateModuleCompletionFunctor_map_val.{0, 1}

/-! Unequal universe assignment (1, 0). -/

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type 0} → {N : Type 0} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    NonUnitalModuleHom A M N →
      (NonUnitalModuleLeftLimit A M →+ NonUnitalModuleLeftLimit A N) :=
  @NonUnitalModuleLeftLimit.mapAddHom.{1, 0, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type 0} → {N : Type 0} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (f : NonUnitalModuleHom A M N) → (x : NonUnitalModuleLeftLimit A M) →
    (e : Idempotent A) → (NonUnitalModuleLeftLimit.mapAddHom f x).val e = f (x.val e) :=
  @NonUnitalModuleLeftLimit.mapAddHom_val.{1, 0, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type 0} → {N : Type 0} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → (f : NonUnitalModuleHom A M N) →
    @NonUnitalModuleHom A (NonUnitalModuleLeftLimit A M) (NonUnitalModuleLeftLimit A N)
      _ _ _ (NonUnitalModuleLeftLimit.nonUnitalModule hA)
      (NonUnitalModuleLeftLimit.nonUnitalModule hA) :=
  @NonUnitalModuleLeftLimit.mapHom.{1, 0, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type 0} → {N : Type 0} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → (f : NonUnitalModuleHom A M N) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
     letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := N) hA
     (NonUnitalModuleLeftLimit.mapHom hA f).toAddMonoidHom =
       NonUnitalModuleLeftLimit.mapAddHom f) :=
  @NonUnitalModuleLeftLimit.mapHom_toAddMonoidHom.{1, 0, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type 0} → {N : Type 0} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → (f : NonUnitalModuleHom A M N) →
    (x : NonUnitalModuleLeftLimit A M) → (e : Idempotent A) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
     letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := N) hA
     (NonUnitalModuleLeftLimit.mapHom hA f x).val e = f (x.val e)) :=
  @NonUnitalModuleLeftLimit.mapHom_val.{1, 0, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type 0} → {N : Type 0} → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → (f : NonUnitalModuleHom A M N) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
     letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := N) hA
     (NonUnitalModuleLeftLimit.mapHom hA f).comp
         (NonUnitalModuleLeftLimit.canonicalHom hA) =
       (NonUnitalModuleLeftLimit.canonicalHom hA).comp f) :=
  @NonUnitalModuleLeftLimit.mapHom_comp_canonicalHom.{1, 0, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    NonUnitalModuleCat.{1, 0} A ⥤ NonUnitalModuleCat.{1, max 1 0} A :=
  @nonUnitalModuleCompletionFunctor.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nonUnitalModuleCompletionFunctor.{1, 0} hA).Additive :=
  @nonUnitalModuleCompletionFunctor_additive.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    NondegenerateModuleCat.{1, 0} A ⥤ NonUnitalModuleCat.{1, max 1 0} A :=
  @nondegenerateModuleCompletionFunctor.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegenerateModuleCompletionFunctor.{1, 0} hA).Additive :=
  @nondegenerateModuleCompletionFunctor_additive.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NonUnitalModuleCat.{1, 0} A) →
    ((nonUnitalModuleCompletionFunctor hA).obj M : Type (max 1 0)) =
      NonUnitalModuleLeftLimit A M :=
  @nonUnitalModuleCompletionFunctor_obj.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NonUnitalModuleCat.{1, 0} A} → (f : M ⟶ N) →
    ((nonUnitalModuleCompletionFunctor hA).map f).toAddMonoidHom =
      NonUnitalModuleLeftLimit.mapAddHom f :=
  @nonUnitalModuleCompletionFunctor_map_toAddMonoidHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    𝟭 (NonUnitalModuleCat.{1, max 1 0} A) ⟶
      nonUnitalModuleCompletionFunctor.{1, max 1 0} hA :=
  @nonUnitalModuleCompletionCanonical.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NonUnitalModuleCat.{1, max 1 0} A) →
    (nonUnitalModuleCompletionCanonical.{1, 0} hA).app M =
      NonUnitalModuleLeftLimit.canonicalHom (M := M) hA :=
  @nonUnitalModuleCompletionCanonical_app.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NonUnitalModuleCat.{1, max 1 0} A) →
    ((nonUnitalModuleCompletionCanonical.{1, 0} hA).app M).toAddMonoidHom =
      NonUnitalModuleLeftLimit.canonical :=
  @nonUnitalModuleCompletionCanonical_app_toAddMonoidHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NonUnitalModuleCat.{1, max 1 0} A) → (m : M) → (e : Idempotent A) →
    (((nonUnitalModuleCompletionCanonical.{1, 0} hA).app M).toAddMonoidHom m).val e =
      (e : A) • m :=
  @nonUnitalModuleCompletionCanonical_app_val.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NonUnitalModuleCat.{1, 0} A) →
    ((nonUnitalModuleCompletionFunctor hA).obj M).isModule =
      NonUnitalModuleLeftLimit.nonUnitalModule hA :=
  @nonUnitalModuleCompletionFunctor_obj_action.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NonUnitalModuleCat.{1, 0} A} → (f : M ⟶ N) →
    (nonUnitalModuleCompletionFunctor hA).map f =
      NonUnitalModuleLeftLimit.mapHom hA f :=
  @nonUnitalModuleCompletionFunctor_map.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NonUnitalModuleCat.{1, 0} A} → (f : M ⟶ N) →
    (x : NonUnitalModuleLeftLimit A M) → (e : Idempotent A) →
    (((nonUnitalModuleCompletionFunctor hA).map f).toAddMonoidHom x).val e =
      f.toAddMonoidHom (x.val e) :=
  @nonUnitalModuleCompletionFunctor_map_val.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NondegenerateModuleCat.{1, 0} A) →
    ((nondegenerateModuleCompletionFunctor hA).obj M : Type (max 1 0)) =
      NonUnitalModuleLeftLimit A M.obj :=
  @nondegenerateModuleCompletionFunctor_obj.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NondegenerateModuleCat.{1, 0} A) →
    ((nondegenerateModuleCompletionFunctor hA).obj M).isModule =
      NonUnitalModuleLeftLimit.nonUnitalModule (M := M.obj) hA :=
  @nondegenerateModuleCompletionFunctor_obj_action.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NondegenerateModuleCat.{1, 0} A} → (f : M ⟶ N) →
    (nondegenerateModuleCompletionFunctor hA).map f =
      NonUnitalModuleLeftLimit.mapHom hA f.hom :=
  @nondegenerateModuleCompletionFunctor_map.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NondegenerateModuleCat.{1, 0} A} → (f : M ⟶ N) →
    ((nondegenerateModuleCompletionFunctor hA).map f).toAddMonoidHom =
      NonUnitalModuleLeftLimit.mapAddHom f.hom :=
  @nondegenerateModuleCompletionFunctor_map_toAddMonoidHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NondegenerateModuleCat.{1, 0} A} → (f : M ⟶ N) →
    (x : NonUnitalModuleLeftLimit A M.obj) → (e : Idempotent A) →
    (((nondegenerateModuleCompletionFunctor hA).map f).toAddMonoidHom x).val e =
      f.hom.toAddMonoidHom (x.val e) :=
  @nondegenerateModuleCompletionFunctor_map_val.{1, 0}

/-! On equal carriers the original zero action remains explicit. -/

example (A : Type uA) [NonUnitalRing A] :
    letI : NonUnitalModule A A := NonUnitalModule.zero
    NonUnitalModuleLeftLimit A A →+ NonUnitalModuleLeftLimit A A := by
  letI : NonUnitalModule A A := NonUnitalModule.zero
  exact NonUnitalModuleLeftLimit.mapAddHom (NonUnitalModuleHom.id A A)

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    letI : NonUnitalModule A A := NonUnitalModule.zero
    letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := A) hA
    (NonUnitalModuleLeftLimit.mapHom hA (NonUnitalModuleHom.id A A)).toAddMonoidHom =
      NonUnitalModuleLeftLimit.mapAddHom (NonUnitalModuleHom.id A A) := by
  exact @NonUnitalModuleLeftLimit.mapHom_toAddMonoidHom A _ A A _ _
    (NonUnitalModule.zero (A := A) (M := A))
    (NonUnitalModule.zero (A := A) (M := A)) hA
    (@NonUnitalModuleHom.id A A _ _ (NonUnitalModule.zero (A := A) (M := A)))

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    letI : NonUnitalModule A A := NonUnitalModule.zero
    ((nonUnitalModuleCompletionFunctor hA).obj (NonUnitalModuleCat.of A A) : Type uA) =
      NonUnitalModuleLeftLimit A A := rfl

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    letI : NonUnitalModule A A := NonUnitalModule.zero
    ∀ (a : A) (x : NonUnitalModuleLeftLimit A A) (e : Idempotent A),
      (NonUnitalModuleLeftLimit.mapAddHom (NonUnitalModuleHom.id A A)
        (NonUnitalModuleLeftLimit.scalarAction hA a x)).val e =
        (NonUnitalModuleLeftLimit.scalarAction hA a
          (NonUnitalModuleLeftLimit.mapAddHom (NonUnitalModuleHom.id A A) x)).val e := by
  intro a x e
  exact congrArg (fun y : @NonUnitalModuleLeftLimit A A _ _
    (NonUnitalModule.zero (A := A) (M := A)) => y.val e)
    (@NonUnitalModuleLeftLimit.mapAddHom_scalarAction A _ A A _ _
      (NonUnitalModule.zero (A := A) (M := A))
      (NonUnitalModule.zero (A := A) (M := A)) hA
      (@NonUnitalModuleHom.id A A _ _ (NonUnitalModule.zero (A := A) (M := A))) a x)

end Langlands.Algebra
