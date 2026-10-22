import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Subrepresentation

/-! Actual subfunctors, finite filtrations, and graded representation functors. -/

open CategoryTheory

namespace Langlands

universe uR uG uV uC vC

variable {R : Type uR} {G : Type uG} [CommRing R] [Monoid G]
  {C : Type uC} [Category.{vC} C]

/-- An actual subrepresentation of every value of a functor, preserved by every map.
This is subfunctor data, not an assumed geometric lemma. -/
structure RepSubfunctor (F : C ⥤ Rep.{uV} R G) where
  obj (X : C) : Subrepresentation (F.obj X).ρ
  map_mem {X Y : C} (f : X ⟶ Y) {v : F.obj X} :
    v ∈ obj X → (F.map f).hom v ∈ obj Y

namespace RepSubfunctor

variable {F : C ⥤ Rep.{uV} R G}

/-- The genuine restricted representation at each object. -/
abbrev representation (S : RepSubfunctor F) (X : C) : Rep R G :=
  Rep.of (S.obj X).toRepresentation

/-- Restriction of the original map to the invariant submodules. -/
def map (S : RepSubfunctor F) {X Y : C} (f : X ⟶ Y) :
    S.representation X ⟶ S.representation Y :=
  Rep.ofHom
    { toLinearMap :=
        { toFun := fun v => ⟨(F.map f).hom v, S.map_mem f v.property⟩
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
      isIntertwining' := by
        intro g
        ext v
        exact Rep.hom_comm_apply (F.map f) g v }

@[simp]
theorem map_apply (S : RepSubfunctor F) {X Y : C} (f : X ⟶ Y)
    (v : S.representation X) :
    ((S.map f).hom v : F.obj Y) = (F.map f).hom v := rfl

/-- The restricted functor, with identity and composition laws proved. -/
def toFunctor (S : RepSubfunctor F) : C ⥤ Rep.{uV} R G where
  obj := S.representation
  map := S.map
  map_id X := by
    ext v
    simp [map]
  map_comp f g := by
    ext v
    simp [map]

/-- Canonical natural inclusion into the original functor. -/
def inclusion (S : RepSubfunctor F) : S.toFunctor ⟶ F where
  app X := Rep.ofHom
    { toLinearMap := (S.obj X).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  naturality _ _ _ := rfl

theorem inclusion_injective (S : RepSubfunctor F) (X : C) :
    Function.Injective (S.inclusion.app X).hom :=
  Subtype.val_injective

/-- Pull the lower subrepresentation back to the upper subrepresentation.
When the lower one is contained in the upper one, this is the usual denominator
of their successive quotient. -/
def lowerInUpper (S T : RepSubfunctor F) (X : C) :
    Subrepresentation (T.representation X).ρ where
  toSubmodule := (S.obj X).toSubmodule.comap (T.obj X).toSubmodule.subtype
  apply_mem_toSubmodule g _ hv := (S.obj X).apply_mem_toSubmodule g hv

/-- The actual quotient of the upper submodule by the pulled-back lower one. -/
abbrev quotientObj (S T : RepSubfunctor F) (X : C) : Rep.{uV} R G :=
  (T.representation X).quotient (S.lowerInUpper T X).toSubmodule
    (fun g _ hv => (S.lowerInUpper T X).apply_mem_toSubmodule g hv)

/-- The canonical map from the upper submodule onto its successive quotient. -/
def quotientProjection (S T : RepSubfunctor F) (X : C) :
    T.representation X ⟶ S.quotientObj T X :=
  (T.representation X).mkQ (S.lowerInUpper T X).toSubmodule
    (fun g _ hv => (S.lowerInUpper T X).apply_mem_toSubmodule g hv)

theorem quotientProjection_surjective (S T : RepSubfunctor F) (X : C) :
    Function.Surjective (S.quotientProjection T X).hom :=
  Submodule.mkQ_surjective _

/-- The original functor map descended to the actual successive quotients. -/
def quotientMap (S T : RepSubfunctor F) {X Y : C} (f : X ⟶ Y) :
    S.quotientObj T X ⟶ S.quotientObj T Y :=
  Rep.ofHom
    { toLinearMap := Submodule.mapQ (S.lowerInUpper T X).toSubmodule
        (S.lowerInUpper T Y).toSubmodule (T.map f).hom.toLinearMap
        (fun _ hv => S.map_mem f hv)
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        obtain ⟨v, rfl⟩ := S.quotientProjection_surjective T X v
        change
          (S.lowerInUpper T Y).toSubmodule.mkQ
            ((T.map f).hom ((T.representation X).ρ g v)) =
          (S.lowerInUpper T Y).toSubmodule.mkQ
            ((T.representation Y).ρ g ((T.map f).hom v))
        rw [Rep.hom_comm_apply (T.map f)] }

@[simp]
theorem quotientMap_projection (S T : RepSubfunctor F) {X Y : C} (f : X ⟶ Y)
    (v : T.representation X) :
    (S.quotientMap T f).hom ((S.quotientProjection T X).hom v) =
      (S.quotientProjection T Y).hom ((T.map f).hom v) := rfl

/-- The actual successive-quotient functor. -/
def quotientFunctor (S T : RepSubfunctor F) : C ⥤ Rep.{uV} R G where
  obj := S.quotientObj T
  map := S.quotientMap T
  map_id X := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    obtain ⟨v, rfl⟩ := S.quotientProjection_surjective T X v
    simp only [Rep.hom_id]
    change (S.quotientProjection T X).hom ((T.map (𝟙 X)).hom v) =
      (S.quotientProjection T X).hom v
    have h := congrArg (fun f => f.hom v) (T.toFunctor.map_id X)
    exact congrArg (S.quotientProjection T X).hom h
  map_comp f g := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    obtain ⟨v, rfl⟩ := S.quotientProjection_surjective T _ v
    simp only [Rep.hom_comp]
    have h := congrArg (fun f => f.hom v) (T.toFunctor.map_comp f g)
    exact congrArg (S.quotientProjection T _).hom h

/-- The projection is natural, not merely objectwise surjective. -/
def quotientNatProjection (S T : RepSubfunctor F) :
    T.toFunctor ⟶ S.quotientFunctor T where
  app := S.quotientProjection T
  naturality _ _ _ := rfl

end RepSubfunctor

/-- A finite increasing filtration by actual subfunctors, beginning at zero
and ending at the original representation at every object. Repeated steps
and zero graded pieces are allowed. -/
structure RepFunctorFiltration (F : C ⥤ Rep.{uV} R G) (n : ℕ) where
  step : Fin (n + 1) → RepSubfunctor F
  monotone (X : C) : Monotone (fun i => (step i).obj X)
  zero (X : C) : (step 0).obj X = ⊥
  top (X : C) : (step (Fin.last n)).obj X = ⊤

namespace RepFunctorFiltration

variable {F : C ⥤ Rep.{uV} R G} {n : ℕ}

/-- The ith successive quotient, with i starting at zero. -/
def graded (s : RepFunctorFiltration F n) (i : Fin n) : C ⥤ Rep.{uV} R G :=
  (s.step i.castSucc).quotientFunctor (s.step i.succ)

theorem step_le_next (s : RepFunctorFiltration F n) (X : C) (i : Fin n) :
    (s.step i.castSucc).obj X ≤ (s.step i.succ).obj X :=
  s.monotone X (Nat.le_succ i.val)

/-- All graded identifications are natural isomorphisms of actual functors. -/
def HasGradedPieces (s : RepFunctorFiltration F n)
    (pieces : Fin n → C ⥤ Rep.{uV} R G) : Prop :=
  ∀ i, Nonempty (s.graded i ≅ pieces i)

end RepFunctorFiltration

/-- An ordered list of actual functors occurs as the graded pieces of one
natural finite filtration. This proposition does not assert its own truth. -/
def HasOrderedFiltration (F : C ⥤ Rep.{uV} R G)
    {n : ℕ} (pieces : Fin n → C ⥤ Rep.{uV} R G) : Prop :=
  ∃ s : RepFunctorFiltration F n, s.HasGradedPieces pieces

/-- Bernstein--Zelevinsky's unordered gluing relation: the ordered filtration
may realize a permutation of the supplied finite list of functors. -/
def IsGluedFrom (F : C ⥤ Rep.{uV} R G)
    {n : ℕ} (pieces : Fin n → C ⥤ Rep.{uV} R G) : Prop :=
  ∃ e : Equiv.Perm (Fin n), HasOrderedFiltration F (pieces ∘ e)

end Langlands
