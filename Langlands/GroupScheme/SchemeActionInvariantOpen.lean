import Langlands.GroupScheme.SchemeAction
import Langlands.GroupScheme.SchemeActionOfPointLaws
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Restricting a scheme action to an invariant open subscheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchemeAction

variable {S : Scheme.{u}} {H : GroupScheme S} {X : Over S}

/-- The actual open subscheme with its inherited structure map. -/
def openSubscheme (V : X.left.Opens) : Over S :=
  Over.mk (V.ι ≫ X.hom)

/-- Inclusion of an actual open subscheme over the same base. -/
def openSubschemeι (V : X.left.Opens) : openSubscheme V ⟶ X :=
  Over.homMk V.ι

instance (V : X.left.Opens) : Mono (openSubschemeι V) := by
  have : Mono (openSubschemeι V).left := by
    change Mono V.ι
    infer_instance
  exact Over.mono_of_mono_left _

instance (V : X.left.Opens) [IsAffine V] : IsAffine (openSubscheme V).left :=
  inferInstanceAs (IsAffine V)

/-- Factor an actual morphism whose scheme image lies in an open subscheme. -/
def liftToOpen (V : X.left.Opens) {Z : Over S} (f : Z ⟶ X)
    (hf : Set.range f.left ⊆ V) : Z ⟶ openSubscheme V := by
  have hr : Set.range f.left ⊆ Set.range V.ι := by
    simpa only [Scheme.Opens.range_ι] using hf
  let g : Z.left ⟶ V.toScheme := IsOpenImmersion.lift V.ι f.left hr
  refine Over.homMk g ?_
  change IsOpenImmersion.lift V.ι f.left hr ≫ (V.ι ≫ X.hom) = Z.hom
  rw [← Category.assoc, IsOpenImmersion.lift_fac]
  exact Over.w f

@[reassoc (attr := simp)]
theorem liftToOpen_comp (V : X.left.Opens) {Z : Over S} (f : Z ⟶ X)
    (hf : Set.range f.left ⊆ V) :
    liftToOpen V f hf ≫ openSubschemeι V = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac V.ι f.left _

variable (a : SchemeAction H X)

/-- Invariance is equality of inverse-image opens on the actual product scheme. -/
def IsInvariantOpen (V : X.left.Opens) : Prop :=
  a.hom.left ⁻¹ᵁ V = (snd H.X X).left ⁻¹ᵁ V

namespace IsInvariantOpen

variable {a} {V : X.left.Opens} (hV : a.IsInvariantOpen V)

include hV

/-- Invariance controls every test morphism and every underlying scheme point. -/
theorem mem_act_iff {Z : Over S} (h : Z ⟶ H.X) (x : Z ⟶ X) (z : Z.left) :
    (a.act h x).left z ∈ V ↔ x.left z ∈ V := by
  have hz := (SetLike.ext_iff.mp hV) ((lift h x).left z)
  change (a.act h x).left z ∈ V ↔
    (lift h x ≫ snd H.X X).left z ∈ V at hz
  simpa only [lift_snd] using hz

/-- The whole image of a test point stays in the open exactly when it starts there. -/
theorem range_act_subset_iff {Z : Over S} (h : Z ⟶ H.X) (x : Z ⟶ X) :
    Set.range (a.act h x).left ⊆ V ↔ Set.range x.left ⊆ V := by
  constructor
  · intro hx y hy
    obtain ⟨z, rfl⟩ := hy
    exact (hV.mem_act_iff h x z).mp (hx ⟨z, rfl⟩)
  · intro hx y hy
    obtain ⟨z, rfl⟩ := hy
    exact (hV.mem_act_iff h x z).mpr (hx ⟨z, rfl⟩)

end IsInvariantOpen

variable {V : X.left.Opens} (hV : a.IsInvariantOpen V)

include hV

/-- The action morphism factors through the invariant open subscheme. -/
def invariantOpenActionHom : H.X ⊗ openSubscheme V ⟶ openSubscheme V :=
  liftToOpen V (a.act (fst H.X (openSubscheme V))
    (snd H.X (openSubscheme V) ≫ openSubschemeι V))
    ((hV.range_act_subset_iff _ _).mpr (by
      rintro _ ⟨z, rfl⟩
      exact ((snd H.X (openSubscheme V)).left z).property))

@[reassoc]
theorem invariantOpenActionHom_comp :
    a.invariantOpenActionHom hV ≫ openSubschemeι V =
      a.act (fst H.X (openSubscheme V))
        (snd H.X (openSubscheme V) ≫ openSubschemeι V) :=
  liftToOpen_comp _ _ _

/-- Inclusion intertwines the induced action morphism on every scheme test. -/
theorem invariantOpenActionHom_act_comp {Z : Over S}
    (h : Z ⟶ H.X) (x : Z ⟶ openSubscheme V) :
    (lift h x ≫ a.invariantOpenActionHom hV) ≫ openSubschemeι V =
      a.act h (x ≫ openSubschemeι V) := by
  rw [Category.assoc, invariantOpenActionHom_comp, a.naturality]
  simp only [lift_fst, lift_snd_assoc]

/-- The actual categorical action on an invariant open subscheme. -/
@[instance_reducible]
def onInvariantOpen : SchemeAction H (openSubscheme V) :=
  schemeActionOfPointLaws (a.invariantOpenActionHom hV)
    (by
      intro Z x
      apply (cancel_mono (openSubschemeι V)).mp
      rw [invariantOpenActionHom_act_comp, a.act_one])
    (by
      intro Z h h' x
      apply (cancel_mono (openSubschemeι V)).mp
      rw [invariantOpenActionHom_act_comp, invariantOpenActionHom_act_comp,
        invariantOpenActionHom_act_comp, a.act_mul])

/-- The restricted action retains the constructed algebraic action morphism. -/
@[simp]
theorem onInvariantOpen_hom :
    (a.onInvariantOpen hV).hom = a.invariantOpenActionHom hV := rfl

/-- The open immersion is equivariant on points of every test scheme. -/
@[reassoc]
theorem onInvariantOpen_act_comp {Z : Over S}
    (h : Z ⟶ H.X) (x : Z ⟶ openSubscheme V) :
    (a.onInvariantOpen hV).act h x ≫ openSubschemeι V =
      a.act h (x ≫ openSubschemeι V) :=
  a.invariantOpenActionHom_act_comp hV h x

/-- The inclusion preserves and reflects all-test fixed points. -/
theorem isFixed_onInvariantOpen_iff {Z : Over S} (x : Z ⟶ openSubscheme V) :
    (a.onInvariantOpen hV).IsFixed x ↔ a.IsFixed (x ≫ openSubschemeι V) := by
  constructor
  · intro hx Z' b h
    rw [← Category.assoc, ← a.onInvariantOpen_act_comp hV, hx Z' b h]
  · intro hx Z' b h
    apply (cancel_mono (openSubschemeι V)).mp
    rw [onInvariantOpen_act_comp, Category.assoc]
    exact hx Z' b h

/-- An ambient fixed point lying in the open remains fixed in the induced action. -/
theorem isFixed_liftToOpen {Z : Over S} (x : Z ⟶ X)
    (hx : a.IsFixed x) (hxV : Set.range x.left ⊆ V) :
    (a.onInvariantOpen hV).IsFixed (liftToOpen V x hxV) := by
  intro Z' b h
  apply (cancel_mono (openSubschemeι V)).mp
  rw [onInvariantOpen_act_comp, Category.assoc, liftToOpen_comp]
  exact hx Z' b h

end Langlands.GroupScheme.SchemeAction
