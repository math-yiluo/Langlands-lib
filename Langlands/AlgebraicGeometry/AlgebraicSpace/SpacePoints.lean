import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Points of presheaves and algebraic spaces and their topology

A point of a presheaf `F` on schemes over `S` is an equivalence class of sections of `F` over
spectra of fields, two sections being equivalent when they agree over a common field extension
(Stacks, Properties of Spaces, Section 4). The topology on the points is the final topology for
the maps from the underlying spaces of schemes with an étale map to `F`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A field-valued point of a presheaf `F` on schemes over `S`: a field, a structure morphism
from its spectrum to `S`, and a section of `F` over that spectrum. -/
structure FieldPoint (F : Presheaf S) where
  /-- The field. -/
  field : Type u
  [instField : Field field]
  /-- The structure morphism of the spectrum of the field to `S`. -/
  base : Spec (CommRingCat.of field) ⟶ S
  /-- The section of `F` over the spectrum of the field. -/
  val : F.obj (op (Over.mk base))

attribute [instance] FieldPoint.instField

namespace FieldPoint

variable {F G : Presheaf S}

/-- The test scheme `Spec Ω` over `S` through a field homomorphism `K → Ω`. -/
abbrev extendTest (p : FieldPoint F) {Ω : Type u} [Field Ω] (i : p.field →+* Ω) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom i) ≫ p.base)

/-- The morphism `Spec Ω ⟶ Spec K` over `S`. -/
abbrev extendMap (p : FieldPoint F) {Ω : Type u} [Field Ω] (i : p.field →+* Ω) :
    p.extendTest i ⟶ Over.mk p.base :=
  Over.homMk (Spec.map (CommRingCat.ofHom i)) rfl

/-- Two field-valued points are related when they become equal over a common field: there
are field homomorphisms `i : K → Ω` and `j : L → Ω` compatible with the structure morphisms
such that the two sections pull back to the same section over `Spec Ω`. -/
def Rel (F : Presheaf S) (p q : FieldPoint F) : Prop :=
  ∃ (Ω : Type u) (_ : Field Ω) (i : p.field →+* Ω) (j : q.field →+* Ω)
    (h : Spec.map (CommRingCat.ofHom j) ≫ q.base = Spec.map (CommRingCat.ofHom i) ≫ p.base),
    F.map (p.extendMap i).op p.val =
      F.map (Over.homMk (Spec.map (CommRingCat.ofHom j)) h :
        p.extendTest i ⟶ Over.mk q.base).op q.val

/-- The image of a field-valued point under a natural transformation. -/
def map (f : F ⟶ G) (p : FieldPoint F) : FieldPoint G :=
  ⟨p.field, p.base, f.app _ p.val⟩

theorem map_rel (f : F ⟶ G) {p q : FieldPoint F} (h : Rel F p q) :
    Rel G (p.map f) (q.map f) := by
  obtain ⟨Ω, _, i, j, hb, he⟩ := h
  refine ⟨Ω, inferInstance, i, j, hb, ?_⟩
  have key : ∀ {X Y : (Over S)ᵒᵖ} (φ : X ⟶ Y) (x : F.obj X),
      G.map φ (f.app X x) = f.app Y (F.map φ x) := fun φ x =>
    (ConcreteCategory.congr_hom (f.naturality φ) x).symm
  show G.map (p.extendMap i).op (f.app _ p.val) =
    G.map (Over.homMk (Spec.map (CommRingCat.ofHom j)) hb :
      p.extendTest i ⟶ Over.mk q.base).op (f.app _ q.val)
  rw [key, key, he]

end FieldPoint

/-- The points of a presheaf on schemes over `S`: field-valued points up to the relation of
agreeing over a common field (Stacks, Tag 03BU). -/
def Points (F : Presheaf S) : Type (u + 1) :=
  Quot (FieldPoint.Rel F)

namespace Points

variable {F G H : Presheaf S}

/-- The map on points induced by a natural transformation. -/
def map (f : F ⟶ G) : Points F → Points G :=
  Quot.lift (fun p => Quot.mk _ (p.map f)) (fun _ _ h => Quot.sound (FieldPoint.map_rel f h))

@[simp] theorem map_mk (f : F ⟶ G) (p : FieldPoint F) :
    map f (Quot.mk _ p) = Quot.mk _ (p.map f) := rfl

theorem map_id (x : Points F) : map (𝟙 F) x = x := by
  induction x using Quot.ind
  rfl

theorem map_comp (f : F ⟶ G) (g : G ⟶ H) (x : Points F) :
    map (f ≫ g) x = map g (map f x) := by
  induction x using Quot.ind
  rfl

end Points

/-- The point of the functor of points of a scheme `U` over `S` given by a point `u` of `U`:
the canonical morphism from the spectrum of the residue field at `u`. -/
def schemePoint (U : Over S) (u : U.left) : Points ((schemeYoneda S).obj U) :=
  Quot.mk _ ⟨U.left.residueField u, U.left.fromSpecResidueField u ≫ U.hom,
    ULift.up (Over.homMk (U.left.fromSpecResidueField u) rfl)⟩

/-- The topology on the points of a presheaf: the final topology for the maps
`|U| → |F|` given by the étale maps `h_U ⟶ F` from schemes `U` over `S`
(Stacks, Tag 03BX). -/
@[instance_reducible]
def pointTopology (F : Presheaf S) : TopologicalSpace (Points F) :=
  ⨆ (U : Over S) (a : (schemeYoneda S).obj U ⟶ F) (_ : IsEtale a),
    TopologicalSpace.coinduced (Points.map a ∘ schemePoint U) inferInstance

end Langlands.AlgebraicGeometry.AlgebraicSpace
