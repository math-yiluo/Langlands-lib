import Mathlib.Topology.Bases
import Mathlib.Topology.Sets.Opens
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Renard's normalized presheaves on a chosen topological basis

The space and the abelian-group carriers have independent universes.
-/

open CategoryTheory Opposite TopologicalSpace

universe u v

namespace Langlands.Sheaf.Renard

/-- An actual chosen basis of the supplied topology, expressed as open sets. -/
structure OpenBasis (X : Type u) [TopologicalSpace X] where
  opens : Set (Opens X)
  isBasis : IsTopologicalBasis ((fun U : Opens X => (U : Set X)) '' opens)

variable {X : Type u} [TopologicalSpace X]

/-- The objects are exactly the chosen basis opens, with their actual inclusion arrows. -/
abbrev BasisOpen (B : OpenBasis X) :=
  (show ObjectProperty (Opens X) from fun U => U ∈ B.opens).FullSubcategory

/-- The fully faithful inclusion of basis opens into all open sets. -/
def basisInclusion (B : OpenBasis X) : BasisOpen B ⥤ Opens X :=
  ObjectProperty.ι _

instance (B : OpenBasis X) : (basisInclusion B).Full :=
  inferInstanceAs (ObjectProperty.ι _).Full

instance (B : OpenBasis X) : (basisInclusion B).Faithful :=
  inferInstanceAs (ObjectProperty.ι _).Faithful

/-- The unique inclusion arrow associated to an inclusion of underlying open sets. -/
def basisHom {B : OpenBasis X} {U V : BasisOpen B} (h : U.obj ≤ V.obj) : U ⟶ V :=
  ObjectProperty.homMk (homOfLE h)

/-- The basis category is thin, with an arrow exactly for an inclusion. -/
theorem basis_hom_nonempty_iff {B : OpenBasis X} (U V : BasisOpen B) :
    Nonempty (U ⟶ V) ↔ U.obj ≤ V.obj :=
  ⟨fun ⟨f⟩ => f.hom.le, fun h => ⟨basisHom h⟩⟩

instance {B : OpenBasis X} (U V : BasisOpen B) : Subsingleton (U ⟶ V) :=
  ⟨fun f g => ObjectProperty.hom_ext _ (Subsingleton.elim f.hom g.hom)⟩

/-- Every point of an open set has a smaller chosen basis neighborhood. -/
theorem OpenBasis.exists_subset (B : OpenBasis X) (U : Opens X) {x : X} (hx : x ∈ U) :
    ∃ V : BasisOpen B, x ∈ V.obj ∧ V.obj ≤ U := by
  obtain ⟨S, ⟨V, hV, rfl⟩, hxV, hVU⟩ := B.isBasis.isOpen_iff.mp U.isOpen x hx
  exact ⟨⟨V, hV⟩, hxV, hVU⟩

/-- Openness is determined by the chosen basis, for the supplied topology. -/
theorem OpenBasis.isOpen_iff (B : OpenBasis X) (S : Set X) :
    IsOpen S ↔ ∀ x ∈ S, ∃ V : BasisOpen B, x ∈ V.obj ∧ (V.obj : Set X) ⊆ S := by
  rw [B.isBasis.isOpen_iff]
  constructor
  · intro h x hx
    obtain ⟨T, ⟨V, hV, rfl⟩, hxV, hVS⟩ := h x hx
    exact ⟨⟨V, hV⟩, hxV, hVS⟩
  · intro h x hx
    obtain ⟨V, hxV, hVS⟩ := h x hx
    exact ⟨V.obj, ⟨V.obj, V.property, rfl⟩, hxV, hVS⟩

/-- Contravariant abelian-group valued functors on the actual basis category. -/
abbrev RawPresheaf (B : OpenBasis X) := (BasisOpen B)ᵒᵖ ⥤ AddCommGrpCat.{v}

/-- Sections on a basis open. -/
abbrev Sections {B : OpenBasis X} (F : RawPresheaf.{u,v} B) (U : BasisOpen B) :=
  F.obj (op U)

/-- Source restriction along an inclusion of basis opens. -/
def restriction {B : OpenBasis X} (F : RawPresheaf.{u,v} B)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) : Sections F V ⟶ Sections F U :=
  F.map (basisHom h).op

@[simp]
theorem restriction_self {B : OpenBasis X} (F : RawPresheaf.{u,v} B) (U : BasisOpen B) :
    restriction F (le_refl U.obj) = 𝟙 (Sections F U) := by
  change F.map (𝟙 (op U)) = _
  exact F.map_id _

/-- Restricting twice equals restricting along the composite inclusion. -/
theorem restriction_comp {B : OpenBasis X} (F : RawPresheaf.{u,v} B)
    {U V W : BasisOpen B} (hUV : U.obj ≤ V.obj) (hVW : V.obj ≤ W.obj) :
    restriction F hVW ≫ restriction F hUV = restriction F (hUV.trans hVW) := by
  exact (F.map_comp (basisHom hVW).op (basisHom hUV).op).symm

@[simp]
theorem restriction_self_apply {B : OpenBasis X} (F : RawPresheaf.{u,v} B)
    (U : BasisOpen B) (s : Sections F U) : restriction F (le_refl U.obj) s = s := by
  simp

theorem restriction_comp_apply {B : OpenBasis X} (F : RawPresheaf.{u,v} B)
    {U V W : BasisOpen B} (hUV : U.obj ≤ V.obj) (hVW : V.obj ≤ W.obj)
    (s : Sections F W) :
    restriction F hUV (restriction F hVW s) = restriction F (hUV.trans hVW) s := by
  exact congrArg (fun f => f s) (restriction_comp F hUV hVW)

/-- Renard's extra convention: the group on an empty basis open has only one element. -/
def IsNormalized {B : OpenBasis X} (F : RawPresheaf.{u,v} B) : Prop :=
  ∀ U : BasisOpen B, U.obj = ⊥ → Subsingleton (Sections F U)

/-- Since each value is a group, normalization says exactly that every empty section is zero. -/
theorem isNormalized_iff_zero {B : OpenBasis X} (F : RawPresheaf.{u,v} B) :
    IsNormalized F ↔ ∀ U : BasisOpen B, U.obj = ⊥ → ∀ s : Sections F U, s = 0 := by
  constructor
  · intro h U hU s
    exact (h U hU).elim s 0
  · intro h U hU
    exact ⟨fun s t => (h U hU s).trans (h U hU t).symm⟩

/-- The source category of normalized basis presheaves, a full functor subcategory. -/
abbrev Presheaf (B : OpenBasis X) :=
  (show ObjectProperty (RawPresheaf.{u,v} B) from IsNormalized).FullSubcategory

/-- Forget only the empty normalization. -/
def presheafInclusion (B : OpenBasis X) : Presheaf.{u,v} B ⥤ RawPresheaf.{u,v} B :=
  ObjectProperty.ι _

/-- Morphisms are precisely the actual natural transformations of the underlying functors. -/
def presheafHomEquiv {B : OpenBasis X} (F G : Presheaf.{u,v} B) :
    (F ⟶ G) ≃ (F.obj ⟶ G.obj) where
  toFun f := f.hom
  invFun f := ObjectProperty.homMk f
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equation (II.2.1.1), in the order of categorical composition. -/
theorem restriction_naturality {B : OpenBasis X} {F G : RawPresheaf.{u,v} B}
    (φ : F ⟶ G) {U V : BasisOpen B} (h : U.obj ≤ V.obj) :
    restriction F h ≫ φ.app (op U) = φ.app (op V) ≫ restriction G h :=
  φ.naturality (basisHom h).op

/-- Equation (II.2.1.1) evaluated on an actual section. -/
theorem restriction_naturality_apply {B : OpenBasis X} {F G : RawPresheaf.{u,v} B}
    (φ : F ⟶ G) {U V : BasisOpen B} (h : U.obj ≤ V.obj) (s : Sections F V) :
    φ.app (op U) (restriction F h s) = restriction G h (φ.app (op V) s) :=
  congrArg (fun f => f s) (restriction_naturality φ h)

@[simp]
theorem presheaf_identity_app {B : OpenBasis X} (F : Presheaf.{u,v} B) (U : BasisOpen B) :
    (𝟙 F : F ⟶ F).hom.app (op U) = 𝟙 (Sections F.obj U) := rfl

@[simp]
theorem presheaf_composition_app {B : OpenBasis X} {F G H : Presheaf.{u,v} B}
    (φ : F ⟶ G) (ψ : G ⟶ H) (U : BasisOpen B) :
    (φ ≫ ψ).hom.app (op U) = φ.hom.app (op U) ≫ ψ.hom.app (op U) := rfl

/-- Normalized presheaves really have the zero group at every empty basis open. -/
theorem empty_section_eq_zero {B : OpenBasis X} (F : Presheaf.{u,v} B)
    (U : BasisOpen B) (hU : U.obj = ⊥) (s : Sections F.obj U) : s = 0 :=
  (isNormalized_iff_zero F.obj).mp F.property U hU s

end Langlands.Sheaf.Renard
