import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Products of field-scheme affinizations -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Limits hiding prodComparison terminalComparison
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme.FieldAffinization

variable {k : Type u} [Field k]

/-- Global functions carry a fibre product of qcqs field schemes to the
corresponding pushout of rings. -/
theorem isPushout_appTop {X Y P : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)} {g : Y ⟶ Spec (CommRingCat.of k)}
    {p : P ⟶ X} {q : P ⟶ Y} (h : IsPullback p q f g)
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    IsPushout f.appTop g.appTop p.appTop q.appTop := by
  let : Field Γ(Spec (CommRingCat.of k), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  have hf : (f.appLE ⊤ ⊤ (by simp)).hom.Flat :=
    RingHom.Flat.of_isField (Field.toIsField _) _
  have hi := isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat
    (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) h
    (by simp) (by simp) (by simp) (isAffineOpen_top _)
    isCompact_univ isQuasiSeparated_univ isCompact_univ
    isQuasiSeparated_univ hf
  have hp := (isIso_pushoutSection_iff h (by simp) (by simp) (by simp)).mp hi
  simpa [Scheme.Hom.appLE] using hp

/-- The geometric finiteness property used for field-group affinization. -/
abbrev qcSeparated : MorphismProperty Scheme.{u} := @QuasiCompact ⊓ @IsSeparated

instance : qcSeparated.HasOfPostcompProperty qcSeparated := by
  have : MorphismProperty.HasOfPostcompProperty @QuasiCompact qcSeparated :=
    .of_le _ @QuasiSeparated (fun _ _ f hf => by have := hf.2; infer_instance)
  have : MorphismProperty.HasOfPostcompProperty @IsSeparated qcSeparated :=
    .of_le _ ⊤ le_top
  infer_instance

/-- The category of quasi-compact schemes separated over the field. -/
abbrev SchemeCategory (k : Type u) [Field k] :=
  (qcSeparated.overObj (X := Spec (CommRingCat.of k))).FullSubcategory

instance : (qcSeparated.overObj (X := Spec (CommRingCat.of k))).IsClosedUnderLimitsOfShape
    (Discrete PEmpty.{1}) := by infer_instance

instance : (qcSeparated.overObj (X := Spec (CommRingCat.of k))).IsClosedUnderLimitsOfShape
    (Discrete WalkingPair) := by
  let P : ObjectProperty (Over (Spec (CommRingCat.of k))) := qcSeparated.overObj
  have : HasFiniteLimits P.FullSubcategory := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits P.ι :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks P.ι
  exact P.isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι _

/-- Forget the quasi-compact separated field-scheme property. -/
abbrev inclusion (k : Type u) [Field k] : SchemeCategory k ⥤ Over (Spec (CommRingCat.of k)) :=
  (qcSeparated.overObj (X := Spec (CommRingCat.of k))).ι

/-- Canonical affinization on quasi-compact separated field schemes. -/
def functor (k : Type u) [Field k] : SchemeCategory k ⥤ Over (Spec (CommRingCat.of k)) :=
  inclusion k ⋙ algΓ (CommRingCat.of k) ⋙ algSpec (CommRingCat.of k)

@[simp]
lemma obj_left (X : SchemeCategory k) :
    ((functor k).obj X).left = Spec Γ(X.obj.left, ⊤) := rfl

@[simp]
lemma obj_hom (X : SchemeCategory k) :
    ((functor k).obj X).hom =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.obj.hom.appTop) := rfl

@[simp]
lemma map_left {X Y : SchemeCategory k} (f : X ⟶ Y) :
    ((functor k).map f).left = Spec.map f.hom.left.appTop := rfl

/-- The actual canonical affinization morphisms form a natural transformation. -/
def unit (k : Type u) [Field k] : inclusion k ⟶ functor k where
  app X := Over.homMk X.obj.left.toSpecΓ (by
    change X.obj.left.toSpecΓ ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.obj.hom.appTop) = X.obj.hom
    simp only [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp)
  naturality {X Y} f := Over.OverMorphism.ext (Scheme.toSpecΓ_naturality f.hom.left)

@[simp]
lemma unit_left (X : SchemeCategory k) :
    ((unit k).app X).left = X.obj.left.toSpecΓ := rfl

instance compactSpace_obj (X : SchemeCategory k) : CompactSpace X.obj.left := by
  have : QuasiCompact X.obj.hom := X.property.1
  exact QuasiCompact.compactSpace_of_compactSpace X.obj.hom

instance separated_obj (X : SchemeCategory k) : IsSeparated X.obj.hom := X.property.2

instance quasiSeparatedSpace_obj (X : SchemeCategory k) : QuasiSeparatedSpace X.obj.left := by
  have := separated_obj X
  exact quasiSeparatedSpace_of_quasiSeparated X.obj.hom

/-- The spectrum of global functions preserves the actual binary product. -/
lemma isPullback_map_fst_snd (X Y : SchemeCategory k) :
    IsPullback ((functor k).map (fst X Y)).left
      ((functor k).map (snd X Y)).left
      ((functor k).obj X).hom ((functor k).obj Y).hom := by
  have hp := isPushout_appTop (IsPullback.of_hasPullback X.obj.hom Y.obj.hom)
  have hs := isPullback_SpecMap_of_isPushout _ _ _ _ hp
  exact hs.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Scheme.Spec.mapIso (Scheme.ΓSpecIso (CommRingCat.of k)).symm.op)
    (by simp) (by simp) (by simp [Spec.map_comp]) (by simp [Spec.map_comp])

instance isIso_prodComparison (X Y : SchemeCategory k) :
    IsIso (prodComparison (functor k) X Y) := by
  have hp := isPullback_map_fst_snd X Y
  have he : (prodComparison (functor k) X Y).left = hp.isoPullback.hom := rfl
  have : IsIso (prodComparison (functor k) X Y).left := by
    rw [he]
    infer_instance
  let : IsIso ((Over.forget _).map (prodComparison (functor k) X Y)) := by
    change IsIso (prodComparison (functor k) X Y).left
    assumption
  exact isIso_of_reflects_iso _ (Over.forget _)

instance isIso_terminalComparison : IsIso (terminalComparison (functor k)) := by
  have he : (terminalComparison (functor k)).left =
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
    change ((functor k).obj (𝟙_ (SchemeCategory k))).hom = _
    simp [obj_hom]
  have : IsIso (terminalComparison (functor k)).left := by
    rw [he]
    infer_instance
  let : IsIso ((Over.forget _).map (terminalComparison (functor k))) := by
    change IsIso (terminalComparison (functor k)).left
    assumption
  exact isIso_of_reflects_iso _ (Over.forget _)

instance preservesFiniteProducts : PreservesFiniteProducts (functor k) := by
  have := preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison (functor k)
  have := preservesLimit_empty_of_isIso_terminalComparison (functor k)
  have := Limits.preservesLimitsOfShape_pempty_of_preservesTerminal (functor k)
  exact .of_preserves_binary_and_terminal _

/-- Affinization is monoidal for the actual cartesian products. -/
instance monoidal : (functor k).Monoidal := .ofChosenFiniteProducts _

end Langlands.GroupScheme.FieldAffinization
