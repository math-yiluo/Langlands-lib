import Langlands.Geometry.FormalGroup.DelignePiSheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Homogeneous sheaf morphisms and the line-sheaf data in Deligne's construction -/

noncomputable section

universe u

namespace Langlands.DeligneFormalSpace

open CategoryTheory AlgebraicGeometry

section HomogeneousMaps

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {d : ℕ} [NeZero d] {R : Sheaf J CommRingCat.{u}}
  {a : (R.obj ⋙ CategoryTheory.forget CommRingCat).sections}

namespace GradedPiSheaf

/-- Homogeneous maps are actual operator-compatible maps preserving each subsheaf. -/
structure Hom (M N : GradedPiSheaf d R a) where
  val : M.toPiSheaf ⟶ N.toPiSheaf
  homogeneous (U : Cᵒᵖ) (i : ZMod d) (x : M.module.val.obj U) :
    x ∈ (M.component i).toSubmodule.obj U →
      val.val.val.app U x ∈ (N.component i).toSubmodule.obj U

@[ext]
theorem Hom.ext {M N : GradedPiSheaf d R a} {f g : Hom M N} (h : f.val = g.val) :
    f = g := by
  cases f
  cases g
  cases h
  rfl

instance category : Category (GradedPiSheaf d R a) where
  Hom := Hom
  id M := ⟨𝟙 M.toPiSheaf, fun _ _ _ hx => hx⟩
  comp f g := ⟨f.val ≫ g.val,
    fun U i x hx => g.homogeneous U i _ (f.homogeneous U i x hx)⟩
  id_comp _f := Hom.ext (Category.id_comp _)
  comp_id _f := Hom.ext (Category.comp_id _)
  assoc _f _g _h := Hom.ext (Category.assoc _ _ _)

/-- Forget only the homogeneous subsheaves. -/
def forgetToPiSheaf : GradedPiSheaf d R a ⥤ PiSheaf d R a where
  obj M := M.toPiSheaf
  map f := f.val

instance : (forgetToPiSheaf (d := d) (R := R) (a := a)).Faithful where
  map_injective h := Hom.ext h

variable {M N K : GradedPiSheaf d R a} (f : M ⟶ N)

/-- A homogeneous map restricted to a homogeneous component. -/
def Hom.componentMap (i : ZMod d) : M.componentSheaf i ⟶ N.componentSheaf i where
  val := {
    app U := ModuleCat.ofHom
      (((f.val.val.val.app U).hom.comp ((M.component i).toSubmodule.obj U).subtype).codRestrict
        _ (fun x => f.homogeneous U i x x.property))
    naturality g := by
      ext x
      apply Subtype.ext
      exact PresheafOfModules.naturality_apply f.val.val.val g x.val }

@[simp]
theorem Hom.componentMap_apply (i : ZMod d) (U : Cᵒᵖ)
    (x : (M.component i).toSubmodule.obj U) :
    ((f.componentMap i).val.app U x).val = f.val.val.val.app U x.val := rfl

@[reassoc (attr := simp)]
theorem Hom.componentMap_inclusion (i : ZMod d) :
    f.componentMap i ≫ N.componentInclusion i = M.componentInclusion i ≫ f.val.val := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  rfl

/-- The component maps commute with the degree-one maps. -/
@[reassoc]
theorem Hom.componentPi_naturality (i : ZMod d) :
    M.componentPi i ≫ f.componentMap (i + 1) = f.componentMap i ≫ N.componentPi i := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  apply Subtype.ext
  exact f.val.map_pi U x.val

/-- Taking a homogeneous part is an actual functor. -/
def componentFunctor (i : ZMod d) :
    GradedPiSheaf d R a ⥤ SheafOfModules (ringSheaf R) where
  obj M := M.componentSheaf i
  map f := f.componentMap i
  map_id M := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    rfl
  map_comp f g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    rfl

instance (e : M ≅ N) (i : ZMod d) : IsIso (e.hom.componentMap i) :=
  inferInstanceAs (IsIso ((componentFunctor i).map e.hom))

end GradedPiSheaf

end HomogeneousMaps

section Schemes

variable (S : Scheme.{u})

/-- The restrictions of an actual global section of a scheme's structure sheaf. -/
def schemeScalar (a : Γ(S, ⊤)) :
    (S.sheaf.obj ⋙ CategoryTheory.forget CommRingCat).sections where
  val U := S.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op a
  property {U V} f := by
    change S.presheaf.map f (S.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op a) =
      S.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op a
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

/-- A line sheaf is locally isomorphic to the actual structure module. -/
def IsLineSheaf (M : S.Modules) : Prop :=
  ∀ x : S, ∃ U : S.Opens, x ∈ U ∧
    Nonempty (M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)

namespace IsLineSheaf

variable {S} {M N : S.Modules}

/-- A genuine sheaf isomorphism preserves the local rank-one condition. -/
theorem of_iso (e : M ≅ N) (h : IsLineSheaf S M) : IsLineSheaf S N := by
  intro x
  obtain ⟨U, hx, ⟨t⟩⟩ := h x
  exact ⟨U, hx, ⟨((Scheme.Modules.restrictFunctor U.ι).mapIso e).symm ≪≫ t⟩⟩

theorem iso_iff (e : M ≅ N) : IsLineSheaf S M ↔ IsLineSheaf S N :=
  ⟨of_iso e, of_iso e.symm⟩

end IsLineSheaf

variable {S} {d : ℕ} [NeZero d] {a : Γ(S, ⊤)}

namespace GradedPiSheaf

instance schemeCategory : Category (GradedPiSheaf d S.sheaf (schemeScalar S a)) :=
  GradedPiSheaf.category (R := S.sheaf) (a := schemeScalar S a)

variable (M : GradedPiSheaf d S.sheaf (schemeScalar S a))

/-- The actual homogeneous sheaf pulled back to Spec of the residue field. -/
def fibreComponent (i : ZMod d) (x : S) : (Spec (S.residueField x)).Modules :=
  (Scheme.Modules.pullback (S.fromSpecResidueField x)).obj (M.componentSheaf i)

/-- The degree-one map on the actual residue-field fibre. -/
def fibrePi (i : ZMod d) (x : S) :
    M.fibreComponent i x ⟶ M.fibreComponent (i + 1) x :=
  (Scheme.Modules.pullback (S.fromSpecResidueField x)).map (M.componentPi i)

/-- The underlying point set of the zero locus of Pi on the i-th line. -/
def piZeroLocus (i : ZMod d) : Set S := {x | M.fibrePi i x = 0}

variable {M} {N : GradedPiSheaf d S.sheaf (schemeScalar S a)}

set_option backward.isDefEq.respectTransparency false in
/-- Isomorphic graded objects have the same zero locus in each degree. -/
theorem mem_piZeroLocus_of_iso (e : M ≅ N) (i : ZMod d) (x : S)
    (hx : x ∈ M.piZeroLocus i) : x ∈ N.piZeroLocus i := by
  let F := Scheme.Modules.pullback (S.fromSpecResidueField x)
  have h := congrArg (fun t => F.map t) (e.hom.componentPi_naturality i)
  change F.map (M.componentPi i ≫ e.hom.componentMap (i + 1)) =
    F.map (e.hom.componentMap i ≫ N.componentPi i) at h
  rw [F.map_comp, F.map_comp] at h
  have hz : F.map (M.componentPi i) = 0 := hx
  change F.map (N.componentPi i) = 0
  have : IsIso (F.map (e.hom.componentMap i)) :=
    (F.mapIso ((componentFunctor (R := S.sheaf) (a := schemeScalar S a) i).mapIso e)).isIso_hom
  apply (cancel_epi (F.map (e.hom.componentMap i))).mp
  rw [Limits.comp_zero, ← h, hz, Limits.zero_comp]

theorem piZeroLocus_eq_of_iso (e : M ≅ N) (i : ZMod d) :
    M.piZeroLocus i = N.piZeroLocus i := by
  ext x
  exact ⟨mem_piZeroLocus_of_iso e i x, mem_piZeroLocus_of_iso e.symm i x⟩

end GradedPiSheaf

/-- The T-part of Deligne's data: a genuine graded sheaf with invertible components. -/
structure LinePiSheaf (d : ℕ) [NeZero d] (S : Scheme.{u}) (a : Γ(S, ⊤)) where
  graded : GradedPiSheaf d S.sheaf (schemeScalar S a)
  line : ∀ i, IsLineSheaf S (graded.componentSheaf i)

namespace LinePiSheaf

/-- Isomorphism of T-data is actual graded operator-compatible isomorphism. -/
def isoSetoid : Setoid (LinePiSheaf d S a) where
  r M N := Nonempty (M.graded ≅ N.graded)
  iseqv := ⟨fun M => ⟨Iso.refl M.graded⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩

/-- Isomorphism classes of the actual line-sheaf data. -/
def IsoClass := Quotient (isoSetoid (d := d) (S := S) (a := a))

end LinePiSheaf

end Schemes

end Langlands.DeligneFormalSpace
