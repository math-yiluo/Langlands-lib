import Langlands.AlgebraicGeometry.Picard.RigidificationAdjustment
import Langlands.AlgebraicGeometry.Picard.MumfordBundle

/-! # Compatible rigidifications along two axes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

variable {S X Y Z : Scheme.{u}}

/-- Restrict an axis trivialization to the base, using the canonical unit
and composition comparisons for the actual module pullback. -/
def axisRestrictionIso (s : S ⟶ X) (i : X ⟶ Z) (M : Z.Modules)
    (α : structureSheaf X ≅ (Scheme.Modules.pullback i).obj M) :
    structureSheaf S ≅ (Scheme.Modules.pullback (s ≫ i)).obj M :=
  (pullbackUnitIso s).symm ≪≫ (Scheme.Modules.pullback s).mapIso α ≪≫
    (Scheme.Modules.pullbackComp s i).app M

/-- Two actual axis trivializations whose restrictions to their common base
agree under the displayed equality of scheme morphisms. -/
structure TwoAxisRigidification (e : S ⟶ X) (t : S ⟶ Y)
    (i : X ⟶ Z) (j : Y ⟶ Z) (h : e ≫ i = t ≫ j) (M : Z.Modules) where
  first : structureSheaf X ≅ (Scheme.Modules.pullback i).obj M
  second : structureSheaf Y ≅ (Scheme.Modules.pullback j).obj M
  compatible :
    axisRestrictionIso e i M first ≪≫ (Scheme.Modules.pullbackCongr h).app M =
      axisRestrictionIso t j M second

namespace TwoAxisRigidification

variable (e : S ⟶ X) (t : S ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ Z)
  (h : e ≫ i = t ≫ j) (M : Z.Modules)

/-- Adjust the second of two trivializations so that it agrees with the
first at their common base. Only the second section needs a retraction. -/
def ofTrivializations (g : Y ⟶ S) (ht : t ≫ g = 𝟙 S)
    (α : structureSheaf X ≅ (Scheme.Modules.pullback i).obj M)
    (β : structureSheaf Y ≅ (Scheme.Modules.pullback j).obj M) :
    TwoAxisRigidification e t i j h M := by
  let F := Scheme.Modules.pullback t
  let G := Scheme.Modules.pullback g
  let η : G ⋙ F ≅ 𝟭 S.Modules :=
    Scheme.Modules.pullbackComp t g ≪≫
      Scheme.Modules.pullbackCongr ht ≪≫ Scheme.Modules.pullbackId S
  let δ : structureSheaf S ≅ F.obj ((Scheme.Modules.pullback j).obj M) :=
    axisRestrictionIso e i M α ≪≫ (Scheme.Modules.pullbackCongr h).app M ≪≫
      ((Scheme.Modules.pullbackComp t j).app M).symm
  let β' := RigidificationAdjustment.adjustIso F G η
    (pullbackUnitIso g ≪≫ β) β (pullbackUnitIso t).symm δ
  refine ⟨α, β', ?_⟩
  have hc := RigidificationAdjustment.adjustIso_compatible F G η
    (pullbackUnitIso g ≪≫ β) β (pullbackUnitIso t).symm δ
  have hc' : (pullbackUnitIso t).symm ≪≫ F.mapIso β' = δ := Iso.ext hc
  calc
    axisRestrictionIso e i M α ≪≫ (Scheme.Modules.pullbackCongr h).app M =
        δ ≪≫ (Scheme.Modules.pullbackComp t j).app M := by
      dsimp only [δ]
      simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
    _ = axisRestrictionIso t j M β' := by
      rw [← hc']
      exact Iso.trans_assoc _ _ _

/-- The construction preserves the chosen first trivialization exactly. -/
@[simp]
lemma ofTrivializations_first (g : Y ⟶ S) (ht : t ≫ g = 𝟙 S)
    (α : structureSheaf X ≅ (Scheme.Modules.pullback i).obj M)
    (β : structureSheaf Y ≅ (Scheme.Modules.pullback j).obj M) :
    (ofTrivializations e t i j h M g ht α β).first = α := rfl

end TwoAxisRigidification

end Langlands.AlgebraicGeometry.Picard

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The explicit second unit axis used in the two-axis extension target. -/
abbrev twoAxisSecond : A.X.left ⟶ (mumfordProduct A).left :=
  pullback.lift (A.X.hom ≫ unitSection A) (𝟙 A.X.left)
    (by simp [Category.assoc, unitSection_comp])

/-- The two unit axes agree after restriction along the unit section. -/
lemma twoAxis_unit_comp :
    unitSection A ≫ mumfordSection A = unitSection A ≫ twoAxisSecond A := by
  apply pullback.hom_ext
  · simp only [mumfordSection, relativeSection, twoAxisSecond,
      Category.assoc, pullback.lift_fst, Category.comp_id]
    rw [← Category.assoc, unitSection_comp, Category.id_comp]
  · simp only [mumfordSection, relativeSection, twoAxisSecond,
      Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [← Category.assoc, unitSection_comp, Category.id_comp]

/-- Construct compatible rigidifications from precisely the two ordinary
trivializations appearing in the valuation-ring extension target. -/
def twoAxisRigidificationOfTrivializations
    (D : LineBundle (mumfordProduct A).left)
    (α : (Scheme.Modules.pullback (mumfordSection A)).obj D.obj ≅
      structureSheaf A.X.left)
    (β : (Scheme.Modules.pullback (twoAxisSecond A)).obj D.obj ≅
      structureSheaf A.X.left) :
    TwoAxisRigidification (unitSection A) (unitSection A)
      (mumfordSection A) (twoAxisSecond A) (twoAxis_unit_comp A) D.obj :=
  TwoAxisRigidification.ofTrivializations _ _ _ _ _ _ A.X.hom
    (unitSection_comp A) α.symm β.symm

/-- Existence of the ordinary axis trivializations suffices for existence of
compatible rigidifications on the same actual line bundle. -/
theorem nonempty_twoAxisRigidification
    (D : LineBundle (mumfordProduct A).left)
    (hα : Nonempty ((Scheme.Modules.pullback (mumfordSection A)).obj D.obj ≅
      structureSheaf A.X.left))
    (hβ : Nonempty ((Scheme.Modules.pullback (twoAxisSecond A)).obj D.obj ≅
      structureSheaf A.X.left)) :
    Nonempty (TwoAxisRigidification (unitSection A) (unitSection A)
      (mumfordSection A) (twoAxisSecond A) (twoAxis_unit_comp A) D.obj) := by
  obtain ⟨α⟩ := hα
  obtain ⟨β⟩ := hβ
  exact ⟨twoAxisRigidificationOfTrivializations A D α β⟩

end Langlands.AbelianScheme
