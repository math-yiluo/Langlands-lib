import Langlands.GroupScheme.Descent.DisjointComponentHoms
import Langlands.GroupScheme.Absolute.CocharacterDescentGroup
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.CategoryTheory.EffectiveEpi.Coproduct

/-! # Descent of homomorphisms along small étale covering families -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.EtaleCoverHomDescent

variable {S : Scheme.{u}} (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)

/-- A small étale covering family is effective epimorphic in schemes. -/
def effectiveFamily : EffectiveEpiFamilyStruct 𝒰.X 𝒰.f := by
  haveI : Etale (Sigma.desc 𝒰.f) := 𝒰.sigma.map_prop PUnit.unit
  haveI : Surjective (Sigma.desc 𝒰.f) := ⟨fun x => by
    obtain ⟨a, y, rfl⟩ := 𝒰.exists_eq x
    exact ⟨Sigma.ι 𝒰.X a y, by simp [← Scheme.Hom.comp_apply]⟩⟩
  haveI : IsIso (Sigma.desc (Sigma.ι 𝒰.X)) := by
    have h : Sigma.desc (Sigma.ι 𝒰.X) = 𝟙 (∐ 𝒰.X) := by ext; simp
    rw [h]
    infer_instance
  haveI {Z : Scheme.{u}} (g : Z ⟶ ∐ 𝒰.X) :
      Epi (Sigma.desc (fun a => pullback.fst g (Sigma.ι 𝒰.X a))) := by
    exact inferInstanceAs (Epi (DisjointComponents.projection (Sigma.ι 𝒰.X) (Over.mk g)))
  exact effectiveEpiFamilyStructOfEffectiveEpiDesc 𝒰.X 𝒰.f

/-- Pullbacks of the cover detect equality of scheme maps. -/
theorem schemeHom_ext {X Y : Scheme.{u}} (s : X ⟶ S) {a b : X ⟶ Y}
    (h : ∀ i, pullback.fst s (𝒰.f i) ≫ a = pullback.fst s (𝒰.f i) ≫ b) : a = b := by
  let 𝒱 := 𝒰.pullback₁ s
  let E := effectiveFamily 𝒱
  have ha : a = E.desc (fun i => 𝒱.f i ≫ a) (fun _ _ g₁ g₂ hg => by
      simpa only [← Category.assoc] using congrArg (fun q => q ≫ a) hg) :=
    E.uniq _ _ a (fun _ => rfl)
  have hb : b = E.desc (fun i => 𝒱.f i ≫ a) (fun _ _ g₁ g₂ hg => by
      simpa only [← Category.assoc] using congrArg (fun q => q ≫ a) hg) := by
    apply E.uniq
    intro i
    exact (h i).symm
  exact ha.trans hb.symm

/-- Restriction of schemes to all members of the cover. -/
abbrev restriction : Over S ⥤ ∀ i, Over (𝒰.X i) :=
  Functor.pi' (fun i => Over.pullback (𝒰.f i))

/-- The restriction functor is faithful. -/
theorem restrictionFaithful : (restriction 𝒰).Faithful where
  map_injective {X Y} {a b} h := by
    apply Over.OverMorphism.ext
    apply schemeHom_ext 𝒰 X.hom
    intro i
    have hi := congrArg (fun k => (k i).left ≫ pullback.fst Y.hom (𝒰.f i)) h
    simpa only [restriction, Functor.pi'_map, Over.pullback_map_left, pullback.lift_fst] using hi

variable {C D : GroupScheme S}
  (a : ∀ i, (baseChange (𝒰.f i)).obj C ⟶ (baseChange (𝒰.f i)).obj D)

/-- Local maps have the same value on every pair of points with equal original
source projection, including points lying over different cover members. -/
def Compatible : Prop :=
  ∀ {Z : Scheme.{u}} (i j : 𝒰.I₀)
    (x : Z ⟶ pullback C.X.hom (𝒰.f i)) (y : Z ⟶ pullback C.X.hom (𝒰.f j)),
    x ≫ pullback.fst C.X.hom (𝒰.f i) = y ≫ pullback.fst C.X.hom (𝒰.f j) →
    x ≫ (a i).hom.hom.left ≫ pullback.fst D.X.hom (𝒰.f i) =
      y ≫ (a j).hom.hom.left ≫ pullback.fst D.X.hom (𝒰.f j)

variable (ha : Compatible 𝒰 a)

/-- Descend the local underlying maps through the pulled-back covering family. -/
def underlying : C.X.left ⟶ D.X.left :=
  (effectiveFamily (𝒰.pullback₁ C.X.hom)).desc
    (fun i => (a i).hom.hom.left ≫ pullback.fst D.X.hom (𝒰.f i)) ha

@[reassoc]
theorem underlying_fac (i : 𝒰.I₀) :
    pullback.fst C.X.hom (𝒰.f i) ≫ underlying 𝒰 a ha =
      (a i).hom.hom.left ≫ pullback.fst D.X.hom (𝒰.f i) :=
  (effectiveFamily (𝒰.pullback₁ C.X.hom)).fac _ _ i

theorem underlying_over : underlying 𝒰 a ha ≫ D.X.hom = C.X.hom := by
  apply schemeHom_ext 𝒰 C.X.hom
  intro i
  rw [← Category.assoc, underlying_fac, Category.assoc, pullback.condition]
  have hw : (a i).hom.hom.left ≫ pullback.snd D.X.hom (𝒰.f i) =
      pullback.snd C.X.hom (𝒰.f i) := Over.w (a i).hom.hom
  simpa only [← Category.assoc, hw] using (pullback.condition (f := C.X.hom) (g := 𝒰.f i)).symm

/-- The actual descended map over the original base. -/
def overHom : C.X ⟶ D.X := Over.homMk (underlying 𝒰 a ha) (underlying_over 𝒰 a ha)

theorem pullback_overHom (i : 𝒰.I₀) :
    (Over.pullback (𝒰.f i)).map (overHom 𝒰 a ha) = (a i).hom.hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (pullback.lift_fst _ _ _).trans (underlying_fac 𝒰 a ha i)
  · exact (pullback.lift_snd _ _ _).trans (Over.w (a i).hom.hom).symm

open MonoidalCategory CartesianMonoidalCategory

local instance pointwiseCartesianMonoidalCategory :
    CartesianMonoidalCategory (∀ i, Over (𝒰.X i)) where
  toMonoidalCategory := Pi.monoidalCategory
  isTerminalTensorUnit := .ofUniqueHom (fun X i => toUnit (X i)) (by
    intro X m; funext i; exact toUnit_unique _ _)
  fst X Y i := fst (X i) (Y i)
  snd X Y i := snd (X i) (Y i)
  fst_def X Y := by funext i; exact fst_def (X i) (Y i)
  snd_def X Y := by funext i; exact snd_def (X i) (Y i)
  tensorProductIsBinaryProduct X Y := BinaryFan.IsLimit.mk _
    (fun f g i => lift (f i) (g i))
    (fun f g => funext (fun i => lift_fst (f i) (g i)))
    (fun f g => funext (fun i => lift_snd (f i) (g i)))
    (fun f g m hf hg => funext (fun i =>
      hom_ext _ _ (by simpa using congrFun hf i) (by simpa using congrFun hg i)))

/-- The local homomorphisms form a homomorphism between pointwise group objects. -/
def componentGroupHom : (restriction 𝒰).mapGrp.obj C ⟶ (restriction 𝒰).mapGrp.obj D :=
  Grp.homMk'' (fun i => (a i).hom.hom)
    (by funext i; exact IsMonHom.one_hom (a i).hom.hom)
    (by funext i; exact IsMonHom.mul_hom (a i).hom.hom)

/-- Faithful monoidal restriction reflects the homomorphism laws. -/
theorem overHom_isMonHom : IsMonHom (overHom 𝒰 a ha) := by
  letI := restrictionFaithful 𝒰
  have hm : (restriction 𝒰).map (overHom 𝒰 a ha) =
      (componentGroupHom 𝒰 a).hom.hom := funext (pullback_overHom 𝒰 a ha)
  haveI : IsMonHom ((restriction 𝒰).map (overHom 𝒰 a ha)) := by
    rw [hm]; infer_instance
  exact GaloisCocharacterDescent.isMonHom_of_faithfulMap (restriction 𝒰) _

/-- The actual descended group-scheme homomorphism. -/
def hom : C ⟶ D :=
  letI := overHom_isMonHom 𝒰 a ha
  Grp.homMk (overHom 𝒰 a ha)

@[simp]
theorem baseChange_hom (i : 𝒰.I₀) : (baseChange (𝒰.f i)).map (hom 𝒰 a ha) = a i := by
  apply Grp.hom_ext
  exact pullback_overHom 𝒰 a ha i

/-- Cover restrictions detect equality of actual group homomorphisms. -/
theorem groupHom_ext {b c : C ⟶ D}
    (h : ∀ i, (baseChange (𝒰.f i)).map b = (baseChange (𝒰.f i)).map c) : b = c := by
  apply Grp.hom_ext
  exact (restrictionFaithful 𝒰).map_injective (funext (fun i =>
    congrArg (fun k => k.hom.hom) (h i)))

/-- Exact recovery characterizes the descended homomorphism. -/
theorem unique (b : C ⟶ D) (hb : ∀ i, (baseChange (𝒰.f i)).map b = a i) :
    b = hom 𝒰 a ha :=
  groupHom_ext 𝒰 (fun i => (hb i).trans (baseChange_hom 𝒰 a ha i).symm)

/-- Glue actual local isomorphisms whose forward and inverse maps both agree
on equal original-source projections. -/
def iso (e : ∀ i, (baseChange (𝒰.f i)).obj C ≅ (baseChange (𝒰.f i)).obj D)
    (he : Compatible 𝒰 (fun i => (e i).hom))
    (hi : Compatible 𝒰 (fun i => (e i).inv)) : C ≅ D where
  hom := hom 𝒰 (fun i => (e i).hom) he
  inv := hom 𝒰 (fun i => (e i).inv) hi
  hom_inv_id := groupHom_ext 𝒰 (fun i => by simp)
  inv_hom_id := groupHom_ext 𝒰 (fun i => by simp)

@[simp]
theorem baseChange_iso
    (e : ∀ i, (baseChange (𝒰.f i)).obj C ≅ (baseChange (𝒰.f i)).obj D)
    (he : Compatible 𝒰 (fun i => (e i).hom))
    (hi : Compatible 𝒰 (fun i => (e i).inv)) (i : 𝒰.I₀) :
    (baseChange (𝒰.f i)).mapIso (iso 𝒰 e he hi) = e i := by
  apply Iso.ext
  exact baseChange_hom 𝒰 (fun i => (e i).hom) he i

end Langlands.GroupScheme.Descent.EtaleCoverHomDescent
