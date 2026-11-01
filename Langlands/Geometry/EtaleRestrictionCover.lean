import Langlands.Geometry.EtalePullbackAdjunction
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Pi.Basic

/-! # Detecting isomorphisms and limits by an etale covering family -/

noncomputable section

universe u v w vA uA

namespace Langlands.Geometry.EtaleRestrictionCover

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open EtalePullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme.{u}} {ι : Type v} (U : ι → X.Etale)

/-- Restrict a sheaf to every member of an actual family of etale objects. -/
def restrictionFamily (A : Type uA) [Category.{vA} A] :
    Sheaf X.smallEtaleTopology A ⥤
      (∀ i, Sheaf (U i).left.smallEtaleTopology A) :=
  Functor.pi' fun i => restriction (U i).hom A

/-- Any arrow into an etale object makes its domain an etale scheme over
that object's underlying scheme. -/
def arrowDomain {V W : X.Etale} (b : W ⟶ V) : V.left.Etale := by
  have hw : b.left ≫ V.hom = W.hom := b.w
  have : Etale (b.left ≫ V.hom) := by rw [hw]; infer_instance
  exact MorphismProperty.Over.mk ⊤ b.left (Etale.of_comp b.left V.hom)

/-- Composing this relative structure recovers the original domain. -/
def arrowDomainIso {V W : X.Etale} (b : W ⟶ V) :
    (siteMap V.hom).obj (arrowDomain b) ≅ W :=
  MorphismProperty.Over.isoMk (Iso.refl W.left) (by
    simp [arrowDomain])

variable {A : Type uA} [Category.{vA} A]

/-- An isomorphism after restriction controls every original-site object
mapping to the restricting object. -/
theorem isIso_app_of_restriction {F G : Sheaf X.smallEtaleTopology A}
    (a : F ⟶ G) {V W : X.Etale} (b : W ⟶ V)
    [IsIso ((restriction V.hom A).map a)] :
    IsIso (a.hom.app (op W)) := by
  have h : IsIso (a.hom.app (op ((siteMap V.hom).obj (arrowDomain b)))) :=
    inferInstanceAs (IsIso
      (((restriction V.hom A).map a).hom.app (op (arrowDomain b))))
  exact (NatTrans.isIso_app_iff_of_iso a.hom (arrowDomainIso b).op).mpr h

/-- Actual etale restrictions along a covering family jointly detect
isomorphisms of sheaves with arbitrary categorical coefficients. -/
theorem isIso_of_restrictionFamily (hU : X.smallEtaleTopology.CoversTop U)
    {F G : Sheaf X.smallEtaleTopology A} (a : F ⟶ G)
    (h : ∀ i, IsIso ((restriction (U i).hom A).map a)) : IsIso a := by
  apply Sheaf.isIso_of_coversTop hU
  intro i
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro W
  have := h i
  exact isIso_app_of_restriction a W.unop.hom

/-- The product of restrictions is conservative on a covering family. -/
theorem restrictionFamilyReflectsIsomorphisms
    (hU : X.smallEtaleTopology.CoversTop U) :
    (restrictionFamily U A).ReflectsIsomorphisms where
  reflects a _ := by
    apply isIso_of_restrictionFamily U hU a
    intro i
    exact inferInstanceAs (IsIso
      ((Pi.eval (fun i => Sheaf (U i).left.smallEtaleTopology A) i).map
        ((restrictionFamily U A).map a)))

/-- Joint surjectivity on scheme points gives the required site covering
family, by checking the identity terminal object. -/
theorem coversTop_of_jointlySurjective
    (hU : ∀ x : X, ∃ i y, (U i).hom y = x) :
    X.smallEtaleTopology.CoversTop U := by
  let T : X.Etale :=
    MorphismProperty.Over.mk ⊤ (𝟙 X) (inferInstance : Etale (𝟙 X))
  apply (X.smallEtaleTopology.coversTop_iff_of_isTerminal T
    (MorphismProperty.Over.mkIdTerminal (@Etale) X) U).2
  rw [EtaleAutomorphism.mem_smallEtaleTopology_iff]
  intro x
  obtain ⟨i, y, hy⟩ := hU x
  refine ⟨U i, MorphismProperty.Over.homMk (U i).hom (by simp [T]), y, ?_, hy⟩
  exact ⟨i, ⟨𝟙 (U i)⟩⟩

/-- The family of small-etale objects attached to a genuine scheme cover. -/
def coverObjects (𝒰 : X.Cover (Scheme.precoverage (@Etale))) :
    𝒰.I₀ → X.Etale :=
  fun i => MorphismProperty.Over.mk ⊤ (𝒰.f i) (𝒰.map_prop i)

theorem coverObjects_coversTop (𝒰 : X.Cover (Scheme.precoverage (@Etale))) :
    X.smallEtaleTopology.CoversTop (coverObjects 𝒰) :=
  coversTop_of_jointlySurjective _ (fun x => 𝒰.exists_eq x)

section Modules

variable (R : Type u) [CommRing R]

/-- The product restriction preserves limits, using the existing actual
extension/restriction adjunction in each component. -/
instance restrictionFamily_preservesLimits :
    PreservesLimitsOfSize.{u, u} (restrictionFamily U (ModuleCat.{u} R)) := by
  have (i : ι) : PreservesLimitsOfSize.{u, u}
      (restriction (U i).hom (ModuleCat.{u} R)) :=
    (extensionAdjunction (U i).hom R).rightAdjoint_preservesLimits
  exact { preservesLimitsOfShape {J} _ := {
    preservesLimit := {
      preserves := fun {c} hc => ⟨{
        lift := fun s i =>
          (isLimitOfPreserves (restriction (U i).hom (ModuleCat.{u} R)) hc).lift {
            pt := s.pt i
            π := {
              app := fun j => s.π.app j i
              naturality := fun j j' a => congr_fun (s.π.naturality a) i } }
        fac := fun s j => by
          funext i
          exact (isLimitOfPreserves
            (restriction (U i).hom (ModuleCat.{u} R)) hc).fac _ j
        uniq := fun s m hm => by
          funext i
          apply (isLimitOfPreserves
            (restriction (U i).hom (ModuleCat.{u} R)) hc).uniq
            { pt := s.pt i
              π := {
                app := fun j => s.π.app j i
                naturality := fun j j' a => congr_fun (s.π.naturality a) i } } (m i)
          intro j
          exact congr_fun (hm j) i }⟩ } } }

/-- A genuine etale covering family reflects limits of module sheaves. -/
theorem restrictionFamilyReflectsLimits
    (hU : X.smallEtaleTopology.CoversTop U) :
    ReflectsLimitsOfSize.{u, u} (restrictionFamily U (ModuleCat.{u} R)) := by
  have := restrictionFamilyReflectsIsomorphisms U (A := ModuleCat.{u} R) hU
  exact reflectsLimits_of_reflectsIsomorphisms

instance restrictionFamily_preservesFiniteLimits :
    PreservesFiniteLimits (restrictionFamily U (ModuleCat.{u} R)) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u}
  intro J _ _
  infer_instance

theorem restrictionFamilyReflectsFiniteLimits
    (hU : X.smallEtaleTopology.CoversTop U) :
    ReflectsFiniteLimits (restrictionFamily U (ModuleCat.{u} R)) := by
  have := restrictionFamilyReflectsIsomorphisms U (A := ModuleCat.{u} R) hU
  infer_instance

end Modules

end Langlands.Geometry.EtaleRestrictionCover
