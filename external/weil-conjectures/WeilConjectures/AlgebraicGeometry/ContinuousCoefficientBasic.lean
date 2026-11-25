/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Continuous coefficient sheaves and immersion restriction

Source: Bhatt--Scholze, Lemmas 4.2.12 and 6.5.8(1), Definition 6.8.1,
Lemma 6.8.2 and the paragraph preceding Definition 6.8.6
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry.Scheme

/-- Continuous-function presheaf of commutative rings on schemes.

Source: Bhatt--Scholze, Definition 6.8.1 (auxiliary; not a blueprint node). -/
noncomputable def continuousMapPresheafCommRing (T : Type v) [TopologicalSpace T]
    [CommRing T] [IsTopologicalRing T] : Scheme.{u}ᵒᵖ ⥤ CommRingCat.{max v u} where
  obj U := CommRingCat.of C(U.unop, T)
  map {U V} f := CommRingCat.ofHom {
    toFun := fun g => ContinuousMap.comp g f.unop.base.hom
    map_one' := by ext; rfl
    map_mul' := by intros; ext; rfl
    map_zero' := by ext; rfl
    map_add' := by intros; ext; rfl }

private theorem commRingForgetReflectsLimit {J : Type v} [Category J]
    (F : J ⥤ CommRingCat.{u}) (c : Limits.Cone F)
    (hc : Limits.IsLimit ((CategoryTheory.forget CommRingCat).mapCone c)) :
    Nonempty (Limits.IsLimit c) := by
  let ext (x y : c.pt) (h : ∀ j, c.π.app j x = c.π.app j y) : x = y := by
    apply (Limits.Types.isLimitEquivSections hc).injective
    exact Subtype.ext (funext h)
  let lift (s : Limits.Cone F) : s.pt ⟶ c.pt := CommRingCat.ofHom
    { toFun := hc.lift ((CategoryTheory.forget CommRingCat).mapCone s)
      map_one' := by
        apply ext
        intro j
        simpa using ConcreteCategory.congr_hom (hc.fac
          ((CategoryTheory.forget CommRingCat).mapCone s) j) (1 : s.pt)
      map_mul' := by
        intro x y
        apply ext
        intro j
        have hj (z : s.pt) : c.π.app j
            (hc.lift ((CategoryTheory.forget CommRingCat).mapCone s) z) = s.π.app j z :=
          ConcreteCategory.congr_hom (hc.fac
            ((CategoryTheory.forget CommRingCat).mapCone s) j) z
        simp only [map_mul]
        rw [hj, hj, hj, map_mul]
      map_zero' := by
        apply ext
        intro j
        simpa using ConcreteCategory.congr_hom (hc.fac
          ((CategoryTheory.forget CommRingCat).mapCone s) j) (0 : s.pt)
      map_add' := by
        intro x y
        apply ext
        intro j
        have hj (z : s.pt) : c.π.app j
            (hc.lift ((CategoryTheory.forget CommRingCat).mapCone s) z) = s.π.app j z :=
          ConcreteCategory.congr_hom (hc.fac
            ((CategoryTheory.forget CommRingCat).mapCone s) j) z
        simp only [map_add]
        rw [hj, hj, hj, map_add] }
  refine ⟨{ lift := lift, fac := ?_, uniq := ?_ }⟩
  · intro s j
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact ConcreteCategory.congr_hom (hc.fac ((CategoryTheory.forget CommRingCat).mapCone s) j) x
  · intro s m hm
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    apply ext
    intro j
    exact (congrArg (fun f : s.pt ⟶ _ ↦ f x) (hm j)).trans
      (ConcreteCategory.congr_hom (hc.fac ((CategoryTheory.forget CommRingCat).mapCone s) j) x).symm

/-- The continuous-function presheaf is a pro-etale sheaf.

Source: Bhatt--Scholze, Lemma 4.2.12 and Definition 6.8.1 (auxiliary; not a blueprint node).
Proof: apply fpqc descent for continuous abelian functions and restrict to the weaker
pro-etale topology. The pointwise ring structure commutes with restriction; reflect
sheafhood through the ring forgetful functor. This is step 1 of the node. -/
theorem continuousMapPresheafCommRing_isSheaf (T : Type v)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Presheaf.IsSheaf proetaleTopology (continuousMapPresheafCommRing T) := by
  have h : Presheaf.IsSheaf proetaleTopology
      (continuousMapPresheafCommRing T ⋙ CategoryTheory.forget _) :=
    Presheaf.IsSheaf.of_le proetaleTopology_le_fpqcTopology
      (isSheaf_fpqcTopology_continuousMapPresheaf T)
  rw [Presheaf.isSheaf_iff_isLimit] at h ⊢
  intro X S hS
  rcases h S hS with ⟨hc⟩
  exact commRingForgetReflectsLimit _ _ hc

/-- The continuous-function coefficient sheaf on the small pro-etale site.

Source: Bhatt--Scholze, Definition 6.8.1 (auxiliary; not a blueprint node). -/
noncomputable def continuousCoefficientSheaf (X : Scheme.{u}) (T : Type v)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Sheaf (ProEt.topology X) CommRingCat.{max v u} :=
  ((ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).obj
    ⟨continuousMapPresheafCommRing T,
      continuousMapPresheafCommRing_isSheaf T⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
