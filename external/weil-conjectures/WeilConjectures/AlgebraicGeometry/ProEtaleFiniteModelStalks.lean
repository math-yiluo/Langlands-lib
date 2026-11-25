/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import all Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Finite geometric stalks of finite local models -/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

private theorem exists_cover_lift {X : Scheme.{u}} {ι : Type (u + 1)}
    {W : ι → Scheme.{u}} {g : ∀ i, W i ⟶ X}
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ∃ i, ∃ y : Spec (.of Ω) ⟶ W i, y ≫ g i = x := by
  have hg' : Presieve.ofArrows W g ∈ Scheme.precoverage @WeaklyEtale X :=
    (show proetalePrecoverage ≤ Scheme.precoverage @WeaklyEtale from inf_le_right) _ hg
  rw [Scheme.ofArrows_mem_precoverage_iff] at hg'
  obtain ⟨i, w, hw⟩ := hg'.1 (x (IsLocalRing.closedPoint Ω))
  have := hg'.2 i
  obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := g i) (g := x) w (IsLocalRing.closedPoint Ω) hw
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale (pullback.snd (g i) x) p
  refine ⟨i, σ ≫ pullback.fst (g i) x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]

private noncomputable def geometricFiber {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ X) : X.ProEt ⥤ Type (u + 1) where
  obj U := ULift.{u + 1} ((Over.mk x) ⟶ (ProEt.forget X).obj U)
  map f := ↾fun y ↦ ⟨y.down ≫ (ProEt.forget X).map f⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def geometricElementsEquiv {X : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ProEtaleGeometricNeighbourhood x ≌ (geometricFiber x).Elements where
  functor.obj U := (geometricFiber x).elementsMk U.right ⟨U.hom⟩
  functor.map f := ⟨f.right, (by apply ULift.ext; exact StructuredArrow.w f)⟩
  inverse.obj U := StructuredArrow.mk U.val.down
  inverse.map f := StructuredArrow.homMk f.hom (congrArg ULift.down f.map_val)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

set_option backward.isDefEq.respectTransparency false in
private noncomputable def geometricPoint {X : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    (ProEt.topology X).Point.{u + 1} where
  fiber := geometricFiber x
  isCofiltered := IsCofiltered.of_equivalence (geometricElementsEquiv x)
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective {V} R hR φ := by
    obtain ⟨P, hP, hPR⟩ := ProEt.mem_topology_iff.mp hR
    obtain ⟨ι, U, f, rfl⟩ := P.exists_eq_ofArrows
    have hP' : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
        Scheme.proetalePrecoverage V.left := by
      rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hP
      exact hP
    obtain ⟨i, y, hy⟩ := exists_cover_lift hP' φ.down.left
    refine ⟨U i, f i, hPR _ _ ⟨i⟩, ⟨Over.homMk y ?_⟩, ?_⟩
    · change y ≫ (U i).hom = x
      rw [← MorphismProperty.Over.w (f i), ← Category.assoc, hy]
      exact Over.w φ.down
    · apply ULift.ext
      apply Over.OverMorphism.ext
      exact hy

private noncomputable def geometricStalkIsoFiber {X : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    proEtaleGeometricFixedModuleStalk x Λ F ≅ (geometricPoint x).sheafFiber.obj F :=
  Functor.Final.colimitIso (geometricElementsEquiv x).functor.op
    ((Functor.Elements.π (geometricPoint x).fiber).op ⋙ F.obj)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sheafFiberOverIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (Φ : J.Point.{u + 1}) {U : C} (x : Φ.fiber.obj U)
    (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf J (ModuleCat.{u + 1} Λ)) :
    (Φ.over x).sheafFiber.obj (F.over U) ≅ Φ.sheafFiber.obj F :=
  Functor.Final.colimitIso
    ((FunctorToTypes.fromOverFunctorElementsEquivalence Φ.fiber x).functor ⋙
      Over.forget (Φ.fiber.elementsMk U x)).op
    ((Functor.Elements.π Φ.fiber).op ⋙ F.obj)

/-- Finite constant models on a pro-etale covering give finite geometric stalks.
Source: Stacks Project, Tags 099Y and 098K.
(auxiliary; not a blueprint node).

Proof: the geometric-point fiber functor sends an object U to the lifts of x to U.
It is a point of the pro-etale site: a weakly etale covering member above the image
of x has a lift over the same algebraically closed field, by splitting its base change
to that field. Its category of elements is equivalent to the category of pointed
geometric neighborhoods, so its sheaf fiber is the specified geometric stalk.
Transport the finite models to slice sites. Lift the terminal fiber element through
the resulting cover to a pointed covering member. The fiber at the corresponding
point of the slice site equals the original fiber, by finality of the over-category
forgetful functor. Apply it to the local constant-model isomorphism. The fiber of the
constant sheaf with value M is M, so the original stalk is finite. Empty covering
members supply no points; for an empty base there is no geometric point. This uses
no conservativity assertion for geometric stalks of arbitrary pro-etale sheaves.
-/
theorem finite_geometricStalk_of_finite_models
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hF : ∃ (ι : Type (u + 1)) (W : ι → Scheme.{u}) (g : ∀ i, W i ⟶ X),
      Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X ∧
        ∀ i, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
          Nonempty (((g i)^*[ModuleCat.{u + 1} Λ]).obj F ≅
            (constantSheaf (ProEt.topology (W i)) (ModuleCat.{u + 1} Λ)).obj M))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    Finite (proEtaleGeometricFixedModuleStalk x Λ F) := by
  obtain ⟨ι, W, g, hg, h⟩ := finiteModels_over Λ F hF
  let Φ := geometricPoint x
  obtain ⟨V, f, hf, v, hv⟩ := Φ.jointly_surjective
    (Sieve.generate (Presieve.ofArrows W g))
    (Precoverage.generate_mem_toGrothendieck hg)
    (ULift.up (Over.homMk x (Category.comp_id x)))
  obtain ⟨_, a, b, ⟨i⟩, hab⟩ := hf
  let v' := Φ.fiber.map a v
  obtain ⟨M, hMF, ⟨e⟩⟩ := h i
  let E := (geometricStalkIsoFiber x Λ F) ≪≫
    (sheafFiberOverIso Φ v' Λ F).symm ≪≫
    (Φ.over v').sheafFiber.mapIso e ≪≫
    (Φ.over v').sheafFiberConstantSheafIso M
  exact Finite.of_equiv M E.toLinearEquiv.toEquiv.symm

end AlgebraicGeometry.ProEtale
