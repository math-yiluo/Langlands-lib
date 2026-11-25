/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfSupportedDiagonalData
import WeilConjectures.AlgebraicGeometry.SfDiagonalInsertionProjection
import WeilConjectures.AlgebraicGeometry.SfSupportedTraceContractions

/-! # Coordinate integrals for a trace-diagonal kernel

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, the two coordinate integrals and triangle calculations.
The definitions use the existing compact-support exchange and composition maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.SfDiagonalKernel

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
variable {f} {B : DerivedCategoryModule A X} (d : TraceDiagonalDatum A f B)

-- Keep identity-functor objects as in the geometric components. Reducing these
-- objects under concrete derived functors makes kernel conversion expensive.
private theorem normalized_insertion
    {C : Type*} [Category C] (T : C ⥤ C) {U V M S Q : C}
    (r : T.obj U ≅ M) (a : U ⟶ V) (t : V ⟶ U)
    (i : M ⟶ S) (j : S ⟶ Q) (q : Q ⟶ T.obj V)
    (hi : i ≫ j ≫ q = r.inv ≫ T.map a) (hn : a ≫ t = 𝟙 U) :
    i ≫ j ≫ q ≫ T.map t ≫ r.hom = 𝟙 M := by
  calc
    _ = (i ≫ j ≫ q) ≫ T.map t ≫ r.hom := by simp only [Category.assoc]
    _ = (r.inv ≫ T.map a) ≫ T.map t ≫ r.hom := by rw [hi]
    _ = r.inv ≫ T.map (a ≫ t) ≫ r.hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = 𝟙 M := by rw [hn, T.map_id, Category.id_comp, Iso.inv_hom_id]

private theorem normalized_pushed_insertion
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (T : C ⥤ C)
    {U V M Q : C} {S : D} (r : T.obj U ≅ M) (a : U ⟶ V) (t : V ⟶ U)
    (i : F.obj M ⟶ S) (j : S ⟶ F.obj Q) (q : Q ⟶ T.obj V)
    (hi : i ≫ j ≫ F.map q = F.map (r.inv ≫ T.map a)) (hn : a ≫ t = 𝟙 U) :
    i ≫ j ≫ F.map (q ≫ T.map t ≫ r.hom) = 𝟙 (F.obj M) := by
  have he : F.map (T.map a) ≫ F.map (T.map t) = 𝟙 _ := by
    rw [← F.map_comp, ← T.map_comp, hn, T.map_id, F.map_id]
  have hi' : i ≫ j ≫ F.map q = (F.mapIso r).inv ≫ F.map (T.map a) := by
    simpa only [Functor.map_comp, Functor.mapIso_inv] using hi
  simpa only [Functor.map_comp, Functor.mapIso_hom, Functor.id_map] using
    normalized_insertion (𝟭 D) (F.mapIso r) (F.map (T.map a))
      (F.map (T.map t)) i j (F.map q) hi' he

private theorem normalized_insertion_ids
    {C : Type*} [Category C] (T : C ⥤ C) {U V M S Q : C}
    (r : T.obj U ≅ M) (a : (𝟭 C).obj U ⟶ V) (t : V ⟶ U)
    (i : (𝟭 C).obj M ⟶ S) (j : S ⟶ Q) (q : Q ⟶ T.obj V)
    (hi : i ≫ j ≫ q = r.inv ≫ T.map a) (hn : a ≫ t = 𝟙 ((𝟭 C).obj U)) :
    i ≫ j ≫ q ≫ T.map t ≫ r.hom = 𝟙 ((𝟭 C).obj M) := by
  simpa only [Functor.id_obj] using
    normalized_insertion T r (show U ⟶ V from a) t (show M ⟶ S from i) j q hi hn

private theorem normalized_pushed_insertion_ids
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (T : C ⥤ C)
    {U V M Q : C} {S : D} (r : T.obj U ≅ M) (a : (𝟭 C).obj U ⟶ V) (t : V ⟶ U)
    (i : F.obj ((𝟭 C).obj M) ⟶ S) (j : S ⟶ F.obj Q) (q : Q ⟶ T.obj V)
    (hi : i ≫ j ≫ F.map q = F.map (r.inv ≫ T.map a)) (hn : a ≫ t = 𝟙 ((𝟭 C).obj U)) :
    i ≫ j ≫ F.map (q ≫ T.map t ≫ r.hom) = 𝟙 (F.obj ((𝟭 C).obj M)) := by
  simpa only [Functor.id_obj] using
    normalized_pushed_insertion F T r (show U ⟶ V from a) t
      (show F.obj M ⟶ S from i) j q hi hn

section ConcreteTriangle

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] unit counit DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor derivedTensorSymmetry

attribute [local implicit_reducible] rightDerivedLowerShriek derivedTensorRight

/-- A normalized diagonal kernel for a pulled-back even shifted line satisfies both
triangles on the entire unbounded derived categories.

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, both triangle computations
(auxiliary; not a blueprint node).

Proof: Transport the trace and diagonal class through the supplied coefficient
isomorphism e and the canonical proper forget-supports comparisons. The resulting
direct-image data have the two trace-exchange equations by the definitions of
traceFirst and traceSecond. Apply CoordinateTrace.contractions to the lisse line J
and its even shift 2d. For the first triangle, precompose its first contraction
equation with direct image of the supported diagonal class tensored with p1* M.
Projection naturality and the section identity for p1 Delta = id identify the
result with direct image of M tensored with the first integral. Its value is
identity by h.1. For the second triangle use the second contraction equation at
K. Both pulled-back coefficients come from the base, so coordinate identifies
them; projection naturality and the section identity for p2 Delta = id identify
the result with the right-adjoint object tensored with the second integral.
It is identity by h.2. The line self-symmetry is identity on a local basis, and
the shift is even, so the tensor rearrangement introduces no sign. The symmetry
factors in the explicitly defined unit and counit cancel with those in the ordered
projection comparisons. Finally the proper forget-supports comparison preserves
the exchange, projection and composition maps, giving precisely the two stated
natural-transformation equations. No boundedness or Noetherian condition occurs. -/
theorem triangles (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hJ : Scheme.IsLisseRankOneSheaf J) (n : ℤ)
    (e : B ≅ (CoordinateTrace.pull A f).obj (CoordinateTrace.shiftedLine A J n))
    (h : Integrals A d (CoordinateTrace.shiftedLine A J n) e) :
    (∀ M : DerivedCategoryModule A X,
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map ((unit A d).app M) ≫
        (counit A d).app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) = 𝟙 _) ∧
    (∀ K : DerivedCategoryModule A Y,
      (unit A d).app
          ((CoordinateTrace.pull A f ⋙
            (derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj K) ≫
        (CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B).map
          ((counit A d).app K) = 𝟙 _) := by
  let F := SupportedTrace.push A f
  obtain ⟨hc₁, hc₂⟩ := SupportedTrace.contractions A f J hJ n e d
  obtain ⟨hi₁, hi₂⟩ :=
    SupportedTrace.insertion_projection A f (CoordinateTrace.shiftedLine A J n) e d.diagonalClass
  have hn₁ :
      (diagonalFirst A f).hom.app
          (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
        (SupportedTrace.push A (pullback.fst f f)).map d.diagonalClass ≫
          traceFirst A d = 𝟙 _ := h.1
  have hn₂ :
      (TraceDiagonalDatum.idIsoDiagonalSnd (Λ := A) f).hom.app
          (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
        (SupportedTrace.push A (pullback.snd f f)).map d.diagonalClass ≫
          traceSecond A d (CoordinateTrace.shiftedLine A J n) e = 𝟙 _ := h.2
  constructor
  · intro M
    rw [unit_app_eq A d M, F.map_comp, Category.assoc, hc₁ M]
    exact normalized_pushed_insertion_ids F
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj M)
      (U := derivedTensorUnit (ModuleCat.{u + 1} A) X) (M := M)
      (V := (SupportedTrace.push A (pullback.fst f f)).obj
        ((CoordinateTrace.pull A (pullback.snd f f)).obj B))
      (Q := (SupportedTrace.push A (pullback.fst f f)).obj (SupportedTrace.kernel A f B M))
      (S := F.obj ((SupportedTrace.push A (pullback.snd f f)).obj
        (SupportedTrace.kernel A f B M)))
      (SupportedTrace.unitRightUnitor (ModuleCat.{u + 1} A) X M)
      ((diagonalFirst A f).hom.app (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
        (SupportedTrace.push A (pullback.fst f f)).map d.diagonalClass)
      (traceFirst A d)
      (F.map (SupportedTrace.insertionApp A f d.diagonalClass M))
      ((SupportedTrace.directComparison A f).hom.app (SupportedTrace.kernel A f B M))
      (SupportedTrace.orderedProjection A (pullback.fst f f) M
        ((CoordinateTrace.pull A (pullback.snd f f)).obj B)).inv
      (hi₁ M) (by simpa -implicitDefEqProofs only [Category.assoc] using hn₁)
  · intro K
    rw [unit_app_eq A d, Category.assoc, hc₂ K]
    exact normalized_insertion_ids
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((CoordinateTrace.pull A f ⋙
          (derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj K))
      (U := derivedTensorUnit (ModuleCat.{u + 1} A) X)
      (M := (CoordinateTrace.pull A f ⋙
        (derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj K)
      (V := (SupportedTrace.push A (pullback.snd f f)).obj
        ((CoordinateTrace.pull A (pullback.snd f f)).obj B))
      (Q := (SupportedTrace.push A (pullback.snd f f)).obj
        (CoordinateTrace.tensor A (pullback f f)
          ((CoordinateTrace.pull A (pullback.snd f f)).obj
            ((CoordinateTrace.pull A f ⋙
              (derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj K))
          ((CoordinateTrace.pull A (pullback.snd f f)).obj B)))
      (S := (SupportedTrace.push A (pullback.snd f f)).obj
        (SupportedTrace.kernel A f B
          ((CoordinateTrace.pull A f ⋙
            (derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj K)))
      (SupportedTrace.unitRightUnitor (ModuleCat.{u + 1} A) X
        ((CoordinateTrace.pull A f ⋙
          (derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj K))
      ((TraceDiagonalDatum.idIsoDiagonalSnd (Λ := A) f).hom.app
          (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
        (SupportedTrace.push A (pullback.snd f f)).map d.diagonalClass)
      (traceSecond A d (CoordinateTrace.shiftedLine A J n) e)
      (SupportedTrace.insertionApp A f d.diagonalClass
        ((CoordinateTrace.pull A f ⋙
          (derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj K))
      ((SupportedTrace.push A (pullback.snd f f)).map
        (((derivedTensor (ModuleCat.{u + 1} A) (pullback f f)).map
          (SupportedTrace.coordinateTwisted A f (CoordinateTrace.shiftedLine A J n) K e).hom).app
            ((CoordinateTrace.pull A (pullback.snd f f)).obj B)))
      (SupportedTrace.orderedProjection A (pullback.snd f f)
        ((CoordinateTrace.pull A f ⋙
          (derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj K)
        ((CoordinateTrace.pull A (pullback.snd f f)).obj B)).inv
      (hi₂ K) (by simpa -implicitDefEqProofs only [Category.assoc] using hn₂)

end ConcreteTriangle

end AlgebraicGeometry.Etale.SfDiagonalKernel
