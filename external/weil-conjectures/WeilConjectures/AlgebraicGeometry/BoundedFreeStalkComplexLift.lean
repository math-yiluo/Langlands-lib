/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.BoundedFreeStalkComplexLocalLift

/-! # Lifting the differential matrices of a bounded free stalk complex

Source: Stacks Project, Tags 0BCD and 0BC7, finite presentation argument;
Tag 00CR and the definition of the module direct image.
(blueprint: lem-sc-bounded-free-stalk-complex-lift).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Restriction of ordinary direct image from an open recovers the original module.
Source: ordinary module direct image, whose sections on V are sections on V intersect U.
For V contained in U, the projection U intersect V to V is an isomorphism. Applying
M to this projection identifies the restriction of direct image with M. The counit
of restriction/direct image has these maps as components, hence is an isomorphism.
This is the direct-image step of lem-sc-bounded-free-stalk-complex-lift. -/
private theorem openModuleDirectImage_restrict_iso (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :
    Nonempty ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).obj
      ((SheafOfModules.pushforward.{u}
        (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U)).obj M) ≅ M) := by
  let adj := SheafOfModules.overPushforwardOverAdj.{u}
    (R := moduleRings X.toRingedSpace) U
  have : (Over.forget U).Full :=
    ⟨fun f ↦ ⟨Over.homMk f (Subsingleton.elim _ _), rfl⟩⟩
  have : IsIso (Over.forgetAdjStar U).unit := inferInstance
  let := Functor.isContinuous_comp (Over.forget U) (Over.star U)
    ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology X)
    ((Opens.grothendieckTopology X).over U)
  let φ := 𝟙 ((moduleRings X.toRingedSpace).over U) ≫
    ((Over.forget U).sheafPushforwardContinuous RingCat _ _).map
      (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U)
  have : IsIso (SheafOfModules.pushforwardNatTrans.{u}
      (G := Over.forget U ⋙ Over.star U)
      (S := (moduleRings X.toRingedSpace).over U) φ
      (Over.forgetAdjStar U).unit) := by
    change IsIso (SheafOfModules.pushforwardNatIso
      (G := Over.forget U ⋙ Over.star U)
      (S := (moduleRings X.toRingedSpace).over U) φ
      (asIso (Over.forgetAdjStar U).unit)).hom
    infer_instance
  have : IsIso (adj.counit.app M) := by
    dsimp [adj, SheafOfModules.overPushforwardOverAdj,
      SheafOfModules.pushforwardPushforwardAdj]
    infer_instance
  exact ⟨asIso (adj.counit.app M)⟩

/-- A bounded free stalk complex lifts as a complex, without a prescribed derived object.

Source: Stacks Project, Tags 0BCD and 0BC7, descent of finite presentations and maps,
and Tag 00CR. The final direct image is only an auxiliary global complex.
(blueprint: lem-sc-bounded-free-stalk-complex-lift).

Proof:
1. Fix bounds a,b. The stalk ring is nonzero, since it is local. A zero free module
   over it has rank zero, so hfree implies d i = 0 outside [a,b], including when b < a.
   Choose bases using hfree, and express the differentials as finite matrices. There
   are only finitely many entries and finitely many equations for the square to vanish.
2. Choose an affine neighbourhood of x. Its stalk is the prime localization of its
   section ring, the filtered colimit of principal localizations (Tag 00CR). Lift all
   entries to one principal neighbourhood. Every entry of each differential composite
   has zero germ; shrink to a common later principal neighbourhood where these finitely
   many entries vanish. Equivalently use the maps and equality clauses of finite
   presentation descent. The rank-d i free modules and these matrices now define a
   bounded free sheaf complex L on this affine open U. Its stalk complex is isomorphic
   to F, since the chosen bases conjugate the differentials to their lifted matrices.
3. Define H by the termwise ordinary direct image along U into X: on an open V its
   sections are the sections of L on V intersect U, with scalars restricted from V.
   Direct image is additive and preserves zero objects, so H is bounded. Its restriction
   to U is L. Neighbourhoods contained in U are cofinal at x, so its stalk complex is
   the stalk complex of L. These identifications give the free-term and stalk isomorphisms.
No comparison with another derived object is made. Empty spectra have no x; rank-zero
terms and empty degree intervals require no entries or equations to lift.
-/
theorem exists_boundedFree_stalk_complex_lift
    (X : Scheme.{u}) (x : X) (d : ℤ → ℕ)
    (F : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (F.X i))
    (hfree : ∀ i : ℤ, Nonempty (F.X i ≅ ModuleCat.of (X.presheaf.stalk x)
      (ULift.{0} (Fin (d i) → X.presheaf.stalk x)))) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ H : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
        (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (H.X i)) ∧
        (∀ i : ℤ, Nonempty
          ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).obj
            (H.X i) ≅ SheafOfModules.free
              (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin (d i))))) ∧
        Nonempty (F ≅
          (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj H)) := by
  classical
  let e := fun i ↦ (hfree i).some
  obtain ⟨a, b, hab⟩ := hbounded
  have hd (i : ℤ) (hi : i < a ∨ b < i) : d i = 0 := by
    have hz := (hab i hi).of_iso (e i).symm
    have hs := ModuleCat.subsingleton_of_isZero hz
    by_contra hne
    have hn : 0 < d i := Nat.pos_of_ne_zero hne
    have h01 := congrArg (fun f ↦ f.down ⟨0, hn⟩)
      (hs.elim (ULift.up (fun _ : Fin (d i) ↦ (0 : X.presheaf.stalk x)))
        (ULift.up (fun _ : Fin (d i) ↦ (1 : X.presheaf.stalk x))))
    exact zero_ne_one h01
  let K : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ :=
    { X := fun i ↦ ModuleCat.of (X.presheaf.stalk x)
        (ULift.{0} (Fin (d i) → X.presheaf.stalk x))
      d := fun i j ↦ (e i).inv ≫ F.d i j ≫ (e j).hom
      shape := fun i j hij ↦ by rw [F.shape i j hij]; simp
      d_comp_d' := fun i j k _ _ ↦ by simp [Category.assoc] }
  have eK : F ≅ K := HomologicalComplex.Hom.isoOfComponents e
    (fun i j _ ↦ by simp [K])
  obtain ⟨U, hxU, hU, L, hLbounded, hLfree, ⟨eLocal⟩⟩ :=
    exists_boundedFree_stalk_complex_local_lift X x d K (fun _ ↦ rfl) a b hd
  let P := SheafOfModules.pushforward.{u}
    (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U)
  let H := (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  refine ⟨U, hxU, hU, H, ?_, ?_, ?_⟩
  · exact ⟨a, b, fun i hi ↦ P.map_isZero (hLbounded i hi)⟩
  · intro i
    obtain ⟨eFree⟩ := hLfree i
    obtain ⟨eRestrict⟩ := openModuleDirectImage_restrict_iso X U (L.X i)
    exact ⟨eRestrict ≪≫ eFree⟩
  · exact ⟨eK ≪≫ eLocal⟩

end
end AlgebraicGeometry.Scheme
