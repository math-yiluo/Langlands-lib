/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.AlgebraicGeometry.BoundedTopMorphisms
import WeilConjectures.AlgebraicGeometry.SiteFiniteConstantExtensionTower

/-! # Local models with constant finite graded terms

Source: Stacks Project, Cohomology on Sites, Tag 094G, the inductive construction
before descending the differentials to the coefficient ring.
-/

@[expose] public section

universe u v z w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace CategoryTheory

/-- Realize a finite tower by successively taking mapping cocones.
Source: Stacks Project, Tag 094G, construction of the final differential and
rotation of the distinguished triangle.
(auxiliary; not a blueprint node)

Proof: Induct on the tower. At width zero use the single complex. For a step,
realize the lower tower and represent its boundary to the top single object by
a chain map using its upper bound. The mapping cocone adds the finite constant
term in the next degree and keeps all other terms up to isomorphism. Comparing
the rotated distinguished triangles and cancelling shifts identifies its
localization with the original object. -/
private theorem constant_tower_has_model
    {B : Type u} [CommRing B]
    {A : Type z} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (S : ModuleCat.{u} B ⥤ A) [S.Additive] (a : ℤ)
    {n : ℕ} {K : DerivedCategory A} (h : FiniteConstantExtensionTower S a n K) :
    ∃ (P : CochainComplex A ℤ) (M : ℤ → ModuleCat.{u} B),
      (∀ q, Module.Finite B (M q)) ∧
      (∀ q, q < a ∨ a + n < q → IsZero (M q)) ∧
      (∀ q, Nonempty (P.X q ≅ S.obj (M q))) ∧
      Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  classical
  induction h with
  | single M hM K e =>
    let N : ℤ → ModuleCat.{u} B := fun q ↦ if q = a then M else 0
    refine ⟨(CochainComplex.singleFunctor A a).obj (S.obj M), N, ?_, ?_, ?_, e⟩
    · intro q
      by_cases hq : q = a
      · exact (congrArg (fun T : ModuleCat.{u} B ↦ Module.Finite B T)
          (show N q = M from ite_eq_left hq)).mpr hM
      · have : Subsingleton (0 : ModuleCat.{u} B) :=
          ModuleCat.subsingleton_of_isZero (isZero_zero _)
        exact (congrArg (fun T : ModuleCat.{u} B ↦ Module.Finite B T)
          (show N q = 0 from ite_eq_right hq)).mpr inferInstance
    · intro q hq
      have hqa : q ≠ a := by omega
      dsimp only [N]
      rw [ite_eq_right hqa]
      exact isZero_zero _
    · intro q
      by_cases hqa : q = a
      · subst q
        simpa only [N, ite_eq_left rfl] using
          (show Nonempty (((CochainComplex.singleFunctor A a).obj (S.obj M)).X a ≅
            S.obj M) from ⟨HomologicalComplex.singleObjXSelf (.up ℤ) a (S.obj M)⟩)
      · dsimp only [N]
        rw [ite_eq_right hqa]
        exact ⟨(HomologicalComplex.isZero_single_obj_X (.up ℤ) a (S.obj M) q hqa).iso
          (S.map_isZero (isZero_zero _))⟩
  | @step n K L M hM hL i δ j hT ih =>
    obtain ⟨E, N, hfinite, hzero, hterm, ⟨eL⟩⟩ := ih
    have hEzero (q : ℤ) (hq : q < a ∨ a + n < q) : IsZero (E.X q) :=
      (S.map_isZero (hzero q hq)).of_iso (hterm q).some
    have : E.IsStrictlyLE (a + n) :=
      (E.isStrictlyLE_iff _).2 (fun q hq ↦ hEzero q (Or.inr hq))
    obtain ⟨f, hf⟩ := DerivedCategory.exists_chainMap_to_single_of_isStrictlyLE
      E (a + n) (S.obj M) (eL.inv ≫ δ)
    let P := CochainComplex.mappingCocone f
    let N' : ℤ → ModuleCat.{u} B := fun q ↦ if q = a + n + 1 then M else N q
    have eP (q : ℤ) : P.X q ≅ E.X q ⊞
        ((CochainComplex.singleFunctor A (a + n)).obj (S.obj M)).X (q - 1) :=
      (CochainComplex.mappingCone f).shiftFunctorObjXIso (-1) q (q - 1) (by omega) ≪≫
        HomologicalComplex.homotopyCofiber.XIsoBiprod f (q - 1) q (by simp)
    refine ⟨P, N', ?_, ?_, ?_, ?_⟩
    · intro q
      by_cases hq : q = a + n + 1
      · exact (congrArg (fun T : ModuleCat.{u} B ↦ Module.Finite B T)
          (show N' q = M from ite_eq_left hq)).mpr hM
      · exact (congrArg (fun T : ModuleCat.{u} B ↦ Module.Finite B T)
          (show N' q = N q from ite_eq_right hq)).mpr (hfinite q)
    · intro q hq
      have hqa : q ≠ a + n + 1 := by omega
      dsimp only [N']
      rw [ite_eq_right hqa]
      exact hzero q (by omega)
    · intro q
      by_cases hqa : q = a + n + 1
      · dsimp only [N']
        rw [ite_eq_left hqa]
        have hq : q - 1 = a + n := by omega
        refine ⟨eP q ≪≫ (isoZeroBiprod (hEzero q (Or.inr (by omega)))).symm ≪≫ ?_⟩
        exact eqToIso (congrArg (fun r ↦
          ((CochainComplex.singleFunctor A (a + n)).obj (S.obj M)).X r) hq) ≪≫
            HomologicalComplex.singleObjXSelf (.up ℤ) (a + n) (S.obj M)
      · dsimp only [N']
        rw [ite_eq_right hqa]
        exact ⟨eP q ≪≫ (isoBiprodZero
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) (a + n) (S.obj M)
            (q - 1) (by omega))).symm ≪≫ (hterm q).some⟩
    · let T := Triangle.mk i δ j
      let T' := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle f)
      have hT' : T' ∈ distTriang _ := DerivedCategory.mappingCocone_triangle_distinguished f
      let e := Pretriangulated.isoTriangleOfIso₁₂ T.rotate T'.rotate
        (Pretriangulated.rot_of_distTriang _ hT)
        (Pretriangulated.rot_of_distTriang _ hT') eL (Iso.refl _) (by
          change δ ≫ 𝟙 _ = eL.hom ≫ DerivedCategory.Q.map f
          rw [hf]
          simp)
      let eShift := Triangle.π₃.mapIso e
      let eCancel := shiftFunctorCompIsoId (DerivedCategory A) (1 : ℤ) (-1) (by omega)
      exact ⟨(eCancel.app K).symm ≪≫ (shiftFunctor _ (-1)).mapIso eShift ≪≫
        eCancel.app (DerivedCategory.Q.obj P)⟩

/-- The cohomological induction produces a bounded sheaf complex whose graded
terms are constant finite modules. Its differentials are still sheaf morphisms.

Source: Stacks Project, Cohomology on Sites, Tag 094G, proof of
`lemma-locally-constant`, construction by induction on the cohomological interval.
(auxiliary; not a blueprint node)

Proof: The cohomological induction is isolated as the local finite constant
extension tower theorem. Its triangles have a finite constant object in degree a
at the bottom and one finite constant attachment in each higher degree. It does
not supply representing complexes or chain maps for the boundary morphisms.
On each covering slice realize the tower by induction, as proved in
constant_tower_has_model. At a successor step, the lower model E vanishes above
n. The bounded-top chain-representative theorem realizes the boundary
Q(E) to the single constant object in degree n by an actual chain map f. Its
mapping cocone has term E^q direct sum F^(q-1). In the new top degree only F
survives; in all other degrees only E survives. Thus its coefficients are finite
and have exactly the requested bounds. Compare the rotated tower and cocone
triangles using the inductive isomorphism and the identity on the single object.
The triangle isomorphism gives the desired comparison after cancelling shifts.
Finally a+(b-a).toNat=b translates the tower's bound into [a,b]. Zero modules
and zero summands cover the zero ring and zero homology cases. -/
theorem exists_site_bounded_constant_graded_model
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (X : C) (hX : IsTerminal X)
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    [HasDerivedCategory.{w} (Sheaf J.toGrothendieck (ModuleCat.{u} B))]
    [∀ U : C, HasDerivedCategory.{w}
      (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B))]
    (K : DerivedCategory (Sheaf J.toGrothendieck (ModuleCat.{u} B)))
    (a b : ℤ) (hab : a < b)
    (hvan : ∀ q : ℤ, q < a ∨ b < q → IsZero
      ((DerivedCategory.homologyFunctor (Sheaf J.toGrothendieck (ModuleCat.{u} B)) q).obj K))
    (hloc : ∀ (q : ℤ) (V : C),
      ∃ (I : Type u) (U : I → C) (f : ∀ i : I, U i ⟶ V),
        Presieve.ofArrows U f ∈ J V ∧
        ∀ i : I, ∃ M : ModuleCat.{u} B, Module.Finite B M ∧ Nonempty
          ((J.toGrothendieck.overPullback (ModuleCat.{u} B) (U i)).obj
            ((DerivedCategory.homologyFunctor
              (Sheaf J.toGrothendieck (ModuleCat.{u} B)) q).obj K) ≅
            (constantSheaf (J.toGrothendieck.over (U i)) (ModuleCat.{u} B)).obj M)) :
    ∃ (I : Type u) (U : I → C) (f : ∀ i : I, U i ⟶ X),
      Presieve.ofArrows U f ∈ J X ∧
      ∀ i : I, ∃ P : CochainComplex
          (Sheaf (J.toGrothendieck.over (U i)) (ModuleCat.{u} B)) ℤ,
        ∃ M : ℤ → ModuleCat.{u} B,
          (∀ q : ℤ, Module.Finite B (M q)) ∧
          (∀ q : ℤ, q < a ∨ b < q → IsZero (M q)) ∧
          (∀ q : ℤ, Nonempty (P.X q ≅
            (constantSheaf (J.toGrothendieck.over (U i)) (ModuleCat.{u} B)).obj (M q))) ∧
          Nonempty
            ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
                (J.toGrothendieck.overPullback (ModuleCat.{u} B) (U i))
                (Functor.additive_of_preserves_binary_products _) _
                ⟨fun _ _ _ ↦ PreservesColimitsOfSize.preservesColimitsOfShape
                  (self := Adjunction.leftAdjoint_preservesColimits
                    (Functor.sheafAdjunctionCocontinuous
                      (Over.forget (U i)) (ModuleCat.{u} B)
                      (J.toGrothendieck.over (U i)) J.toGrothendieck))⟩).obj K ≅
              DerivedCategory.Q.obj P) := by
  obtain ⟨I, U, f, hcover, htower⟩ :=
    exists_site_finite_constant_extension_tower J X hX B K a b (le_of_lt hab) hvan hloc
  refine ⟨I, U, f, hcover, fun i ↦ ?_⟩
  obtain ⟨P, M, hfinite, hzero, hterm, he⟩ := constant_tower_has_model
    (constantSheaf (J.toGrothendieck.over (U i)) (ModuleCat.{u} B)) a (htower i)
  refine ⟨P, M, hfinite, ?_, hterm, he⟩
  intro q hq
  apply hzero q
  have hwidth : a + (b - a).toNat = b := by omega
  omega

end CategoryTheory
