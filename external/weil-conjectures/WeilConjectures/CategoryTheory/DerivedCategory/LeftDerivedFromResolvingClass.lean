/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedExactOfLocalization
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy

/-!
# Left derived functors computed by a resolving class

Source: Stacks Project, Tags 06XN and 05SE, in Situation 05S8
(blueprint: lem-pur-left-derived-from-kflat-class).
-/

@[expose] public section

universe w v u v' u'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- Stacks Project, Tag 06XN (dual part) and Tag 05SE (left derived functor part)
(blueprint: lem-pur-left-derived-from-kflat-class).
An exact functor on the homotopy category has an everywhere defined exact left derived
functor if every object has a resolution in `P` and quasi-isomorphisms between objects
of `P` are sent to isomorphisms. Objects of `P` compute the left derived functor.

Proof:
1. By the resolution hypothesis, the arrows from objects of `P` to each `X` form a
cofinal subcategory of the category of quasi-isomorphisms into `X`. The second hypothesis
makes the corresponding pro-object essentially constant. For `X` in `P`, use the identity
resolution (Stacks Tag 06XN).
2. The Stacks-to-Kan bridge identifies this essential constancy with a pointwise right
Kan extension and its comparison map (`lem-pur-left-derived-defined-pointwise-kan-bridge`).
3. Assemble these pointwise extensions into a right Kan extension along `Qh`, giving the
universal pair (`lem-pur-total-left-derived-localization`).
4. Quasi-isomorphisms are saturated and compatible with the triangulation
(`lem-pur-quasi-isos-saturated-triangulated`). The everywhere-defined left derived functor
is exact by Tag 05SE (`lem-pur-left-derived-exact-when-defined`). The identity resolution
and the comparison clause of the bridge show that the counit is an isomorphism on `P`. -/
theorem leftDerived_from_resolvingClass
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (D' : Type u') [Category.{v'} D'] [Preadditive D'] [HasZeroObject D']
    [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D')
    [F.CommShift ℤ] [F.IsTriangulated]
    (P : Set (HomotopyCategory A (ComplexShape.up ℤ)))
    (hres : ∀ X : HomotopyCategory A (ComplexShape.up ℤ),
      ∃ (X' : HomotopyCategory A (ComplexShape.up ℤ)) (s : X' ⟶ X),
        X' ∈ P ∧ HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s)
    (hinv : ∀ (X X' : HomotopyCategory A (ComplexShape.up ℤ)) (s : X ⟶ X'),
      X ∈ P → X' ∈ P → HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s →
        IsIso (F.map s)) :
    F.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ∧
      ∃ (LF : DerivedCategory A ⥤ D') (ε : DerivedCategory.Qh ⋙ LF ⟶ F),
        LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ∧
          (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
            ∀ X : HomotopyCategory A (ComplexShape.up ℤ), X ∈ P → IsIso (ε.app X) := by
  classical
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := A)
  obtain ⟨hleft, hright, htri, hsat, htwo, _, _, _, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated A
  let : W.HasRightCalculusOfFractions := hright
  let : W.HasTwoOutOfThreeProperty := htwo
  have hS : W.IsSaturatedTriangulatedMultiplicativeSystem :=
    ⟨⟨⟨hleft, hright⟩, fun _ _ _ _ h g f ↦ hsat _ _ _ _ g h f⟩, htri⟩
  have hwitness := resolvingClass_essentialConstancy W F P hres hinv
  have hpw : F.HasPointwiseLeftDerivedFunctor W := by
    intro X
    obtain ⟨Y, u, hc, hr, _⟩ := hwitness X
    have hb := leftDerived_defined_pointwiseKan_bridge W Q F X Y hc u hr
    exact (F.hasPointwiseLeftDerivedFunctorAt_iff Q W X).2 hb.1
  let : F.HasPointwiseLeftDerivedFunctor W := hpw
  let LF := F.totalLeftDerived Q W
  let ε := F.totalLeftDerivedCounit Q W
  have hLF : LF.IsLeftDerivedFunctor ε W := inferInstance
  have hdefined : ∀ X, F.IsTriangulatedLeftDerivedDefinedAt W hS X := by
    intro X
    obtain ⟨Y, _, hc, _, _⟩ := hwitness X
    exact ⟨Y, hc⟩
  refine ⟨hpw, LF, ε, hLF, ?_, ?_⟩
  · exact leftDerived_exact_of_localization A D' F hS LF ε hLF hdefined
  · intro X hX
    obtain ⟨Y, u, hc, hr, hu⟩ := hwitness X
    obtain ⟨_, π, ⟨hπ⟩, _, hidentity⟩ :=
      leftDerived_defined_pointwiseKan_bridge W Q F X Y hc u hr
    let hcanonical :=
      isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor LF ε W (Q.obj X)
    let e := hcanonical.conePointUniqueUpToIso hπ
    have hid : W (𝟙 X) := W.id_mem X
    have : IsIso (u.app (⟨Over.mk (𝟙 X), hid⟩ : W.Over ⊤ X)) := hu hid hX
    have : IsIso (π.app (StructuredArrow.mk (𝟙 (Q.obj X)))) := by
      rw [hidentity hid]
      infer_instance
    have he := hcanonical.conePointUniqueUpToIso_hom_comp hπ
      (StructuredArrow.mk (𝟙 (Q.obj X)))
    have he' : e.hom ≫ π.app (StructuredArrow.mk (𝟙 (Q.obj X))) = ε.app X := by
      simpa [RightExtension.coneAt] using he
    rw [← he']
    infer_instance

end CategoryTheory.Functor
