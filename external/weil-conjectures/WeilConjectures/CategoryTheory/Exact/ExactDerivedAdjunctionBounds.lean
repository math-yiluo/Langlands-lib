/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Bounds and conservativity of exact derived adjunctions

Source: Stacks Project, Derived Categories, Tags 015F and 05TC; Zheng,
Construction 4.1 and Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe a av b bv da db
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory

variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{da} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{db} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (FD : DerivedCategory A ⥤ DerivedCategory B)
  (fac : DerivedCategory.Q ⋙ FD ≅
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)

private def exactDerivedIso : FD ≅ F.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
    (DerivedCategory.Q ⋙ FD) (DerivedCategory.Q ⋙ F.mapDerivedCategory)
    FD F.mapDerivedCategory (fac ≪≫ F.mapDerivedCategoryFactors.symm)

include F fac

private theorem exactDerived_isGE (X : DerivedCategory A) (n : ℤ) [X.IsGE n] :
    (FD.obj X).IsGE n := by
  have := F.isGE_mapDerivedCategory_obj X n
  exact DerivedCategory.TStructure.t.isGE_of_iso (exactDerivedIso F FD fac |>.app X).symm n

private theorem exactDerived_isLE (X : DerivedCategory A) (n : ℤ) [X.IsLE n] :
    (FD.obj X).IsLE n := by
  have := F.isLE_mapDerivedCategory_obj X n
  exact DerivedCategory.TStructure.t.isLE_of_iso (exactDerivedIso F FD fac |>.app X).symm n

/-- A right adjoint to an exact derived inverse image preserves each lower bound.
Source: Stacks 05TC. Proof: a map from an object in degrees at most n-1 to the
right-adjoint image transposes to a map into the original object in degrees at least n.
Exactness preserves the upper bound, so that transpose and hence the map vanish.
(blueprint: lem-pur-exact-derived-adjunction-bounds). -/
theorem exactDerivedAdjunction_isGE
    {RD : DerivedCategory B ⥤ DerivedCategory A} (adj : FD ⊣ RD)
    (X : DerivedCategory B) (n : ℤ) [X.IsGE n] : (RD.obj X).IsGE n := by
  change DerivedCategory.TStructure.t.IsGE (RD.obj X) n
  rw [DerivedCategory.TStructure.t.isGE_iff_orthogonal (n - 1) n (by omega)]
  intro Y f hY
  have := exactDerived_isLE F FD fac Y (n - 1)
  have : FD.Additive := Functor.additive_of_iso (exactDerivedIso F FD fac).symm
  have : RD.Additive := adj.right_adjoint_additive
  have hz : (adj.homEquiv Y X).symm f = 0 :=
    DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ (n - 1) n (by omega)
      inferInstance inferInstance
  have := congrArg (adj.homEquiv Y X) hz
  simpa [Adjunction.homEquiv_unit] using this

/-- Faithfulness on bounded-below derived objects makes an exact derived functor
conservative on the entire unbounded category.
Source: Zheng, proof of Lemma 4.10, with Stacks 015F. Proof: degree-zero single
functors are fully faithful, so the hypothesis first makes F faithful on the abelian
categories. Exactness identifies the image of every cohomology morphism with the
cohomology of the image. Faithful exact functors reflect isomorphisms, and cohomology
jointly detects isomorphisms in the unbounded derived category.
(blueprint: lem-pur-exact-derived-adjunction-bounds). -/
theorem exactDerived_reflectsIso_of_boundedBelow_faithful
    (hfaith : ∀ (X Y : DerivedCategory A),
      (∃ n : ℤ, X.IsGE n) → (∃ n : ℤ, Y.IsGE n) →
      Function.Injective (FD.map : (X ⟶ Y) → _)) : FD.ReflectsIsomorphisms := by
  let sA := DerivedCategory.singleFunctor A 0
  let sB := DerivedCategory.singleFunctor B 0
  let c : sA ⋙ FD ≅ F ⋙ sB :=
    isoWhiskerLeft sA (exactDerivedIso F FD fac) ≪≫ F.mapDerivedCategorySingleFunctor 0
  have hF : F.Faithful := by
    constructor
    intro X Y f g hfg
    apply sA.map_injective
    apply hfaith (sA.obj X) (sA.obj Y) ⟨0, inferInstance⟩ ⟨0, inferInstance⟩
    apply (cancel_mono (c.hom.app Y)).mp
    change (sA ⋙ FD).map f ≫ c.hom.app Y = (sA ⋙ FD).map g ≫ c.hom.app Y
    rw [c.hom.naturality, c.hom.naturality]
    simp only [Functor.comp_map, hfg]
  have hD : F.mapDerivedCategory.ReflectsIsomorphisms := by
    constructor
    intro X Y f hf
    rw [DerivedCategory.isIso_iff]
    intro n
    have hi : IsIso (F.map ((DerivedCategory.homologyFunctor A n).map f)) :=
      (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) f).2
        (by change IsIso ((DerivedCategory.homologyFunctor B n).map
          (F.mapDerivedCategory.map f)); infer_instance)
    exact isIso_of_reflects_iso _ F
  constructor
  intro X Y f hf
  have : IsIso (F.mapDerivedCategory.map f) :=
    (NatIso.isIso_map_iff (exactDerivedIso F FD fac) f).1 hf
  exact isIso_of_reflects_iso f F.mapDerivedCategory

/-- Full faithfulness on bounded-below objects makes the counit invertible on their
essential image, even though the adjunction itself lives on unbounded categories.
Source: Zheng, Lemma 4.10. Proof: postcomposition with the unit on a bounded-below X
is the composite of the full-faithfulness bijection and adjunction. Its target is
bounded below by the preceding bound theorem. Surjectivity at that target supplies a
left inverse, and injectivity at X supplies the other inverse. The triangle identity
then inverts the counit on FD X; naturality transports this to its essential image.
(blueprint: lem-pur-exact-derived-adjunction-bounds). -/
theorem exactDerivedAdjunction_counit_isIso_of_origin
    {RD : DerivedCategory B ⥤ DerivedCategory A} (adj : FD ⊣ RD)
    (hfull : ∀ (X Y : DerivedCategory A),
      (∃ n : ℤ, X.IsGE n) → (∃ n : ℤ, Y.IsGE n) →
      Function.Bijective (FD.map : (X ⟶ Y) → _))
    (M : DerivedCategory B) (X : DerivedCategory A) (hX : ∃ n : ℤ, X.IsGE n)
    (e : FD.obj X ≅ M) : IsIso (adj.counit.app M) := by
  obtain ⟨n, hn⟩ := hX
  have hFX : (FD.obj X).IsGE n := exactDerived_isGE F FD fac X n
  have hRFX : (RD.obj (FD.obj X)).IsGE n :=
    exactDerivedAdjunction_isGE F FD fac adj (FD.obj X) n
  have hb (Y : DerivedCategory A) (hY : ∃ n : ℤ, Y.IsGE n) :
      Function.Bijective (fun f : Y ⟶ X ↦ f ≫ adj.unit.app X) := by
    have he : (fun f : Y ⟶ X ↦ f ≫ adj.unit.app X) =
        (adj.homEquiv Y (FD.obj X)) ∘ FD.map := by
      funext f
      simp only [Function.comp_apply, Adjunction.homEquiv_unit]
      exact adj.unit.naturality f
    rw [he]
    exact (adj.homEquiv Y (FD.obj X)).bijective.comp (hfull Y X hY ⟨n, hn⟩)
  obtain ⟨r, hr⟩ := (hb (RD.obj (FD.obj X)) ⟨n, hRFX⟩).2 (𝟙 _)
  have hη : IsIso (adj.unit.app X) := by
    refine ⟨r, ?_, hr⟩
    apply (hb X ⟨n, hn⟩).1
    dsimp only at hr ⊢
    rw [Category.assoc, hr]
    simp
  have hc : IsIso (adj.counit.app (FD.obj X)) := by
    have hi : IsIso (FD.map (adj.unit.app X) ≫ adj.counit.app (FD.obj X)) := by
      have he : FD.map (adj.unit.app X) ≫ adj.counit.app (FD.obj X) = 𝟙 _ :=
        adj.left_triangle_components X
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_left (FD.map (adj.unit.app X)) _
  have hcomp : IsIso ((RD ⋙ FD).map e.hom ≫ adj.counit.app M) := by
    change IsIso (FD.map (RD.map e.hom) ≫ adj.counit.app M)
    have he : FD.map (RD.map e.hom) ≫ adj.counit.app M =
        adj.counit.app (FD.obj X) ≫ e.hom := adj.counit.naturality e.hom
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left ((RD ⋙ FD).map e.hom) _

end CategoryTheory
