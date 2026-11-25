/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-! # Acyclic tensor tests along tensor-compatible equivalences

Let `F : C ⥤ D` be an additive equivalence of abelian monoidal categories together with a
natural isomorphism `F (X ⊗ Y) ≅ F X ⊗ F Y`. Applied termwise, `F` carries total tensor
complexes to total tensor complexes, and it preserves and reflects the acyclic tensor test
for K-flatness: `Tot(Z ⊗ P)` is acyclic for every acyclic `Z`.

No monoidal coherence of the comparison isomorphism is needed.

Source: Stacks Project, Cohomology on Sites, Tag 06YN
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CochainComplex

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- An additive equivalence compatible with tensor products carries total tensor complexes of
cochain complexes to total tensor complexes of their images.
Source: Stacks Project, Tag 06YN (auxiliary; not a blueprint node).

Proof: the tensor comparison is a natural transformation between the two bifunctors, and an
equivalence preserves the coproducts defining the total complexes; the induced comparison of
total complexes is an isomorphism since all its components are. -/
theorem nonempty_mapHomologicalComplex_mapBifunctor_tensor_iso
    [Preadditive C] [Preadditive D]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalCategory D] [(curriedTensor D).PreservesZeroMorphisms]
    [∀ X, ((curriedTensor D).obj X).PreservesZeroMorphisms]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (V W : CochainComplex C ℤ) :
    Nonempty ((F.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor V W (curriedTensor C)) ≅
        CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj V)
          ((F.mapHomologicalComplex (.up ℤ)).obj W) (curriedTensor D)) := by
  let τ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D) :=
    { app X :=
        { app Y := e.hom.app (X, Y)
          naturality Y Y' g := by
            simpa using e.hom.naturality (X := (X, Y)) (Y := (X, Y')) (𝟙 X, g) }
      naturality X X' f := by
        ext Y
        simpa using e.hom.naturality (X := (X, Y)) (Y := (X', Y)) (f, 𝟙 Y) }
  have (X Y : C) : IsIso ((τ.app X).app Y) := (e.app (X, Y)).isIso_hom
  exact ⟨asIso (HomologicalComplex.mapBifunctorComparison τ (.up ℤ) V W)⟩

/-- Acyclicity is preserved and reflected by an additive equivalence applied termwise.
Source: Stacks Project, Tag 06YN (auxiliary; not a blueprint node).

Proof: a faithful exact functor preserves and reflects exactness of each short complex. -/
theorem acyclic_mapHomologicalComplex_iff_of_isEquivalence [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence] (P : CochainComplex C ℤ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj P).Acyclic ↔ P.Acyclic :=
  ⟨fun h i ↦ (P.sc i).exact_map_iff_of_faithful F |>.1 (h i),
    fun h i ↦ (P.sc i).exact_map_iff_of_faithful F |>.2 (h i)⟩

/-- The acyclic tensor test for K-flatness is invariant under isomorphism.
Source: Stacks Project, Tag 06YN (auxiliary; not a blueprint node).

Proof: the total tensor complex is functorial in its second variable. -/
theorem acyclicTensorTest_of_iso [Abelian C] [MonoidalCategory C]
    [(curriedTensor C).PreservesZeroMorphisms]
    [∀ X, ((curriedTensor C).obj X).PreservesZeroMorphisms]
    [HasColimitsOfSize.{0, 0} C] {P Q : CochainComplex C ℤ} (e : P ≅ Q)
    (hP : ∀ Z : CochainComplex C ℤ, Z.Acyclic →
      (CochainComplex.mapBifunctor Z P (curriedTensor C)).Acyclic) :
    ∀ Z : CochainComplex C ℤ, Z.Acyclic →
      (CochainComplex.mapBifunctor Z Q (curriedTensor C)).Acyclic := by
  intro Z hZ i
  exact (hP Z hZ i).of_iso
    ((((curriedTensor C).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).obj Z).mapIso e)

/-- An additive equivalence compatible with tensor products preserves and reflects the acyclic
tensor test for K-flatness.
Source: Stacks Project, Tag 06YN (auxiliary; not a blueprint node).

Proof: write a test complex of `D` as the image of a test complex of `C` up to the counit.
The equivalence preserves and reflects acyclicity, and it identifies the image of a total
tensor complex with the total tensor complex of the images. -/
theorem acyclicTensorTest_mapHomologicalComplex_iff [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalCategory D] [(curriedTensor D).PreservesZeroMorphisms]
    [∀ X, ((curriedTensor D).obj X).PreservesZeroMorphisms]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D) (P : CochainComplex C ℤ) :
    (∀ Z : CochainComplex D ℤ, Z.Acyclic →
      (CochainComplex.mapBifunctor Z ((F.mapHomologicalComplex (.up ℤ)).obj P)
        (curriedTensor D)).Acyclic) ↔
    (∀ Z : CochainComplex C ℤ, Z.Acyclic →
      (CochainComplex.mapBifunctor Z P (curriedTensor C)).Acyclic) := by
  let W := F.mapHomologicalComplex (.up ℤ)
  constructor
  · intro h Z hz
    apply (acyclic_mapHomologicalComplex_iff_of_isEquivalence F _).mp
    obtain ⟨q⟩ := nonempty_mapHomologicalComplex_mapBifunctor_tensor_iso F e Z P
    exact fun i ↦ (h (W.obj Z)
      ((acyclic_mapHomologicalComplex_iff_of_isEquivalence F Z).mpr hz) i).of_iso q.symm
  · intro h Z hz
    have : W.IsEquivalence :=
      (F.asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
    let V := W.asEquivalence
    let Z' := V.inverse.obj Z
    have hZ' : Z'.Acyclic :=
      (acyclic_mapHomologicalComplex_iff_of_isEquivalence F Z').mp
        (fun i ↦ (hz i).of_iso (V.counitIso.app Z).symm)
    obtain ⟨q⟩ := nonempty_mapHomologicalComplex_mapBifunctor_tensor_iso F e Z' P
    have hq : (CochainComplex.mapBifunctor (W.obj Z') (W.obj P) (curriedTensor D)).Acyclic :=
      fun i ↦ ((acyclic_mapHomologicalComplex_iff_of_isEquivalence F _).mpr (h Z' hZ') i).of_iso q
    exact fun i ↦ (hq i).of_iso
      ((((curriedTensor D).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).mapIso
        (V.counitIso.app Z)).app _)


/-- The acyclic tensor test implies K-flatness for the class of quasi-isomorphisms.
Source: Stacks Project, Tag 06YN (auxiliary; not a blueprint node).

Proof: in the homotopy category, K-flatness means that tensoring with the complex on either
side preserves acyclic objects; the braiding exchanges the two sides. -/
theorem kFlat_of_acyclicTensorTest
    [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [BraidedCategory C] [HasColimitsOfSize.{0, 0} C] (P : CochainComplex C ℤ)
    (hP : ∀ Z : CochainComplex C ℤ, Z.Acyclic →
      (CochainComplex.mapBifunctor Z P (curriedTensor C)).Acyclic) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro Z hZ
  obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hZ
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor Z P (curriedTensor C))).2 (hP Z hZ)
  exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr, hr⟩

end CochainComplex
