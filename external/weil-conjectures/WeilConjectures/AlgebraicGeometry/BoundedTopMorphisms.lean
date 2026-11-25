/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Chain representatives for morphisms out of the top degree

Source: Stacks Project, Cohomology on Sites, Tag 094G, the boundary map from the
lower bounded model to the top free term, using the canonical derived t-structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace DerivedCategory

set_option backward.isDefEq.respectTransparency false in
/-- A derived map from a strictly upper bounded complex to an object in its
highest degree is represented by an actual chain map. The terms of the source
need not be projective.

Source: Stacks Project, Cohomology on Sites, Tag 094G, boundary-map step.
(auxiliary; not a blueprint node)

Proof: The outgoing differential at n vanishes, so H^n(P) is the cokernel of the
incoming differential. Transport the top cohomology map of the derived morphism
through the localization comparison, and precompose it with this cokernel quotient.
It kills the incoming differential and defines a chain map to the single complex.
Its induced top homology map is the prescribed one, by the naturality of the
cycles and opcycles maps and their single-complex comparison isomorphisms. The
canonical t-structure makes H^n injective on maps from objects bounded above by n
to objects bounded below by n; hence the localized chain map is the original
morphism. That injectivity follows by truncating source and target to the shifted
heart, where the single-complex functor is fully faithful. -/
theorem exists_chainMap_to_single_of_isStrictlyLE
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (P : CochainComplex A ℤ) (n : ℤ) [P.IsStrictlyLE n] (X : A)
    (φ : Q.obj P ⟶ Q.obj ((CochainComplex.singleFunctor A n).obj X)) :
    ∃ f : P ⟶ (CochainComplex.singleFunctor A n).obj X, Q.map f = φ := by
  classical
  let S := (CochainComplex.singleFunctor A n).obj X
  have hd : P.d n (n + 1) = 0 :=
    (P.isZero_of_isStrictlyLE n (n + 1) (by omega)).eq_of_tgt _ _
  let e := P.isoHomologyι n (n + 1) (by simp) hd
  let h : P.homology n ⟶ S.homology n :=
    ((homologyFunctorFactors A n).app P).inv ≫ (homologyFunctor A n).map φ ≫
      ((homologyFunctorFactors A n).app S).hom
  let ψ : P.X n ⟶ X := P.pOpcycles n ≫ e.inv ≫ h ≫
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n X).hom
  have hψ (i : ℤ) (_hi : (ComplexShape.up ℤ).Rel i n) : P.d i n ≫ ψ = 0 := by
    dsimp only [ψ]
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
    simp
  let f : P ⟶ S := HomologicalComplex.mkHomToSingle ψ hψ
  refine ⟨f, ?_⟩
  apply (homologyFunctor_map_bijective_of_isLE_of_isGE (C := A)
    (X := Q.obj P) (Y := Q.obj S) n).1
  have hf : HomologicalComplex.homologyMap f n = h := by
    apply (cancel_epi (P.homologyπ n)).mp
    apply (cancel_mono (S.homologyι n)).mp
    simp only [Category.assoc]
    rw [HomologicalComplex.homologyι_naturality,
      ← Category.assoc, HomologicalComplex.homology_π_ι]
    rw [Category.assoc, HomologicalComplex.p_opcyclesMap]
    dsimp only [f]
    rw [HomologicalComplex.mkHomToSingle_f]
    dsimp only [ψ]
    simp only [Category.assoc]
    erw [← HomologicalComplex.singleObjOpcyclesSelfIso_hom,
      HomologicalComplex.singleObjHomologySelfIso_hom_singleObjOpcyclesSelfIso_hom]
    rw [← HomologicalComplex.homology_π_ι_assoc]
    change P.homologyπ n ≫ e.hom ≫ e.inv ≫ h ≫ S.homologyι n = _
    simp only [Iso.hom_inv_id_assoc]
  have hn := (homologyFunctorFactors A n).hom.naturality f
  change (homologyFunctor A n).map (Q.map f) ≫ _ = _ ≫
    HomologicalComplex.homologyMap f n at hn
  rw [hf] at hn
  dsimp only [h] at hn
  change (homologyFunctor A n).map (Q.map f) ≫
      ((homologyFunctorFactors A n).app S).hom =
    ((homologyFunctorFactors A n).app P).hom ≫
      ((homologyFunctorFactors A n).app P).inv ≫
      (homologyFunctor A n).map φ ≫ ((homologyFunctorFactors A n).app S).hom at hn
  rw [Iso.hom_inv_id_assoc] at hn
  exact (cancel_mono ((homologyFunctorFactors A n).app S).hom).mp hn

end DerivedCategory
