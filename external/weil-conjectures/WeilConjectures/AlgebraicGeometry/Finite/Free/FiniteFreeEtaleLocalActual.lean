/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.Finite.Free.FiniteFreeEtaleAcyclicHomotopy
import WeilConjectures.Algebra.Homology.DerivedCategory.ReductionDatum
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-!
# Local chain representatives for finite free constant complexes

Source: Stacks Project, sites-cohomology.tex, Tag 08FR, assertions (1) and (2)
(blueprint: lem-weil-pbc-finite-free-etale-local-actual).

Constant coefficients are expressed as sheaves valued in `ModuleCat B`, the usual
constant-ring-module encoding. Étale inverse image is restriction to the localized site.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

private theorem lift_of_local_cone_homotopy
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (R : C ⥤ D) [R.Additive]
    {E F G : CochainComplex C ℤ} (q : F ⟶ G) (β : E ⟶ G)
    (H : Homotopy
      ((R.mapHomologicalComplex (.up ℤ)).map (β ≫ CochainComplex.mappingCone.inr q)) 0) :
    ∃ α : (R.mapHomologicalComplex (.up ℤ)).obj E ⟶
        (R.mapHomologicalComplex (.up ℤ)).obj F,
      Nonempty (Homotopy (α ≫ (R.mapHomologicalComplex (.up ℤ)).map q)
        ((R.mapHomologicalComplex (.up ℤ)).map β)) := by
  let K := HomotopyCategory.quotient D (.up ℤ)
  let T := (R.mapHomotopyCategory (.up ℤ)).mapTriangle.obj
    (CochainComplex.mappingCone.triangleh q)
  have hT : T ∈ distTriang _ :=
    (R.mapHomotopyCategory (.up ℤ)).map_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished q)
  have hβ : K.map ((R.mapHomologicalComplex (.up ℤ)).map β) ≫ T.mor₂ = 0 := by
    change K.map ((R.mapHomologicalComplex (.up ℤ)).map β) ≫
      K.map ((R.mapHomologicalComplex (.up ℤ)).map (CochainComplex.mappingCone.inr q)) = 0
    simpa only [← Functor.map_comp, Functor.map_zero] using
      (HomotopyCategory.eq_of_homotopy _ _ H)
  obtain ⟨a, ha⟩ := T.coyoneda_exact₂ hT
    (K.map ((R.mapHomologicalComplex (.up ℤ)).map β)) hβ
  obtain ⟨α, rfl⟩ := K.map_surjective a
  refine ⟨α, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  change K.map (α ≫ (R.mapHomologicalComplex (.up ℤ)).map q) = _
  rw [Functor.map_comp]
  exact ha.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Derived maps from a bounded finite free constant complex have local chain
representatives, and a chain map vanishing in the derived category is locally homotopic
to zero. Source: Stacks Project, Tag 08FR (lemma-local-actual), assertions (1) and (2)
(blueprint: lem-weil-pbc-finite-free-etale-local-actual).

Proof:
1. A map from the bounded finite free source into an acyclic complex becomes
   null-homotopic on an etale cover, by descending induction on its finite support
   interval (lem-weil-pbc-finite-free-etale-acyclic-homotopy).
2. Represent a derived morphism by a fraction E -> G <- F with F -> G a
   quasi-isomorphism. Its cone is acyclic. Apply step 1 to E -> G -> Cone(F -> G).
   Exactness of Hom into the restricted cone triangle gives a chain lift E -> F
   up to homotopy on each cover member. Cancel the restricted quasi-isomorphism
   in the derived category. Naturality of mapDerivedCategoryFactors identifies the
   resulting map with the specified restriction of the original derived morphism.
3. If Q(alpha) = 0, the calculus of fractions gives a quasi-isomorphism q: Z -> E
   with q followed by alpha null-homotopic. Exactness of Hom out of its cone
   triangle factors alpha through E -> Cone(q), up to homotopy. Apply step 1 to
   this map into the acyclic cone, and compose its local homotopies with the
   factor Cone(q) -> F. This makes alpha itself locally null-homotopic.

Source for steps 1 and 2: Stacks Tags 08FP, 08FQ and 08FR. Step 3 supplies
Tag 08FR's omitted proof of assertion (2) by the same cone argument.
-/
theorem finiteFree_etale_local_actual
    (U : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (P : CochainComplex (ModuleCat.{u + 1} B) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (P.X n ≅ ModuleCat.of B (Fin r → B)))
    (F : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ) :
    (∀ φ : DerivedCategory.Q.obj
        (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ⟶ DerivedCategory.Q.obj F,
      ∃ 𝒰 : Cover.{u} etalePrecoverage U, ∀ j : 𝒰.I₀,
        ∃ α :
          (((Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
              (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ⟶
          (((Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj F),
          DerivedCategory.Q.map α =
            (Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).mapDerivedCategoryFactors.inv.app
              (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P) ≫
            (Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).mapDerivedCategory.map φ ≫
            (Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).mapDerivedCategoryFactors.hom.app F) ∧
    (∀ α :
        (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ⟶ F,
      DerivedCategory.Q.map α = 0 →
      ∃ 𝒰 : Cover.{u} etalePrecoverage U, ∀ j : 𝒰.I₀,
        Nonempty (Homotopy
          (((Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α) 0)) := by
  classical
  let E := ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
    (.up ℤ)).obj P
  constructor
  · intro φ
    obtain ⟨G, β, q, hq, hφ⟩ := DerivedCategory.left_fac φ
    have hqi : QuasiIso q := (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).1 hq
    obtain ⟨𝒰, h𝒰⟩ := finiteFree_etale_acyclic_homotopy U B P hbounded hfree
      (CochainComplex.mappingCone q) ((CochainComplex.mappingCone.quasiIso_iff_acyclic q).1 hqi)
      (β ≫ CochainComplex.mappingCone.inr q)
    refine ⟨𝒰, fun j ↦ ?_⟩
    let R := Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)
    obtain ⟨H⟩ := h𝒰 j
    obtain ⟨α, ⟨hα⟩⟩ := lift_of_local_cone_homotopy R q β H
    refine ⟨α, ?_⟩
    have hRq : IsIso (DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map q)) := by
      infer_instance
    apply (cancel_mono (DerivedCategory.Q.map
      ((R.mapHomologicalComplex (.up ℤ)).map q))).mp
    rw [← DerivedCategory.Q.map_comp, DerivedCategory.Q_map_eq_of_homotopy _ hα]
    change DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map β) =
      (R.mapDerivedCategoryFactors.inv.app E ≫ R.mapDerivedCategory.map φ ≫
        R.mapDerivedCategoryFactors.hom.app F) ≫
          DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map q)
    simp only [Category.assoc]
    erw [← R.mapDerivedCategoryFactors.hom.naturality q]
    simp only [Functor.comp_map, ← Functor.map_comp_assoc]
    have hφq : φ ≫ DerivedCategory.Q.map q = DerivedCategory.Q.map β := by
      rw [hφ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [hφq]
    erw [R.mapDerivedCategoryFactors.hom.naturality β]
    change _ = R.mapDerivedCategoryFactors.inv.app E ≫
      R.mapDerivedCategoryFactors.hom.app E ≫ _
    rw [Iso.inv_hom_id_app_assoc]
    rfl
  · intro α hα
    obtain ⟨Z, q, hq, ⟨H⟩⟩ :=
      DerivedCategory.exists_quasiIso_homotopy_zero_of_Q_map_eq_zero α hα
    let K := HomotopyCategory.quotient
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)) (.up ℤ)
    let T := CochainComplex.mappingCone.triangleh q
    have hT := HomotopyCategory.mappingCone_triangleh_distinguished q
    have hzero : T.mor₁ ≫ K.map α = 0 := by
      change K.map q ≫ K.map α = 0
      simpa only [← Functor.map_comp, Functor.map_zero] using
        HomotopyCategory.eq_of_homotopy _ _ H
    obtain ⟨b, hb⟩ := T.yoneda_exact₂ hT (K.map α) hzero
    obtain ⟨β, rfl⟩ := K.map_surjective b
    have Hα : Homotopy α (CochainComplex.mappingCone.inr q ≫ β) :=
      HomotopyCategory.homotopyOfEq _ _ (by
        change K.map α = K.map (CochainComplex.mappingCone.inr q ≫ β)
        rw [Functor.map_comp]
        exact hb)
    obtain ⟨𝒰, h𝒰⟩ := finiteFree_etale_acyclic_homotopy U B P hbounded hfree
      (CochainComplex.mappingCone q) ((CochainComplex.mappingCone.quasiIso_iff_acyclic q).1 hq)
      (CochainComplex.mappingCone.inr q)
    refine ⟨𝒰, fun j ↦ ?_⟩
    let R := Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)
    obtain ⟨h⟩ := h𝒰 j
    refine ⟨(R.mapHomotopy Hα).trans ?_⟩
    rw [Functor.map_comp]
    exact (h.compRight ((R.mapHomologicalComplex (.up ℤ)).map β)).trans
      (Homotopy.ofEq (by simp))

end AlgebraicGeometry
