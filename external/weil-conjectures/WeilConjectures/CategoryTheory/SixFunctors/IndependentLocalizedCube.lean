/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Localization cubes with specified representative comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
universe q
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory.{q} C]
  {D : Type*} [Category D] [Abelian D] [HasDerivedCategory.{q} D]
  {E : Type*} [Category E] [Abelian E] [HasDerivedCategory.{q} E]
  {F : Type*} [Category F] [Abelian F] [HasDerivedCategory.{q} F]
  {G : Type*} [Category G] [Abelian G] [HasDerivedCategory.{q} G]
  {H : Type*} [Category H] [Abelian H] [HasDerivedCategory.{q} H]
  {I : Type*} [Category I] [Abelian I] [HasDerivedCategory.{q} I]
  {J : Type*} [Category J] [Abelian J] [HasDerivedCategory.{q} J]
  (a : C ⥤ D) [a.Additive]
  (b : D ⥤ E) [b.Additive]
  (c : E ⥤ F) [c.Additive]
  (d : C ⥤ G) [d.Additive]
  (e : G ⥤ E) [e.Additive]
  (f : G ⥤ H) [f.Additive]
  (g : H ⥤ F) [g.Additive]
  (h : C ⥤ I) [h.Additive]
  (i : I ⥤ H) [i.Additive]
  (j : D ⥤ J) [j.Additive]
  (k : J ⥤ F) [k.Additive]
  (m : I ⥤ J) [m.Additive]
  (aD : DerivedCategory C ⥤ DerivedCategory D)
  (bD : DerivedCategory D ⥤ DerivedCategory E)
  (cD : DerivedCategory E ⥤ DerivedCategory F)
  (dD : DerivedCategory C ⥤ DerivedCategory G)
  (eD : DerivedCategory G ⥤ DerivedCategory E)
  (fD : DerivedCategory G ⥤ DerivedCategory H)
  (gD : DerivedCategory H ⥤ DerivedCategory F)
  (hD : DerivedCategory C ⥤ DerivedCategory I)
  (iD : DerivedCategory I ⥤ DerivedCategory H)
  (jD : DerivedCategory D ⥤ DerivedCategory J)
  (kD : DerivedCategory J ⥤ DerivedCategory F)
  (mD : DerivedCategory I ⥤ DerivedCategory J)
  (φa : DerivedCategory.Q ⋙ aD ≅ a.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φb : DerivedCategory.Q ⋙ bD ≅ b.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φc : DerivedCategory.Q ⋙ cD ≅ c.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φd : DerivedCategory.Q ⋙ dD ≅ d.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φe : DerivedCategory.Q ⋙ eD ≅ e.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φf : DerivedCategory.Q ⋙ fD ≅ f.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φg : DerivedCategory.Q ⋙ gD ≅ g.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φh : DerivedCategory.Q ⋙ hD ≅ h.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φi : DerivedCategory.Q ⋙ iD ≅ i.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φj : DerivedCategory.Q ⋙ jD ≅ j.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φk : DerivedCategory.Q ⋙ kD ≅ k.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φm : DerivedCategory.Q ⋙ mD ≅ m.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)

/-- Localization preserves a cube with all six faces fixed on complex representatives.
Source: Stacks 05S7 and 014F; Zheng Construction 4.1
(blueprint: lem-sf-independent-localized-exact-cube).

Proof: precompose with Q, a fully faithful operation on functor categories. Cancel
three terminal factorization isomorphisms. Substitute the six representative
identities, using naturality to move the factors to the beginning of each path.
Both paths are the same initial factors followed by Q of the ordinary cube.
Equality holds degree by degree by the ordinary cube equation. -/
theorem localized_exactCube
    (q1 : a ⋙ b ≅ d ⋙ e)
    (q2 : e ⋙ c ≅ f ⋙ g)
    (q3 : d ⋙ f ≅ h ⋙ i)
    (q4 : b ⋙ c ≅ j ⋙ k)
    (q5 : a ⋙ j ≅ h ⋙ m)
    (q6 : m ⋙ k ≅ i ⋙ g)
    (s1 : aD ⋙ bD ≅ dD ⋙ eD)
    (s2 : eD ⋙ cD ≅ fD ⋙ gD)
    (s3 : dD ⋙ fD ≅ hD ⋙ iD)
    (s4 : bD ⋙ cD ≅ jD ⋙ kD)
    (s5 : aD ⋙ jD ≅ hD ⋙ mD)
    (s6 : mD ⋙ kD ≅ iD ⋙ gD)
    (r1 : ∀ X, s1.hom.app (DerivedCategory.Q.obj X) ≫
      eD.map (φd.hom.app X) ≫
      φe.hom.app ((d.mapHomologicalComplex (.up ℤ)).obj X) =
      bD.map (φa.hom.app X) ≫
      φb.hom.app ((a.mapHomologicalComplex (.up ℤ)).obj X) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q1.hom (.up ℤ)).app X))
    (r2 : ∀ X, s2.hom.app (DerivedCategory.Q.obj X) ≫
      gD.map (φf.hom.app X) ≫
      φg.hom.app ((f.mapHomologicalComplex (.up ℤ)).obj X) =
      cD.map (φe.hom.app X) ≫
      φc.hom.app ((e.mapHomologicalComplex (.up ℤ)).obj X) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q2.hom (.up ℤ)).app X))
    (r3 : ∀ X, s3.hom.app (DerivedCategory.Q.obj X) ≫
      iD.map (φh.hom.app X) ≫
      φi.hom.app ((h.mapHomologicalComplex (.up ℤ)).obj X) =
      fD.map (φd.hom.app X) ≫
      φf.hom.app ((d.mapHomologicalComplex (.up ℤ)).obj X) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q3.hom (.up ℤ)).app X))
    (r4 : ∀ X, s4.hom.app (DerivedCategory.Q.obj X) ≫
      kD.map (φj.hom.app X) ≫
      φk.hom.app ((j.mapHomologicalComplex (.up ℤ)).obj X) =
      cD.map (φb.hom.app X) ≫
      φc.hom.app ((b.mapHomologicalComplex (.up ℤ)).obj X) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q4.hom (.up ℤ)).app X))
    (r5 : ∀ X, s5.hom.app (DerivedCategory.Q.obj X) ≫
      mD.map (φh.hom.app X) ≫
      φm.hom.app ((h.mapHomologicalComplex (.up ℤ)).obj X) =
      jD.map (φa.hom.app X) ≫
      φj.hom.app ((a.mapHomologicalComplex (.up ℤ)).obj X) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q5.hom (.up ℤ)).app X))
    (r6 : ∀ X, s6.hom.app (DerivedCategory.Q.obj X) ≫
      gD.map (φi.hom.app X) ≫
      φg.hom.app ((i.mapHomologicalComplex (.up ℤ)).obj X) =
      kD.map (φm.hom.app X) ≫
      φk.hom.app ((m.mapHomologicalComplex (.up ℤ)).obj X) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q6.hom (.up ℤ)).app X))
    (comm : ∀ X : C,
      c.map (q1.hom.app X) ≫ q2.hom.app (d.obj X) ≫ g.map (q3.hom.app X) =
        q4.hom.app (a.obj X) ≫ k.map (q5.hom.app X) ≫ q6.hom.app (h.obj X)) :
    whiskerRight s1.hom cD ≫ whiskerLeft dD s2.hom ≫ whiskerRight s3.hom gD =
      whiskerLeft aD s4.hom ≫ whiskerRight s5.hom kD ≫ whiskerLeft hD s6.hom := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
  intro X
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  apply (cancel_mono
    (gD.map (iD.map
        (φh.hom.app X)) ≫
      gD.map (φi.hom.app
        ((h.mapHomologicalComplex (.up ℤ)).obj X)) ≫
      φg.hom.app
        ((i.mapHomologicalComplex (.up ℤ)).obj
          ((h.mapHomologicalComplex (.up ℤ)).obj X)))).mp
  have h1 := r1 X
  have h2 := r2 ((d.mapHomologicalComplex (.up ℤ)).obj X)
  have h3 := r3 X
  have h4 := r4 ((a.mapHomologicalComplex (.up ℤ)).obj X)
  have h5 := r5 X
  have h6 := r6 ((h.mapHomologicalComplex (.up ℤ)).obj X)
  have n2 := s2.hom.naturality (φd.hom.app X)
  have n4 := s4.hom.naturality (φa.hom.app X)
  have n6 := s6.hom.naturality (φh.hom.app X)
  dsimp only [Functor.comp_map] at n2 n4 n6
  have nl : cD.map (s1.hom.app (DerivedCategory.Q.obj X)) ≫
      s2.hom.app (dD.obj (DerivedCategory.Q.obj X)) ≫
      gD.map (s3.hom.app (DerivedCategory.Q.obj X)) ≫
      gD.map (iD.map
        (φh.hom.app X)) ≫
      gD.map (φi.hom.app
        ((h.mapHomologicalComplex (.up ℤ)).obj X)) ≫
      φg.hom.app
        ((i.mapHomologicalComplex (.up ℤ)).obj
          ((h.mapHomologicalComplex (.up ℤ)).obj X)) =
      cD.map (bD.map
        (φa.hom.app X)) ≫
      cD.map (φb.hom.app
        ((a.mapHomologicalComplex (.up ℤ)).obj X)) ≫
      φc.hom.app
        ((b.mapHomologicalComplex (.up ℤ)).obj
          ((a.mapHomologicalComplex (.up ℤ)).obj X)) ≫
      DerivedCategory.Q.map
        ((c.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex q1.hom (.up ℤ)).app X) ≫
          (NatTrans.mapHomologicalComplex q2.hom (.up ℤ)).app
            ((d.mapHomologicalComplex (.up ℤ)).obj X) ≫
          (g.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex q3.hom (.up ℤ)).app X)) := by
    erw [← gD.map_comp_assoc, ← gD.map_comp_assoc]
    simp only [Category.assoc]
    erw [h3]
    simp only [Functor.map_comp, Category.assoc]
    erw [φg.hom.naturality]
    erw [← reassoc_of% n2, reassoc_of% h2]
    erw [← cD.map_comp_assoc, ← cD.map_comp_assoc]
    simp only [Category.assoc]
    erw [h1]
    simp only [Functor.map_comp, Category.assoc]
    erw [NatTrans.naturality_assoc φc.hom]
    simp only [Functor.comp_map]
  simp only [Category.assoc]
  erw [nl]
  erw [← reassoc_of% n6]
  erw [h6]
  erw [← kD.map_comp_assoc, ← kD.map_comp_assoc]
  simp only [Category.assoc]
  erw [h5]
  simp only [Functor.map_comp, Category.assoc]
  erw [NatTrans.naturality_assoc φk.hom]
  erw [← reassoc_of% n4, reassoc_of% h4]
  simp only [Functor.comp_map, ← Functor.map_comp]
  repeat' apply congrArg (fun t ↦ _ ≫ t)
  apply congrArg DerivedCategory.Q.map
  ext n
  exact comm (X.X n)

end CategoryTheory.Functor
