/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Localization preserves a cube of exact functors

Source: Stacks Project, Tags 05S7 and 014F, universal property of localization
(blueprint: lem-fix-site-open-exchange-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

section Face

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory E] [HasDerivedCategory F]
  (R : C ⥤ D) (G : D ⥤ F) (L : C ⥤ E) (S : E ⥤ F)
  [R.Additive] [G.Additive] [L.Additive] [S.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private noncomputable def face (q : R ⋙ G ≅ L ⋙ S) :
    R.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      L.mapDerivedCategory ⋙ S.mapDerivedCategory :=
  mapDerivedCategoryCompIso R G ≪≫
    mapDerivedCategoryNatIso q ≪≫ (mapDerivedCategoryCompIso L S).symm

private lemma comp_fac (K : CochainComplex C ℤ) :
    (mapDerivedCategoryCompIso R G).inv.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((R.mapHomologicalComplex (.up ℤ)).obj K) =
      (R ⋙ G).mapDerivedCategoryFactors.hom.app K := by
  have h := mapDerivedCategoryCompIso_fac R G K
  have hi : DerivedCategory.Q.map
      ((mapHomologicalComplexCompIso (Iso.refl (R ⋙ G)) (.up ℤ)).hom.app K) = 𝟙 _ := by
    change DerivedCategory.Q.map (𝟙 _) = _
    exact DerivedCategory.Q.map_id _
  erw [hi, Category.comp_id] at h
  exact h

private lemma face_fac (q : R ⋙ G ≅ L ⋙ S) (K : CochainComplex C ℤ) :
    (face R G L S q).hom.app (DerivedCategory.Q.obj K) ≫
      S.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
      S.mapDerivedCategoryFactors.hom.app
        ((L.mapHomologicalComplex (.up ℤ)).obj K) =
      G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q.hom (.up ℤ)).app K) := by
  have hi : (mapDerivedCategoryCompIso R G).hom.app (DerivedCategory.Q.obj K) ≫
      (R ⋙ G).mapDerivedCategoryFactors.hom.app K =
      G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((R.mapHomologicalComplex (.up ℤ)).obj K) := by
    apply (cancel_epi ((mapDerivedCategoryCompIso R G).inv.app
      (DerivedCategory.Q.obj K))).mp
    rw [Iso.inv_hom_id_app_assoc]
    exact (comp_fac R G K).symm
  simp only [face, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [comp_fac, mapDerivedCategoryNatIso_fac]
  rw [← Category.assoc, hi, Category.assoc]

end Face

variable {C : Type*} {D : Type*} {E : Type*} {F : Type*}
variable {G : Type*} {H : Type*} {I : Type*} {J : Type*}
  [Category C] [Abelian C] [HasDerivedCategory C]
  [Category D] [Abelian D] [HasDerivedCategory D]
  [Category E] [Abelian E] [HasDerivedCategory E]
  [Category F] [Abelian F] [HasDerivedCategory F]
  [Category G] [Abelian G] [HasDerivedCategory G]
  [Category H] [Abelian H] [HasDerivedCategory H]
  [Category I] [Abelian I] [HasDerivedCategory I]
  [Category J] [Abelian J] [HasDerivedCategory J]
  (a : C ⥤ D)
  (b : D ⥤ E)
  (c : E ⥤ F)
  (d : C ⥤ G)
  (e : G ⥤ E)
  (f : G ⥤ H)
  (g : H ⥤ F)
  (h : C ⥤ I)
  (i : I ⥤ H)
  (j : D ⥤ J)
  (k : J ⥤ F)
  (m : I ⥤ J)
  [a.Additive] [PreservesFiniteLimits a] [PreservesFiniteColimits a]
  [b.Additive] [PreservesFiniteLimits b] [PreservesFiniteColimits b]
  [c.Additive] [PreservesFiniteLimits c] [PreservesFiniteColimits c]
  [d.Additive] [PreservesFiniteLimits d] [PreservesFiniteColimits d]
  [e.Additive] [PreservesFiniteLimits e] [PreservesFiniteColimits e]
  [f.Additive] [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [g.Additive] [PreservesFiniteLimits g] [PreservesFiniteColimits g]
  [h.Additive] [PreservesFiniteLimits h] [PreservesFiniteColimits h]
  [i.Additive] [PreservesFiniteLimits i] [PreservesFiniteColimits i]
  [j.Additive] [PreservesFiniteLimits j] [PreservesFiniteColimits j]
  [k.Additive] [PreservesFiniteLimits k] [PreservesFiniteColimits k]
  [m.Additive] [PreservesFiniteLimits m] [PreservesFiniteColimits m]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Exact-functor localization preserves an ordinary commutative cube.
Source: Stacks Project, Tags 05S7 and 014F.
(blueprint: lem-fix-site-open-exchange-localization).

Proof: Apply localization extensionality for the quasi-isomorphism localization Q.
Postcompose both sides with the three invertible factorization comparisons of h,
i and g. Use the factorization equations for each of the six derived square
comparisons and naturality to move factorization maps to the source. Both sides
become the same three source factors, followed by Q applied to the corresponding
ordinary composite on complexes. The assumed equation holds in each degree, so
extensionality of complex morphisms identifies these composites. Cancel the target
factors and conclude by localization extensionality. No boundedness, faithfulness
or preservation of injectives is assumed. -/
theorem mapDerivedCategory_exactCube
    (q1 : a ⋙ b ≅ d ⋙ e)
    (q2 : e ⋙ c ≅ f ⋙ g)
    (q3 : d ⋙ f ≅ h ⋙ i)
    (q4 : b ⋙ c ≅ j ⋙ k)
    (q5 : a ⋙ j ≅ h ⋙ m)
    (q6 : m ⋙ k ≅ i ⋙ g)
    (comm : ∀ X : C,
      c.map (q1.hom.app X) ≫ q2.hom.app (d.obj X) ≫ g.map (q3.hom.app X) =
        q4.hom.app (a.obj X) ≫ k.map (q5.hom.app X) ≫ q6.hom.app (h.obj X)) :
    let s1 := mapDerivedCategoryCompIso a b ≪≫
      mapDerivedCategoryNatIso q1 ≪≫ (mapDerivedCategoryCompIso d e).symm
    let s2 := mapDerivedCategoryCompIso e c ≪≫
      mapDerivedCategoryNatIso q2 ≪≫ (mapDerivedCategoryCompIso f g).symm
    let s3 := mapDerivedCategoryCompIso d f ≪≫
      mapDerivedCategoryNatIso q3 ≪≫ (mapDerivedCategoryCompIso h i).symm
    let s4 := mapDerivedCategoryCompIso b c ≪≫
      mapDerivedCategoryNatIso q4 ≪≫ (mapDerivedCategoryCompIso j k).symm
    let s5 := mapDerivedCategoryCompIso a j ≪≫
      mapDerivedCategoryNatIso q5 ≪≫ (mapDerivedCategoryCompIso h m).symm
    let s6 := mapDerivedCategoryCompIso m k ≪≫
      mapDerivedCategoryNatIso q6 ≪≫ (mapDerivedCategoryCompIso i g).symm
    whiskerRight s1.hom c.mapDerivedCategory ≫
        whiskerLeft d.mapDerivedCategory s2.hom ≫
        whiskerRight s3.hom g.mapDerivedCategory =
      whiskerLeft a.mapDerivedCategory s4.hom ≫
        whiskerRight s5.hom k.mapDerivedCategory ≫
        whiskerLeft h.mapDerivedCategory s6.hom := by
  let s1 := face a b d e q1
  let s2 := face e c f g q2
  let s3 := face d f h i q3
  let s4 := face b c j k q4
  let s5 := face a j h m q5
  let s6 := face m k i g q6
  change whiskerRight s1.hom c.mapDerivedCategory ≫
      whiskerLeft d.mapDerivedCategory s2.hom ≫
      whiskerRight s3.hom g.mapDerivedCategory =
    whiskerLeft a.mapDerivedCategory s4.hom ≫
      whiskerRight s5.hom k.mapDerivedCategory ≫
      whiskerLeft h.mapDerivedCategory s6.hom
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
  intro X
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  apply (cancel_mono
    (g.mapDerivedCategory.map (i.mapDerivedCategory.map
        (h.mapDerivedCategoryFactors.hom.app X)) ≫
      g.mapDerivedCategory.map (i.mapDerivedCategoryFactors.hom.app
        ((h.mapHomologicalComplex (.up ℤ)).obj X)) ≫
      g.mapDerivedCategoryFactors.hom.app
        ((i.mapHomologicalComplex (.up ℤ)).obj
          ((h.mapHomologicalComplex (.up ℤ)).obj X)))).mp
  have h1 := face_fac a b d e q1 X
  have h2 := face_fac e c f g q2 ((d.mapHomologicalComplex (.up ℤ)).obj X)
  have h3 := face_fac d f h i q3 X
  have h4 := face_fac b c j k q4 ((a.mapHomologicalComplex (.up ℤ)).obj X)
  have h5 := face_fac a j h m q5 X
  have h6 := face_fac m k i g q6 ((h.mapHomologicalComplex (.up ℤ)).obj X)
  have n2 := s2.hom.naturality (d.mapDerivedCategoryFactors.hom.app X)
  have n4 := s4.hom.naturality (a.mapDerivedCategoryFactors.hom.app X)
  have n6 := s6.hom.naturality (h.mapDerivedCategoryFactors.hom.app X)
  dsimp only [Functor.comp_map] at n2 n4 n6
  have nl : c.mapDerivedCategory.map (s1.hom.app (DerivedCategory.Q.obj X)) ≫
      s2.hom.app (d.mapDerivedCategory.obj (DerivedCategory.Q.obj X)) ≫
      g.mapDerivedCategory.map (s3.hom.app (DerivedCategory.Q.obj X)) ≫
      g.mapDerivedCategory.map (i.mapDerivedCategory.map
        (h.mapDerivedCategoryFactors.hom.app X)) ≫
      g.mapDerivedCategory.map (i.mapDerivedCategoryFactors.hom.app
        ((h.mapHomologicalComplex (.up ℤ)).obj X)) ≫
      g.mapDerivedCategoryFactors.hom.app
        ((i.mapHomologicalComplex (.up ℤ)).obj
          ((h.mapHomologicalComplex (.up ℤ)).obj X)) =
      c.mapDerivedCategory.map (b.mapDerivedCategory.map
        (a.mapDerivedCategoryFactors.hom.app X)) ≫
      c.mapDerivedCategory.map (b.mapDerivedCategoryFactors.hom.app
        ((a.mapHomologicalComplex (.up ℤ)).obj X)) ≫
      c.mapDerivedCategoryFactors.hom.app
        ((b.mapHomologicalComplex (.up ℤ)).obj
          ((a.mapHomologicalComplex (.up ℤ)).obj X)) ≫
      DerivedCategory.Q.map
        ((c.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex q1.hom (.up ℤ)).app X) ≫
          (NatTrans.mapHomologicalComplex q2.hom (.up ℤ)).app
            ((d.mapHomologicalComplex (.up ℤ)).obj X) ≫
          (g.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex q3.hom (.up ℤ)).app X)) := by
    erw [← g.mapDerivedCategory.map_comp_assoc, ← g.mapDerivedCategory.map_comp_assoc]
    simp only [Category.assoc]
    erw [h3]
    simp only [Functor.map_comp, Category.assoc]
    erw [g.mapDerivedCategoryFactors_hom_naturality]
    erw [← reassoc_of% n2, reassoc_of% h2]
    erw [← c.mapDerivedCategory.map_comp_assoc, ← c.mapDerivedCategory.map_comp_assoc]
    simp only [Category.assoc]
    erw [h1]
    simp only [Functor.map_comp, Category.assoc]
    erw [c.mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [Category.assoc]
  erw [nl]
  erw [← reassoc_of% n6]
  erw [h6]
  erw [← k.mapDerivedCategory.map_comp_assoc, ← k.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  erw [h5]
  simp only [Functor.map_comp, Category.assoc]
  erw [k.mapDerivedCategoryFactors_hom_naturality_assoc]
  erw [← reassoc_of% n4, reassoc_of% h4]
  simp only [← Functor.map_comp]
  repeat' apply congrArg (fun t ↦ _ ≫ t)
  apply congrArg DerivedCategory.Q.map
  ext n
  exact comm (X.X n)

end CategoryTheory.Functor
