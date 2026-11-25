/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import WeilConjectures.Compactification.CategoryBaseChange
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenIdentificationNormalization
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparisonIso
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparisonComposition

/-!
# Compact-support base change with finite coefficients and arbitrary refinements

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/thm-cbc-finite-torsion;
Stacks Project, Tags 0DDE, 0F7I, 0F7J and 0F7F (blueprint:
proposition-composition-base-change-rf-shriek).

The exchange map, its invertibility, identity and horizontal pasting, and its canonical
compactification-independent version and vertical pasting already exist upstream. The theorem
below also identifies the comparisons specified by the node with the canonical comparisons
for every proper refinement, including refinements whose square over the open is not Cartesian.
Together with the recorded upstream declarations, this states all clauses of the node.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The comparison `C_r = Rp₂*(α_r)`, followed by direct-image composition, for any
proper refinement fixing the open. The map `α_r` is exactly `properOpenComparison`, not an
exchange requiring a Cartesian refinement square.
Source: blueprint proposition-composition-base-change-rf-shriek, proof steps 4 and 5; Stacks
Project, Tag 0F7I (blueprint: proposition-composition-base-change-rf-shriek). -/
noncomputable def compactSupportProperOpenRefinementMap
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) d).obj K ⟶
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K :=
  letI : (lowerStar (ModuleCat.{u + 1} Λ) r.hom).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r.hom)
  (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) d.g).map
      (properOpenComparison Λ r.hom c.i d.i r.i_hom K) ≫
    (Functor.rightDerivedFunctorPlusCompIso'
      (lowerStar (ModuleCat.{u + 1} Λ) r.hom) (lowerStar (ModuleCat.{u + 1} Λ) d.g)
      (lowerStarComp (ModuleCat.{u + 1} Λ) r.hom d.g c.g r.hom_g.symm)).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus.obj K)

-- Retain the chosen-resolution interfaces while elaborating the private proofs.
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryPlus
  lowerStar upperStar
  properOpenComparison properOpenIdentification
  CategoryTheory.Functor.rightDerivedFunctorPlusCompIso' properOpenDirectImageCompIso

private theorem comparison_of_restriction
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L₀ : C ⥤ D} {R₀ : D ⥤ C} {L₁ : C ⥤ E} {R₁ : E ⥤ C}
    {A : E ⥤ D} {B : D ⥤ E}
    (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁) (adj : A ⊣ B)
    (comp : R₁ ≅ A ⋙ R₀) (β : L₀ ≅ L₁ ⋙ A) (K : C)
    [Mono (adj₀.unit.app K)]
    (hβ : adj₀.unit.app K ≫ R₀.map (β.hom.app K) =
      adj₁.unit.app K ≫ comp.hom.app (L₁.obj K))
    (θ : R₁.obj (B.obj (L₀.obj K)) ≅ K)
    (hθ : θ.hom ≫ adj₀.unit.app K =
      comp.hom.app (B.obj (L₀.obj K)) ≫ R₀.map (adj.counit.app (L₀.obj K))) :
    L₁.map θ.inv ≫ adj₁.counit.app (B.obj (L₀.obj K)) =
      adj.unit.app (L₁.obj K) ≫ B.map (β.inv.app K) := by
  apply (adj₁.homEquiv _ _).injective
  change (adj₁.homEquiv _ _) ((adj₁.homEquiv _ _).symm θ.inv) = _
  rw [Equiv.apply_symm_apply]
  apply (cancel_mono θ.hom).mp
  rw [Iso.inv_hom_id]
  apply (cancel_mono (adj₀.unit.app K)).mp
  rw [Category.id_comp]
  simp only [Adjunction.homEquiv_unit, Category.assoc]
  rw [hθ]
  rw [reassoc_of% (comp.hom.naturality
    (adj.unit.app (L₁.obj K) ≫ B.map (β.inv.app K)))]
  rw [← Category.assoc, ← hβ]
  simp only [Category.assoc, ← Functor.map_comp]
  have h : A.map (adj.unit.app (L₁.obj K) ≫ B.map (β.inv.app K)) ≫
      adj.counit.app (L₀.obj K) = β.inv.app K := by
    exact (adj.homEquiv _ _).symm_apply_apply (β.inv.app K)
  rw [h, Iso.hom_inv_id_app]
  simp

private theorem properOpenComparison_cartesian
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    properOpenComparison Λ r.hom c.i d.i r.i_hom K =
      (refinementOpenImmersionLowerShriekComparison (ModuleCat.{u + 1} Λ) r hr).app K := by
  have h := comparison_of_restriction
    (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus (ModuleCat.{u + 1} Λ) c.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus (ModuleCat.{u + 1} Λ) d.i)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r.hom).derivedPlus
    (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) c.i r.hom d.i r.i_hom.symm)
    (refinementLowerShriekBaseChangeDerivedPlusIso (ModuleCat.{u + 1} Λ) r hr) K
    (unit_map_refinementLowerShriekBaseChangeDerivedPlusIso_hom_app
      (ModuleCat.{u + 1} Λ) r hr K)
    (properOpenIdentification Λ r.hom c.i d.i r.i_hom K)
    (properOpenIdentification_unit Λ r.hom c.i d.i r.i_hom K)
  simpa only [properOpenComparison, refinementOpenImmersionLowerShriekComparison,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    rightDerivedLowerStarPlus, Functor.id_obj] using h

private theorem compose_maps
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (R : A ⥤ B) (S : B ⥤ C) (T : C ⥤ D)
    (RS : A ⥤ C) (ST : B ⥤ D) (RST : A ⥤ D)
    (α : R ⋙ S ≅ RS) (β : S ⋙ T ≅ ST)
    (γ : RS ⋙ T ≅ RST) (δ : R ⋙ ST ≅ RST)
    {M : A} {N : B} {P : C}
    (a : N ⟶ R.obj M) (b : P ⟶ S.obj N) (ab : P ⟶ RS.obj M)
    (hc : T.map (α.hom.app M) ≫ γ.hom.app M = β.hom.app (R.obj M) ≫ δ.hom.app M)
    (hab : ab = b ≫ S.map a ≫ α.hom.app M) :
    T.map ab ≫ γ.hom.app M =
      (T.map b ≫ β.hom.app N) ≫ ST.map a ≫ δ.hom.app M := by
  have hn := β.hom.naturality a
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [hab]
  simp only [Functor.map_comp, Category.assoc]
  rw [hc, reassoc_of% hn]

private noncomputable def pushforwardCompIso
    (Λ : Type (u + 1)) [CommRing Λ] {U V W : Scheme.{u}}
    (a : U ⟶ V) (b : V ⟶ W) (ab : U ⟶ W) (h : a ≫ b = ab) :
    rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) a ⋙
        rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) b ≅
      rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) ab := by
  letI : (lowerStar (ModuleCat.{u + 1} Λ) a).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a)
  exact Functor.rightDerivedFunctorPlusCompIso'
    (lowerStar (ModuleCat.{u + 1} Λ) a) (lowerStar (ModuleCat.{u + 1} Λ) b)
    (lowerStarComp (ModuleCat.{u + 1} Λ) a b ab h.symm)

private theorem compactSupportProperOpenRefinementMap_eq
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    compactSupportProperOpenRefinementMap Λ r K =
      (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) d.g).map
        (properOpenComparison Λ r.hom c.i d.i r.i_hom K) ≫
      (pushforwardCompIso Λ r.hom d.g c.g r.hom_g).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus.obj K) := by
  rfl

private theorem refinement_compositors
    (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d e : Compactification f}
    (r : c.Refinement d) (s : d.Refinement e)
    (M : DerivedCategory.Plus (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) e.g).map
        ((pushforwardCompIso Λ r.hom s.hom (r.comp s).hom rfl).hom.app M) ≫
      (pushforwardCompIso Λ (r.comp s).hom e.g c.g (r.comp s).hom_g).hom.app M =
      (pushforwardCompIso Λ s.hom e.g d.g s.hom_g).hom.app
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r.hom).obj M) ≫
      (pushforwardCompIso Λ r.hom d.g c.g r.hom_g).hom.app M := by
  have h := NatTrans.congr_app (rightDerivedFunctorPlusCompIso'_lowerStarComp_assoc
    (ModuleCat.{u + 1} Λ) r.hom s.hom e.g (r.comp s).hom d.g c.g
    rfl s.hom_g.symm (r.comp s).hom_g.symm) M
  simpa only [pushforwardCompIso, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, rightDerivedLowerStarPlus] using h

private theorem refinement_alpha_comp
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d e : Compactification f}
    (r : c.Refinement d) (s : d.Refinement e)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    properOpenComparison Λ (r.comp s).hom c.i e.i (r.comp s).i_hom K =
      properOpenComparison Λ s.hom d.i e.i s.i_hom K ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) s.hom).map
          (properOpenComparison Λ r.hom c.i d.i r.i_hom K) ≫
        (pushforwardCompIso Λ r.hom s.hom (r.comp s).hom rfl).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus.obj K) := by
  simpa only [pushforwardCompIso, properOpenDirectImageCompIso,
    Compactification.Refinement.comp] using
    properOpenComparison_comp Λ r.hom s.hom c.i d.i e.i r.i_hom s.i_hom K

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem compactSupportProperOpenRefinementMap_comp
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d e : Compactification f}
    (r : c.Refinement d) (s : d.Refinement e)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    compactSupportProperOpenRefinementMap Λ (r.comp s) K =
      compactSupportProperOpenRefinementMap Λ s K ≫
        compactSupportProperOpenRefinementMap Λ r K := by
  rw [compactSupportProperOpenRefinementMap_eq Λ (r.comp s),
    compactSupportProperOpenRefinementMap_eq Λ s, compactSupportProperOpenRefinementMap_eq Λ r]
  refine compose_maps
    (M := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus.obj K)
    (N := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) d.i).mapDerivedCategoryPlus.obj K)
    (P := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) e.i).mapDerivedCategoryPlus.obj K)
    (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r.hom)
    (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) s.hom)
    (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) e.g)
    (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) (r.comp s).hom)
    (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) d.g)
    (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) c.g)
    (pushforwardCompIso Λ r.hom s.hom (r.comp s).hom rfl)
    (pushforwardCompIso Λ s.hom e.g d.g s.hom_g)
    (pushforwardCompIso Λ (r.comp s).hom e.g c.g (r.comp s).hom_g)
    (pushforwardCompIso Λ r.hom d.g c.g r.hom_g)
    (properOpenComparison Λ r.hom c.i d.i r.i_hom K)
    (properOpenComparison Λ s.hom d.i e.i s.i_hom K)
    (properOpenComparison Λ (r.comp s).hom c.i e.i (r.comp s).i_hom K)
    (refinement_compositors Λ r s
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus.obj K)) ?_
  exact refinement_alpha_comp Λ r s K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem compactSupportProperOpenRefinementMap_cartesian
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    compactSupportProperOpenRefinementMap Λ r K =
      ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).refinementComparison r hr).app K := by
  unfold compactSupportProperOpenRefinementMap
  rw [derivedPlusFormalism_refinementComparison,
    rightDerivedLowerShriekOfCompactificationPlusComparison_eq]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    properOpenComparison_cartesian Λ r hr K]
  rw [refinementLowerStarComp_eq]
  rfl

/-- Compact-support exchange is invertible at every bounded-below complex, and the
specified proper/open refinement maps are the canonical comparison isomorphisms, for all
refinements without a Cartesian or density hypothesis.
Source: blueprint proposition-composition-base-change-rf-shriek; Stacks Project, Tags 0DDE and 0F7I
(blueprint: proposition-composition-base-change-rf-shriek).

Proof:
1. The existing proper-base-change instance makes the compactification exchange invertible.
2. For a Cartesian refinement, transpose both comparisons under the open-extension
   adjunction. The unit formula for open base change and the normalization of
   `properOpenIdentification` identify the transposes. Cancel the restriction isomorphism
   and the open-extension unit, and apply the adjunction triangle identity.
3. Proper/open comparison composition, direct-image compositor naturality and
   direct-image associativity give the reverse composition equation for refinement maps.
4. Put `w = infFst c c`. Both `w` and `w.comp r` are Cartesian over the open. Invertibility
   of the proper/open comparison makes the map for `w` invertible. The composition equation
   writes the map for `r` as the map for `w.comp r` followed by the inverse map for `w`.
5. Replace those two maps by the formalism refinement comparisons. Their ratio is exactly
   `shriekIso d c` by its common-refinement formula. The other clauses of the mixed DAG node
   remain supplied by the existing upstream declarations recorded in its Lean attachment. -/
theorem compactSupportFiniteTorsion
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    (∀ K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso ((rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c).app K)) ∧
    (∀ (d : Compactification f) (r : c.Refinement d)
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      compactSupportProperOpenRefinementMap Λ r K =
        ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekIso d c).hom.app K) := by
  constructor
  · intro K
    infer_instance
  · intro d r K
    let w := Compactification.infFst c c
    have hw := Compactification.isPullback_infFst c c
    have hwr := Compactification.Refinement.isPullback_of_inf (w.comp r)
    have := isIso_properOpenComparison Λ w.hom (Compactification.inf c c).i c.i
      w.i_hom K
    have : IsIso (compactSupportProperOpenRefinementMap Λ w K) := by
      unfold compactSupportProperOpenRefinementMap
      infer_instance
    calc
      compactSupportProperOpenRefinementMap Λ r K =
          compactSupportProperOpenRefinementMap Λ (w.comp r) K ≫
            inv (compactSupportProperOpenRefinementMap Λ w K) := by
        rw [compactSupportProperOpenRefinementMap_comp]
        simp
      _ = ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekIso d c).hom.app K := by
        rw [(derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekIso_eq (w.comp r) w hwr hw]
        simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, asIso_hom, asIso_inv]
        simp only [compactSupportProperOpenRefinementMap_cartesian Λ (w.comp r) hwr,
          compactSupportProperOpenRefinementMap_cartesian Λ w hw]
        have : IsIso ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).refinementComparison
            w hw) := CompactSupportFormalism.isIso_refinementComparison _ _ _
        simp only [NatIso.isIso_inv_app]

end AlgebraicGeometry.Etale
