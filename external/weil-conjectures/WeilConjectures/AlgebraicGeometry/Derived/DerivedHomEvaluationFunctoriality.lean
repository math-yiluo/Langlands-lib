/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison

/-! # Functoriality of local derived morphism evaluation

Source: Stacks Tags 09B1, 0946, 09BE and 0F63. Transpose the local comparison
identities under the two adjunctions, then cancel the bijective sheafification unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
  (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
private theorem homEvaluation_unit
    (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B A D)).obj.obj (op U)) :
    proEtaleDerivedHomUnit X B A D U (derivedHomEvaluation X B A D U hU s) =
      (derivedHomSheafComparison X B A D).hom.app (op U) s := by
  exact (Equiv.ofBijective (proEtaleDerivedHomUnit X B A D U)
    (proEtaleDerivedUnits_bijective X B A D U hU).1).apply_symm_apply _

private theorem isoEvaluation_unit
    (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.obj (op U)) :
    proEtaleDerivedIsoUnit X B A D U (derivedIsoEvaluation X B A D U hU s) =
      (derivedIsoSheafComparison X B A D).hom.app (op U) s := by
  exact (Equiv.ofBijective (proEtaleDerivedIsoUnit X B A D U)
    (proEtaleDerivedUnits_bijective X B A D U hU).2).apply_symm_apply _

private theorem comparisonLocalHom_natural
    (A' D' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (f : A' ⟶ A) (g : D ⟶ D') (V : X.Etale)
    (a : (derivedSliceRestriction X.smallEtaleTopology B V).obj A ⟶
      (derivedSliceRestriction X.smallEtaleTopology B V).obj D) :
    derivedComparisonLocalHom X B A' D' V
      ((derivedSliceRestriction X.smallEtaleTopology B V).map f ≫ a ≫
        (derivedSliceRestriction X.smallEtaleTopology B V).map g) =
      (derivedSliceRestriction (ProEt.topology X) B ((toProEt X).obj V)).map
        ((derivedComparison X B).map f) ≫ derivedComparisonLocalHom X B A D V a ≫
      (derivedSliceRestriction (ProEt.topology X) B ((toProEt X).obj V)).map
        ((derivedComparison X B).map g) := by
  simp only [derivedComparisonLocalHom, Functor.map_comp, Category.assoc]
  have hf := (derivedComparisonSliceIso X B V).inv.naturality f
  have hg := (derivedComparisonSliceIso X B V).hom.naturality g
  dsimp only [Functor.comp_map] at hf hg
  rw [← Category.assoc, ← Category.assoc, ← hf]
  simp only [Category.assoc]
  rw [hg]

private theorem comparisonHom_natural
    (A' D' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (f : A' ⟶ A) (g : D ⟶ D') :
    (comparisonSetUpperStar X).map (derivedLocalHomSheafMap f g) ≫
        derivedHomSheafComparison X B A' D' =
      derivedHomSheafComparison X B A D ≫
        derivedLocalHomSheafMap ((derivedComparison X B).map f)
          ((derivedComparison X B).map g) := by
  let θ := derivedLocalHomSheafMap ((derivedComparison X B).map f)
    ((derivedComparison X B).map g)
  let R := (toProEt X).sheafPushforwardContinuous (Type (u + 1))
    X.smallEtaleTopology (ProEt.topology X)
  have hp : derivedLocalHomPresheafMap f g ≫ derivedComparisonHomPresheafMap X B A' D' =
      derivedComparisonHomPresheafMap X B A D ≫ (R.map θ).hom := by
    ext V a
    change derivedComparisonHomUnit X B A' D' V.unop
      ((derivedSliceRestriction X.smallEtaleTopology B V.unop).map f ≫ a ≫
        (derivedSliceRestriction X.smallEtaleTopology B V.unop).map g) =
      θ.hom.app (op ((toProEt X).obj V.unop)) (derivedComparisonHomUnit X B A D V.unop a)
    have hn := (sheafificationAdjunction (ProEt.topology X) (Type (u + 1))).unit.naturality
      (derivedLocalHomPresheafMap ((derivedComparison X B).map f)
        ((derivedComparison X B).map g))
    have hn' := congrArg (fun k ↦ k.app (op ((toProEt X).obj V.unop))
      (derivedComparisonLocalHom X B A D V.unop a)) hn
    exact (congrArg
      ((toSheafify (ProEt.topology X)
        (derivedLocalHomPresheaf (ProEt.topology X) B
          ((derivedComparison X B).obj A') ((derivedComparison X B).obj D'))).app
            (op ((toProEt X).obj V.unop)))
      (comparisonLocalHom_natural X B A D A' D' f g V.unop a)).trans hn'
  have hs := Adjunction.homEquiv_naturality_right_square
    (sheafificationAdjunction X.smallEtaleTopology (Type (u + 1)))
    (Y := R.obj (derivedComparisonHomTarget X B A D))
    (Y' := R.obj (derivedComparisonHomTarget X B A' D'))
    (derivedLocalHomPresheafMap f g)
      (derivedComparisonHomPresheafMap X B A' D')
      (derivedComparisonHomPresheafMap X B A D) (R.map θ) hp
  exact (proEtaleSiteComparison X).homEquiv_naturality_right_square
    (Y := derivedComparisonHomTarget X B A D)
    (Y' := derivedComparisonHomTarget X B A' D')
    (derivedLocalHomSheafMap f g) _ _ θ hs

/-- Evaluation is natural in both derived arguments, contravariantly in the first and covariantly in
the second.

Source: Stacks Project, Pro-etale Cohomology, Tags 09B1 and 0F63; Cohomology on Sites, Tags 0946
and 09BE; the blueprint amplification proof, finite-source extension.

Proof: Apply naturality of the comparison slice isomorphisms to f and g. Local derived pullback
then intertwines precomposition and postcomposition. Sheafification and adjunction transposition
preserve this equality of presheaf maps. Finally invert the pro-etale sheafification unit, whose
naturality in both objects follows from its definition, to get the stated conjugation-free
formula.
(blueprint: lem-weil-pbc-derived-hom-evaluation-naturality)
-/
theorem derivedHomEvaluation_natural
    (A' D' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (f : A' ⟶ A) (g : D ⟶ D') (U : X.ProEt) [IsAffine U.left]
    (hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology B A D)).obj.obj (op U)) :
    derivedHomEvaluation X B A' D' U hU
        (((comparisonSetUpperStar X).map
          ((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).map
            (derivedLocalHomPresheafMap f g))).hom.app (op U) s) =
      (derivedSliceRestriction (ProEt.topology X) B U).map
          ((derivedComparison X B).map f) ≫
        derivedHomEvaluation X B A D U hU s ≫
          (derivedSliceRestriction (ProEt.topology X) B U).map
            ((derivedComparison X B).map g) := by
  apply (proEtaleDerivedUnits_bijective X B A' D' U hU).1.1
  have hc := congrArg (fun k ↦ k.hom.app (op U) s)
    (comparisonHom_natural X B A D A' D' f g)
  have hn := (sheafificationAdjunction (ProEt.topology X) (Type (u + 1))).unit.naturality
    (derivedLocalHomPresheafMap ((derivedComparison X B).map f)
      ((derivedComparison X B).map g))
  have hn' := congrArg (fun k ↦ k.app (op U) (derivedHomEvaluation X B A D U hU s)) hn
  exact (homEvaluation_unit X B A' D' U hU _).trans
    (hc.trans ((congrArg
      ((derivedLocalHomSheafMap ((derivedComparison X B).map f)
        ((derivedComparison X B).map g)).hom.app (op U))
      (homEvaluation_unit X B A D U hU s).symm).trans hn'.symm))

private noncomputable abbrev originFunctor (X : Scheme.{u}) :=
  presheafToSheaf X.smallEtaleTopology (Type (u + 1)) ⋙ comparisonSetUpperStar X

private noncomputable abbrev originAdjunction (X : Scheme.{u}) :=
  (sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).comp
    (proEtaleSiteComparison X)

private theorem hom_transpose (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    ((originAdjunction X).homEquiv _ _) (derivedHomSheafComparison X B A D) =
      derivedComparisonHomPresheafMap X B A D := by
  change ((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv _ _)
    (((proEtaleSiteComparison X).homEquiv _ _) (derivedHomSheafComparison X B A D)) = _
  rw [derivedHomSheafComparison, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private theorem iso_transpose (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    ((originAdjunction X).homEquiv _ _) (derivedIsoSheafComparison X B A D) =
      derivedComparisonIsoPresheafMap X B A D := by
  change ((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv _ _)
    (((proEtaleSiteComparison X).homEquiv _ _) (derivedIsoSheafComparison X B A D)) = _
  rw [derivedIsoSheafComparison, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private theorem iso_hom (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    derivedIsoSheafComparison X B A D ≫
        (presheafToSheaf (ProEt.topology X) (Type (u + 1))).map
          (derivedLocalIsoToHomPresheaf (J := ProEt.topology X) (B := B)
            (A := (derivedComparison X B).obj A) (D := (derivedComparison X B).obj D)) =
      (originFunctor X).map
        (derivedLocalIsoToHomPresheaf (J := X.smallEtaleTopology) (B := B)
          (A := A) (D := D)) ≫ derivedHomSheafComparison X B A D := by
  apply ((originAdjunction X).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    iso_transpose, hom_transpose]
  ext V f
  have hn := toSheafify_naturality (ProEt.topology X)
    (derivedLocalIsoToHomPresheaf (J := ProEt.topology X) (B := B)
      (A := (derivedComparison X B).obj A) (D := (derivedComparison X B).obj D))
  exact (ConcreteCategory.congr_hom (congr_app hn (op ((toProEt X).obj V.unop)))
    (derivedComparisonLocalIso X B A D V.unop f)).symm

/-- Evaluation sends the Isom-to-Hom projection to the underlying evaluated arrow.
Source: Stacks Tags 09BV and 0F63.
(blueprint: lem-weil-pbc-derived-isomorphism-evaluation-hom).

Proof: Transpose the local comparison identity for the Isom-to-Hom projection under
sheafification and comparison adjunctions. Evaluate that identity and use naturality
of the pro-etale sheafification unit. Its bijectivity identifies the two arrows. -/
theorem derivedIsoEvaluation_hom
    (U : X.ProEt) [IsAffine U.left]
    (hw : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.obj (op U)) :
    derivedHomEvaluation X B A D U hw
        (((comparisonSetUpperStar X).map
          ((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).map
            (derivedLocalIsoToHomPresheaf (J := X.smallEtaleTopology) (B := B)
              (A := A) (D := D)))).hom.app (op U) s) =
      (derivedIsoEvaluation X B A D U hw s).hom := by
  apply (proEtaleDerivedUnits_bijective X B A D U hw).1.1
  rw [homEvaluation_unit]
  have hc := congrArg (fun k ↦ k.hom.app (op U) s) (iso_hom X B A D)
  have hn := toSheafify_naturality (ProEt.topology X)
    (derivedLocalIsoToHomPresheaf (J := ProEt.topology X) (B := B)
      (A := (derivedComparison X B).obj A) (D := (derivedComparison X B).obj D))
  have ht := ConcreteCategory.congr_hom (congr_app hn (op U))
    (derivedIsoEvaluation X B A D U hw s)
  exact hc.symm.trans ((congrArg
    ((derivedLocalIsoToHomSheaf (J := ProEt.topology X) (B := B)
      (A := (derivedComparison X B).obj A) (D := (derivedComparison X B).obj D)).hom.app
        (op U)) (isoEvaluation_unit X B A D U hw s).symm).trans ht.symm)

end AlgebraicGeometry.Scheme
