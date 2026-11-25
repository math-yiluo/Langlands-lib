/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import all WeilConjectures.Algebra.Homology.OpenCoverMateComplexShortExact

/-! # Natural open-cover short exact sequences of etale sheaves

Source: Stacks Project, Tag 0GKK, proof of `lemma-mayer-vietoris-shriek`.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private lemma counitSequence_shortExact
    {C : Type*} [Category* C] [Abelian C]
    {W U V F : C} (iU : W ⟶ U) (iV : W ⟶ V)
    (eU : U ⟶ F) (eV : V ⟶ F) (eW : W ⟶ F)
    (hU : iU ≫ eU = eW) (hV : iV ≫ eV = eW)
    [IsIso eU] [IsIso eV] [IsIso eW]
    (hz : biprod.lift iU (-iV) ≫ biprod.desc eU eV = 0) :
    (ShortComplex.mk (biprod.lift iU (-iV)) (biprod.desc eU eV) hz).ShortExact := by
  have hiU : iU = eW ≫ inv eU := by
    apply (cancel_mono eU).mp
    simpa using hU
  have hiV : iV = eW ≫ inv eV := by
    apply (cancel_mono eV).mp
    simpa using hV
  let S := ShortComplex.mk (biprod.lift iU (-iV)) (biprod.desc eU eV) hz
  have sp : S.Splitting :=
    { r := biprod.fst ≫ eU ≫ inv eW
      s := inv eV ≫ biprod.inr
      f_r := by simp [S, hiU]
      s_g := by simp [S, Category.assoc]
      id := by
        dsimp [S]
        ext <;> simp [hiU, hiV, Category.assoc] }
  exact sp.shortExact

private lemma counitSequence_shortExact_left
    {C : Type*} [Category* C] [Abelian C]
    {W U V F : C} (iU : W ⟶ U) (iV : W ⟶ V)
    (eU : U ⟶ F) (eV : V ⟶ F)
    [IsIso eU] (hW : IsZero W) (hV : IsZero V)
    (hz : biprod.lift iU (-iV) ≫ biprod.desc eU eV = 0) :
    (ShortComplex.mk (biprod.lift iU (-iV)) (biprod.desc eU eV) hz).ShortExact := by
  let e : U ⊞ V ≅ F :=
    { hom := biprod.desc eU eV
      inv := inv eU ≫ biprod.inl
      hom_inv_id := by
        apply biprod.hom_ext'
        · simp
        · exact hV.eq_of_src _ _
      inv_hom_id := by simp }
  have : IsIso (biprod.desc eU eV) := e.isIso_hom
  exact (ShortComplex.Splitting.ofIsZeroOfIsIso _ hW inferInstance).shortExact

private lemma counitSequence_shortExact_right
    {C : Type*} [Category* C] [Abelian C]
    {W U V F : C} (iU : W ⟶ U) (iV : W ⟶ V)
    (eU : U ⟶ F) (eV : V ⟶ F)
    [IsIso eV] (hW : IsZero W) (hU : IsZero U)
    (hz : biprod.lift iU (-iV) ≫ biprod.desc eU eV = 0) :
    (ShortComplex.mk (biprod.lift iU (-iV)) (biprod.desc eU eV) hz).ShortExact := by
  let e : U ⊞ V ≅ F :=
    { hom := biprod.desc eU eV
      inv := inv eV ≫ biprod.inr
      hom_inv_id := by
        apply biprod.hom_ext'
        · exact hU.eq_of_src _ _
        · simp
      inv_hom_id := by simp }
  have : IsIso (biprod.desc eU eV) := e.isIso_hom
  exact (ShortComplex.Splitting.ofIsZeroOfIsIso _ hW inferInstance).shortExact

/-- The natural sheaf-level sequence needed before applying a complex functor.
Source: Stacks Project, Tag 0GKK, proof of `lemma-mayer-vietoris-shriek`.
(blueprint: lem-weil-pbc-etale-open-cover-shriek-natural-ses).

Proof: For W contained in T, compose the inverse of the restriction-composition
isomorphism with restriction of the unit for T, then apply the adjunction for W.
This gives a natural transformation from jW! jW* to jT! jT*. Its composite with
counit T is counit W by the right triangle identity and naturality of the
restriction-composition isomorphism. Thus the signed pair of these maps,
followed by the pair of counits, has zero composite. On a geometric stalk in
both opens this is the split sequence with maps (1,-1) and (1,1). In only U or
only V, the intersection stalk and the other summand vanish, and the remaining
counit is an isomorphism. The covering assumption rules out a point in neither
open. Exact geometric stalk functors jointly reflect short exactness, proving
the assertion. The natural transformations are constructed before specializing
to F, so they commute with arbitrary morphisms. No finiteness hypothesis is
used. Empty opens, equal opens, empty X, characteristic two, and the zero ring
satisfy the same three stalk calculations.
-/
theorem exists_natural_shortExact_openCover_lowerShriek
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let E (T : X.Opens) := upperStar (ModuleCat.{u + 1} Λ) T.ι ⋙
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.ι
    ∃ (iU : E (U ⊓ V) ⟶ E U) (iV : E (U ⊓ V) ⟶ E V),
      ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      ∃ hz : biprod.lift (iU.app F) (-(iV.app F)) ≫
          biprod.desc
            ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
              U.ι).counit.app F)
            ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
              V.ι).counit.app F) = 0,
        (ShortComplex.mk (biprod.lift (iU.app F) (-(iV.app F)))
          (biprod.desc
            ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
              U.ι).counit.app F)
            ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
              V.ι).counit.app F)) hz).ShortExact := by
  let A := ModuleCat.{u + 1} Λ
  let R (T : X.Opens) := upperStar A T.ι
  let S (T : X.Opens) := openImmersionLowerShriek A T.ι
  let a (T : X.Opens) := openImmersionLowerShriekUpperStarAdjunction A T.ι
  let cU : R U ⋙ upperStar A (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) ≅ R (U ⊓ V) :=
    (upperStarComp A (X.homOfLE inf_le_left) U.ι (U ⊓ V).ι
      (X.homOfLE_ι inf_le_left).symm).symm
  let cV : R V ⋙ upperStar A (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) ≅ R (U ⊓ V) :=
    (upperStarComp A (X.homOfLE inf_le_right) V.ι (U ⊓ V).ι
      (X.homOfLE_ι inf_le_right).symm).symm
  let tU := SheafOfModules.nestedMate (R U) (R (U ⊓ V))
    (upperStar A (X.homOfLE inf_le_left)) (S U) (S (U ⊓ V)) (a U) (a (U ⊓ V)) cU
  let tV := SheafOfModules.nestedMate (R V) (R (U ⊓ V))
    (upperStar A (X.homOfLE inf_le_right)) (S V) (S (U ⊓ V)) (a V) (a (U ⊓ V)) cV
  refine ⟨tU, tV, fun F ↦ ?_⟩
  have hcU : tU.app F ≫ (a U).counit.app F = (a (U ⊓ V)).counit.app F := by
    rw [SheafOfModules.nestedMate_app]
    exact SheafOfModules.nestedTranspose_counit _ _ _ _ _ (a U) (a (U ⊓ V)) cU F
  have hcV : tV.app F ≫ (a V).counit.app F = (a (U ⊓ V)).counit.app F := by
    rw [SheafOfModules.nestedMate_app]
    exact SheafOfModules.nestedTranspose_counit _ _ _ _ _ (a V) (a (U ⊓ V)) cV F
  have hz : biprod.lift (tU.app F) (-(tV.app F)) ≫
      biprod.desc ((a U).counit.app F) ((a V).counit.app F) = 0 := by
    simp only [biprod.lift_desc, Preadditive.neg_comp, hcU, hcV, add_neg_cancel]
  refine ⟨hz, ?_⟩
  apply ((Scheme.jointlyReflectIsomorphisms_ulift_pointSmallEtale X A).shortExact_iff _).mpr
  rintro ⟨-, ⟨x⟩⟩
  let G := (X.uliftPointSmallEtale x).sheafFiber (A := A)
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  have : PreservesBinaryBiproducts G :=
    preservesBinaryBiproducts_of_preservesBiproducts G
  let ε (T : X.Opens) := (a T).counit.app F
  have hiso (T : X.Opens) (hx : x ∈ T) : IsIso (G.map (ε T)) := by
    let s := X.algClosurePoint x
    have hs : s.base (IsLocalRing.closedPoint _) ∈ Set.range T.ι.base := by
      simpa [s, Scheme.Opens.range_ι] using hx
    have hh := isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map A T.ι (ε T)
      (by dsimp [ε, a]; infer_instance)
      (IsOpenImmersion.lift T.ι s (Scheme.range_base_subset_of_closedPoint_mem s hs))
    rw [IsOpenImmersion.lift_fac] at hh
    exact hh
  have hzero (T : X.Opens) (hx : x ∉ T) : IsZero (G.obj ((R T ⋙ S T).obj F)) := by
    apply isZero_uliftSheafFiber_openImmersionLowerShriek_obj A T.ι (X.algClosurePoint x)
    simpa [Scheme.Opens.range_ι] using hx
  have hGU : G.map (tU.app F) ≫ G.map (ε U) = G.map (ε (U ⊓ V)) := by
    rw [← G.map_comp, hcU]
  have hGV : G.map (tV.app F) ≫ G.map (ε V) = G.map (ε (U ⊓ V)) := by
    rw [← G.map_comp, hcV]
  have hzn : biprod.lift (G.map (tU.app F)) (-(G.map (tV.app F))) ≫
      biprod.desc (G.map (ε U)) (G.map (ε V)) = 0 := by
    simp only [biprod.lift_desc, Preadditive.neg_comp, hGU, hGV, add_neg_cancel]
  have hn : (ShortComplex.mk
      (biprod.lift (G.map (tU.app F)) (-(G.map (tV.app F))))
      (biprod.desc (G.map (ε U)) (G.map (ε V))) hzn).ShortExact := by
    by_cases hxU : x ∈ U
    · have := hiso U hxU
      by_cases hxV : x ∈ V
      · have := hiso V hxV
        have := hiso (U ⊓ V) ⟨hxU, hxV⟩
        exact counitSequence_shortExact _ _ _ _ _ hGU hGV hzn
      · exact counitSequence_shortExact_left _ _ _ _
          (hzero (U ⊓ V) (fun h ↦ hxV h.2)) (hzero V hxV) hzn
    · have hxV : x ∈ V := by
        have hx : x ∈ U ⊔ V := by rw [hcover]; trivial
        exact hx.resolve_left hxU
      have := hiso V hxV
      exact counitSequence_shortExact_right _ _ _ _
        (hzero (U ⊓ V) (fun h ↦ hxU h.1)) (hzero U hxU) hzn
  let e := G.mapBiprod ((R U ⋙ S U).obj F) ((R V ⋙ S V).obj F)
  apply ShortComplex.shortExact_of_iso _ hn
  refine ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _) ?_ ?_
  · change G.map (biprod.lift (tU.app F) (-(tV.app F))) =
      biprod.lift (G.map (tU.app F)) (-(G.map (tV.app F))) ≫ e.inv
    simpa only [Functor.map_neg] using
      (biprod.lift_mapBiprod G _ _ (tU.app F) (-(tV.app F))).symm
  · change e.inv ≫ G.map (biprod.desc (ε U) (ε V)) =
      biprod.desc (G.map (ε U)) (G.map (ε V))
    exact biprod.mapBiprod_inv_map_desc G _ _ (ε U) (ε V)

end AlgebraicGeometry.Etale
