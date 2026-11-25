/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.Etale.Affine.EtaleAffineLineShriekSheafConstructible
import WeilConjectures.AlgebraicGeometry.Etale.EtaleShriekQcqsComposition
import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteShriekConstructible
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.Compactification.Affine
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Etale.EtaleShriekRelativeMayerVietoris
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleEtaleModuleQcqsAffineLocal
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion

/-!
# Constructibility of the etale compact-support candidate

Source: Stacks Project, Tag 0GL0, theorem-constructible-shriek,
finite-ring bounded-below specialization.
(blueprint: lem-weil-pbc-etale-compactification-constructibility).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A fixed compact-support candidate preserves constructible cohomology on bounded-below
complexes as soon as it does on constructible sheaves placed in degree zero.
Source: Stacks Project, Tag 0GL0, final paragraph (the truncation alternative).
(blueprint: lem-weil-pbc-etale-compactification-constructibility).

Proof: extension by zero is exact and right derived direct image is left t-exact, so their
composite preserves every lower cohomological bound. For each degree n, truncate the input
above n. Its constructible cohomology and lower bound make it bounded constructible.
Bounded truncation dévissage, using the constructible weak Serre class, proves the assertion
for this truncation from the sheaf hypothesis. Apply the compact-support functor to the
truncation triangle. The third term still vanishes through degree n, so the induced map in
degree n is an isomorphism. Transfer constructibility across this isomorphism. -/
private lemma constructible_compactSupport_of_sheaf
    {X Y : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (f : X ⟶ Y) (c : Compactification f)
    (hsheaf : ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      Scheme.IsConstructibleSheaf F →
      DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) X K.obj) :
    DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K.obj) := by
  let R := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c
  have hGE (L : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ) [L.IsGE a] :
      (R.obj L).IsGE a := by
    have := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).isGE_mapDerivedCategory_obj L a
    exact Functor.isGE_rightDerivedFunctor_obj _ _ a
  intro n
  have hb : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
      ((_root_.DerivedCategory.TStructure.t.truncLE n).obj K.obj) := by
    obtain ⟨a, ha⟩ := K.property
    have : K.obj.IsGE a := ha
    refine ⟨⟨⟨a, ?_⟩, ⟨n, inferInstance⟩⟩, ?_⟩
    · exact inferInstanceAs (_root_.DerivedCategory.TStructure.t.IsGE
        ((_root_.DerivedCategory.TStructure.t.truncLE n).obj K.obj) a)
    · rw [DerivedCategory.constructibleHomology_eq] at hK ⊢
      exact _root_.DerivedCategory.homologyProperty_truncLE hK n
  have hbounded := prop_of_boundedConstructible
    ((DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) Y).inverseImage R)
    hsheaf hb
  let T := (_root_.DerivedCategory.TStructure.t.triangleLEGT n).obj K.obj
  have hT := _root_.DerivedCategory.TStructure.t.triangleLEGT_distinguished n K.obj
  have : T.obj₃.IsGE (n + 1) := inferInstanceAs
    (_root_.DerivedCategory.TStructure.t.IsGE
      ((_root_.DerivedCategory.TStructure.t.truncGT n).obj K.obj) (n + 1))
  have hR : (R.obj T.obj₃).IsGE (n + 1) := hGE T.obj₃ (n + 1)
  have : IsIso ((_root_.DerivedCategory.homologyFunctor _ n).map (R.map T.mor₁)) :=
    _root_.DerivedCategory.isIso_homologyMap_mor₁ _ (R.map_distinguished _ hT)
      (n - 1) n (by omega)
      (_root_.DerivedCategory.isZero_of_isGE _ (n + 1) _ (by omega) (hX := hR))
      (_root_.DerivedCategory.isZero_of_isGE _ (n + 1) _ (by omega) (hX := hR))
  have : Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ n).obj (R.obj T.obj₁)) := hbounded n
  exact Scheme.IsConstructibleSheaf.of_iso
    (asIso ((_root_.DerivedCategory.homologyFunctor _ n).map (R.map T.mor₁)))

private lemma compactSupportPlus_of_sheaf
    {X Y : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (f : X ⟶ Y) (c : Compactification f)
    (hsheaf : ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      Scheme.IsConstructibleEtaleModuleSheaf F → ∀ q : ℤ,
      Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))))
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)) :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  have htotal : DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K.obj) := by
    apply constructible_compactSupport_of_sheaf Λ f c ?_ K
      (fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hK q))
    intro F hF q
    have h := hsheaf F
      ((Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr hF) q
    have : Scheme.IsConstructibleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp h
    exact Scheme.IsConstructibleSheaf.of_iso
      (F := (_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F)))
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
        (((rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} Λ) c).app
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≪≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).mapIso
            ((_root_.DerivedCategory.Plus.singleFunctorιIso _ 0).app F)))
  intro q
  have := htotal q
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  exact Scheme.IsConstructibleSheaf.of_iso
    (F := (_root_.DerivedCategory.homologyFunctor _ q).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K.obj))
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} Λ) c).app K)).symm

private lemma compactSupportPlus_comp
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (c : Compactification (f ≫ g))
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hf : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cf).obj K)))
    (hg : ∀ L : _root_.DerivedCategory.Plus
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj L)) →
      ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cg).obj L))) :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  obtain ⟨e⟩ := nonempty_iso_etaleShriek_qcqs_compactification_comp Λ f g cf cg c
  intro q
  have h := hg
    ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cf).obj K) hf q
  have : Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cg).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cf).obj K))) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp h
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  exact Scheme.IsConstructibleSheaf.of_iso
    (F := (_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cg).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cf).obj K)))
    ((_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso (e.app K))

private lemma compactSupportPlus_affineSpace
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (Y : Scheme.{u}) [IsAffine Y]
    (hΛ : ∀ (a : Λ) (y : Y), IsUnit (addOrderOf a : Y.presheaf.stalk y)) (n : ℕ)
    (c : Compactification (AffineSpace (ULift.{u} (Fin n)) Y ↘ Y))
    (K : _root_.DerivedCategory.Plus
      (Sheaf (AffineSpace (ULift.{u} (Fin n)) Y).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)) :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  induction n generalizing Y with
  | zero =>
    have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
    exact constructibleCohomology_lowerShriek_of_isClosedImmersion Λ _ K hK c
  | succ n ih =>
    let N := ULift.{u} (Fin n)
    let L := ULift.{u} (Fin 1)
    let B := AffineSpace N Y
    let e : ULift.{u} (Fin (n + 1)) ≃ N ⊕ L :=
      Equiv.ulift.trans ((finSumFinEquiv (m := n) (n := 1)).symm.trans
        (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm))
    let E := (AffineSpace.reindexIso (S := Y) e.symm) ≪≫
      (AffineSpace.sumIso (n := N) (m := L) Y)
    let a : AffineSpace L B ⟶ B := AffineSpace L B ↘ B
    let b : B ⟶ Y := B ↘ Y
    have hfac : E.hom ≫ a ≫ b = AffineSpace (ULift.{u} (Fin (n + 1))) Y ↘ Y := by
      dsimp [E, a, b, B]
      rw [Category.assoc, AffineSpace.sumIso_hom_over_over]
      exact AffineSpace.reindex_over _ _
    let cE := Compactification.ofIsProper E.hom
    let ca : Compactification a := HasCompactification.compactification a
    let cb : Compactification b := HasCompactification.compactification b
    have : QuasiCompact cE.i := cE.quasiCompact_openImmersion inferInstance
    have hE := constructibleCohomology_lowerShriek_of_isClosedImmersion Λ E.hom K hK cE
    have ha : ∀ M : _root_.DerivedCategory.Plus
        (Sheaf (AffineSpace L B).smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj M)) →
        ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
            ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) ca).obj M)) := by
      intro M hM
      apply compactSupportPlus_of_sheaf Λ a ca ?_ M hM
      exact fun F hF q ↦ isConstructibleEtaleModuleSheaf_affineLine_shriek Λ B
        (fun a x ↦ by simpa using (hΛ a (b x)).map (b.stalkMap x).hom) F hF ca q
    let cEa : Compactification (E.hom ≫ a) := ca.precomp E.hom
    have hEa := compactSupportPlus_comp Λ E.hom a cE ca cEa K hE ha
    exact compactSupportPlus_comp Λ (E.hom ≫ a) b cEa cb
      (c.copy (by simpa [Category.assoc] using hfac)) K hEa (fun M hM ↦ ih Y hΛ cb M hM)

/-- The affine-source, affine-base case of compact-support constructibility.
Source: Stacks Project, Tag 0GL0, second paragraph.
(blueprint: lem-weil-pbc-etale-compactification-constructibility).

Proof: present the finitely presented coordinate algebra as a quotient of a finite polynomial
algebra, giving a finitely presented closed immersion into affine space. Its compact-support
image is constructible by quasi-finite constructibility. Induct on the dimension of affine
space, factoring its projection into successive relative affine lines. The affine-line sheaf
theorem, lifted to bounded-below inputs by truncation dévissage, handles each factor.
Compact-support composition identifies the successive outputs with the desired candidate.
Exact open extension and left t-exact right derived direct image preserve boundedness below
at each step. Compactification independence permits every chosen compactification. -/
private lemma constructible_compactSupport_affine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : ∀ (a : Λ) (y : Y), IsUnit (addOrderOf a : Y.presheaf.stalk y))
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] (c : Compactification f)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)) :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_closure_range_appTop_union_eq_top f
  let v : ULift.{u} (Fin s.card) → Γ(X, ⊤) := fun i ↦ (s.equivFin.symm i.down).val
  have hv : Set.range v = (s : Set Γ(X, ⊤)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i.down).property
    · intro hx
      exact ⟨⟨s.equivFin ⟨x, hx⟩⟩, by simp [v]⟩
  let i := AffineSpace.homOfVector f v
  let p : AffineSpace (ULift.{u} (Fin s.card)) Y ⟶ Y :=
    AffineSpace (ULift.{u} (Fin s.card)) Y ↘ Y
  have hi : IsClosedImmersion i := AffineSpace.isClosedImmersion_homOfVector f v
    (by rw [hv]; exact hs)
  have hfac : i ≫ p = f := AffineSpace.homOfVector_over f v
  have : LocallyOfFinitePresentation (i ≫ p) := hfac.symm ▸ inferInstance
  have : LocallyOfFinitePresentation i := locallyOfFinitePresentation_of_comp i p
  let ci := Compactification.ofIsProper i
  let cp : Compactification p := HasCompactification.compactification p
  have : QuasiCompact ci.i := ci.quasiCompact_openImmersion inferInstance
  have hci := constructibleCohomology_lowerShriek_of_isClosedImmersion Λ i K hK ci
  exact compactSupportPlus_comp Λ i p ci cp (c.copy hfac) K hci
    (fun M hM ↦ compactSupportPlus_affineSpace Λ Y hΛ s.card cp M hM)

private lemma constructible_pullback_complex
    {X T : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (g : T ⟶ X)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)) :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        (((upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus).obj K)) := by
  intro q
  have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hK q)
  have := Scheme.IsConstructibleSheaf.upperStar g
    ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  exact Scheme.IsConstructibleSheaf.of_iso
    (F := (upperStar (ModuleCat.{u + 1} Λ) g).obj
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K))
    (((upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusHomologyFunctorIso q).app K)

private lemma constructible_compactSupport_of_cover
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {Y : Scheme.{u}} [IsAffine Y]
    (hΛ : ∀ (a : Λ) (y : Y), IsUnit (addOrderOf a : Y.presheaf.stalk y)) (n : ℕ) :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (f : X ⟶ Y) [IsSeparated f] [LocallyOfFinitePresentation f]
      [QuasiCompact f] [QuasiSeparated f]
      (U : Fin (n + 1) → X.Opens), (∀ i, IsAffineOpen (U i)) → ⨆ i, U i = ⊤ →
      ∀ (c : Compactification f)
        (K : _root_.DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)) →
      ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  induction n with
  | zero =>
    intro X _ _ f _ _ _ _ U hU hcov c K hK
    have h0 : U 0 = ⊤ := by
      rw [← hcov]
      exact le_antisymm (le_iSup U 0) (iSup_le fun i ↦ by
        rw [(Fin.ext (by have := i.2; omega) : i = 0)])
    have : IsAffine X := by
      have h := hU 0
      rw [h0] at h
      have : IsAffine (⊤ : X.Opens).toScheme := h
      exact .of_isIso X.topIso.inv
    exact constructible_compactSupport_affine Λ hΛ f c K hK
  | succ n ih =>
    intro X _ _ f _ _ _ _ U hU hcov c K hK
    let V : X.Opens := ⨆ i : Fin (n + 1), U i.castSucc
    let W : X.Opens := U (Fin.last _)
    have hcover : V ⊔ W = ⊤ := by
      refine eq_top_iff.mpr (hcov.symm.le.trans (iSup_le fun i ↦ ?_))
      induction i using Fin.lastCases with
      | last => exact le_sup_right
      | cast i => exact (le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i).trans le_sup_left
    have hV : IsCompact (V : Set X) := by
      change IsCompact ((⨆ i : Fin (n + 1), U i.castSucc : X.Opens) : Set X)
      rw [TopologicalSpace.Opens.coe_iSup]
      exact isCompact_iUnion fun i ↦ (hU i.castSucc).isCompact
    have hW : IsCompact (W : Set X) := (hU (Fin.last _)).isCompact
    have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
    have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
    have : QuasiSeparatedSpace V.toScheme := quasiSeparatedSpace_of_quasiSeparated V.ι
    have : QuasiSeparatedSpace W.toScheme := quasiSeparatedSpace_of_quasiSeparated W.ι
    have : CompactSpace (V ⊓ W).toScheme := by
      apply isCompact_iff_compactSpace.mp
      exact hV.inter_of_isOpen hW V.isOpen W.isOpen
    have : QuasiSeparatedSpace (V ⊓ W).toScheme :=
      quasiSeparatedSpace_of_quasiSeparated (V ⊓ W).ι
    let cV : Compactification (V.ι ≫ f) := c.precomp V.ι
    let cW : Compactification (W.ι ≫ f) := c.precomp W.ι
    let cVW : Compactification ((V ⊓ W).ι ≫ f) := c.precomp (V ⊓ W).ι
    have hsep := isAffineHom_diagonal_iff.mp
      (inferInstance : IsAffineHom (Limits.pullback.diagonal f)) ⊤ (isAffineOpen_top Y)
    have hKV := constructible_pullback_complex Λ V.ι K hK
    have hKW := constructible_pullback_complex Λ W.ι K hK
    have hKVW := constructible_pullback_complex Λ (V ⊓ W).ι K hK
    have hUV (i : Fin (n + 1)) : U i.castSucc ≤ Scheme.Hom.opensRange V.ι := by
      rw [Scheme.Opens.opensRange_ι]
      exact le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i
    have hcovV : ⨆ i : Fin (n + 1), V.ι ⁻¹ᵁ U i.castSucc = ⊤ := by
      rw [← Scheme.Hom.preimage_iSup]
      exact Scheme.Opens.ι_preimage_self V
    have hRV := ih (V.ι ≫ f) (fun i ↦ V.ι ⁻¹ᵁ U i.castSucc)
      (fun i ↦ (hU _).preimage_of_isOpenImmersion _ (hUV i)) hcovV cV
      (((upperStar (ModuleCat.{u + 1} Λ) V.ι).mapDerivedCategoryPlus).obj K) hKV
    have hUVW (i : Fin (n + 1)) :
        U i.castSucc ⊓ W ≤ Scheme.Hom.opensRange (V ⊓ W).ι := by
      rw [Scheme.Opens.opensRange_ι]
      exact inf_le_inf_right _ (le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i)
    have hcovVW : ⨆ i : Fin (n + 1), (V ⊓ W).ι ⁻¹ᵁ (U i.castSucc ⊓ W) = ⊤ := by
      rw [← Scheme.Hom.preimage_iSup, ← iSup_inf_eq]
      exact Scheme.Opens.ι_preimage_self (V ⊓ W)
    have hRVW := ih ((V ⊓ W).ι ≫ f)
      (fun i ↦ (V ⊓ W).ι ⁻¹ᵁ (U i.castSucc ⊓ W))
      (fun i ↦ (hsep _ (by simp) _ (by simp) (hU _) (hU _)).preimage_of_isOpenImmersion _
        (hUVW i)) hcovVW cVW
      (((upperStar (ModuleCat.{u + 1} Λ) (V ⊓ W).ι).mapDerivedCategoryPlus).obj K) hKVW
    have : IsAffine W.toScheme := hU _
    have hRW := constructible_compactSupport_affine Λ hΛ (W.ι ≫ f) cW
      (((upperStar (ModuleCat.{u + 1} Λ) W.ι).mapDerivedCategoryPlus).obj K) hKW
    obtain ⟨α, β, δ, hT⟩ :=
      exists_distinguished_relativeMayerVietoris Λ f V W hV hW hcover cV cW cVW c K
    let T := Pretriangulated.Triangle.mk α β δ
    let P := (DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) Y).inverseImage
      _root_.DerivedCategory.Plus.ι
    have : P.IsTriangulated := by
      dsimp [P]
      infer_instance
    have hP₁ : P T.obj₁ := fun q ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hRVW q)
    have hP₂ : P T.obj₂ := by
      intro q
      have : Scheme.IsConstructibleSheaf
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
            ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cV).obj
              (((upperStar (ModuleCat.{u + 1} Λ) V.ι).mapDerivedCategoryPlus).obj K))) :=
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hRV q)
      have : Scheme.IsConstructibleSheaf
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
            ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cW).obj
              (((upperStar (ModuleCat.{u + 1} Λ) W.ι).mapDerivedCategoryPlus).obj K))) :=
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hRW q)
      let H := _root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q
      have hH : H.Additive := by
        dsimp [H, _root_.DerivedCategory.Plus.homologyFunctor]
        infer_instance
      let M := (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cV).obj
        (((upperStar (ModuleCat.{u + 1} Λ) V.ι).mapDerivedCategoryPlus).obj K)
      let N := (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cW).obj
        (((upperStar (ModuleCat.{u + 1} Λ) W.ι).mapDerivedCategoryPlus).obj K)
      have : Limits.PreservesBinaryBiproducts H :=
        Limits.preservesBinaryBiproducts_of_preservesBiproducts H
      have := Scheme.IsConstructibleSheaf.biprod (H.obj M) (H.obj N)
      exact Scheme.IsConstructibleSheaf.of_iso
        (F := H.obj M ⊞ H.obj N) (H.mapBiprod M N).symm
    have hP₃ : P T.obj₃ := P.ext_of_isTriangulatedClosed₃ T hT hP₁ hP₂
    intro q
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hP₃ q)

/-- Compact-support constructibility over an affine base, by a finite affine cover.
Source: Stacks Project, Tag 0GL0, first paragraph. -/
private lemma compactSupportPlus_affineBase
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [IsAffine Y]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : ∀ (a : Λ) (y : Y), IsUnit (addOrderOf a : Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f] (c : Compactification f)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)) :
    ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens ↦ (U : Set X))
    (fun U ↦ U.1.isOpen) (by
      intro x _
      have : x ∈ (⨆ i : X.affineOpens, (i : X.Opens)) := by
        rw [iSup_affineOpens_eq_top]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using this)
  let U : Fin (s.card + 1) → X.Opens :=
    Fin.cons ⊥ fun i ↦ (s.equivFin.symm i).1.1
  have hU : ∀ i, IsAffineOpen (U i) := by
    intro i
    induction i using Fin.cases with
    | zero => exact isAffineOpen_bot X
    | succ i => exact (s.equivFin.symm i).1.2
  have hcov : ⨆ i, U i = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨W, hW, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨(s.equivFin ⟨W, hW⟩).succ, by simpa [U] using hx⟩
  exact constructible_compactSupport_of_cover Λ hΛ s.card f U hU hcov c K hK

private lemma constructible_of_affine_restrictions
    {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : ∀ W : Y.Opens, IsAffineOpen W →
      Scheme.IsConstructibleEtaleModuleSheaf
        ((upperStar (ModuleCat.{u + 1} Λ) W.ι).obj G)) :
    Scheme.IsConstructibleEtaleModuleSheaf G := by
  apply ((Scheme.constructible_etale_module_qcqs_affine_local G).out 2 3).mp
  refine ⟨{W | IsAffineOpen W}, ?_, ?_⟩
  · intro y
    obtain ⟨W, hW, hy⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y)
      (show y ∈ (⊤ : Y.Opens) from trivial)
    exact ⟨W, hW, hy.1⟩
  · intro W hW U hU
    have : IsAffine W.toScheme := hW
    have :=
      (Scheme.constructible_etale_module_qcqs_affine_local
        ((upperStar (ModuleCat.{u + 1} Λ) W.ι).obj G)).out 3 1 |>.mp (hG W hW)
    obtain ⟨S, hS, hr, hf⟩ := this U hU
    refine ⟨S, hS, hr, fun k ↦ ?_⟩
    have := hf k
    exact Scheme.IsFiniteLocallyConstantSheaf.of_iso
      (F := (upperStar (ModuleCat.{u + 1} Λ) (S.immersion k ≫ U.ι)).obj
        ((upperStar (ModuleCat.{u + 1} Λ) W.ι).obj G))
      ((upperStarComp (ModuleCat.{u + 1} Λ) (S.immersion k ≫ U.ι) W.ι
        (S.immersion k ≫ U.ι ≫ W.ι) (Category.assoc _ _ _).symm).app G).symm

private lemma compactSupport_constructible_of_affine_base
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (q : ℤ)
    (hlocal : ∀ W : Y.Opens, IsAffineOpen W →
      Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
          ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
            (c.baseChange W.ι)).obj
            (((upperStar (ModuleCat.{u + 1} Λ)
              (Limits.pullback.fst f W.ι)).mapDerivedCategoryPlus).obj K)))) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
  apply constructible_of_affine_restrictions Λ
  intro W hW
  have hex := (compactSupportFiniteTorsion Λ (IsPullback.of_hasPullback f W.ι) c).1 K
  let e := (upperStar (ModuleCat.{u + 1} Λ) W.ι).mapDerivedCategoryPlusHomologyFunctorIso q
  have h := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
    (hlocal W hW)
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  let eout :=
    (((_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (asIso ((rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ
        (IsPullback.of_hasPullback f W.ι) c).app K))).symm ≪≫
      (e.app ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)).symm)
  have : Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        (((upperStar (ModuleCat.{u + 1} Λ) (Limits.pullback.fst f W.ι)).mapDerivedCategoryPlus ⋙
          rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
            (c.ofIsPullback (IsPullback.of_hasPullback f W.ι))).obj K)) := by
    exact h
  exact Scheme.IsConstructibleSheaf.of_iso eout

/-- The compact-support candidate has constructible cohomology for bounded-below inputs,
when the additive orders of the coefficients are invertible on the base.
Source: Stacks Project, Tag 0GL0, theorem-constructible-shriek (torsion prime to the
characteristics of the base).
(blueprint: lem-weil-pbc-etale-compactification-constructibility).

Proof: dévissage through bounded truncations promotes the affine-line sheaf theorem to
bounded-below complexes. Induct on affine-space dimension using the composition theorem.
A finite-type morphism of affine schemes factors as a finitely presented closed immersion
into finite-dimensional affine space followed by its projection; quasi-finite constructibility
handles the closed immersion. Over an affine base, use a finite affine cover of the source
and induct on its size. Separation makes intersections affine, and the relative Mayer--Vietoris
triangle together with the constructible weak Serre property gives the induction step.
Finally restrict the base to its affine opens. Compact-support base change and exact inverse
image identify these restrictions with the affine-base cases. Affine-local constructibility
and the compatibility of bounded-below and total compact-support candidates conclude. -/
theorem isConstructibleEtaleModuleSheaf_homology_compactSupportCandidate
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : ∀ (a : Λ) (y : Y), IsUnit (addOrderOf a : Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f] (c : Compactification f)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K.obj)) (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K.obj))   := by
  have hK' : ∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ n).obj K) := hK
  have hplus : Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) := by
    apply compactSupport_constructible_of_affine_base Λ f c K q
    intro W hW
    have : IsAffine W.toScheme := hW
    have : CompactSpace ↥(Limits.pullback f W.ι) :=
      QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.snd f W.ι)
    have : QuasiSeparatedSpace ↥(Limits.pullback f W.ι) :=
      quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.snd f W.ι)
    exact compactSupportPlus_affineBase Λ
      (fun a w ↦ by simpa using (hΛ a (W.ι w)).map (W.ι.stalkMap w).hom)
      (Limits.pullback.snd f W.ι) (c.baseChange W.ι)
      (((upperStar (ModuleCat.{u + 1} Λ) (Limits.pullback.fst f W.ι)).mapDerivedCategoryPlus).obj K)
      (constructible_pullback_complex Λ (Limits.pullback.fst f W.ι) K hK') q
  have : Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K)) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hplus
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  exact Scheme.IsConstructibleSheaf.of_iso
    (F := (_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K))
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} Λ) c).app K))

end AlgebraicGeometry.Etale
