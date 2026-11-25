/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphCoherence

/-!
# Normalization of compact supports for an etale morphism

Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tag 03S6
(blueprint: lem-asd-etale-compact-support-normalization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- A simultaneous normalization, on all unbounded complexes. The graph-extension equation
specifies the sheaf comparison, and the homotopy equation specifies its derived descent;
neither comparison is an arbitrary isomorphism. Proper refinements are compared using the
same normalized comparison for the coarser open immersion.
Source: SGA 4 XVII 5.2.2, 6.2.11; Stacks Project Tag 03S6
(blueprint: lem-asd-etale-compact-support-normalization). -/
structure EtaleCompactSupportNormalization (A : Type (u + 1)) [CommRing A] where
  /-- The compact-support-to-sum comparison. -/
  comparison : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f),
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory
  /-- Inverse comparison on sheaves: extend each sheet section by zero off its graph. -/
  sheafComparison : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f),
    etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g
  /-- The sheaf map is the specified graph-extension map inside direct image. -/
  sheaf_normalization : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f) (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
    (sheafComparison f c).app M ≫ (compactificationSheafToDirectImage A c).app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f M
  /-- On every homotopy representative, descend the preceding sheaf map degreewise and
  then apply the total-right-derived unit. -/
  derived_normalization : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f)
    (K : HomotopyCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (ComplexShape.up ℤ)),
    (comparison f c).inv.app (DerivedCategory.Qh.obj K) =
      compactSupportComparisonOnHomotopy A f c (sheafComparison f c) K
  /-- The actual proper/open exchange agrees with the specified inverse sum exchange. -/
  base_change : ∀ {U X X' : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [QuasiCompact f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian X'] [CompactSpace X'] (c : Compactification f) (g : X' ⟶ X),
    exactCompactSupportExchange A c g ≫
        Functor.whiskerLeft
          (upperStar (ModuleCat.{u + 1} A) (pullback.snd g f)).mapDerivedCategory
          (comparison (pullback.fst g f)
            (c.ofIsPullback (IsPullback.of_hasPullback g f).flip)).hom =
      Functor.whiskerRight (comparison f c).hom
          (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≫
        (exactEtaleSumExchange A f g).hom
  /-- Compatibility for two changes of base, with the canonical pasting associators.
  The exchanges are the specified maps, so this is compatibility with their composite. -/
  composition : ∀ {U X X' X'' : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [QuasiCompact f] [IsLocallyNoetherian U] [CompactSpace U]
    [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian X'] [CompactSpace X']
    [IsLocallyNoetherian X''] [CompactSpace X'']
    (c : Compactification f) (g : X' ⟶ X) (k : X'' ⟶ X'),
    ((exactCompactSupportExchangeSquare A c g).vComp
        (exactCompactSupportExchangeSquare A
          (c.ofIsPullback (IsPullback.of_hasPullback g f).flip) k)) ≫
      Functor.whiskerLeft
        ((upperStar (ModuleCat.{u + 1} A) (pullback.snd g f)).mapDerivedCategory ⋙
          (upperStar (ModuleCat.{u + 1} A)
            (pullback.snd k (pullback.fst g f))).mapDerivedCategory)
        (comparison (pullback.fst k (pullback.fst g f))
          ((c.ofIsPullback (IsPullback.of_hasPullback g f).flip).ofIsPullback
            (IsPullback.of_hasPullback k (pullback.fst g f)).flip)).hom =
      Functor.whiskerRight (comparison f c).hom
        ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
          (upperStar (ModuleCat.{u + 1} A) k).mapDerivedCategory) ≫
        ((exactEtaleSumExchangeSquare A f g).vComp
          (exactEtaleSumExchangeSquare A (pullback.fst g f) k))
  /-- Under a proper refinement, use the comparison for the coarser open immersion,
  normalized by graph extension (hence identity over U), and then compose direct images. -/
  refinement : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c d : Compactification f) (r : c.Refinement d)
    [IsLocallyNoetherian d.Z] [CompactSpace d.Z],
    Functor.whiskerRight (comparison d.i (refinementOpenCompactification r)).inv
        (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar (ModuleCat.{u + 1} A) r.hom)
          (lowerStar (ModuleCat.{u + 1} A) d.g)
          (lowerStarComp (ModuleCat.{u + 1} A) r.hom d.g c.g r.hom_g.symm)).hom ≫
      (comparison f c).hom = (comparison f d).hom
  /-- For an identity morphism the normalized comparison is the identity after removing
  the identity functor. Refinement compatibility supplies every other compactification. -/
  identity : ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X],
    comparison (𝟙 X) (Compactification.ofIsProper (𝟙 X)) =
      identityEtaleCompactSupportComparison A X
  /-- Every chosen compact-support adjunction is identified with the degreewise
  sum/evaluation adjunction, with the unique counit-preserving right-adjoint comparison. -/
  adjunction : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f)
    (R : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ R),
    ∃! e : R ≅ (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory,
      Functor.whiskerLeft R (comparison f c).hom ≫
        Functor.whiskerRight e.hom
          (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory ≫
        (Adjunction.mapDerivedCategoryAdjunction
          (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) f inferInstance)).counit =
        adj.counit

/-- The right-adjoint comparison is uniquely determined by preservation of the counit.
Source: adjunction conjugacy; SGA 4 XVII 5.2.2
(blueprint: lem-asd-etale-compact-support-normalization). -/
theorem counitPreservingComparison
    {C D : Type*} [Category C] [Category D]
    {L S : C ⥤ D} {R T : D ⥤ C}
    (e : L ≅ S) (adj : L ⊣ R) (sumAdj : S ⊣ T) :
    ∃! q : R ≅ T,
      Functor.whiskerLeft R e.hom ≫ Functor.whiskerRight q.hom S ≫ sumAdj.counit =
        adj.counit := by
  let q : R ≅ T := conjugateIsoEquiv adj sumAdj e.symm
  have hq : Functor.whiskerLeft R e.hom ≫
      Functor.whiskerRight q.hom S ≫ sumAdj.counit = adj.counit := by
    ext Y
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    change e.hom.app (R.obj Y) ≫
      S.map (((conjugateEquiv adj sumAdj) e.inv).app Y) ≫ sumAdj.counit.app Y = _
    rw [conjugateEquiv_counit adj sumAdj e.inv Y]
    simp
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply Iso.ext
  ext Y
  apply (sumAdj.homEquiv _ _).symm.injective
  change S.map (q'.hom.app Y) ≫ sumAdj.counit.app Y =
    S.map (q.hom.app Y) ≫ sumAdj.counit.app Y
  apply (cancel_epi (e.hom.app (R.obj Y))).1
  exact (NatTrans.congr_app hq' Y).trans (NatTrans.congr_app hq Y).symm

/-- Comparisons of two squares are preserved by vertical composition.
Source: functoriality and associativity; SGA 4 XVII 6.2.11
(blueprint: lem-asd-etale-compact-support-normalization). -/
theorem comparison_vComp
    {C₀ C₁ C₂ C₃ C₄ C₅ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] [Category C₅]
    {F₀ S₀ : C₀ ⥤ C₁} {F₁ S₁ : C₂ ⥤ C₃} {F₂ S₂ : C₄ ⥤ C₅}
    {H₀ : C₀ ⥤ C₂} {H₁ : C₂ ⥤ C₄} {G₀ : C₁ ⥤ C₃} {G₁ : C₃ ⥤ C₅}
    (a₀ : TwoSquare F₀ H₀ G₀ F₁) (a₁ : TwoSquare F₁ H₁ G₁ F₂)
    (b₀ : TwoSquare S₀ H₀ G₀ S₁) (b₁ : TwoSquare S₁ H₁ G₁ S₂)
    (e₀ : F₀ ≅ S₀) (e₁ : F₁ ≅ S₁) (e₂ : F₂ ≅ S₂)
    (h₀ : a₀ ≫ Functor.whiskerLeft H₀ e₁.hom =
      Functor.whiskerRight e₀.hom G₀ ≫ b₀)
    (h₁ : a₁ ≫ Functor.whiskerLeft H₁ e₂.hom =
      Functor.whiskerRight e₁.hom G₁ ≫ b₁) :
    (a₀.vComp a₁) ≫ Functor.whiskerLeft (H₀ ⋙ H₁) e₂.hom =
      Functor.whiskerRight e₀.hom (G₀ ⋙ G₁) ≫ (b₀.vComp b₁) := by
  ext K
  have h₀K := NatTrans.congr_app h₀ K
  have h₁K := NatTrans.congr_app h₁ (H₀.obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h₀K h₁K
  simp only [TwoSquare.vComp, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.comp_map, Category.id_comp, Category.comp_id, Category.assoc]
  rw [h₁K, ← G₁.map_comp_assoc, h₀K, G₁.map_comp, Category.assoc]

/-- The canonical graph normalization, with its actual comparison maps exposed.
This is the specified witness of `nonempty_etaleCompactSupportNormalization`, constructed
from `canonicalEtaleCompactSupportCore` and graph coherence. Vertical pasting supplies
composition, and conjugacy supplies the unique counit-preserving adjoint comparison.
Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tag 03S6
(blueprint: lem-asd-etale-compact-support-normalization). -/
noncomputable def canonicalEtaleCompactSupportNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    EtaleCompactSupportNormalization A := by
  let core := canonicalEtaleCompactSupportCore A
  have coh := etaleCompactSupportGraph_coherence A
  exact {
    comparison := core.comparison
    sheafComparison := core.sheafComparison
    sheaf_normalization := core.sheaf_normalization
    derived_normalization := core.derived_normalization
    base_change := coh.base_change
    composition := by
      intro U X X' X'' f hf hs hq hU hUc hX hXc hX' hX'c hX'' hX''c c g k
      exact comparison_vComp
        (exactCompactSupportExchangeSquare A c g)
        (exactCompactSupportExchangeSquare A
          (c.ofIsPullback (IsPullback.of_hasPullback g f).flip) k)
        (exactEtaleSumExchangeSquare A f g)
        (exactEtaleSumExchangeSquare A (pullback.fst g f) k)
        (core.comparison f c)
        (core.comparison (pullback.fst g f)
          (c.ofIsPullback (IsPullback.of_hasPullback g f).flip))
        (core.comparison (pullback.fst k (pullback.fst g f))
          ((c.ofIsPullback (IsPullback.of_hasPullback g f).flip).ofIsPullback
            (IsPullback.of_hasPullback k (pullback.fst g f)).flip))
        (coh.base_change f c g)
        (coh.base_change (pullback.fst g f)
          (c.ofIsPullback (IsPullback.of_hasPullback g f).flip) k)
    refinement := coh.refinement
    identity := coh.identity
    adjunction := by
      intro U X f hf hs hU hUc hX hXc c R adj
      exact counitPreservingComparison (core.comparison f c) adj
        (Adjunction.mapDerivedCategoryAdjunction
          (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) f inferInstance))
  }

/-- The canonical compact-support-to-sum normalization, including its degree-zero,
refinement, sum/evaluation adjunction, base-change and identity/composition normalizations.
Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tag 03S6
(blueprint: lem-asd-etale-compact-support-normalization).

Proof:
1. Construct the clopen compactification graph and its actual projection. Transpose the
   inverse specified sum exchange followed by that projection under proper direct image.
   Descend this sheaf transformation degreewise through the localization; the component
   formula is proved on every homotopy representative.
2. The graph sheaf normalization identifies its composite into direct image with the
   canonical graph-extension arrow. The derived graph isomorphism theorem gives the
   uniquely specified inverse. Together they form canonicalEtaleCompactSupportCore.
   For finite etale morphisms the derived isomorphism is proved by sheaf normalization,
   preservation of K-injectives and cancellation of the derived-composition unit.
3. The graph coherence theorem supplies the single-base-change, proper-refinement and
   identity equations for this fixed inverse. Two applications of the single-square
   equation prove the displayed vertical composite by functoriality and associativity.
4. For any chosen compact-support adjunction, conjugate the inverse comparison under it
   and the degreewise sum/evaluation adjunction. The conjugacy counit law proves the
   specified equality. Cancel the invertible comparison and use injectivity of the sum
   adjunction bijection to prove uniqueness of the right-adjoint isomorphism. -/
theorem nonempty_etaleCompactSupportNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    Nonempty (EtaleCompactSupportNormalization A) := by
  exact ⟨canonicalEtaleCompactSupportNormalization A⟩

end AlgebraicGeometry.Etale
