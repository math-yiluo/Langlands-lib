/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.StrictRoosComparison
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.StrictRoosModel

/-!
# Resolution formula for the descended Roos comparison

Source: Stacks Project, Tags 0940 and 0941, and the final paragraph of
literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe uC vC r uD vD s wA wB
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

section Inclusions
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]

private def signedχ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :=
  roosχ X p ≪≫ biprod.braiding _ _ ≪≫
    biprod.mapIso (Iso.refl _) (-Iso.refl _)

private theorem signedιχ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosι X).f (p + 1) ≫ (signedχ X p).hom =
      biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π X.asFunctor (op n))).f (p + 1)) 0 := by
  dsimp only [signedχ, Iso.trans_hom]
  rw [← Category.assoc, ← Category.assoc, roosι_χ]
  apply biprod.hom_ext <;> simp [Category.assoc]

private theorem inclusion_exists
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (U : CochainComplex A ℤ)
    (hU : U = roosF.obj X)
    (χ : ∀ p : ℤ, U.X (p + 1) ≅ (roosP X).X (p + 1) ⊞ (roosP X).X p)
    (hc : ∀ p, (χ p).hom =
      (eqToIso (congrArg (fun V ↦ V.X (p + 1)) hU)).hom ≫ (signedχ X p).hom) :
    ∃ ι : limit X.asFunctor ⟶ U, ∀ p : ℤ, ι.f (p + 1) ≫ (χ p).hom =
      biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π X.asFunctor (op n))).f (p + 1)) 0 := by
  subst U
  refine ⟨roosι X, ?_⟩
  intro p
  simpa only [hc, eqToIso_refl, Iso.refl_hom, Category.id_comp] using signedιχ X p

private theorem inclusion_natural
    (H : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ)
    (χ : ∀ X p, (H.obj X).X (p + 1) ≅ (roosP X).X (p + 1) ⊞ (roosP X).X p)
    (hm : ∀ {X Y} (f : X ⟶ Y) p, (H.map f).f (p + 1) ≫ (χ Y p).hom =
      (χ X p).hom ≫ biprod.map ((roosPmap f).f (p + 1)) ((roosPmap f).f p))
    (ι : ∀ X, limit X.asFunctor ⟶ H.obj X)
    (hi : ∀ X p, (ι X).f (p + 1) ≫ (χ X p).hom =
      biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π X.asFunctor (op n))).f (p + 1)) 0)
    {X Y} (f : X ⟶ Y) : roosLimitFunctor.map f ≫ ι Y = ι X ≫ H.map f := by
  have hprod : roosLimitFunctor.map f ≫
      Pi.lift (fun n : ℕ ↦ limit.π Y.asFunctor (op n)) =
      Pi.lift (fun n : ℕ ↦ limit.π X.asFunctor (op n)) ≫ roosPmap f := by
    apply Pi.hom_ext
    intro n
    dsimp only [roosLimitFunctor, Functor.comp_map]
    simp only [Category.assoc, Pi.lift_comp_π, Pi.map_π, Pi.lift_comp_π_assoc]
    exact limMap_π _ (op n)
  apply HomologicalComplex.Hom.ext
  funext i
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
  apply (cancel_mono (χ Y p).hom).mp
  change ((roosLimitFunctor.map f).f (p + 1) ≫ (ι Y).f (p + 1)) ≫ (χ Y p).hom =
    ((ι X).f (p + 1) ≫ (H.map f).f (p + 1)) ≫ (χ Y p).hom
  simp only [Category.assoc]
  erw [hm f p, hi Y p]
  erw [← Category.assoc, hi X p]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc,
      biprod.lift_fst]
    erw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
    exact congrArg (fun z ↦ z.f (p + 1)) hprod
  · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc,
      biprod.lift_snd, zero_comp, comp_zero]

private def ordinaryLimitIso :
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      roosLimitFunctor (A := A) :=
  Functor.isoWhiskerLeft HomologicalComplex.complexOfFunctorsToFunctorToComplex
    (HomologicalComplex.functorEquivalenceInverseCompMapHomologicalComplexLim
      A (ComplexShape.up ℤ) ℕᵒᵖ)

private theorem limit_unit_iso [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    (R : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ R)
    [R.IsRightDerivedFunctor η (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] : IsIso (η.app I) := by
  have hd : (CochainComplex.KInjectives.localizerMorphism (ℕᵒᵖ ⥤ A)).Derives
      (roosLimitFunctor ⋙ DerivedCategory.Q.{w}) := by
    intro X Y f hf
    have : X.obj.IsKInjective := X.property
    have : Y.obj.IsKInjective := Y.property
    obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp hf
    let L := (lim : (ℕᵒᵖ ⥤ A) ⥤ A)
    have : L.Additive := Functor.additive_of_preserves_binary_products L
    have : QuasiIso ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom) := by
      rw [← he]
      exact (L.mapHomotopyEquiv e).quasiIso_hom
    have hn := (ordinaryLimitIso (A := A)).hom.naturality f.hom
    have eqn : roosLimitFunctor.map f.hom =
        (ordinaryLimitIso (A := A)).inv.app X.obj ≫
          (L.mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom ≫
          (ordinaryLimitIso (A := A)).hom.app Y.obj := by
      simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using
        (congrArg (fun z ↦ (ordinaryLimitIso (A := A)).inv.app X.obj ≫ z) hn).symm
    change IsIso (DerivedCategory.Q.map (roosLimitFunctor.map f.hom))
    rw [eqn, Functor.map_comp, Functor.map_comp]
    infer_instance
  exact hd.isIso_of_isRightDerivedFunctor η (CochainComplex.KInjectives.mk I)

omit [HasCountableProducts A] in
private theorem normalized_unit [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ A)]
    (H : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ)
    (R : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ R)
    (θ : DerivedCategory.Q.{w} ⋙ R ≅ H ⋙ DerivedCategory.Q.{w})
    (ι : ∀ X, limit X.asFunctor ⟶ H.obj X)
    (hin : ∀ {X Y} (f : X ⟶ Y), roosLimitFunctor.map f ≫ ι Y = ι X ≫ H.map f)
    (hn : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] (_ : ∀ p : ℤ, Injective (I.X p)),
      η.app I ≫ θ.hom.app I = DerivedCategory.Q.map (ι I)) :
    ∀ X, η.app X ≫ θ.hom.app X = DerivedCategory.Q.map (ι X) := by
  intro X
  let T := CochainComplex.kInjectiveResolutionFunctor.{v} (ℕᵒᵖ ⥤ A)
  let q : X ⟶ T.obj X := (CochainComplex.toKInjectiveResolution.{v} (ℕᵒᵖ ⥤ A)).app X
  have : QuasiIso q := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ X).2
  have hθ : R.map (DerivedCategory.Q.map q) ≫ θ.hom.app (T.obj X) =
      θ.hom.app X ≫ DerivedCategory.Q.map (H.map q) := θ.hom.naturality q
  have hη : DerivedCategory.Q.map (roosLimitFunctor.map q) ≫ η.app (T.obj X) =
      η.app X ≫ R.map (DerivedCategory.Q.map q) := η.naturality q
  have hq : IsIso (DerivedCategory.Q.map (H.map q)) := by
    have he : DerivedCategory.Q.map (H.map q) =
        θ.inv.app X ≫ R.map (DerivedCategory.Q.map q) ≫ θ.hom.app (T.obj X) := by
      rw [hθ, Iso.inv_hom_id_app_assoc]
    rw [he]
    infer_instance
  apply (cancel_mono (DerivedCategory.Q.map (H.map q))).mp
  have hnT := hn (T.obj X) (fun p ↦ inferInstance)
  calc
    _ = η.app X ≫ R.map (DerivedCategory.Q.map q) ≫ θ.hom.app (T.obj X) := by
      rw [Category.assoc, ← hθ]
    _ = DerivedCategory.Q.map (roosLimitFunctor.map q) ≫
        η.app (T.obj X) ≫ θ.hom.app (T.obj X) := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ z ≫ θ.hom.app (T.obj X)) hη.symm
    _ = _ := by
      erw [hnT]
      exact (DerivedCategory.Q.map_comp _ _).symm.trans
        ((congrArg DerivedCategory.Q.map (hin q)).trans
          (DerivedCategory.Q.map_comp _ _))

private theorem inclusion_unique
    {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {U : CochainComplex A ℤ}
    (χ : ∀ p : ℤ, U.X (p + 1) ≅ (roosP X).X (p + 1) ⊞ (roosP X).X p)
    (f g : limit X.asFunctor ⟶ U)
    (hf : ∀ p, f.f (p + 1) ≫ (χ p).hom =
      biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π X.asFunctor (op n))).f (p + 1)) 0)
    (hg : ∀ p, g.f (p + 1) ≫ (χ p).hom =
      biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π X.asFunctor (op n))).f (p + 1)) 0) : f = g := by
  apply HomologicalComplex.Hom.ext
  funext i
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
  exact (cancel_mono (χ p).hom).mp ((hf p).trans (hg p).symm)

omit [HasLimitsOfShape ℕᵒᵖ A] in
private theorem product_component_ext (T : ℕ → CochainComplex A ℤ) {V : A} (i : ℤ)
    (f g : V ⟶ (∏ᶜ T).X i)
    (h : ∀ n, f ≫ (Pi.π T n).f i = g ≫ (Pi.π T n).f i) : f = g := by
  apply (cancel_mono (piComparison (HomologicalComplex.eval A (ComplexShape.up ℤ) i) T)).mp
  apply Pi.hom_ext
  intro n
  simpa only [Category.assoc, piComparison_comp_π, HomologicalComplex.eval_map] using h n

omit [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A] in
private theorem towerGrothendieck [IsGrothendieckAbelian.{v} A] :
    IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ A) := by
  have ht (K : Type v) [SmallCategory K] : IsGrothendieckAbelian.{v} (K ⥤ A) := by
    let G := separator A
    have hG := isSeparator_separator A
    have hS : ObjectProperty.IsSeparating
        (.ofObj fun j : K ↦ (evaluationLeftAdjoint A j).obj G) := by
      intro F F' f g hfg
      apply NatTrans.ext
      funext j
      apply hG.def
      intro a
      let adj := evaluationAdjunctionRight A j
      apply (adj.homEquiv G F').symm.injective
      have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
      exact (adj.homEquiv_naturality_right_symm a f).trans
        (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
    let : HasSeparator (K ⥤ A) := ⟨_, hS.isSeparator_coproduct⟩
    let : HasFilteredColimitsOfSize.{v, v} (K ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
    let : AB5OfSize.{v, v} (K ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
    exact {}
  let : IsGrothendieckAbelian.{v} (AsSmall.{v} ℕᵒᵖ ⥤ A) := ht (AsSmall.{v} ℕᵒᵖ)
  exact IsGrothendieckAbelian.of_equivalence
    (Equivalence.congrLeft (AsSmall.equiv : ℕᵒᵖ ≌ AsSmall.{v} ℕᵒᵖ).symm)

end Inclusions

-- The simultaneous cone and localization comparisons require extra elaboration steps.
/-- The resolution formula for a fixed comparison satisfying the localization square.

Source: Stacks Project, Tags 0940 and 0941, and the final paragraph of
literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md.
(auxiliary; not a blueprint node).

Proof in words:
Construct the signed inclusion of the ordinary limit into the Roos cone, with
coordinates (limit projections, zero), and prove its naturality by product projections.
Functorial K-injective resolutions with injective tower terms extend the assumed
normalization eta theta = Q(iota) to every complex: apply naturality and cancel
Q(H(q)), which is invertible by theta. The two coordinate equations for kappa and
the projection equations for beta give F(iotaA) kappa = beta iotaB. Apply Q and
the prescribed square to obtain the derived-unit comparison at every complex.
On K-injectives the derived units are isomorphisms, by the K-injective derivability
structure: quasi-isomorphisms between K-injectives are homotopy equivalences,
and the additive ordinary-limit functor preserves those homotopies. Define dI
and dJ from these units and the inverses of LA(Qq) and LB(Qr). Naturality of
lambda, the localization comparison, and etaB gives the required resolution formula.
This proves only the resolution formula for the already fixed lambda; it does
not construct lambda or prove its localization square. -/
theorem exactProductFunctorRoosResolution
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    {D : Type uD} [Category.{vD} D] (K : GrothendieckTopology D)
    [HasSheafify K AddCommGrpCat.{max uD vD s}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max uD vD s}]
    (S : Sheaf K RingCat.{max uD vD s})
    (_hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (_hS : ∀ (U : Dᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uD vD s} S)]
    [HasDerivedCategory.{wA} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wB} (ringedSiteModules.{max uD vD s} S)]
    [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S)]
    (F : ringedSiteModules.{max uC vC r} R ⥤ ringedSiteModules.{max uD vD s} S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (_hphi : ∀ (M : ℕ → ringedSiteModules.{max uC vC r} R), IsIso (piComparison F M))
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤ DerivedCategory.{wA}
      (ringedSiteModules.{max uC vC r} R))
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ⥤ DerivedCategory.{wB}
      (ringedSiteModules.{max uD vD s} S))
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ) ⥤ CochainComplex
        (ringedSiteModules.{max uC vC r} R) ℤ) ⋙ DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙
        LA)
    (_hLA : LA.IsRightDerivedFunctor etaA
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) (ComplexShape.up ℤ)))
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max uD vD s} S) ℤ) ⥤ CochainComplex
        (ringedSiteModules.{max uD vD s} S) ℤ) ⋙ DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙
        LB)
    (_hLB : LB.IsRightDerivedFunctor etaB
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) (ComplexShape.up ℤ)))
    (HA : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ ⥤ CochainComplex
      (ringedSiteModules.{max uC vC r} R) ℤ) (HB : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD
      vD s} S) ℤ ⥤ CochainComplex (ringedSiteModules.{max uD vD s} S) ℤ)
      (hAobj : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ, HA.obj X =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (X).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (hBobj : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ, HB.obj X =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (X).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (chiA : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (p : ℤ), (HA.obj
        X).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (X).asFunctor.obj (op n))).X p)
      (chiB : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ) (p : ℤ), (HB.obj
        X).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (X).asFunctor.obj (op n))).X p)
      (thetaA : DerivedCategory.Q.{wA} ⋙ LA ≅ HA ⋙ DerivedCategory.Q.{wA})
      (thetaB : DerivedCategory.Q.{wB} ⋙ LB ≅ HB ⋙ DerivedCategory.Q.{wB})
      (_psi : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op
        n))) ≅ (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X).asFunctor.obj (op n))))
      (kappa : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (HA.obj X) ≅ HB.obj
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        X))
      (beta : ∀ I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (limit I.asFunctor) ≅ limit
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        I).asFunctor)
    (hcoord :
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (p : ℤ), (chiA X p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ ↦ V.X (p +
          1)) (hAobj X))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ) (p : ℤ), (chiB X p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (ringedSiteModules.{max uD vD s} S) ℤ ↦ V.X (p +
          1)) (hBobj X))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)))
    (hmaps :
      (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ} (f : X ⟶ Y) (p : ℤ),
        (HA.map f).f (p + 1) ≫ (chiA Y p).hom = (chiA X p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)) ∧
      (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ} (f : X ⟶ Y) (p : ℤ),
        (HB.map f).f (p + 1) ≫ (chiB Y p).hom = (chiB X p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)))
    (hnorm :
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) [I.IsKInjective] (_hIinj :
        ∀ p : ℤ, Injective (I.X p)),
        ∃ iota : limit I.asFunctor ⟶ HA.obj I,
          QuasiIso iota ∧
          (∀ p : ℤ, iota.f (p + 1) ≫ (chiA I p).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          etaA.app I ≫ thetaA.hom.app I = DerivedCategory.Q.{wA}.map iota) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ) [I.IsKInjective] (_hIinj :
        ∀ p : ℤ, Injective (I.X p)),
        ∃ iota : limit I.asFunctor ⟶ HB.obj I,
          QuasiIso iota ∧
          (∀ p : ℤ, iota.f (p + 1) ≫ (chiB I p).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          etaB.app I ≫ thetaB.hom.app I = DerivedCategory.Q.{wB}.map iota))
    (hkappa :
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (p : ℤ) (n : ℕ),
        (kappa X).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n).f (p + 1) =
          F.map ((chiA X p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (p + 1)) ∧
        (kappa X).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n).f p =
          F.map ((chiA X p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f p)))
    (_hknat :
      (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ}
        (f : X ⟶ Y),
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (HA.map f) ≫ (kappa Y).hom =
          (kappa X).hom ≫ HB.map
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).map f)))
    (hbeta :
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (n : ℕ), (beta I).hom ≫
        limit.π ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
        ℤ)).obj I).asFunctor (op n) =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (limit.π I.asFunctor (op n))))
    (lambda : LA ⋙ F.mapDerivedCategory ≅ (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun
        _ _ _ ↦ inferInstance⟩)) ⋙ LB)
    (hsquare : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ,
        (F.mapDerivedCategory).map (thetaA.hom.app X) ≫ F.mapDerivedCategoryFactors.hom.app (HA.obj
          X) ≫
            DerivedCategory.Q.{wB}.map (kappa X).hom =
          lambda.hom.app (DerivedCategory.Q.{wA}.obj X) ≫
            LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
              ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
              inferInstance⟩)).hom.app X) ≫
            thetaB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X)) :
    ∀ (X I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (q : X ⟶ I) [QuasiIso q]
        [I.IsKInjective]
        (Jt : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ) (r :
          (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          I ⟶ Jt) [QuasiIso r] [Jt.IsKInjective],
        ∃ (dI : DerivedCategory.Q.{wA}.obj (limit I.asFunctor) ≅ LA.obj (DerivedCategory.Q.{wA}.obj
          X))
          (dJ : DerivedCategory.Q.{wB}.obj (limit Jt.asFunctor) ≅ LB.obj (DerivedCategory.Q.{wB}.obj
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
            ℤ)).obj I))),
          dI.hom ≫ LA.map (DerivedCategory.Q.{wA}.map q) = etaA.app I ∧
          dJ.hom ≫ LB.map (DerivedCategory.Q.{wB}.map r) = etaB.app Jt ∧
          (F.mapDerivedCategory).map dI.hom ≫ lambda.hom.app (DerivedCategory.Q.{wA}.obj X) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app X) ≫
              LB.map (DerivedCategory.Q.{wB}.map ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                F).mapHomologicalComplex (ComplexShape.up ℤ)).map q)) =
            F.mapDerivedCategoryFactors.hom.app (limit I.asFunctor) ≫
              DerivedCategory.Q.{wB}.map (beta I).hom ≫
              DerivedCategory.Q.{wB}.map (lim.map
                (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map r)) ≫ dJ.hom := by
  classical
  have : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let A := ringedSiteModules.{max uC vC r} R
  let B := ringedSiteModules.{max uD vD s} S
  have : IsGrothendieckAbelian.{max uC vC r} A :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{uC, vC, max uC vC r, 0} J R
  have : IsGrothendieckAbelian.{max uD vD s} B :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{uD, vD, max uD vD s, 0} K S
  have : IsGrothendieckAbelian.{max uC vC r} (ℕᵒᵖ ⥤ A) := towerGrothendieck (A := A)
  have : IsGrothendieckAbelian.{max uD vD s} (ℕᵒᵖ ⥤ B) := towerGrothendieck (A := B)
  let Fc := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let Ftw := (Functor.whiskeringRight ℕᵒᵖ _ _).obj F
  let Ft := Ftw.mapHomologicalComplex (ComplexShape.up ℤ)
  let FD := F.mapDerivedCategory
  let TD := Ftw.mapDerivedCategory
  have hcA X p : (chiA X p).hom =
      (eqToIso (congrArg (fun V ↦ V.X (p + 1)) (hAobj X))).hom ≫
        (signedχ X p).hom := by
    simpa [signedχ, roosχ, Category.assoc] using hcoord.1 X p
  have hcB X p : (chiB X p).hom =
      (eqToIso (congrArg (fun V ↦ V.X (p + 1)) (hBobj X))).hom ≫
        (signedχ X p).hom := by
    simpa [signedχ, roosχ, Category.assoc] using hcoord.2 X p
  choose ιA hiA using fun X ↦ inclusion_exists X (HA.obj X) (hAobj X) (chiA X) (hcA X)
  choose ιB hiB using fun X ↦ inclusion_exists X (HB.obj X) (hBobj X) (chiB X) (hcB X)
  have hnA {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) :
      roosLimitFunctor.map f ≫ ιA Y = ιA X ≫ HA.map f :=
    inclusion_natural HA chiA hmaps.1 ιA hiA f
  have hnB {X Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} (f : X ⟶ Y) :
      roosLimitFunctor.map f ≫ ιB Y = ιB X ≫ HB.map f :=
    inclusion_natural HB chiB hmaps.2 ιB hiB f
  have huA : ∀ X, etaA.app X ≫ thetaA.hom.app X = DerivedCategory.Q.map (ιA X) := by
    apply normalized_unit HA LA etaA thetaA ιA hnA
    intro I hI hinj
    obtain ⟨ι, _, hc, hu⟩ := hnorm.1 I hinj
    have he : ι = ιA I := inclusion_unique (chiA I) ι (ιA I) hc (hiA I)
    simpa only [he] using hu
  have huB : ∀ X, etaB.app X ≫ thetaB.hom.app X = DerivedCategory.Q.map (ιB X) := by
    apply normalized_unit HB LB etaB thetaB ιB hnB
    intro I hI hinj
    obtain ⟨ι, _, hc, hu⟩ := hnorm.2 I hinj
    have he : ι = ιB I := inclusion_unique (chiB I) ι (ιB I) hc (hiB I)
    simpa only [he] using hu
  have hι (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      Fc.map (ιA I) ≫ (kappa I).hom = (beta I).hom ≫ ιB (Ft.obj I) := by
    apply HomologicalComplex.Hom.ext
    funext i
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
    apply (cancel_mono (chiB (Ft.obj I) p).hom).mp
    apply biprod.hom_ext
    · apply product_component_ext _ (p + 1)
      intro n
      dsimp only [HomologicalComplex.comp_f, Fc, Functor.mapHomologicalComplex_map_f]
      change (F.map ((ιA I).f (p + 1)) ≫ (kappa I).hom.f (p + 1)) ≫
          (chiB (Ft.obj I) p).hom ≫ biprod.fst ≫ _ =
        ((beta I).hom.f (p + 1) ≫ (ιB (Ft.obj I)).f (p + 1)) ≫
          (chiB (Ft.obj I) p).hom ≫ biprod.fst ≫ _
      simp only [Category.assoc]
      erw [(hkappa I p n).1]
      rw [← F.map_comp]
      simp only [← Category.assoc, hiA, hiB]
      simp only [Category.assoc, biprod.lift_fst_assoc]
      have hπA := congrArg (fun z ↦ z.f (p + 1))
        (Pi.lift_comp_π (fun n : ℕ ↦ limit.π I.asFunctor (op n)) n)
      have hπB := congrArg (fun z ↦ z.f (p + 1))
        (Pi.lift_comp_π (fun n : ℕ ↦ limit.π (Ft.obj I).asFunctor (op n)) n)
      simp only [HomologicalComplex.comp_f] at hπA hπB
      erw [hπA, hπB]
      exact (congrArg (fun z ↦ z.f (p + 1)) (hbeta I n)).symm
    · apply product_component_ext _ p
      intro n
      dsimp only [HomologicalComplex.comp_f, Fc, Functor.mapHomologicalComplex_map_f]
      change (F.map ((ιA I).f (p + 1)) ≫ (kappa I).hom.f (p + 1)) ≫
          (chiB (Ft.obj I) p).hom ≫ biprod.snd ≫ _ =
        ((beta I).hom.f (p + 1) ≫ (ιB (Ft.obj I)).f (p + 1)) ≫
          (chiB (Ft.obj I) p).hom ≫ biprod.snd ≫ _
      simp only [Category.assoc]
      erw [(hkappa I p n).2]
      rw [← F.map_comp]
      simp only [← Category.assoc, hiA, hiB]
      simp [Category.assoc]
  have hunit (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      FD.map (etaA.app I) ≫ lambda.hom.app (DerivedCategory.Q.obj I) ≫
        LB.map (Ftw.mapDerivedCategoryFactors.hom.app I) =
      F.mapDerivedCategoryFactors.hom.app (limit I.asFunctor) ≫
        DerivedCategory.Q.map (beta I).hom ≫ etaB.app (Ft.obj I) := by
    apply (cancel_mono (thetaB.hom.app (Ft.obj I))).mp
    calc
      _ = FD.map (etaA.app I ≫ thetaA.hom.app I) ≫
          F.mapDerivedCategoryFactors.hom.app (HA.obj I) ≫
          DerivedCategory.Q.map (kappa I).hom := by
        rw [Functor.map_comp]
        simpa only [Category.assoc] using congrArg (fun z ↦ FD.map (etaA.app I) ≫ z)
          (hsquare I).symm
      _ = F.mapDerivedCategoryFactors.hom.app (limit I.asFunctor) ≫
          DerivedCategory.Q.map (Fc.map (ιA I) ≫ (kappa I).hom) := by
        rw [huA, F.mapDerivedCategoryFactors_hom_naturality_assoc]
        rw [Functor.map_comp]
      _ = _ := by rw [hι, Functor.map_comp]; simp only [Category.assoc, huB]
  intro X I q hq hI Jt r hr hJt
  have : IsIso (etaA.app I) := limit_unit_iso LA etaA I
  have : IsIso (etaB.app Jt) := limit_unit_iso LB etaB Jt
  let dI : DerivedCategory.Q.obj (limit I.asFunctor) ≅ LA.obj (DerivedCategory.Q.obj X) :=
    asIso (etaA.app I) ≪≫ (asIso (LA.map (DerivedCategory.Q.map q))).symm
  let dJ : DerivedCategory.Q.obj (limit Jt.asFunctor) ≅
      LB.obj (DerivedCategory.Q.obj (Ft.obj I)) :=
    asIso (etaB.app Jt) ≪≫ (asIso (LB.map (DerivedCategory.Q.map r))).symm
  have hdI : dI.hom ≫ LA.map (DerivedCategory.Q.map q) = etaA.app I := by simp [dI]
  have hdJ : dJ.hom ≫ LB.map (DerivedCategory.Q.map r) = etaB.app Jt := by simp [dJ]
  refine ⟨dI, dJ, hdI, hdJ, ?_⟩
  have hnat := lambda.hom.naturality (DerivedCategory.Q.map q)
  have hfac := Ftw.mapDerivedCategoryFactors.hom.naturality q
  dsimp only [Functor.comp_map] at hnat hfac
  calc
    _ = FD.map (etaA.app I) ≫ lambda.hom.app (DerivedCategory.Q.obj I) ≫
        LB.map (Ftw.mapDerivedCategoryFactors.hom.app I) := by
      erw [← LB.map_comp, ← hfac, LB.map_comp, ← reassoc_of% hnat,
        ← FD.map_comp_assoc, hdI]
    _ = F.mapDerivedCategoryFactors.hom.app (limit I.asFunctor) ≫
        DerivedCategory.Q.map (beta I).hom ≫ etaB.app (Ft.obj I) := hunit I
    _ = _ := by
      apply (cancel_mono (LB.map (DerivedCategory.Q.map r))).mp
      simp only [Category.assoc, hdJ]
      exact congrArg (fun z ↦ F.mapDerivedCategoryFactors.hom.app (limit I.asFunctor) ≫
        DerivedCategory.Q.map (beta I).hom ≫ z) (etaB.naturality r).symm

end CategoryTheory
