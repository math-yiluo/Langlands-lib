/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleLevelData
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectChartEtaleOrigin
import WeilConjectures.ConstructibleSheaf.InternalHom
import WeilConjectures.SixFunctors.Etale.Derived.Stability.TorSheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-! # Descent of one finite perfect quotient and its geometric fibre

Source: Stacks Project, Tag 09C6, the construction of L_n and its algebraic fibre;
Tags 09AL, 09B1 and 03Q3.
(blueprint: lem-weil-pbc-finite-perfect-adic-etale-level-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite ZeroObject
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Exactness of the coefficient universe lift before passing to derived categories. -/
private theorem algebraLift_exact (B : Type t) [CommRing B] :
    let S := ModuleCat.uliftFunctor.{t + 1, t} B ⋙
      ModuleCat.restrictScalars.{t + 1}
        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
    PreservesFiniteLimits S ∧ PreservesFiniteColimits S := by
  have : (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B)).isEquivalence_functor
  have : PreservesLimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom) :=
    Adjunction.isEquivalencePreservesLimits _
  have : PreservesColimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom) :=
    Adjunction.isEquivalence_preservesColimits _
  exact ⟨inferInstance, inferInstance⟩

/-- Cohomology and bounds of a constant bounded finite-projective complex. -/
private theorem constantPerfect_cohomology (Y : Scheme.{t})
    (B : Type t) [CommRing B] [Finite B]
    (P : CochainComplex (ModuleCat.{t} B) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hP : ∀ i : ℤ, Module.Projective B (P.X i) ∧ Module.Finite B (P.X i)) :
    let C := constantSheaf Y.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1} B))
    let K := C.mapDerivedCategory.obj
      ((finitePerfectAdicAlgebraLift B).obj (DerivedCategory.Q.obj P))
    (∀ q : ℤ, q < a ∨ b < q → IsZero
      ((DerivedCategory.homologyFunctor _ q).obj K)) ∧
    ∀ q : ℤ, IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor _ q).obj K) := by
  let S := ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
  have := (algebraLift_exact B).1
  have := (algebraLift_exact B).2
  let C := constantSheaf Y.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1} B))
  have hperfect : DerivedCategory.IsPerfect (DerivedCategory.Q.obj P) :=
    ⟨P, a, b, ha, hb, hP, ⟨Iso.refl _⟩⟩
  have hzero (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (DerivedCategory.Q.obj P)) := by
    rcases hq with hq | hq
    · exact DerivedCategory.isZero_of_isGE _ a q hq
    · exact DerivedCategory.isZero_of_isLE _ b q hq
  refine ⟨fun q hq ↦ ?_, fun q ↦ ?_⟩
  · exact C.isZero_homologyFunctor_mapDerivedCategory_obj
      (S.isZero_homologyFunctor_mapDerivedCategory_obj (hzero q hq))
  · have := hperfect.finite_homology q
    have : Finite ((DerivedCategory.homologyFunctor (ModuleCat.{t} B) q).obj
        (DerivedCategory.Q.obj P)) := Module.finite_of_finite B
    let H := S.obj ((DerivedCategory.homologyFunctor _ q).obj (DerivedCategory.Q.obj P))
    have : Finite H := inferInstanceAs (Finite (ULift.{t + 1}
      ((DerivedCategory.homologyFunctor (ModuleCat.{t} B) q).obj (DerivedCategory.Q.obj P))))
    have : Module.Finite (ULift.{t + 1} B) H := Module.Finite.of_finite
    have : ∀ (U : Y.Etale) (Q : (Over U)ᵒᵖ ⥤ ModuleCat.{t + 1} (ULift.{t + 1} B)),
        (Over.forget U).op.HasPointwiseRightKanExtension Q := by
      intro U Q Z
      have : EssentiallySmall.{t + 1} (StructuredArrow Z (Over.forget U).op) :=
        essentiallySmallSelf.{0} _
      have : HasLimitsOfShape (StructuredArrow Z (Over.forget U).op)
          (ModuleCat.{t + 1} (ULift.{t + 1} B)) :=
        hasLimitsOfShape_of_essentiallySmall.{t + 1} _ _
      exact HasLimitsOfShape.has_limit _
    have : IsFiniteLocallyConstantSheaf (C.obj H) :=
      { toIsLocallyConstantSheaf :=
          (Sheaf.isConstant_of_iso _ (Iso.refl _)).isLocallyConstantSheaf
        toIsFiniteSheaf := isFiniteSheaf_constantSheaf H }
    have : IsFiniteLocallyConstantSheaf (C.obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{t} B) q ⋙ S).obj
          (DerivedCategory.Q.obj P))) := inferInstanceAs
      (IsFiniteLocallyConstantSheaf (C.obj H))
    exact IsFiniteLocallyConstantSheaf.of_iso
      (C.mapIso ((S.mapDerivedCategoryHomologyFunctorIso q).app
        (DerivedCategory.Q.obj P)) ≪≫
        (C.mapDerivedCategoryHomologyFunctorIso q).app
          (S.mapDerivedCategory.obj (DerivedCategory.Q.obj P)))

/-- Pull a supplied constant model to a further chart. -/
private def pull_constant_model (Y U W : Scheme.{t}) (B : Type (t + 1)) [CommRing B]
    (f : U ⟶ Y) (g : W ⟶ U)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} B)))
    (E : DerivedCategory (ModuleCat.{t + 1} B))
    (e : (AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} B) f).mapDerivedCategory.obj K ≅
      (constantSheaf U.smallEtaleTopology (ModuleCat.{t + 1} B)).mapDerivedCategory.obj E) :
    (AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} B)
      (g ≫ f)).mapDerivedCategory.obj K ≅
      (constantSheaf W.smallEtaleTopology (ModuleCat.{t + 1} B)).mapDerivedCategory.obj E :=
  (Functor.mapDerivedCategoryNatIso
    (AlgebraicGeometry.Etale.upperStarComp (ModuleCat.{t + 1} B) g f)).app K ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm.app K ≪≫
    (AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} B) g).mapDerivedCategory.mapIso e ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).app E ≪≫
    (Functor.mapDerivedCategoryNatIso
      (upperStarConstantSheafIso (ModuleCat.{t + 1} B) g)).app E

/-- The stalk of a locally supplied constant model, at a specified lifted geometric point. -/
private def stalk_constant_model
    (Y U : Scheme.{t}) (B : Type (t + 1)) [CommRing B]
    (f : U ⟶ Y) (y : Y)
    (s : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ U)
    (hs : s ≫ f = Y.algClosurePoint y)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} B)))
    (E : DerivedCategory (ModuleCat.{t + 1} B))
    (e : (AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} B) f).mapDerivedCategory.obj K ≅
      (constantSheaf U.smallEtaleTopology (ModuleCat.{t + 1} B)).mapDerivedCategory.obj E) :
    (finitePerfectAdicEtaleStalk Y B y).obj K ≅ E := by
  let Φ := (pointSmallEtale s).ulift.{t + 1}
  let S := Φ.sheafFiber (A := ModuleCat.{t + 1} B)
  have : S.Additive := Functor.additive_of_preserves_binary_products _
  let C := constantSheaf U.smallEtaleTopology (ModuleCat.{t + 1} B)
  have : ((pointSmallEtale (s ≫ f)).ulift.{t + 1}).sheafFiber
      (A := ModuleCat.{t + 1} B) |>.Additive :=
    Functor.additive_of_preserves_binary_products _
  let d := (Functor.mapDerivedCategoryNatIso
    (AlgebraicGeometry.Etale.upperStarCompUliftSheafFiberIso (ModuleCat.{t + 1} B) f s)).app K
  have d' : (finitePerfectAdicEtaleStalk Y B y).obj K ≅
      S.mapDerivedCategory.obj
        ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} B) f).mapDerivedCategory.obj K) := by
    simpa only [hs, finitePerfectAdicEtaleStalk, uliftPointSmallEtale, S, Φ,
      Functor.comp_obj] using
      d.symm ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm.app K
  exact d' ≪≫ S.mapDerivedCategory.mapIso e ≪≫
    (Functor.mapDerivedCategoryCompIso C S).app E ≪≫
    (Functor.mapDerivedCategoryNatIso
      (Φ.constantSheafCompSheafFiberIso U.smallEtaleTopology (ModuleCat.{t + 1} B))).app E ≪≫
    (Functor.mapDerivedCategoryIdIso (ModuleCat.{t + 1} B)).app E

/-- One finite quotient with etale local perfect constant models descends to an etale
complex, and its geometric fibre at the specified point has a perfect small model.
There is no consecutive scalar-extension assertion and no choice of a cover here.

Source: Stacks Project, proetale.tex, lemma-connected-adic-lisse (Tag 09C6), the
construction of L_n; lemma-compare-constructible-derived (Tag 09AL), and Tag 09B1.
(blueprint: lem-weil-pbc-finite-perfect-adic-etale-level-descent).

Proof: use the weakly etale slice equivalence on V and transport coefficients through
phi_n. The given finite-projective constant models imply bounded finite locally
constant cohomology, with the specified interval. Finite-ring constructible derived
origin descends this single quotient to an etale complex L. Exact cohomology comparison
reflects the interval and finite local constancy. Lift the geometric point at v to a
member of the model covering. Exact geometric stalk and the constant-stalk comparison
identify the stalk of L with the universe lift of that member's finite-projective
complex P. Set the small algebraic object to Q(P); its bounded projective representative
proves perfectness. For a supplied constant-model isomorphism on U, apply finite
coefficient inverse image and its constant-realization comparison. Compose with the
descent isomorphism for the actual quotient, then restrict along W. This construction
works for every supplied algebraic F, and asserts no local trivialization by itself.
Zero rings and zero complexes are included; the chosen point ensures the chart is
nonempty, but neither connectedness nor a neighboring coefficient level is required. -/
theorem finitePerfectAdic_etale_level_descent
    (X : Scheme.{t}) [IsLocallyNoetherian X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n))
    (M : DerivedCategory (CompletedAdicModules X d))
    (V : X.Etale) (v : V.left) (n : ℕ) (a b : ℤ) (hab : a ≤ b)
    (hmodel : FinitePerfectModelsOn X d φ M n V a b) :
    Nonempty (FinitePerfectAdicEtaleLevelData X d φ M V v n) := by
  classical
  have : Finite (A ⧸ d.ideal ^ (n + 1)) := d.quotientFinite n
  let B := A ⧸ d.ideal ^ (n + 1)
  let K := (completedAdicQuotientReduction X d n).obj M
  obtain ⟨T, hT, hTmodel⟩ := hmodel
  have hmodel' : ∀ (W : X.Etale) (g : W ⟶ V), T g →
        ∃ P : CochainComplex (ModuleCat.{t} B) ℤ,
          P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ i : ℤ, Module.Projective B (P.X i) ∧ Module.Finite B (P.X i)) ∧
          Nonempty
            (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
                ((toProEt X).obj W) K ≅
              ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
                ((toProEt X).obj W) ((completedAdicDerivedChange X (φ n)).obj
                  ((finitePerfectAdicDerivedConstant X B).obj (DerivedCategory.Q.obj P)))) := by
    intro W g hg
    obtain ⟨P, ha, hb, hP, ⟨e⟩⟩ := hTmodel W g hg
    have := (finitePerfectAdicConstant_exact X B).1
    have := (finitePerfectAdicConstant_exact X B).2.1
    have := (finitePerfectAdicConstant_exact X B).2.2
    have := (ringedOverFunctor_exactGeneral (completedAdicFiniteRing X d n)
      ((toProEt X).obj W)).1
    have := (ringedOverFunctor_exactGeneral (completedAdicFiniteRing X d n)
      ((toProEt X).obj W)).2.1
    have := (ringedOverFunctor_exactGeneral (completedAdicFiniteRing X d n)
      ((toProEt X).obj W)).2.2
    let R := ringedDerivedRestrictionGeneral (completedAdicFiniteRing X d n)
      ((toProEt X).obj W)
    let c := (finitePerfectAdicConstant X B).mapDerivedCategoryFactors.app P
    -- The representative-based restriction and the exact derived functor agree.
    let r (J : DerivedCategory (SheafOfModules.{t + 1}
        (completedAdicFiniteRing X d n))) :
        R.obj J ≅ ringedSiteDerivedRestrictionOfUniverses
          (completedAdicFiniteRing X d n) ((toProEt X).obj W) J :=
      R.mapIso (DerivedCategory.Q.objObjPreimageIso J).symm ≪≫
        (SheafOfModules.overFunctor (completedAdicFiniteRing X d n)
          ((toProEt X).obj W)).mapDerivedCategoryFactors.app _
    refine ⟨P, ha, hb, hP, ⟨e ≪≫ ?_⟩⟩
    exact (r _).symm ≪≫
      R.mapIso ((completedAdicDerivedChange X (φ n)).mapIso c.symm) ≪≫ r _
  obtain ⟨L, hL⟩ := finitePerfectChart_etale_origin X B
    (completedAdicFiniteCommRing X d n) (φ n) (hφ n) K V a b hab ⟨T, hT, hmodel'⟩
  have hx (x : V.left) : ∃ (W : X.Etale) (g : W ⟶ V),
      T g ∧ ∃ w : W.left, g.left w = x :=
    (mem_smallEtaleTopology_iff T).mp hT x
  choose W g hg w hw using hx
  have hmodels (x : V.left) : ∃ P : CochainComplex (ModuleCat.{t} B) ℤ,
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Projective B (P.X i) ∧ Module.Finite B (P.X i)) ∧
      Nonempty
        ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B))
            (g x).left).mapDerivedCategory.obj L ≅
          (constantSheaf (W x).left.smallEtaleTopology
            (ModuleCat.{t + 1} (ULift.{t + 1} B))).mapDerivedCategory.obj
              ((finitePerfectAdicAlgebraLift B).obj (DerivedCategory.Q.obj P))) := by
    obtain ⟨P, ha, hb, hP, e⟩ := hmodel' (W x) (g x) (hg x)
    exact ⟨P, ha, hb, hP, (hL (W x) (g x) (DerivedCategory.Q.obj P)).mpr e⟩
  choose P ha hb hP eP using hmodels
  let 𝒰 : Cover.{t} etalePrecoverage V.left :=
    Cover.mkOfCovers V.left (fun x ↦ (W x).left) (fun x ↦ (g x).left)
      (fun x ↦ ⟨x, w x, hw x⟩) (fun x ↦ inferInstance)
  let H (q : ℤ) := (DerivedCategory.homologyFunctor
    (Sheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1} B))) q).obj L
  let c (x : V.left) (q : ℤ) :=
    ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B))
      (g x).left).mapDerivedCategoryHomologyFunctorIso q).app L ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso (eP x).some
  have hbounded (q : ℤ) (hq : q < a ∨ b < q) : IsZero (H q) := by
    have hz (x : V.left) : IsZero
        ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B))
          (g x).left).obj (H q)) :=
      (((constantPerfect_cohomology (W x).left B (P x) a b
        (ha x) (hb x) (hP x)).1 q hq).of_iso (c x q))
    have : IsIso (0 : H q ⟶ 0) :=
      AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map_of_cover 𝒰 _ fun x ↦ by
        exact isIso_of_source_target_iso_zero _ (hz x).isoZero
          ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B))
            (g x).left).map_isZero (isZero_zero _)).isoZero
    exact (isZero_zero _).of_iso (asIso (0 : H q ⟶ 0))
  have hlisse (q : ℤ) : IsFiniteLocallyConstantSheaf (H q) := by
    have (x : V.left) : IsFiniteLocallyConstantSheaf
        ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B))
          (g x).left).obj (H q)) := by
      have := (constantPerfect_cohomology (W x).left B
        (P x) a b (ha x) (hb x) (hP x)).2 q
      exact IsFiniteLocallyConstantSheaf.of_iso (c x q).symm
    have : ∀ i : 𝒰.I₀, IsFiniteLocallyConstantSheaf
        ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B))
          (𝒰.f i)).obj (H q)) := fun i ↦ inferInstanceAs
      (IsFiniteLocallyConstantSheaf
        ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} B))
          (g i).left).obj (H q)))
    exact IsFiniteLocallyConstantSheaf.of_cover 𝒰 (H q)
  obtain ⟨i, s, hs⟩ := 𝒰.exists_comp_eq_of_isSepClosed (V.left.algClosurePoint v)
  refine ⟨{ level := L
            bounded := ⟨a, b, hbounded⟩
            lisse := hlisse
            algebra := DerivedCategory.Q.obj (P i)
            perfect := ⟨P i, a, b, ha i, hb i, hP i, ⟨Iso.refl _⟩⟩
            stalk := ⟨stalk_constant_model V.left (W i).left _ (g i).left v s hs
              L _ (eP i).some⟩
            transport := ?_ }⟩
  intro U F ⟨e⟩ Z j
  let k : Z ⟶ V := MorphismProperty.Over.homMk (j.left ≫ U.hom) (by
    rw [Category.assoc]
    exact MorphismProperty.Over.w j)
  exact (hL Z k F).mp ⟨pull_constant_model V.left U.left Z.left _ U.hom j.left
    L ((finitePerfectAdicAlgebraLift B).obj F) e⟩

end AlgebraicGeometry.Scheme
