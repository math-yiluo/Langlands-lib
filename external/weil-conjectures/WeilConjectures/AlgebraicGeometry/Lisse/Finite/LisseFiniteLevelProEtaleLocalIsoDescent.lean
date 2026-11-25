/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerEtaleDescentData
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingDerivedLocalConstancy
import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import WeilConjectures.ConstructibleSheaf.InternalHom

/-! # Geometric descent of a local fixed-realization isomorphism

## Implementation details

The boundedness and finite local constancy hypotheses on `D` in
`exists_proetale_local_iso_section_of_fixed_realization_local_model` are essential: independent
quadratic local systems in infinitely many degrees over `Spec ℚ` become constant on a pro-étale
cover but have no common étale trivializing neighbourhood.

## References

* Stacks Project, Tags 099Y, 099Z, 09B1 and 09BV
* Tag 094G
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow lisseTowerFixedRealization

private theorem comparison_cover_lift
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {V : T.ProEt} (R : Sieve V) (hR : R ∈ ProEt.topology T V)
    (v : Spec (.of Ω) ⟶ V.left) :
    ∃ (W : T.ProEt) (g : W ⟶ V) (_ : R g) (w : Spec (.of Ω) ⟶ W.left),
      w ≫ g.left = v := by
  obtain ⟨S, hS, hSR⟩ := ProEt.mem_topology_iff.1 hR
  obtain ⟨ι, Z, f, rfl⟩ := S.exists_eq_ofArrows
  have hS' : Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage V.left := by
    simpa only [ProEt.mem_precoverage_iff, Presieve.map_ofArrows,
      Functor.comp_obj, Functor.comp_map, ProEt.forget, MorphismProperty.Over.forget,
      MorphismProperty.Comma.forget, Over.forget, Comma.fst] using hS
  have hb := Precoverage.mem_coverings_of_isPullback (fun i ↦ (f i).left) hS' v
    (fun i ↦ pullback.snd (f i).left v) (fun i ↦ pullback.fst (f i).left v)
    (fun i ↦ (IsPullback.of_hasPullback (f i).left v).flip)
  obtain ⟨i, z, hz⟩ :=
    ((ofArrows_mem_precoverage_iff _).1 (propQCPrecoverage_le_precoverage _ hb)).1
      (IsLocalRing.closedPoint Ω)
  have : WeaklyEtale (f i).left :=
    ((ofArrows_mem_precoverage_iff _).1 (propQCPrecoverage_le_precoverage _ hS')).2 i
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale
    (pullback.snd (f i).left v) z
  refine ⟨Z i, f i, hSR _ _ ⟨i⟩, σ ≫ pullback.fst (f i).left v, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]

private noncomputable def comparisonPoint
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) : (ProEt.topology T).Point.{u + 1} where
  fiber := (ProEt.forget T ⋙ coyoneda.obj (op (Over.mk t))) ⋙ uliftFunctor.{u + 1}
  isCofiltered := by
    have : IsCofiltered (ProEt.forget T ⋙ coyoneda.obj (op (Over.mk t))).Elements :=
      Functor.isCofiltered_elements _
    exact .of_equivalence
      (Functor.Elements.uliftEquivalence.{u + 1}
        (ProEt.forget T ⋙ coyoneda.obj (op (Over.mk t)))).symm
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective R hR x := by
    obtain ⟨W, g, hg, w, hw⟩ := comparison_cover_lift R hR x.down.left
    refine ⟨W, g, hg, ULift.up (Over.homMk w ?_), ?_⟩
    · change w ≫ W.hom = t
      rw [← MorphismProperty.Over.w g, ← Category.assoc, hw]
      exact Over.w x.down
    · apply ULift.ext
      apply Over.OverMorphism.ext
      exact hw

private theorem comparisonPoint_additive
    {Z : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (z : Spec (.of Ω) ⟶ Z) (B : Type (u + 1)) [CommRing B] :
    ((comparisonPoint z).sheafFiber (A := ModuleCat.{u + 1} B)).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] comparisonPoint_additive

private def constantProEtaleFiberIso
    (Z : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ Z) :
    (constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} B)).mapDerivedCategory ⋙
      (comparisonPoint z).sheafFiber.mapDerivedCategory ≅ 𝟭 _ := by
  let F := (comparisonPoint z).sheafFiber (A := ModuleCat.{u + 1} B)
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  exact Functor.mapDerivedCategoryCompIso _ F ≪≫
    Functor.mapDerivedCategoryNatIso
      ((comparisonPoint z).constantSheafCompSheafFiberIso _ _) ≪≫
    Functor.mapDerivedCategoryIdIso _

private def localComparisonConstantIso
    {S Z : Scheme.{u}} (f : Z ⟶ S) (B : Type (u + 1)) [CommRing B] :
    normalizationConstant S.smallEtaleTopology ⋙ localProEtaleComparison f B ≅
      (constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} B)).mapDerivedCategory := by
  let c := constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} B)
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) S
  let F := ProEtale.upperStar (ModuleCat.{u + 1} B) f
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso c ν ≪≫
      Functor.mapDerivedCategoryNatIso
        (ProEtale.constantSheafCompComparisonUpperStarIso _ S)) F.mapDerivedCategory ≪≫
    Functor.mapDerivedCategoryCompIso _ F ≪≫
    Functor.mapDerivedCategoryNatIso (ProEtale.constantSheafCompUpperStarIso _ f)

private def localComparisonCompIso
    {S V W : Scheme.{u}} (a : W ⟶ V) (b : V ⟶ S)
    (B : Type (u + 1)) [CommRing B] :
    localProEtaleComparison (a ≫ b) B ≅
      (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} B) b).mapDerivedCategory ⋙
        localProEtaleComparison a B := by
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) S
  let Fa := ProEtale.upperStar (ModuleCat.{u + 1} B) a
  let Fb := ProEtale.upperStar (ModuleCat.{u + 1} B) b
  exact Functor.isoWhiskerLeft ν.mapDerivedCategory
      (Functor.mapDerivedCategoryTriangleIso (ProEtale.upperStarComp _ a b)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategorySquareIso
      (ProEtale.comparisonUpperStarUpperStarIso _ b)) Fa.mapDerivedCategory ≪≫
    Functor.associator _ _ _

private def etaleConstantPullbackIso
    {S V : Scheme.{u}} (b : V ⟶ S) (B : Type (u + 1)) [CommRing B] :
    normalizationConstant S.smallEtaleTopology ⋙
      (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} B) b).mapDerivedCategory ≅
        normalizationConstant V.smallEtaleTopology :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarConstantSheafIso _ b)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def overRestrictionIso
    {X : Scheme.{u}} (B : Type (u + 1)) [CommRing B] (U : X.Etale) :
    X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) U ⋙
      (Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} B)).functor ≅
        AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} B) U.hom :=
  let R := GrothendieckTopology.localizationRestriction (ModuleCat.{u + 1} B)
    @AlgebraicGeometry.Etale @AlgebraicGeometry.Etale le_rfl U.hom U.prop
  let e : X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} B) U ⋙
      (Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} B)).functor ≅ R :=
    ((fullyFaithfulSheafToPresheaf U.left.smallEtaleTopology
      (ModuleCat.{u + 1} B)).whiskeringRight _).preimageIso
        (NatIso.ofComponents
          (fun F ↦ by
            change ((Scheme.Etale.etaleToOver U).op ⋙
              (Over.forget U).op ⋙ F.obj) ≅ _
            exact Functor.isoWhiskerRight
              (NatIso.op (Scheme.Etale.etaleToOverCompForgetIso U).symm) F.obj)
          (by
            intro F G φ
            apply NatTrans.ext
            funext T
            dsimp
            exact (φ.hom.naturality _).symm))
  e ≪≫ (GrothendieckTopology.upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} B) @AlgebraicGeometry.Etale @AlgebraicGeometry.Etale
    le_rfl U.hom U.prop).symm

private theorem sliceIsoOfPullback
    {S : Scheme.{u}} (V : S.Etale) (B : Type (u + 1)) [CommRing B]
    (K D : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (e :
      (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj K ≅
      (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj D) :
    Nonempty ((derivedSliceRestriction S.smallEtaleTopology B V).obj K ≅
      (derivedSliceRestriction S.smallEtaleTopology B V).obj D) := by
  let F := (Etale.overSheafEquiv V (ModuleCat.{u + 1} B)).functor
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  let h := Functor.mapDerivedCategoryCompIso _ F ≪≫
    Functor.mapDerivedCategoryNatIso (overRestrictionIso B V)
  exact ⟨F.mapDerivedCategory.preimageIso ((h.app K) ≪≫ e ≪≫ (h.app D).symm)⟩

/-- Bounded finite-lisse local models descend to actual etale local isomorphisms. -/
theorem exists_etale_local_iso_of_fixed_realization_local_model
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (D : DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (hDbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj D))
    (hDlisse : ∀ q : ℤ, IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor _ q).obj D))
    (hlocal : ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((lisseTowerFixedRealization (W.hom ≫ g) d n).obj
            ((localProEtaleComparison w.left (lisseTowerEtaleRing d n)).obj
              ((normalizationConstant U.left.smallEtaleTopology).obj E)) ≅
          (lisseTowerFixedRealization (W.hom ≫ g) d n).obj
            ((localProEtaleComparison w.left (lisseTowerEtaleRing d n)).obj D))) :
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ U.left),
      ∃ (V : U.left.Etale) (_v : (pointSmallEtale x).fiber.obj V),
        Nonempty ((localIsomorphismRestriction U.left (lisseTowerEtaleRing d n) V).obj
            ((normalizationConstant U.left.smallEtaleTopology).obj E) ≅
          (localIsomorphismRestriction U.left (lisseTowerEtaleRing d n) V).obj D) := by
  classical
  let B := lisseTowerEtaleRing d n
  obtain ⟨𝒰, h𝒰⟩ :=
    (AlgebraicGeometry.Etale.finiteRing_derived_local_constancy U.left B D
      hDbounded hDlisse).1
  obtain ⟨T, hT, hmodels⟩ := hlocal
  intro Ω instΩ instSep x
  obtain ⟨i, v, hv⟩ := 𝒰.exists_comp_eq_of_isSepClosed x
  let V : U.left.Etale := Etale.mk (𝒰.f i)
  let b := 𝒰.f i
  obtain ⟨G₀, hGbounded, hGfinite, ⟨eG₀⟩⟩ := h𝒰 i
  let G := DerivedCategory.Q.obj G₀
  let cV := constantSheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} B)
  let eG :
      (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} B) b).mapDerivedCategory.obj D ≅
        (normalizationConstant V.left.smallEtaleTopology).obj G :=
    eG₀ ≪≫ (cV.mapDerivedCategoryFactors.app G₀).symm
  let VY : Y.ProEt := ProEt.mk (b ≫ U.hom)
  let vY : VY ⟶ U := MorphismProperty.Over.homMk b rfl
  let Ω' := AlgebraicClosure (V.left.residueField (v default))
  let zV : Spec (.of Ω') ⟶ V.left := V.left.algClosurePoint (v default)
  obtain ⟨W, w, hw, z, hz⟩ := comparison_cover_lift (T.pullback vY)
    ((ProEt.topology Y).pullback_stable vY hT) zV
  let a := w.left
  obtain ⟨e⟩ := hmodels W (w ≫ vY) hw
  let eLocal := (lisseTowerFixedRealization (W.hom ≫ g) d n).preimageIso e
  let eW :
      (constantSheaf (ProEt.topology W.left) (ModuleCat.{u + 1} B)).mapDerivedCategory.obj E ≅
      (constantSheaf (ProEt.topology W.left) (ModuleCat.{u + 1} B)).mapDerivedCategory.obj G :=
    ((localComparisonConstantIso (a ≫ b) B).app E).symm ≪≫ eLocal ≪≫
      (localComparisonCompIso a b B).app D ≪≫
      (localProEtaleComparison a B).mapIso eG ≪≫
      (localComparisonConstantIso a B).app G
  let eAlgebra : E ≅ G :=
    ((constantProEtaleFiberIso W.left B z).app E).symm ≪≫
      (comparisonPoint z).sheafFiber.mapDerivedCategory.mapIso eW ≪≫
      (constantProEtaleFiberIso W.left B z).app G
  let eV := (etaleConstantPullbackIso b B).app E ≪≫
    (normalizationConstant V.left.smallEtaleTopology).mapIso eAlgebra ≪≫ eG.symm
  exact ⟨V, Over.homMk v hv, ⟨eV⟩⟩

/-- A local fixed-realization isomorphism on a pro-etale covering sieve gives a local
section of the derived Isom presheaf through every geometric point, provided `D` is bounded
with finite locally constant cohomology sheaves. -/
theorem exists_proetale_local_iso_section_of_fixed_realization_local_model
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (D : DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (hDbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj D))
    (hDlisse : ∀ q : ℤ, IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor _ q).obj D))
    (hlocal : ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((lisseTowerFixedRealization (W.hom ≫ g) d n).obj
            ((localProEtaleComparison w.left (lisseTowerEtaleRing d n)).obj
              ((normalizationConstant U.left.smallEtaleTopology).obj E)) ≅
          (lisseTowerFixedRealization (W.hom ≫ g) d n).obj
            ((localProEtaleComparison w.left (lisseTowerEtaleRing d n)).obj D))) :
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ U.left),
      ∃ (V : U.left.Etale) (_v : (pointSmallEtale x).fiber.obj V),
        Nonempty ((derivedLocalIsoPresheaf (ProEt.topology U.left)
          (lisseTowerEtaleRing d n)
          ((derivedComparison U.left (lisseTowerEtaleRing d n)).obj
            ((normalizationConstant U.left.smallEtaleTopology).obj E))
          ((derivedComparison U.left (lisseTowerEtaleRing d n)).obj D)).obj
            (op ((toProEt U.left).obj V))) := by
  intro Ω instΩ instSep x
  obtain ⟨V, v, ⟨eV⟩⟩ := exists_etale_local_iso_of_fixed_realization_local_model
    X Y g d U n E D hDbounded hDlisse hlocal Ω x
  obtain ⟨eSlice⟩ := sliceIsoOfPullback V (lisseTowerEtaleRing d n)
    ((normalizationConstant U.left.smallEtaleTopology).obj E) D eV
  exact ⟨V, v, ⟨derivedComparisonLocalIso U.left (lisseTowerEtaleRing d n)
    ((normalizationConstant U.left.smallEtaleTopology).obj E) D V eSlice⟩⟩

end AlgebraicGeometry.Scheme
