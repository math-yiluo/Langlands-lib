/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.PerfectProjection.PerfectProjectionFormula
public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateThickLocus
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedCoefficientDirectImageSquare

/-! # Transport of scalar mates through coefficient isomorphisms

Source: Stacks Project, Cohomology on Sites, Tags 06YY and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace CompletedProjection

/-- View an object over the completed ring on X over the literal inverse image of
that on Y, using the specified completed coefficient isomorphism.
Source: blueprint order 1275; Stacks 07A6
(blueprint: lem-pbc-completed-scalar-mate-coefficient-transport). -/
abbrev inverseObject {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PerfectProjection.derived d X) :=
  (pbcDerivedRestrict (PerfectProjection.coefficients d f).hom).obj K

end CompletedProjection

private theorem completedCoefficientComparison_square
    {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    (PerfectProjection.coefficients d f).hom ≫ (pbcCompletedComparison X d).hom =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (pbcCompletedComparison Y d).hom ≫ completedCoefficientMap f d := by
  apply limit.hom_ext
  intro n
  simp only [Category.assoc, pbcCompletedComparison, HasLimit.isoOfNatIso_hom_π,
    completedCoefficientMap, limit.lift_π, completedCoefficientComponent,
    completedFiniteCoefficientMap, PerfectProjection.coefficients,
    asIso_hom, PerfectProjection.coefficientMap, limit.lift_π_assoc]
  change _ =
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (HasLimit.isoOfNatIso (pbcConstantSystemComparison Y d)).hom ≫
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (limit.π (pbcAdicRings Y d) n) ≫ _
  conv_rhs =>
    rw [← Category.assoc, ← Functor.map_comp, HasLimit.isoOfNatIso_hom_π]
  simp only [pbcConstantSystemComparison, NatIso.ofComponents_hom_app,
    Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, proEtaleConstantComparison]

private theorem scalarMateTranspose
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {S₁ : C ⥤ E} {U₁ : E ⥤ C} {S₂ : D ⥤ F} {U₂ : F ⥤ D}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (s : S₁ ⊣ U₁) (t : S₂ ⊣ U₂)
    (τ : U₁ ⋙ L₁ ≅ L₂ ⋙ U₂) (l : S₁ ⋙ L₂ ≅ L₁ ⋙ S₂)
    (c : R₁ ⋙ S₁ ⟶ S₂ ⋙ R₂) (d : R₂ ⋙ U₁ ⟶ U₂ ⋙ R₁)
    (M : D)
    (hu : L₁.map (s.unit.app (R₁.obj M)) ≫ τ.hom.app (S₁.obj (R₁.obj M)) =
      t.unit.app (L₁.obj (R₁.obj M)) ≫ U₂.map (l.inv.app (R₁.obj M)))
    (hc : L₂.map (c.app M) ≫ b.counit.app (S₂.obj M) =
      l.hom.app (R₁.obj M) ≫ S₂.map (a.counit.app M))
    (hd : L₁.map (d.app (S₂.obj M)) ≫ a.counit.app (U₂.obj (S₂.obj M)) =
      τ.hom.app (R₂.obj (S₂.obj M)) ≫ U₂.map (b.counit.app (S₂.obj M))) :
    s.unit.app (R₁.obj M) ≫ U₁.map (c.app M) ≫ d.app (S₂.obj M) =
      R₁.map (t.unit.app M) := by
  apply (a.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [hd]
  have hn := τ.hom.naturality (c.app M)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← U₂.map_comp, hc, U₂.map_comp]
  rw [← Category.assoc, ← Category.assoc, hu]
  simp only [Category.assoc, ← U₂.map_comp_assoc, Iso.inv_hom_id_app]
  have ha := a.counit.naturality (t.unit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at ha
  apply Eq.trans ?_ ha.symm
  have ht := (t.unit.naturality (a.counit.app M)).symm
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Functor.comp_obj, Functor.comp_map,
    Functor.id_obj, Functor.id_map] using ht

private theorem literalBeta_transpose
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (χ : R ⟶ S)
    (K : DerivedCategory (proEtaleRingModules X (DerivedScalarMate.inverseRing f R))) :
    (pbcDerivedScalarAdjunction χ).homEquiv _ _ ((DerivedScalarMate.beta f χ).app K) =
      (DerivedScalarMate.push f R).map
          ((pbcDerivedScalarAdjunction (DerivedScalarMate.inverseMap f χ)).unit.app K) ≫
        (DerivedScalarMate.restrictionPush f χ).inv.app
          ((proEtaleRingDerivedExtension (DerivedScalarMate.inverseMap f χ)).obj K) := by
  let b := proEtaleRingRestrictionDerivedPullback f R S
    (DerivedScalarMate.inverseRing f R) (DerivedScalarMate.inverseRing f S)
    χ (DerivedScalarMate.inverseMap f χ) (Iso.refl _) (Iso.refl _) (by simp)
  let τ := b.symm
  let l := DerivedScalarMate.scalarPullback f χ
  let a := DerivedScalarMate.adjunction f R
  let az := DerivedScalarMate.adjunction f S
  let av := pbcDerivedScalarAdjunction χ
  let au := pbcDerivedScalarAdjunction (DerivedScalarMate.inverseMap f χ)
  have hu := unit_mateEquiv_symm av au (TwoSquare.mk _ _ _ _ b.inv)
    ((DerivedScalarMate.push f R).obj K)
  change (DerivedScalarMate.pull f R).map (av.unit.app _) ≫ τ.hom.app _ =
    au.unit.app _ ≫ (pbcDerivedRestrict (DerivedScalarMate.inverseMap f χ)).map
      (l.inv.app _) at hu
  have hβ := mateEquiv_counit a az (TwoSquare.mk _ _ _ _ l.hom) K
  change (DerivedScalarMate.pull f S).map ((DerivedScalarMate.beta f χ).app K) ≫
    az.counit.app _ = l.hom.app _ ≫
      (proEtaleRingDerivedExtension (DerivedScalarMate.inverseMap f χ)).map
        (a.counit.app K) at hβ
  have hm : (mateEquiv az a (TwoSquare.mk _ _ _ _ b.inv)) =
      (DerivedScalarMate.restrictionPush f χ).hom := by
    apply NatTrans.ext
    funext N
    have h := (proEtaleRingSheafChangeAdjunction f R S
      (DerivedScalarMate.inverseRing f R) (DerivedScalarMate.inverseRing f S)
      χ (DerivedScalarMate.inverseMap f χ) (Iso.refl _) (Iso.refl _) (by simp)).2.2
      ((DerivedScalarMate.push f S).obj N) N (az.counit.app N)
    have hid : az.homEquiv _ _ (az.counit.app N) = 𝟙 _ := by
      rw [← az.homEquiv_symm_id N]
      exact (az.homEquiv _ _).apply_symm_apply _
    change a.homEquiv _ _ (b.inv.app _ ≫
      (pbcDerivedRestrict (DerivedScalarMate.inverseMap f χ)).map (az.counit.app N)) =
        (pbcDerivedRestrict χ).map (az.homEquiv _ _ (az.counit.app N)) ≫
          (DerivedScalarMate.restrictionPush f χ).hom.app N at h
    rw [hid, CategoryTheory.Functor.map_id, Category.id_comp] at h
    rw [← h]
    simp only [mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app,
      Functor.comp_obj, Functor.comp_map, Functor.rightUnitor_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.leftUnitor_hom_app, Category.id_comp,
      Adjunction.homEquiv_unit, Functor.map_comp]
    erw [Category.comp_id]
    rfl
  have hd := mateEquiv_counit az a (TwoSquare.mk _ _ _ _ b.inv)
    ((proEtaleRingDerivedExtension (DerivedScalarMate.inverseMap f χ)).obj K)
  change (DerivedScalarMate.pull f R).map
      (((mateEquiv az a (TwoSquare.mk _ _ _ _ b.inv))).app _) ≫
      a.counit.app _ = τ.hom.app _ ≫
      (pbcDerivedRestrict (DerivedScalarMate.inverseMap f χ)).map (az.counit.app _) at hd
  rw [hm] at hd
  have h := scalarMateTranspose a az av au τ l (DerivedScalarMate.beta f χ)
    (DerivedScalarMate.restrictionPush f χ).hom K hu hβ hd
  apply (cancel_mono ((DerivedScalarMate.restrictionPush f χ).hom.app _)).mp
  simp only [Adjunction.homEquiv_unit, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact h

/-- The scalar-adjunction mate is invariant under the two coefficient isomorphisms
and the normalized presentations of ordinary direct image. The arrow on the right
is the existing scalar mate over literal inverse-image ring sheaves. No tensor
model, projection-formula arrow, or perfectness hypothesis occurs here.

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 07A6; the canonical
coefficient-change comparisons of Tags 0D6D and 0D6E; blueprint orders 1275-1276.
(blueprint: lem-pbc-completed-scalar-mate-coefficient-transport).

Proof: put b_T = pbcCompletedComparison T d. The finite-level constant comparisons
commute with coefficient inverse image, so their limit maps satisfy
f^{-1}(b_Y);c_f = c_f^0;b_X. Restriction along b_T and c_f^0 is an exact
equivalence. The coefficient square hc identifies the transported map on X with
the inverse image of b_Y;phiY, followed by the given target-ring isomorphism c.
For extension use the unique left-adjoint comparisons of these restriction
functors, with the tensor-unit normalized scalar adjunctions. For direct image
use the section-normalized coefficient-change comparison. This gives s and t.
The equality hF (respectively hG) identifies its ordinary presentation with the
canonical ringed functor. The normalization hi determines its ordinary comparison
uniquely: both are identity on sections. The equation he and uniqueness of right
derivation identify its derived comparison with the canonical one. Consequently
the transported transpose F(eta_X);e is the transpose of the literal-ring
scalar mate beta. Adjunction naturality and the triangle identities identify their
mates, giving the displayed equality. No invertibility of beta is used. Exact
restriction and flat K-flat resolutions make all comparisons valid for unbounded
inputs, including zero rings and the empty site. -/
theorem completedScalarMateCoefficientTransport
    {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) [IsIso (completedCoefficientMap f d)]
    (SY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (SX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (φY : pbcAdicCompletion Y d ⟶ SY) (φX : pbcAdicCompletion X d ⟶ SX)
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)
    (hc : completedCoefficientMap f d ≫ φX =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map φY ≫ c.hom)
    (F : pbcModules X (pbcAdicCompletion X d) ⥤ pbcModules Y (pbcAdicCompletion Y d))
    [F.Additive]
    (hF : F = proEtaleRingModuleDirectImage f (pbcAdicCompletion Y d)
      (pbcAdicCompletion X d) (asIso (completedCoefficientMap f d)))
    (G : pbcModules X SX ⥤ pbcModules Y SY) [G.Additive]
    (hG : G = proEtaleRingModuleDirectImage f SY SX c)
    (i : pbcRestrict φX ⋙ F ≅
      G ⋙ pbcRestrict φY)
    (hi : ∀ (M : pbcModules X SX) (U : Y.ProEtᵒᵖ),
      HEq (fun x ↦ (i.hom.app M).val.app U x)
        (fun x : ((proEtaleRingModuleDirectImage f SY SX c).obj M).val.obj U ↦ x))
    (e : pbcDerivedRestrict φX ⋙ F.rightDerivedFunctor ≅
      G.rightDerivedFunctor ⋙ pbcDerivedRestrict φY)
    (he : ∀ C : CochainComplex (pbcModules X SX) ℤ,
      F.rightDerivedFunctorUnitQ
          (((pbcRestrict φX).mapHomologicalComplex (.up ℤ)).obj C) ≫
        F.rightDerivedFunctor.map
          ((pbcRestrict φX).mapDerivedCategoryFactors.inv.app C) ≫
        e.hom.app (DerivedCategory.Q.obj C) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex i.hom (.up ℤ)).app C) ≫
        (pbcRestrict φY).mapDerivedCategoryFactors.inv.app
          ((G.mapHomologicalComplex (.up ℤ)).obj C) ≫
        (pbcDerivedRestrict φY).map (G.rightDerivedFunctorUnitQ C))
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    let χ := (pbcCompletedComparison Y d).hom ≫ φY
    let K₀ := (pbcDerivedRestrict (pbcCompletedComparison X d).hom).obj K
    let Kᵢ := CompletedProjection.inverseObject f d K₀
    ∃ (s : (pbcDerivedRestrict (pbcCompletedComparison Y d).hom).obj
          ((pbcDerivedRestrict φY).obj
            ((pbcDerivedExtend φY).obj (F.rightDerivedFunctor.obj K))) ≅
        ((DerivedScalarMate.push f (PerfectProjection.ring d Y) ⋙
          proEtaleRingDerivedExtension χ) ⋙
          (DerivedScalarMate.restriction χ).mapDerivedCategory).obj Kᵢ)
      (t : (pbcDerivedRestrict (pbcCompletedComparison Y d).hom).obj
          ((pbcDerivedRestrict φY).obj
            (G.rightDerivedFunctor.obj ((pbcDerivedExtend φX).obj K))) ≅
        ((proEtaleRingDerivedExtension (DerivedScalarMate.inverseMap f χ) ⋙
          DerivedScalarMate.push f SY) ⋙
          (DerivedScalarMate.restriction χ).mapDerivedCategory).obj Kᵢ),
      (pbcDerivedRestrict (pbcCompletedComparison Y d).hom).map
          ((pbcDerivedRestrict φY).map
            (((pbcDerivedScalarAdjunction φY).homEquiv _ _).symm
              (F.rightDerivedFunctor.map
                  ((pbcDerivedScalarAdjunction φX).unit.app K) ≫
                e.hom.app ((pbcDerivedExtend φX).obj K)))) ≫ t.hom =
        s.hom ≫ (DerivedScalarMate.restriction χ).mapDerivedCategory.map
          ((DerivedScalarMate.beta f χ).app Kᵢ) := by
  let χ := (pbcCompletedComparison Y d).hom ≫ φY
  let ψ := DerivedScalarMate.inverseMap f χ
  let bY := pbcCompletedComparison Y d
  let q := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso bY ≪≫
    asIso (completedCoefficientMap f d)
  let B := pbcDerivedRestrict bY.hom
  let U := pbcDerivedRestrict q.hom
  let V := pbcDerivedRestrict c.hom
  let R := pbcDerivedRestrict χ
  let H := DerivedScalarMate.push f (adicLisseCompletedRing Y d.ideal)
  let J := DerivedScalarMate.push f SY
  have hq : q.hom ≫ φX = ψ ≫ c.hom := by
    dsimp only [q, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, ψ, χ,
      DerivedScalarMate.inverseMap, bY]
    rw [Category.assoc, hc, ← Category.assoc, ← Functor.map_comp]
  let k : pbcDerivedRestrict φX ⋙ U ≅ V ⋙ pbcDerivedRestrict ψ :=
    derivedRestrictionSquare q.hom φX c.hom ψ hq
  let r : pbcDerivedRestrict φY ⋙ B ≅ R :=
    pbcDerivedRestrictComp bY.hom φY χ rfl
  have : B.IsEquivalence := derivedRestrictIso_isEquivalence bY
  have : U.IsEquivalence := derivedRestrictIso_isEquivalence q
  have : V.IsEquivalence := derivedRestrictIso_isEquivalence c
  obtain ⟨aY, haY⟩ := scalarAdjunctionCoefficientEquivalence
    (pbcDerivedScalarAdjunction φY) (pbcDerivedScalarAdjunction χ)
    B (𝟭 _) (r ≪≫ (Functor.leftUnitor _).symm)
  obtain ⟨aX, haX⟩ := scalarAdjunctionCoefficientEquivalence
    (pbcDerivedScalarAdjunction φX) (pbcDerivedScalarAdjunction ψ) U V k
  let p : F.rightDerivedFunctor ⋙ B ≅ U ⋙ H :=
    normalizedCoefficientSourceComparison f (adicLisseCompletedRing Y d.ideal)
    (pbcAdicCompletion Y d) (pbcAdicCompletion X d) bY
    (asIso (completedCoefficientMap f d)) F hF
  let z : G.rightDerivedFunctor ≅ V ⋙ J :=
    normalizedCoefficientTargetComparison f SY SX c G hG
  have hpz := normalizedCoefficientDirectImageSquare f
    (adicLisseCompletedRing Y d.ideal) (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
    bY SY SX φY φX (asIso (completedCoefficientMap f d)) c hc F hF G hG i hi e he
  have hpz' : ∀ M : DerivedCategory (pbcModules X SX),
      B.map (e.hom.app M) ≫ r.hom.app (G.rightDerivedFunctor.obj M) ≫
          R.map (z.hom.app M) =
        p.hom.app ((pbcDerivedRestrict φX).obj M) ≫ H.map (k.hom.app M) ≫
          (DerivedScalarMate.restrictionPush f χ).inv.app (V.obj M) := hpz
  let σ : (pbcDerivedExtend φY).obj (F.rightDerivedFunctor.obj K) ⟶
      G.rightDerivedFunctor.obj ((pbcDerivedExtend φX).obj K) :=
    ((pbcDerivedScalarAdjunction φY).homEquiv _ _).symm
    (F.rightDerivedFunctor.map ((pbcDerivedScalarAdjunction φX).unit.app K) ≫
      e.hom.app ((pbcDerivedExtend φX).obj K))
  let u : (pbcDerivedExtend φY).obj (F.rightDerivedFunctor.obj K) ≅
      (pbcDerivedExtend χ).obj (B.obj (F.rightDerivedFunctor.obj K)) :=
    aY.app (F.rightDerivedFunctor.obj K)
  let sx := R.mapIso u ≪≫ R.mapIso ((proEtaleRingDerivedExtension χ).mapIso (p.app K))
  let tx := R.mapIso (z.app ((pbcDerivedExtend φX).obj K)) ≪≫
    R.mapIso (J.mapIso (aX.app K))
  have hσ : (pbcDerivedScalarAdjunction φY).unit.app (F.rightDerivedFunctor.obj K) ≫
      (pbcDerivedRestrict φY).map σ =
      F.rightDerivedFunctor.map ((pbcDerivedScalarAdjunction φX).unit.app K) ≫
        e.hom.app ((pbcDerivedExtend φX).obj K) :=
    ((pbcDerivedScalarAdjunction φY).homEquiv _ _).apply_symm_apply _
  have hunit : (pbcDerivedScalarAdjunction χ).unit.app
      (B.obj (F.rightDerivedFunctor.obj K)) ≫ R.map u.inv =
      B.map ((pbcDerivedScalarAdjunction φY).unit.app (F.rightDerivedFunctor.obj K)) ≫
        r.hom.app ((pbcDerivedExtend φY).obj (F.rightDerivedFunctor.obj K)) := by
    have h := haY (F.rightDerivedFunctor.obj K)
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.leftUnitor_inv_app, Category.comp_id] at h
    change B.map ((pbcDerivedScalarAdjunction φY).unit.app
        (F.rightDerivedFunctor.obj K)) ≫ r.hom.app _ ≫ R.map u.hom = _ at h
    rw [← h]
    simp only [Category.assoc, ← R.map_comp, u.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have hr := r.hom.naturality σ
  change B.map ((pbcDerivedRestrict φY).map σ) ≫ r.hom.app _ =
    r.hom.app _ ≫ R.map σ at hr
  have htransport :
      (pbcDerivedScalarAdjunction χ).unit.app (B.obj (F.rightDerivedFunctor.obj K)) ≫
        R.map (u.inv ≫ σ) =
      B.map (F.rightDerivedFunctor.map ((pbcDerivedScalarAdjunction φX).unit.app K) ≫
        e.hom.app ((pbcDerivedExtend φX).obj K)) ≫
          r.hom.app (G.rightDerivedFunctor.obj ((pbcDerivedExtend φX).obj K)) := by
    rw [R.map_comp, ← Category.assoc, hunit, Category.assoc]
    rw [← hr]
    rw [← Category.assoc, ← B.map_comp, hσ]
  have hn := p.hom.naturality ((pbcDerivedScalarAdjunction φX).unit.app K)
  dsimp only [Functor.comp_map] at hn
  have hd := (DerivedScalarMate.restrictionPush f χ).inv.naturality (aX.hom.app K)
  dsimp only [Functor.comp_map] at hd
  have hd' : H.map ((pbcDerivedRestrict ψ).map (aX.hom.app K)) ≫
      (DerivedScalarMate.restrictionPush f χ).inv.app
        ((pbcDerivedExtend ψ).obj (U.obj K)) =
      (DerivedScalarMate.restrictionPush f χ).inv.app
          (V.obj ((pbcDerivedExtend φX).obj K)) ≫ R.map (J.map (aX.hom.app K)) := hd
  have hb := literalBeta_transpose f χ (U.obj K)
  change (pbcDerivedScalarAdjunction χ).homEquiv (H.obj (U.obj K))
      (J.obj ((pbcDerivedExtend ψ).obj (U.obj K)))
        ((DerivedScalarMate.beta f χ).app (U.obj K)) =
      H.map ((pbcDerivedScalarAdjunction ψ).unit.app (U.obj K)) ≫
        (DerivedScalarMate.restrictionPush f χ).inv.app
          ((pbcDerivedExtend ψ).obj (U.obj K)) at hb
  have hmate : u.inv ≫ σ ≫ z.hom.app ((pbcDerivedExtend φX).obj K) ≫
      J.map (aX.hom.app K) =
      (proEtaleRingDerivedExtension χ).map (p.hom.app K) ≫
        (DerivedScalarMate.beta f χ).app (U.obj K) := by
    apply ((pbcDerivedScalarAdjunction χ).homEquiv _ _).injective
    rw [(pbcDerivedScalarAdjunction χ).homEquiv_naturality_left]
    dsimp only [Functor.comp_obj]
    rw [hb]
    simp only [Adjunction.homEquiv_unit, Functor.map_comp]
    have ht := htransport
    rw [R.map_comp] at ht
    rw [reassoc_of% ht]
    simp only [B.map_comp, Category.assoc]
    rw [reassoc_of% (hpz' ((pbcDerivedExtend φX).obj K)), reassoc_of% hn]
    rw [← hd', ← H.map_comp_assoc, ← H.map_comp_assoc]
    simp only [Category.assoc]
    rw [haX K]
  have hsquare : R.map σ ≫ tx.hom = sx.hom ≫
      R.map ((DerivedScalarMate.beta f χ).app (U.obj K)) := by
    apply (cancel_epi (R.map u.inv)).mp
    simp only [sx, tx, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    change R.map u.inv ≫ R.map σ ≫
        R.map (z.hom.app ((pbcDerivedExtend φX).obj K)) ≫
        R.map (J.map (aX.hom.app K)) =
      R.map u.inv ≫ R.map u.hom ≫
        R.map ((proEtaleRingDerivedExtension χ).map (p.hom.app K)) ≫
        R.map ((DerivedScalarMate.beta f χ).app (U.obj K))
    conv_rhs =>
      rw [← R.map_comp_assoc, u.inv_hom_id, R.map_id, Category.id_comp]
    simpa only [Functor.map_comp, Category.assoc] using congrArg R.map hmate
  let sq := r.app ((pbcDerivedExtend φY).obj (F.rightDerivedFunctor.obj K)) ≪≫ sx
  let tq := r.app (G.rightDerivedFunctor.obj ((pbcDerivedExtend φX).obj K)) ≪≫ tx
  have hsq : B.map ((pbcDerivedRestrict φY).map σ) ≫ tq.hom =
      sq.hom ≫ R.map ((DerivedScalarMate.beta f χ).app (U.obj K)) := by
    change B.map ((pbcDerivedRestrict φY).map σ) ≫ (r.hom.app _ ≫ tx.hom) =
      (r.hom.app _ ≫ sx.hom) ≫ R.map ((DerivedScalarMate.beta f χ).app (U.obj K))
    rw [← Category.assoc, hr, Category.assoc, hsquare, Category.assoc]
  let K₀ := (pbcDerivedRestrict (pbcCompletedComparison X d).hom).obj K
  let Kᵢ := CompletedProjection.inverseObject f d K₀
  let jq : U.obj K ≅ Kᵢ :=
    (pbcDerivedRestrictComp (PerfectProjection.coefficients d f).hom
      (pbcCompletedComparison X d).hom q.hom
      (completedCoefficientComparison_square f d)).symm.app K
  let S := (H ⋙ proEtaleRingDerivedExtension χ) ⋙ R
  let T := (proEtaleRingDerivedExtension ψ ⋙ J) ⋙ R
  refine ⟨sq ≪≫ S.mapIso jq, tq ≪≫ T.mapIso jq, ?_⟩
  change B.map ((pbcDerivedRestrict φY).map σ) ≫
      (tq.hom ≫ T.map jq.hom) =
    (sq.hom ≫ S.map jq.hom) ≫ R.map ((DerivedScalarMate.beta f χ).app Kᵢ)
  rw [← Category.assoc, hsq, Category.assoc]
  have hnat := (DerivedScalarMate.beta f χ).naturality jq.hom
  have hh := congrArg R.map hnat
  simpa only [S, T, H, J, R, ψ, Functor.map_comp, Functor.comp_map, Category.assoc] using
    congrArg (fun w ↦ sq.hom ≫ w) hh.symm

end AlgebraicGeometry.Scheme
