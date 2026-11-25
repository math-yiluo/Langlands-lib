/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.AffineSpectrumCanonicalComparisonSquare

/-! # Affine spectrum transport before the coefficient morphism

Source: Stacks Project, Tags 0DJ8, 0098 and 0D5S.
(blueprint: lem-pc-affine-spectrum-comparison-source-transport).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

private theorem transport_automorphism_hom
    {C D : Type*} [Category C] [Category D] (J : C ⥤ D)
    {P K : C} {Q : D} (e : P ≅ K) (e0 : Q ≅ J.obj K) (d : Q ≅ J.obj P) :
    (e0 ≪≫ J.mapIso e.symm ≪≫ d.symm).hom ≫ d.hom ≫ J.map e.hom = e0.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp, Iso.inv_hom_id]
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem transport_representatives
    {C₁ C₂ D₁ D₂ A₀ : Type*}
    [Category C₁] [Category C₂] [Category D₁] [Category D₂] [Category A₀]
    (L : C₁ ⥤ D₁) (L0 : C₂ ⥤ D₂) (J : C₁ ⥤ C₂) (J' : D₁ ⥤ D₂)
    (H : D₁ ⥤ A₀) (H0 : D₂ ⥤ A₀)
    (T : H ≅ J' ⋙ H0) (c : J ⋙ L0 ≅ L ⋙ J')
    {P K : C₁} {Q : C₂} {U V : A₀}
    (e : P ≅ K) (e0 : Q ≅ J.obj K) (d : Q ≅ J.obj P)
    (q : U ⟶ H.obj (L.obj P)) (q0 : V ⟶ H0.obj (L0.obj Q))
    (l0 : U ≅ V) (a : Q ≅ Q) (b : V ≅ V)
    (ha : a.hom ≫ d.hom ≫ J.map e.hom = e0.hom)
    (hb : b.hom ≫ q0 = q0 ≫ H0.map (L0.map a.hom))
    (h : l0.hom ≫ q0 ≫ H0.map (L0.map d.hom) =
      q ≫ T.hom.app (L.obj P) ≫ H0.map (c.inv.app P)) :
    (l0 ≪≫ b.symm).hom ≫ q0 ≫ H0.map (L0.map e0.hom) =
      q ≫ H.map (L.map e.hom) ≫ T.hom.app (L.obj K) ≫ H0.map (c.inv.app K) := by
  have hb' : b.inv ≫ q0 ≫ H0.map (L0.map a.hom) = q0 := by
    apply (cancel_epi b.hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hb.symm
  have hn : b.inv ≫ q0 ≫ H0.map (L0.map e0.hom) =
      q0 ≫ H0.map (L0.map d.hom) ≫ H0.map (L0.map (J.map e.hom)) := by
    rw [← ha]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun k ↦ k ≫ H0.map (L0.map d.hom) ≫
        H0.map (L0.map (J.map e.hom))) hb'
  have hc := congrArg (fun k ↦ H0.map k) (c.inv.naturality e.hom)
  simp only [Functor.comp_map, Functor.map_comp] at hc
  have ht := T.hom.naturality (L.map e.hom)
  simp only [Functor.comp_map] at ht
  have hh := congrArg (fun k ↦ k ≫ H0.map (L0.map (J.map e.hom))) h
  have hc' := congrArg (fun k ↦ q ≫ T.hom.app (L.obj P) ≫ k) hc.symm
  have ht' := congrArg (fun k ↦ q ≫ k ≫ H0.map (c.inv.app K)) ht.symm
  calc
    _ = l0.hom ≫ q0 ≫ H0.map (L0.map d.hom) ≫
        H0.map (L0.map (J.map e.hom)) := by
      simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using
        congrArg (fun k ↦ l0.hom ≫ k) hn
    _ = q ≫ T.hom.app (L.obj P) ≫ H0.map (c.inv.app P) ≫
        H0.map (L0.map (J.map e.hom)) := by
      simpa only [Category.assoc] using hh
    _ = q ≫ T.hom.app (L.obj P) ≫ H0.map (J'.map (L.map e.hom)) ≫
        H0.map (c.inv.app K) := by simpa only [Category.assoc] using hc'
    _ = _ := by simpa only [Category.assoc] using ht'


set_option linter.unusedVariables false in
-- The quantified proof hypotheses occur only in the proof, not in the conclusion.
/-- Transport the localized tensor comparison into derived pullback, independently
of any coefficient morphism or target representative.

Proof: use isoPullbackStalkCohomologyIso along X'.isoSpec.inv for T.
This is a concrete natural isomorphism obtained from restriction-stalks,
exact homology factors and the invertible universal pullback counit.
Apply exists_affineSpectrum_canonicalComparison_square to P and Q with the
canonical isomorphism d from the spectrum pullback counit. For arbitrary e
and e0, put a = e0 followed by pullback of e inverse followed by d inverse.
This is an automorphism of the derived object represented by Q. The theorem
exists_comparisonSourceIso lifts a to a tensor-algebra source automorphism;
comparisonIntoPullback_naturality gives its commuting square. Extend scalars
and forget to obtain b on the additive source. Set l = l0 followed by b inverse.
The identity a;d;J(e)=e0 and cancellation of b first replace the canonical
target identification by e0. Naturality of T and of the specified inverse
composition comparison then give the displayed equation with e. The private
transport_representatives lemma proves this categorical diagram calculation.
No localized comparison is required to be invertible. Empty schemes, zero
complexes and rings, arbitrary degrees and unbounded complexes are covered.
Source: Stacks Project, Tag 0DJ8, equation-bc and affine reduction;
Tag 0098, lemma-stalk-pullback; Tag 0D5S, lemma-pullback-composition.
(blueprint: lem-pc-affine-spectrum-comparison-source-transport). -/
theorem exists_affineSpectrum_comparisonIntoPullback_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤)) (i : ℤ) :
    let z := X'.isoSpec.inv z0
    let H := comparisonStalkCohomology X' z i
    let H0 := comparisonStalkCohomology (Spec Γ(X', ⊤)) z0 i
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
      AddCommGrpCat.{u}
    ∃ T : H ⋙ F ≅ derivedPullback X'.isoSpec.inv ⋙ H0 ⋙ F0,
      ∀ (K : schemeDerivedCategory X)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
        (Q : CochainComplex
          (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace)) ℤ)
        (hP : P.IsKFlatTensor) (hQ : Q.IsKFlatTensor)
        (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
        (hcQ : IsIso ((counit (Spec.map g'.appTop)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
        (e : DerivedCategory.Q.obj P ≅ K)
        (e0 : DerivedCategory.Q.obj Q ≅ affineSpectrumDerivedObject X K)
        (hQ0 : Q = ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
          (.up ℤ)).obj P),
      ∃ l : F.obj (Arrow.mk (comparisonIntoPullback f f' g g' sq z P hcP i)).left ≅
          F0.obj (Arrow.mk
            (comparisonIntoPullback (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 Q hcQ i)).left,
        l.hom ≫ F0.map
          (comparisonIntoPullback (Spec.map f.appTop) (Spec.map f'.appTop)
            (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 Q hcQ i ≫
              H0.map ((derivedPullback (Spec.map g'.appTop)).map e0.hom)) =
        F.map (comparisonIntoPullback f f' g g' sq z P hcP i ≫
          H.map ((derivedPullback g').map e.hom)) ≫
            T.hom.app ((derivedPullback g').obj K) ≫
              F0.map (H0.map ((affineSpectrumDerivedPullbackIso g').inv.app K)) := by
  dsimp only
  let T := isoPullbackStalkCohomologyIso X'.isoSpec.inv z0 i
  refine ⟨T, ?_⟩
  intro K P Q hP hQ hcP hcQ e e0 hQ0
  let z := X'.isoSpec.inv z0
  let H := comparisonStalkCohomology X' z i
  let H0 := comparisonStalkCohomology (Spec Γ(X', ⊤)) z0 i
  let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
  let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
    AddCommGrpCat.{u}
  let j := X.isoSpec.inv
  let g0 := Spec.map g'.appTop
  let f0 := Spec.map f.appTop
  let f0' := Spec.map f'.appTop
  let s0 := Spec.map g.appTop
  let d : DerivedCategory.Q.obj Q ≅ affineSpectrumDerivedObject X
      (DerivedCategory.Q.obj P) :=
    eqToIso (congrArg (fun W ↦ DerivedCategory.Q.obj W) hQ0) ≪≫
      (isoPullbackComplexCounitIso j).symm.app P
  -- Projections avoid rechecking the large stalk models during existential elimination.
  have hcanonical := exists_affineSpectrum_canonicalComparison_square
    f f' g g' sq sq0 z0 i P Q hP hQ hcP hcQ hQ0
  let l0 := hcanonical.choose
  have hl0 := hcanonical.choose_spec
  change DerivedCategory.Q.obj Q ≅ (derivedPullback j).obj K at e0
  change DerivedCategory.Q.obj Q ≅ (derivedPullback j).obj (DerivedCategory.Q.obj P) at d
  let a : DerivedCategory.Q.obj Q ≅ DerivedCategory.Q.obj Q :=
    e0 ≪≫ (derivedPullback j).mapIso e.symm ≪≫ d.symm
  let := leftAlgebra f0 g0 z0
  let := rightAlgebra f0 f0' s0 g0 sq0 z0
  let := (tensorMap f0 f0' s0 g0 sq0 z0).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f0 g0 z0))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f0' z0))
  have hsource := (exists_comparisonSourceIso f0 f0' s0 g0 sq0 z0 Q Q a i).exists
  let c := hsource.choose
  have hc := hsource.choose_spec
  let E := ModuleCat.extendScalars.{u, u, u}
    (algebraMap (TensorProduct (R f0 g0 z0) (A g0 z0) (B f0' z0)) (C z0))
  let b := F0.mapIso (E.mapIso c)
  have hn := comparisonIntoPullback_naturality f0 f0' s0 g0 sq0 z0
    Q Q hQ hQ hcQ hcQ a i c hc
  have ha : a.hom ≫ d.hom ≫ (derivedPullback j).map e.hom = e0.hom :=
    transport_automorphism_hom (derivedPullback j) e e0 d
  have hb := congrArg (fun k ↦ F0.map k) hn.symm
  simp only [Functor.map_comp] at hb
  change l0.hom ≫ F0.map
      (comparisonIntoPullback f0 f0' s0 g0 sq0 z0 Q hcQ i ≫
        H0.map ((derivedPullback g0).map d.hom)) =
    F.map (comparisonIntoPullback f f' g g' sq z P hcP i) ≫
        T.hom.app ((derivedPullback g').obj (DerivedCategory.Q.obj P)) ≫
          F0.map (H0.map ((affineSpectrumDerivedPullbackIso g').inv.app
            (DerivedCategory.Q.obj P))) at hl0
  simp only [Functor.map_comp] at hl0
  refine ⟨l0 ≪≫ b.symm, ?_⟩
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
    transport_representatives (derivedPullback g') (derivedPullback g0)
      (derivedPullback j) (derivedPullback X'.isoSpec.inv) (H ⋙ F) (H0 ⋙ F0)
      T (affineSpectrumDerivedPullbackIso g') e e0 d
      (F.map (comparisonIntoPullback f f' g g' sq z P hcP i))
      (F0.map (comparisonIntoPullback f0 f0' s0 g0 sq0 z0 Q hcQ i))
      l0 a b ha hb hl0

end AlgebraicGeometry.SingleComplexBaseChange
