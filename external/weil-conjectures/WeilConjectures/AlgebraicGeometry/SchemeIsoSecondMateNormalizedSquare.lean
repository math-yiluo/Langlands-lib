/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeIsoRightAdjointNormalized
public import WeilConjectures.AlgebraicGeometry.DualityEquationBaseChangeMap
import WeilConjectures.AlgebraicGeometry.SchemeIsoInverseBaseChangeTransport
import WeilConjectures.AlgebraicGeometry.SchemeIsoLiftedComparisonCounit

/-! # Commutation of normalized source-isomorphism transport with the second mate

Source: Stacks Project, Tags 0ATR and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section
/-- The source comparison uses only pullback composition and the supplied comparison of
right adjoints. All its data are explicit; no witness of existence is chosen.
Source: Stacks Project, Tags 0ATR and 0D5S. 
(blueprint: lem-sc-scheme-iso-second-mate-normalized-square)
-/
def schemeIsoMateSourceIso
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P U S T : Scheme.{u}}
    (f : P ⟶ S) (f' : U ⟶ S) (e : U ≅ P) (g : T ⟶ S)
    (a : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory P)
    (b : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory U)
    (K : schemeDerivedQCohCategory S) (r : pullback f' g ⟶ pullback f g)
    (hr₁ : r ≫ pullback.fst f g = pullback.fst f' g ≫ e.hom)
    (φ : (a ⋙ (schemeDerivedQCohProperty P).ι) ⋙ derivedPullback e.hom ≅
      b ⋙ (schemeDerivedQCohProperty U).ι) :
    (derivedPullback r).obj
        ((derivedPullback (pullback.fst f g)).obj (a.obj K).obj) ≅
      (derivedPullback (pullback.fst f' g)).obj (b.obj K).obj :=
  let comp := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))
  (comp r (pullback.fst f g)).app (a.obj K).obj ≪≫
    eqToIso (congrArg (fun k ↦ (derivedPullback k).obj (a.obj K).obj) hr₁) ≪≫
    ((comp (pullback.fst f' g) e.hom).app (a.obj K).obj).symm ≪≫
    (derivedPullback (pullback.fst f' g)).mapIso (φ.app K)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem source_iso_mate_comparison
    {C U X Y S T : Type*}
    [Category C] [Category U] [Category X] [Category Y] [Category S] [Category T]
    {F : C ⥤ S} {F' : U ⥤ S} {A : S ⥤ C} {B : S ⥤ U}
    {D : X ⥤ T} {D' : Y ⥤ T} {a : T ⥤ X} {b : T ⥤ Y}
    {L : C ⥤ U} {M : X ⥤ Y} {H : C ⥤ X} {H' : U ⥤ Y} {G : S ⥤ T}
    (adjA : F ⊣ A) (adjB : F' ⊣ B) (adja : D ⊣ a) (adjb : D' ⊣ b)
    (k : F ⟶ L ⋙ F') (q : D ⟶ M ⋙ D') [IsIso q]
    (σ : H ⋙ M ≅ L ⋙ H') (φ : A ⋙ L ≅ B) (ψ : a ⋙ M ≅ b)
    (α : TwoSquare H F D G) (β : TwoSquare H' F' D' G)
    (hk : ∀ K : S, k.app (A.obj K) ≫ F'.map (φ.hom.app K) ≫
      adjB.counit.app K = adjA.counit.app K)
    (hq : ∀ Z : T, q.app (a.obj Z) ≫ D'.map (ψ.hom.app Z) ≫
      adjb.counit.app Z = adja.counit.app Z)
    (hα : ∀ E : C, q.app (H.obj E) ≫ D'.map (σ.hom.app E) ≫
      β.app (L.obj E) = α.app E ≫ G.map (k.app E)) (K : S) :
    σ.hom.app (A.obj K) ≫ H'.map (φ.hom.app K) ≫
        (mateEquiv adjB adjb β).app K =
      M.map ((mateEquiv adjA adja α).app K) ≫ ψ.hom.app (G.obj K) := by
  let m := (mateEquiv adjA adja α).app K
  let n := (mateEquiv adjB adjb β).app K
  have hm := mateEquiv_counit adjA adja α K
  have hn := mateEquiv_counit adjB adjb β K
  apply (adjb.homEquiv _ _).symm.injective
  change D'.map (σ.hom.app (A.obj K) ≫ H'.map (φ.hom.app K) ≫ n) ≫
      adjb.counit.app (G.obj K) =
    D'.map (M.map m ≫ ψ.hom.app (G.obj K)) ≫ adjb.counit.app (G.obj K)
  apply (cancel_epi (q.app (H.obj (A.obj K)))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  rw [← Category.assoc (D'.map (H'.map (φ.hom.app K))),
    ← Functor.comp_map, β.naturality]
  simp only [Functor.comp_map, Functor.comp_obj, Category.assoc]
  rw [reassoc_of% hα]
  rw [← G.map_comp_assoc, ← G.map_comp, Category.assoc (k.app (A.obj K)), hk]
  have hqm : D.map m ≫ q.app (a.obj (G.obj K)) =
      q.app (H.obj (A.obj K)) ≫ D'.map (M.map m) := by
    simpa only [Functor.comp_obj, Functor.comp_map] using q.naturality m
  rw [← Category.assoc (q.app (H.obj (A.obj K))), ← hqm]
  simp only [Category.assoc]
  rw [hq]
  exact hm.symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The normalized endpoint comparisons commute with the fixed second-mate formula.
Unlike the transport theorem, this asserts an equality of specified morphisms;
it neither supplies endpoint isomorphisms nor constructs an arrow isomorphism.
Source: Stacks Project, Tag 0ATR, composite adjunction and conjugate calculation.
(blueprint: lem-sc-scheme-iso-second-mate-normalized-square)

Proof: Expand the fixed second mate into pullback of the base unit, pullback of the
inverse conjugate of ordinary base change, and the upper counit. The normalization
of φ and ψ is the counit identity for the transported vertical adjunctions; by
adjunction transposition it gives their unit identities too. Transpose the ordinary
base-change maps under the canonical pullback/direct-image adjunctions. Use he,
hr₁ and hr₂ and associativity of the fixed pullback composition comparisons to
identify these transposes. Injectivity of the Hom equivalences identifies ordinary
base change after transport. ConjugateEquiv respects this equality and the endpoint
comparisons; as ordinary base change is invertible, its conjugate inverse respects
it as well. Substitute in the expanded second-mate formulas. Move the normalized
comparisons past the units and counits by the preceding identities, and cancel
the inverse comparison pairs. The remaining equation is the stated square, with
its source comparison the explicit pullback-composition expression above. No
second mate is inverted. Zero objects and empty schemes require no extra cases. -/
theorem schemeIso_secondMate_normalized_square
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P U S T : Scheme.{u}}
    [CompactSpace P] [QuasiSeparatedSpace P] [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : P ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (f' : U ⟶ S) [QuasiCompact f'] [QuasiSeparated f']
    (e : U ≅ P) (he : e.hom ≫ f = f') (g : T ⟶ S)
    (a : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory P)
    (b : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory U)
    (d : schemeDerivedQCohCategory T ⥤ schemeDerivedQCohCategory (pullback f g))
    (b' : schemeDerivedQCohCategory T ⥤ schemeDerivedQCohCategory (pullback f' g))
    (adja : (schemeDerivedQCohProperty S).lift
      ((schemeDerivedQCohProperty P).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
        f _ _).fst E.obj E.property) ⊣ a)
    (adjb : (schemeDerivedQCohProperty S).lift
      ((schemeDerivedQCohProperty U).ι ⋙ schemeDerivedDirectImage f')
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated f') _ _ _ _
        f' _ _).fst E.obj E.property) ⊣ b)
    (adjd : (schemeDerivedQCohProperty T).lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙ schemeDerivedDirectImage (pullback.snd f g))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _).fst E.obj E.property) ⊣ d)
    (adjb' : (schemeDerivedQCohProperty T).lift
      ((schemeDerivedQCohProperty (pullback f' g)).ι ⋙ schemeDerivedDirectImage (pullback.snd f' g))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f' g)) _ _ _ _
        (pullback.snd f' g) _ _).fst E.obj E.property) ⊣ b')
    (hβ : ∀ E : schemeDerivedQCohCategory U,
      IsIso (schemeDerivedBaseChangeMap f' (pullback.snd f' g) g
        (pullback.fst f' g) pullback.condition E.obj))
    (K : schemeDerivedQCohCategory S)
    (r : pullback f' g ⟶ pullback f g)
    (hr₁ : r ≫ pullback.fst f g = pullback.fst f' g ≫ e.hom)
    (hr₂ : r ≫ pullback.snd f g = pullback.snd f' g)
    [IsIso r]
    [QuasiSeparatedSpace (pullback f g : Scheme.{u})]
    [QuasiSeparatedSpace (pullback f' g : Scheme.{u})]
    (hβf : ∀ E : schemeDerivedQCohCategory P,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition E.obj))
    (φ : (a ⋙ (schemeDerivedQCohProperty P).ι) ⋙ derivedPullback e.hom ≅
      b ⋙ (schemeDerivedQCohProperty U).ι)
    (ψ : (d ⋙ (schemeDerivedQCohProperty (pullback f g)).ι) ⋙ derivedPullback r ≅
      b' ⋙ (schemeDerivedQCohProperty (pullback f' g)).ι)
    (hφ : SchemeIsoRightAdjointNormalized f f' e he a b adja adjb φ)
    (hψ : SchemeIsoRightAdjointNormalized (pullback.snd f g) (pullback.snd f' g)
      (asIso r) hr₂ d b' adjd adjb' ψ) :
    (schemeIsoMateSourceIso f f' e g a b K r hr₁ φ).hom ≫
        (dualityEquationBaseChangeMap f' g b b' adjb adjb' hβ K).hom =
      (derivedPullback r).map
          (dualityEquationBaseChangeMap f g a d adja adjd hβf K).hom ≫
        ψ.hom.app (((schemeDerivedQCohProperty T).lift
          ((schemeDerivedQCohProperty S).ι ⋙ derivedPullback g)
          (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1 E.obj E.property)).obj K)
    := by
  classical
  let L := qcPullback e.hom
  let M := qcPullback r
  let φq : a ⋙ L ≅ b := NatIso.ofComponents
    (fun E ↦ (schemeDerivedQCohProperty U).isoMk (φ.app E)) (by
      intro E F t
      ext
      exact φ.hom.naturality t)
  let ψq : d ⋙ M ≅ b' := NatIso.ofComponents
    (fun E ↦ (schemeDerivedQCohProperty (pullback f' g)).isoMk (ψ.app E)) (by
      intro E F t
      ext
      exact ψ.hom.naturality t)
  obtain ⟨k, q, σ, hqiso, hordinary, hkapp, hqapp, hσapp⟩ :=
    schemeIso_inverseBaseChange_transport
    f f' e he g r hr₁ hr₂ hβ hβf
  let : IsIso q := hqiso
  have hk : ∀ E : schemeDerivedQCohCategory S,
      k.app (a.obj E) ≫ (qcDirectImage f').map (φq.hom.app E) ≫
        adjb.counit.app E = adja.counit.app E := by
    intro E
    ext
    change (k.app (a.obj E)).hom ≫
        (schemeDerivedDirectImage f').map (φ.hom.app E) ≫
        (adjb.counit.app E).hom = (adja.counit.app E).hom
    rw [hkapp]
    simpa only [Category.assoc] using hφ E
  have hq : ∀ E : schemeDerivedQCohCategory T,
      q.app (d.obj E) ≫ (qcDirectImage (pullback.snd f' g)).map (ψq.hom.app E) ≫
        adjb'.counit.app E = adjd.counit.app E := by
    intro E
    ext
    change (q.app (d.obj E)).hom ≫
        (schemeDerivedDirectImage (pullback.snd f' g)).map (ψ.hom.app E) ≫
        (adjb'.counit.app E).hom = (adjd.counit.app E).hom
    exact schemeIso_liftedComparison_counit (pullback.snd f g) (pullback.snd f' g)
      (asIso r) hr₂ d b' adjd adjb' ψ q hqapp hψ E
  have h := source_iso_mate_comparison adja adjb adjd adjb' k q σ φq ψq
    (qcInverseBaseChange f g hβf) (qcInverseBaseChange f' g hβ)
    hk hq hordinary K
  rw [← dualityEquationBaseChangeMap_eq_inverseSquareMate f g a d adja adjd hβf K,
    ← dualityEquationBaseChangeMap_eq_inverseSquareMate f' g b b' adjb adjb' hβ K] at h
  have hambient := congrArg (fun t ↦ t.hom) h
  change (σ.hom.app (a.obj K)).hom ≫
      (derivedPullback (pullback.fst f' g)).map (φ.hom.app K) ≫
      (dualityEquationBaseChangeMap f' g b b' adjb adjb' hβ K).hom =
    (derivedPullback r).map (dualityEquationBaseChangeMap f g a d adja adjd hβf K).hom ≫
      ψ.hom.app ((qcPullback g).obj K) at hambient
  rw [hσapp] at hambient
  simpa only [schemeIsoMateSourceIso, Iso.trans_hom, Iso.app_hom, Iso.app_inv,
    Iso.symm_hom, eqToIso.hom, Functor.mapIso_hom, Category.assoc]
    using hambient

end
end AlgebraicGeometry
