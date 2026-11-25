/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeSourceIso
import WeilConjectures.AlgebraicGeometry.SingleComplexNestedCoefficientCoherence
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVCoverRows
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-! # Compatible strict chain models for a source-open union

## References

* Stacks Project, Tags 08HZ, 08HY, 0DJ9 and 013N--013O
* Tags 013N--013O for strictification of the resolved diagram
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem nested_arrow_iso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (W Z : X.Opens) (hZW : Z ≤ W) :
    let hW : pullback.snd g' W.ι ≫ (W.ι ≫ f) =
        (pullback.fst g' W.ι ≫ f') ≫ g := by
      rw [← pullback.condition_assoc, Category.assoc, h, ← Category.assoc]
    let φW : (derivedPullback (pullback.snd g' W.ι)).obj
        ((derivedPullback W.ι).obj K) ⟶
        (derivedPullback (pullback.fst g' W.ι)).obj K' :=
    (((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))))
      (pullback.snd g' W.ι) W.ι).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
      (pullback.condition (f := g') (g := W.ι)).symm) ≫
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))))
      (pullback.fst g' W.ι) g').inv.app K ≫
    (derivedPullback (pullback.fst g' W.ι)).map φ)
    Nonempty (Arrow.mk (singleComplexOpenComparison f f' g g' h K K' φ Z) ≅
      Arrow.mk (singleComplexOpenComparison (W.ι ≫ f) (pullback.fst g' W.ι ≫ f')
        g (pullback.snd g' W.ι) hW ((derivedPullback W.ι).obj K)
        ((derivedPullback (pullback.fst g' W.ι)).obj K') φW (W.ι ⁻¹ᵁ Z))) := by
  classical
  intro hW phiW
  let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))
  let A := W.ι ⁻¹ᵁ Z
  let e := Scheme.Opens.isoOfLE hZW
  let q := pullback.snd g' W.ι
  let p := pullback.fst g' W.ι
  let t := pullback.snd q A.ι
  let r := pullback.fst q A.ι
  let e' : pullback q A.ι ≅ pullback g' Z.ι :=
    pullbackLeftPullbackSndIso g' W.ι A.ι ≪≫
      asIso (pullback.map g' (A.ι ≫ W.ι) g' Z.ι (𝟙 _) e.hom (𝟙 _)
        (by simp) (by simp [e, A]))
  have hp : e'.hom ≫ pullback.fst g' Z.ι = r ≫ p := by
    simp [e', r, p, q]
  have hq : e'.hom ≫ pullback.snd g' Z.ι = t ≫ e.hom := by
    simp [e', t, q]
  let KW := (derivedPullback W.ι).obj K
  let KW' := (derivedPullback p).obj K'
  let KZ := (derivedPullback Z.ι).obj K
  let KZ' := (derivedPullback (pullback.fst g' Z.ι)).obj K'
  let phiZ := (c (pullback.snd g' Z.ι) Z.ι).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
      (pullback.condition (f := g') (g := Z.ι)).symm) ≫
    (c (pullback.fst g' Z.ι) g').inv.app K ≫
    (derivedPullback (pullback.fst g' Z.ι)).map φ
  let phiA := (c t A.ι).hom.app KW ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj KW)
      (pullback.condition (f := q) (g := A.ι)).symm) ≫
    (c r q).inv.app KW ≫ (derivedPullback r).map phiW
  let alpha : (derivedPullback e.hom).obj KZ ≅ (derivedPullback A.ι).obj KW :=
    (c e.hom Z.ι).app K ≪≫
      eqToIso (congrArg (fun k ↦ (derivedPullback k).obj K)
        (Scheme.Opens.isoOfLE_hom_ι hZW)) ≪≫ (c A.ι W.ι).symm.app K
  let beta : (derivedPullback e'.hom).obj KZ' ≅ (derivedPullback r).obj KW' :=
    (c e'.hom (pullback.fst g' Z.ι)).app K' ≪≫
      eqToIso (congrArg (fun k ↦ (derivedPullback k).obj K') hp) ≪≫
      (c r p).symm.app K'
  have hphi : (derivedPullback t).map alpha.hom ≫ phiA =
      (c t e.hom).hom.app KZ ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj KZ) hq.symm) ≫
      (c e'.hom (pullback.snd g' Z.ι)).inv.app KZ ≫
      (derivedPullback e'.hom).map phiZ ≫ beta.hom := by
    exact singleComplex_nested_coefficient_coherence g' K K' φ W Z hZW e' hp hq
  have hf : e.hom ≫ (Z.ι ≫ f) = A.ι ≫ (W.ι ≫ f) := by
    simp [e, A]
  have hf' : e'.hom ≫ (pullback.fst g' Z.ι ≫ f') = r ≫ (p ≫ f') := by
    rw [← Category.assoc, hp, Category.assoc]
  have hZ : pullback.snd g' Z.ι ≫ (Z.ι ≫ f) =
      (pullback.fst g' Z.ι ≫ f') ≫ g := by
    rw [← pullback.condition_assoc, Category.assoc, h, ← Category.assoc]
  have h0 : t ≫ (e.hom ≫ (Z.ι ≫ f)) =
      (e'.hom ≫ (pullback.fst g' Z.ι ≫ f')) ≫ g := by
    rw [← Category.assoc, ← hq, Category.assoc, hZ, ← Category.assoc]
  have transport := exists_derivedBaseChange_source_iso
    (Z.ι ≫ f) (pullback.fst g' Z.ι ≫ f') g (pullback.snd g' Z.ι) hZ
    e e' t hq.symm h0 KZ KZ' ((derivedPullback A.ι).obj KW)
    ((derivedPullback r).obj KW') phiZ phiA alpha beta hphi
  revert transport h0
  rw [hf, hf']
  intro h0 transport
  obtain ⟨a, b, hab⟩ := transport
  exact ⟨Arrow.isoMk a b hab.symm⟩

-- Normalize the nested comparison to the relative-arrow interface once, at a variable open.
private theorem unionChain_local_arrow
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (W Z : X.Opens) (hZW : Z ≤ W) :
    let fW := W.ι ≫ f
    let p := pullback.fst g' W.ι
    let q := pullback.snd g' W.ι
    let fW' := p ≫ f'
    let sqW : IsPullback q fW' fW g :=
      (IsPullback.of_hasPullback g' W.ι).flip.paste_vert sq
    let KW := (derivedPullback W.ι).obj K
    let KW' := (derivedPullback p).obj K'
    let φW := (relativeMVComp q W.ι).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (pullback.condition (f := g') (g := W.ι)).symm) ≫
      (relativeMVComp p g').inv.app K ≫ (derivedPullback p).map φ
    Nonempty (relativeMVLocalArrow fW fW' g q sqW KW KW' φW (W.ι ⁻¹ᵁ Z) ≅
      Arrow.mk (singleComplexOpenComparison f f' g g' sq.w K K' φ Z)) := by
  exact ⟨(Classical.choice (nested_arrow_iso f f' g g' sq.w K K' φ W Z hZW)).symm⟩

-- Assemble the cone model over abstract arrows, before specializing to scheme comparisons.
private theorem unionChain_of_rows
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (a₀ aU aV aUV bU bV bUV : Arrow (DerivedCategory C))
    (P P' : ShortComplex (CochainComplex C ℤ)) (m : P ⟶ P')
    (e₁ : DerivedCategory.Q.obj P.X₁ ≅ a₀.left)
    (e₂ : DerivedCategory.Q.obj P.X₂ ≅ bU.left ⊞ bV.left)
    (e₃ : DerivedCategory.Q.obj P.X₃ ≅ bUV.left)
    (e₁' : DerivedCategory.Q.obj P'.X₁ ≅ a₀.right)
    (e₂' : DerivedCategory.Q.obj P'.X₂ ≅ bU.right ⊞ bV.right)
    (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ bUV.right)
    (hP : P.ShortExact) (hP' : P'.ShortExact)
    (hα : DerivedCategory.Q.map m.τ₁ ≫ e₁'.hom = e₁.hom ≫ a₀.hom)
    (hU : DerivedCategory.Q.map m.τ₂ ≫ e₂'.hom ≫ biprod.fst =
      e₂.hom ≫ biprod.fst ≫ bU.hom)
    (hV : DerivedCategory.Q.map m.τ₂ ≫ e₂'.hom ≫ biprod.snd =
      e₂.hom ≫ biprod.snd ≫ bV.hom)
    (hγ : DerivedCategory.Q.map m.τ₃ ≫ e₃'.hom = e₃.hom ≫ bUV.hom)
    (jU : bU ≅ aU) (jV : bV ≅ aV) (jUV : bUV ≅ aUV) :
    ∃ (A B A' B' : CochainComplex C ℤ)
      (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
      (hc : t ≫ β = α ≫ t')
      (e₁ : DerivedCategory.Q.obj A ≅ a₀.left)
      (e₂ : DerivedCategory.Q.obj B ≅ aU.left ⊞ aV.left)
      (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅ aUV.left)
      (e₁' : DerivedCategory.Q.obj A' ≅ a₀.right)
      (e₂' : DerivedCategory.Q.obj B' ≅ aU.right ⊞ aV.right)
      (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅ aUV.right),
      DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a₀.hom ∧
      DerivedCategory.Q.map β ≫ e₂'.hom = e₂.hom ≫ biprod.map aU.hom aV.hom ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.map t t' α β hc) ≫ e₃'.hom =
        e₃.hom ≫ aUV.hom := by
  let l₂ := biprod.mapIso (Arrow.leftFunc.mapIso jU) (Arrow.leftFunc.mapIso jV)
  let r₂ := biprod.mapIso (Arrow.rightFunc.mapIso jU) (Arrow.rightFunc.mapIso jV)
  have hβ : DerivedCategory.Q.map m.τ₂ ≫ e₂'.hom =
      e₂.hom ≫ biprod.map bU.hom bV.hom := by
    apply biprod.hom_ext
    · simp only [Category.assoc]
      erw [biprod.map_fst]
      exact hU
    · simp only [Category.assoc]
      erw [biprod.map_snd]
      exact hV
  have h₂ : biprod.map bU.hom bV.hom ≫ r₂.hom =
      l₂.hom ≫ biprod.map aU.hom aV.hom := by
    change biprod.map bU.hom bV.hom ≫
        biprod.map jU.hom.right jV.hom.right =
      biprod.map jU.hom.left jV.hom.left ≫ biprod.map aU.hom aV.hom
    apply biprod.hom_ext
    · simp only [Category.assoc]
      erw [biprod.map_fst, biprod.map_fst_assoc, biprod.map_fst,
        biprod.map_fst_assoc]
      exact congrArg (fun k ↦ biprod.fst ≫ k) jU.hom.w.symm
    · simp only [Category.assoc]
      erw [biprod.map_snd, biprod.map_snd_assoc, biprod.map_snd,
        biprod.map_snd_assoc]
      exact congrArg (fun k ↦ biprod.snd ≫ k) jV.hom.w.symm
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hP
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hP'
  let d := asIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex P))
  let d' := asIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex P'))
  refine ⟨P.X₁, P.X₂, P'.X₁, P'.X₂, P.f, P'.f, m.τ₁, m.τ₂,
    m.comm₁₂.symm, e₁, e₂ ≪≫ l₂, d ≪≫ e₃ ≪≫ Arrow.leftFunc.mapIso jUV,
    e₁', e₂' ≪≫ r₂, d' ≪≫ e₃' ≪≫ Arrow.rightFunc.mapIso jUV, hα, ?_, ?_⟩
  · simp only [Iso.trans_hom, Category.assoc]
    rw [reassoc_of% hβ, h₂]
    rfl
  · dsimp only [Iso.trans_hom, d, d', asIso_hom]
    rw [← DerivedCategory.Q.map_comp_assoc,
      CochainComplex.mappingCone.map_descShortComplex,
      DerivedCategory.Q.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hγ]
    change DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex P) ≫
        e₃.hom ≫ bUV.hom ≫ jUV.hom.right =
      DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex P) ≫
        e₃.hom ≫ jUV.hom.left ≫ aUV.hom
    rw [← jUV.hom.w]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compatible chain models before the short exact cylinder construction. -/
theorem singleComplexOpenComparison_union_compatible_chain_data
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffine S] [IsAffine S']
    [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens)
    (hUqc : IsCompact (U : Set X)) (hVqc : IsCompact (V : Set X))
    (hUVqc : IsCompact ((U ⊓ V : X.Opens) : Set X)) :
    let a : X.Opens → Arrow (schemeDerivedCategory S') := fun Z ↦
      Arrow.mk (singleComplexOpenComparison f f' g g' sq.w K K' φ Z)
    ∃ (A B A' B' : CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
      (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
      (hc : t ≫ β = α ≫ t')
      (e₁ : DerivedCategory.Q.obj A ≅ (a (U ⊔ V)).left)
      (e₂ : DerivedCategory.Q.obj B ≅ (a U).left ⊞ (a V).left)
      (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅
        (a (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj A' ≅ (a (U ⊔ V)).right)
      (e₂' : DerivedCategory.Q.obj B' ≅ (a U).right ⊞ (a V).right)
      (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅
        (a (U ⊓ V)).right),
      DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ (a (U ⊔ V)).hom ∧
      DerivedCategory.Q.map β ≫ e₂'.hom =
        e₂.hom ≫ biprod.map (a U).hom (a V).hom ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.map t t' α β hc) ≫ e₃'.hom =
        e₃.hom ≫ (a (U ⊓ V)).hom := by
  have _ := hK
  have _ := hK'
  have _ := hUqc
  have _ := hVqc
  have _ := hUVqc
  classical
  let W : X.Opens := U ⊔ V
  let fW := W.ι ≫ f
  let p := pullback.fst g' W.ι
  let q := pullback.snd g' W.ι
  let fW' := p ≫ f'
  have sqW : IsPullback q fW' fW g :=
    (IsPullback.of_hasPullback g' W.ι).flip.paste_vert sq
  let KW := (derivedPullback W.ι).obj K
  let KW' := (derivedPullback p).obj K'
  let φW := (relativeMVComp q W.ι).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
      (pullback.condition (f := g') (g := W.ι)).symm) ≫
    (relativeMVComp p g').inv.app K ≫ (derivedPullback p).map φ
  let A : W.toScheme.Opens := W.ι ⁻¹ᵁ U
  let B : W.toScheme.Opens := W.ι ⁻¹ᵁ V
  have hcover : A ⊔ B = ⊤ := by
    change (W.ι ⁻¹ᵁ U) ⊔ (W.ι ⁻¹ᵁ V) = ⊤
    rw [← Scheme.Hom.preimage_sup]
    exact W.ι_preimage_self
  obtain ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hP, hP', hα, hU, hV, hγ⟩ :=
    relativeMV_cover_rows fW fW' g q sqW KW KW' φW A B hcover
  let b := relativeMVLocalArrow fW fW' g q sqW KW KW' φW
  let a : X.Opens → Arrow (schemeDerivedCategory S') := fun Z ↦
    Arrow.mk (singleComplexOpenComparison f f' g g' sq.w K K' φ Z)
  let jU := Classical.choice (unionChain_local_arrow f f' g g' sq K K' φ W U le_sup_left)
  let jV := Classical.choice (unionChain_local_arrow f f' g g' sq K K' φ W V le_sup_right)
  let jUV := Classical.choice (unionChain_local_arrow f f' g g' sq K K' φ W (U ⊓ V)
    (inf_le_left.trans le_sup_left))
  exact unionChain_of_rows (a (U ⊔ V)) (a U) (a V) (a (U ⊓ V))
    (b A) (b B) (b (A ⊓ B)) P P' m e₁ e₂ e₃ e₁' e₂' e₃'
    hP hP' hα hU hV hγ jU jV jUV

end AlgebraicGeometry
