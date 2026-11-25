/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.HypercoverDescent

/-!
# Continuity of étale cohomology at inverse limits

Let `(Xᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over a scheme `S`, with
affine transition maps and limit `X`, and let `F` be an étale sheaf of `Λ`-modules on `S`. Then
`Hᵠ(X, F|_X) = colimᵢ Hᵠ(Xᵢ, F|_{Xᵢ})` ([Stacks, Tag 09YQ]). For `Λ = ℤ` these are abelian
étale sheaves; no torsion hypothesis is needed.

The statement is spelled out elementwise
(`AlgebraicGeometry.Etale.exists_cohomologyRestrictOver_eq_of_isLimit`,
`AlgebraicGeometry.Etale.exists_cohomologyRestrictOver_eq_zero_of_isLimit`): every class on `X`
comes from some `Xᵢ`, and a class on `Xᵢ` which dies on `X` dies on some `Xⱼ`.

## Main definitions

- `AlgebraicGeometry.Etale.cohomologyRestrictOver`: for a morphism `f: Y ⟶ Z` of schemes over
  `S`, the restriction map `Hᵠ(Z, F|_Z) ⟶ Hᵠ(Y, F|_Y)`.

## Implementation details

A class on `X` is the class of a cocycle on a qcqs hypercover of
`X` (`AlgebraicGeometry.Scheme.exists_cohomologyClass_eq_of_isQcqsHypercover`); the truncation of
the hypercover in degrees `≤ q + 1` descends to some `Xᵢ`, and so do the cocycle and the cocycle
condition by continuity of sections.
For injectivity one descends in the same way a refinement on which the cocycle becomes a coboundary
(`AlgebraicGeometry.Scheme.exists_isCoboundary_of_isQcqsHypercover`), the refinement map and the
primitive.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {S : Scheme.{u}}

/-- For a morphism `f : Y ⟶ Z` of schemes over `S` (with structure maps `pY`, `pZ`), the
restriction map `Hᵠ(Z, F|_Z) ⟶ Hᵠ(Y, F|_Y)` of the étale cohomology of the pullbacks of a sheaf
`F` on `S`: pullback along `f` followed by the identification `f^* (pZ^* F) ≅ pY^* F`. -/
noncomputable def cohomologyRestrictOver {Y Z : Scheme.{u}} (pY : Y ⟶ S) (pZ : Z ⟶ S)
    (f : Y ⟶ Z) (hf : f ≫ pZ = pY) (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (q : ℕ) :
    Ext (SemiSimplicialObject.constSheaf Z.smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) pZ).obj F) q →+
      Ext (SemiSimplicialObject.constSheaf Y.smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) pY).obj F) q :=
  (Ext.mk₀ ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) f pZ pY hf.symm).inv.app F)).postcomp _
      (add_zero q) |>.comp (Etale.cohomologyRestrict Λ f _ q)

section Restrict

open SemiSimplicialObject

variable {Λ} {Y Z : Scheme.{u}} (pY : Y ⟶ S) (pZ : Z ⟶ S) (g : Y ⟶ Z) (hg : g ≫ pZ = pY)
  {V : SemiSimplicialObject Z.Etale} {U : SemiSimplicialObject Y.Etale}
  (φ : U ⟶ V.baseChange g)

variable (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- Restriction of sections of `pZ^* F` over `V_n` to sections of `pY^* F` over `U_n` along a
morphism `φ : U ⟶ V ×_Z Y`. -/
noncomputable abbrev restrictAlongBaseChange (n : ℕ) :
    ((pZ)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (V.obj n)) ⟶
      ((pY)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (U.obj n)) :=
  ModuleSheaf.restrictAlong pZ F g pY hg.symm (baseChangeProj g φ n) (baseChangeProj_w g φ n)

lemma cochainDifferential_restrictAlongBaseChange (n : ℕ)
    (s : ((pZ)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (V.obj n))) :
    (U.cochainDifferential ((pY)^*[ModuleCat.{u + 1} Λ].obj F).obj n).hom
        (restrictAlongBaseChange pY pZ g hg φ F n s) =
      restrictAlongBaseChange pY pZ g hg φ F (n + 1)
        ((V.cochainDifferential ((pZ)^*[ModuleCat.{u + 1} Λ].obj F).obj n).hom s) := by
  simp only [cochainDifferential, ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  rw [ModuleSheaf.map_restrictAlong, ModuleSheaf.restrictAlong_map]
  exact congrArg (fun r ↦ r s)
    (ModuleSheaf.restrictAlong_congr pZ F g pY hg.symm _ (baseChangeProj_δ g φ n i).symm)

lemma _root_.CategoryTheory.SemiSimplicialObject.IsCocycle.restrictAlongBaseChange {q : ℕ}
    {s : ((pZ)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (V.obj q))}
    (hs : V.IsCocycle ((pZ)^*[ModuleCat.{u + 1} Λ].obj F) q s) :
    U.IsCocycle ((pY)^*[ModuleCat.{u + 1} Λ].obj F) q
      (restrictAlongBaseChange pY pZ g hg φ F q s) := by
  rw [IsCocycle, cochainDifferential_restrictAlongBaseChange, hs, map_zero]

/-- **Base change of hypercover classes**: for a morphism `g : Y ⟶ Z` over `S`, hypercovers `V`
of `Z` and `U` of `Y` and a morphism `φ : U ⟶ V ×_Z Y`, the restriction to `Y` of the class of a
cocycle `s` on `V` is the class of the restriction of `s` along `φ`. -/
theorem cohomologyRestrictOver_cohomologyClass (hV : V.IsHypercover Z.smallEtaleTopology)
    (hU : U.IsHypercover Y.smallEtaleTopology) (q : ℕ)
    (s : ((pZ)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (V.obj q)))
    (hs : V.IsCocycle ((pZ)^*[ModuleCat.{u + 1} Λ].obj F) q s) :
    cohomologyRestrictOver Λ pY pZ g hg F q (hV.cohomologyClass _ q s hs) =
      hU.cohomologyClass _ q (restrictAlongBaseChange pY pZ g hg φ F q s)
        (hs.restrictAlongBaseChange pY pZ g hg φ F) := by
  let ψ := (Etale.upperStarComp (ModuleCat.{u + 1} Λ) g pZ pY hg.symm).inv.app F
  have h₁ : cohomologyRestrictOver Λ pY pZ g hg F q (hV.cohomologyClass _ q s hs) =
      (Etale.cohomologyRestrict Λ g _ q (hV.cohomologyClass _ q s hs)).comp (Ext.mk₀ ψ)
        (add_zero q) := rfl
  rw [h₁, Etale.cohomologyRestrict_cohomologyClass, ← IsHypercover.cohomologyClass_map,
    ← IsHypercover.cohomologyClass_restrict _ hU φ]
  refine IsHypercover.cohomologyClass_congr _ _ _ ?_ _ _
  simp only [restrictAlongBaseChange, ModuleSheaf.restrictAlong, ModuleSheaf.transition]
  have : homToPullback g (baseChangeProj g φ q) (baseChangeProj_w g φ q) =
      φ.app q := by
    apply hom_ext_pullback
    simp [baseChangeProj_eq]
  rw [this]
  rfl


/-- Restricting along `φ : U ⟶ V ×_Z Y` and then further along the base change `U ×_Y Y' ⟶ U` is
restricting along the composite. -/
lemma restrictAlongBaseChange_trans {Y' : Scheme.{u}} (pY' : Y' ⟶ S) (g' : Y' ⟶ Y)
    (hg' : g' ≫ pY = pY') (n : ℕ)
    (s : ((pZ)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (V.obj n))) :
    restrictAlongBaseChange pY' pZ (g' ≫ g) (by rw [Category.assoc, hg, hg'])
        (baseChangeTrans g' g (baseChangeComp g' (𝟙 (U.baseChange g')) φ)) F n s =
      restrictAlongBaseChange pY' pY g' hg' (𝟙 (U.baseChange g')) F n
        (restrictAlongBaseChange pY pZ g hg φ F n s) := by
  simp only [restrictAlongBaseChange]
  rw [ModuleSheaf.restrictAlong_restrictAlong]
  have hm : baseChangeProj (g' ≫ g) (baseChangeTrans g' g
      (baseChangeComp g' (𝟙 (U.baseChange g')) φ)) n =
        baseChangeProj g' (𝟙 (U.baseChange g')) n ≫ baseChangeProj g φ n := by
    rw [baseChangeProj_baseChangeTrans, baseChangeProj_baseChangeComp, baseChangeProj_eq g φ,
      Category.assoc]
  rw [ModuleSheaf.restrictAlong_congr _ _ _ _ _ _ hm]

/-- Restricting along `𝟙 : V ×_Z Z' ⟶ V ×_Z Z'` and then along the induced morphism
`U ⟶ (V ×_Z Z') ×_{Z'} Y` is restricting along `φ : U ⟶ V ×_Z Y`. -/
lemma restrictAlongBaseChange_baseChangeLift {Z' : Scheme.{u}} (pZ' : Z' ⟶ S) (g' : Y ⟶ Z')
    (h : Z' ⟶ Z) (hgh : g' ≫ h = g) (hh : h ≫ pZ = pZ') (hg' : g' ≫ pZ' = pY) (n : ℕ)
    (s : ((pZ)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (V.obj n))) :
    restrictAlongBaseChange pY pZ' g' hg' (baseChangeLift g φ g' h hgh) F n
        (restrictAlongBaseChange pZ' pZ h hh (𝟙 (V.baseChange h)) F n s) =
      restrictAlongBaseChange pY pZ g hg φ F n s := by
  simp only [restrictAlongBaseChange]
  rw [ModuleSheaf.restrictAlong_restrictAlong, ModuleSheaf.restrictAlong_congr_hom F pZ pY _ hgh]
  have hm : baseChangeProj g' (baseChangeLift g φ g' h hgh) n ≫
      baseChangeProj h (𝟙 (V.baseChange h)) n = baseChangeProj g φ n := by
    rw [baseChangeProj_id, baseChangeProj_baseChangeLift]
  rw [ModuleSheaf.restrictAlong_congr _ _ _ _ _ _ hm]

lemma cohomologyRestrictOver_congr' {g₁ g₂ : Y ⟶ Z} (hg₁ : g₁ ≫ pZ = pY) (h : g₁ = g₂) (q : ℕ) :
    cohomologyRestrictOver Λ pY pZ g₁ hg₁ F q =
      cohomologyRestrictOver Λ pY pZ g₂ (h ▸ hg₁) F q := by
  subst h
  rfl
end Restrict

variable {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Over S)
  [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
  (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
  (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))

include hc

/-- **Continuity of étale cohomology, surjectivity**: every cohomology class of the pullback of `F`
to
the limit `X = lim Xᵢ` comes from some `Xᵢ`. -/
@[stacks 09YQ]
theorem exists_cohomologyRestrictOver_eq_of_isLimit (q : ℕ)
    (x : Ext (SemiSimplicialObject.constSheaf c.pt.left.smallEtaleTopology Λ)
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) c.pt.hom).obj F) q) :
    ∃ (i : I) (y : Ext (SemiSimplicialObject.constSheaf (D.obj i).left.smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.obj i).hom).obj F) q),
      cohomologyRestrictOver Λ c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _) F q y = x := by
  classical
  let D' := D ⋙ Over.forget S
  let c' := (Over.forget S).mapCone c
  let π : D' ⟶ (Functor.const I).obj S :=
    { app i := (D.obj i).hom
      naturality _ _ f := by simp [D'] }
  have hP (j : I) : c.pt.hom = c'.π.app j ≫ π.app j := (Over.w (c.π.app j)).symm
  have : ∀ i, CompactSpace (D'.obj i) := fun i ↦ inferInstanceAs (CompactSpace (D.obj i).left)
  have : ∀ i, QuasiSeparatedSpace (D'.obj i) := fun i ↦
    inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D'.map f) := fun f ↦
    inferInstanceAs (IsAffineHom (D.map f).left)
  have : CompactSpace c.pt.left := Scheme.compactSpace_of_isLimit D' c' hc
  have : QuasiSeparatedSpace c.pt.left := quasiSeparatedSpace_pt hc
  -- a class on the limit is the class of a cocycle on a qcqs hypercover `U`
  obtain ⟨U, hU, z, hz, rfl⟩ := Scheme.exists_cohomologyClass_eq_of_isQcqsHypercover Λ _ q x
  -- the truncation of `U` in degrees `≤ q + 1` descends to a stage
  obtain ⟨k, ⟨d⟩⟩ := exists_truncatedDescent hc U
    (fun n ↦ ⟨hU.compactSpace n, hU.quasiSeparatedSpace n⟩) (q + 1)
  obtain ⟨k₀, f₀, hk₀⟩ := d.exists_isHypercover hc hU.isHypercover
  have hq : q ≤ q + 1 := Nat.le_succ q
  obtain ⟨_, _⟩ := d.qcqs q hq
  -- the cocycle descends to a stage
  obtain ⟨K, h, hK⟩ := ModuleSheaf.exists_restrictAlong_eq_of_isLimit hc π c.pt.hom hP F
    (d.T.obj q hq) (d.m q hq) (d.isPullback q hq) z
  obtain ⟨k', a, b, hab⟩ := IsCofiltered.cospan h f₀
  let d' := d.baseChange (b ≫ f₀)
  let V := d'.T.cosk
  have hV : V.IsHypercover (D'.obj k').smallEtaleTopology := hk₀ k' b
  let m' : (V.obj q).left ⟶ (d.T.obj q hq).left :=
    (d'.T.coskIso q hq).hom.left ≫ pullback.fst _ _
  have hm' : m' ≫ (d.T.obj q hq).hom = (V.obj q).hom ≫ D'.map (a ≫ h) := by
    have := MorphismProperty.Over.w (d'.T.coskIso q hq).hom
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      show (d'.T.coskIso q hq).hom.left ≫ pullback.snd _ _ = (V.obj q).hom from this, hab]
  have hnm : baseChangeProj (c'.π.app k') d'.toCosk q ≫ m' = d.m q hq := by
    simp only [baseChangeProj, m', Category.assoc]
    rw [← Category.assoc (d'.toCosk.app q).left, d'.toCosk_app_left_fst q hq, Category.assoc,
      ← Category.assoc (d'.T.coskIso q hq).inv.left, Scheme.Etale.inv_hom_id_left,
      Category.id_comp]
    exact pullback.lift_fst _ _ _
  obtain ⟨s, hs⟩ := hK a (V.obj q) m' hm' _ (baseChangeProj_w (c'.π.app k') d'.toCosk q) hnm
  -- the cocycle condition descends to a later stage
  let ds := (V.cochainDifferential ((π.app k')^*[ModuleCat.{u + 1} Λ].obj F).obj q).hom s
  have hds : restrictAlongBaseChange c.pt.hom (π.app k') (c'.π.app k') (hP k').symm d'.toCosk F
      (q + 1) ds = 0 := by
    rw [← cochainDifferential_restrictAlongBaseChange]
    exact (congrArg _ hs).trans hz
  obtain ⟨_, _⟩ : Scheme.Etale.qcqs _ (V.obj (q + 1)) :=
    (Scheme.Etale.qcqs _).prop_of_iso (d'.T.coskIso (q + 1) le_rfl).symm (d'.qcqs (q + 1) le_rfl)
  have hpb : IsPullback (baseChangeProj (c'.π.app k') d'.toCosk (q + 1)) (U.obj (q + 1)).hom
      (V.obj (q + 1)).hom (c'.π.app k') := by
    have := d'.isIso_toCosk_app (q + 1) le_rfl
    refine IsPullback.of_iso_pullback ⟨baseChangeProj_w _ _ _⟩
      (Scheme.Etale.leftIso (asIso (d'.toCosk.app (q + 1)))) rfl ?_
    exact MorphismProperty.Over.w (d'.toCosk.app (q + 1))
  obtain ⟨k'', f'', hk''⟩ := ModuleSheaf.exists_restrictAlong_eq_zero_of_isLimit hc π c.pt.hom
    hP F (V.obj (q + 1)) _ hpb ds hds
  let W := V.baseChange (D'.map f'')
  have hW : W.IsHypercover (D'.obj k'').smallEtaleTopology := hV.baseChange _
  have hπ : D'.map f'' ≫ π.app k' = π.app k'' := π.naturality f'' |>.trans (Category.comp_id _)
  let s'' := restrictAlongBaseChange (π.app k'') (π.app k') (D'.map f'') hπ (𝟙 W) F q s
  have hs'' : W.IsCocycle _ q s'' := by
    rw [SemiSimplicialObject.IsCocycle, cochainDifferential_restrictAlongBaseChange]
    exact hk'' (𝟙 _) f'' (Category.id_comp _) _ _ _
  refine ⟨k'', hW.cohomologyClass _ q s'' hs'', ?_⟩
  have hgh : c'.π.app k'' ≫ D'.map f'' = c'.π.app k' := c'.w f''
  refine (cohomologyRestrictOver_cohomologyClass c.pt.hom (π.app k'') (c'.π.app k'') (Over.w _)
    (baseChangeLift (c'.π.app k') d'.toCosk (c'.π.app k'') (D'.map f'') hgh) F hW hU.isHypercover
    q s'' hs'').trans ?_
  apply SemiSimplicialObject.IsHypercover.cohomologyClass_congr
  rw [← hs]
  simp only [restrictAlongBaseChange, s'']
  rw [ModuleSheaf.restrictAlong_restrictAlong,
    ModuleSheaf.restrictAlong_congr_hom F (π.app k') c.pt.hom _ hgh]
  have hm : baseChangeProj (c'.π.app k'')
      (baseChangeLift (c'.π.app k') d'.toCosk (c'.π.app k'') (D'.map f'') hgh) q ≫
        baseChangeProj (D'.map f'') (𝟙 W) q = baseChangeProj (c'.π.app k') d'.toCosk q := by
    simpa [baseChangeProj] using baseChangeProj_baseChangeLift (c'.π.app k') d'.toCosk
      (c'.π.app k'') (D'.map f'') hgh q
  rw [ModuleSheaf.restrictAlong_congr _ _ _ _ _ _ hm]

-- the descent of the refinement, the cocycle and its primitive is a long elaboration
/-- **Continuity of étale cohomology, injectivity**: a cohomology class of the pullback of `F` to
some
`Xᵢ` which vanishes on the limit `X = lim Xᵢ` vanishes on some `Xⱼ`, `j ⟶ i`. -/
@[stacks 09YQ]
theorem exists_cohomologyRestrictOver_eq_zero_of_isLimit (q : ℕ) (i : I)
    (y : Ext (SemiSimplicialObject.constSheaf (D.obj i).left.smallEtaleTopology Λ)
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.obj i).hom).obj F) q)
    (hy : cohomologyRestrictOver Λ c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _) F q y = 0) :
    ∃ (j : I) (φ : j ⟶ i),
      cohomologyRestrictOver Λ (D.obj j).hom (D.obj i).hom (D.map φ).left (Over.w _) F q y = 0 := by
  classical
  set D' := D ⋙ Over.forget S with hD'
  set c' := (Over.forget S).mapCone c with hc'
  let π : D' ⟶ (Functor.const I).obj S :=
    { app i := (D.obj i).hom
      naturality _ _ f := by simp [D'] }
  have hP (j : I) : c.pt.hom = c'.π.app j ≫ π.app j := (Over.w (c.π.app j)).symm
  have hπ {j j' : I} (f : j ⟶ j') : D'.map f ≫ π.app j' = π.app j :=
    (π.naturality f).trans (Category.comp_id _)
  have : ∀ i, CompactSpace (D'.obj i) := fun i ↦ inferInstanceAs (CompactSpace (D.obj i).left)
  have : ∀ i, QuasiSeparatedSpace (D'.obj i) := fun i ↦
    inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D'.map f) := fun f ↦
    inferInstanceAs (IsAffineHom (D.map f).left)
  have : CompactSpace c.pt.left := Scheme.compactSpace_of_isLimit D' c' hc
  have : QuasiSeparatedSpace c.pt.left := quasiSeparatedSpace_pt hc
  -- the final step: a class whose restriction along a morphism of hypercovers is a coboundary
  -- vanishes at that stage
  have final {V : SemiSimplicialObject (D'.obj i).Etale}
      (hV : V.IsHypercover (D'.obj i).smallEtaleTopology)
      {s : ((π.app i)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (V.obj q))}
      (hs : V.IsCocycle ((π.app i)^*[ModuleCat.{u + 1} Λ].obj F) q s) {j : I} (φ : j ⟶ i)
      {W : SemiSimplicialObject (D'.obj j).Etale}
      (hW : W.IsHypercover (D'.obj j).smallEtaleTopology)
      (g : D'.obj j ⟶ D'.obj i) (hgφ : D'.map φ = g) (ψ : W ⟶ V.baseChange g)
      (h : W.IsCoboundary _ q
        (restrictAlongBaseChange (π.app j) (π.app i) g (hgφ ▸ hπ φ) ψ F q s)) :
      cohomologyRestrictOver Λ (D.obj j).hom (D.obj i).hom (D.map φ).left (Over.w _) F q
        (hV.cohomologyClass _ q s hs) = 0 := by
    subst hgφ
    refine (cohomologyRestrictOver_cohomologyClass (π.app j) (π.app i) (D'.map φ) (hπ φ) ψ F hV
      hW q s hs).trans ?_
    exact SemiSimplicialObject.IsHypercover.cohomologyClass_eq_zero_of_isCoboundary _ _ _ _ _ h
  -- a class on the stage `i` is the class of a cocycle on a qcqs hypercover `V₀`
  obtain ⟨V₀, hV₀, s₀, hs₀, rfl⟩ := Scheme.exists_cohomologyClass_eq_of_isQcqsHypercover Λ _ q y
  -- replace `V₀` by a hypercover `V` with unique lifts above degree `q + 1`
  obtain ⟨V, w, hV, hw, hVl⟩ := exists_coskeletal_replacement V₀ hV₀.isHypercover (q + 1)
  let G : Sheaf (D'.obj i).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    (π.app i)^*[ModuleCat.{u + 1} Λ].obj F
  have hw₀ := hw q (Nat.le_succ q)
  have hw₁ := hw (q + 1) le_rfl
  let s : G.obj.obj (op (V.obj q)) := (G.obj.map (inv (w.app q)).op) s₀
  have hws : (G.obj.map (w.app q).op) s = s₀ := by
    simp only [s, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      IsIso.hom_inv_id, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  have hs : V.IsCocycle G q s := by
    have h1 := SemiSimplicialObject.cochainDifferential_restrict_apply w G.obj q s
    rw [hws, show (V₀.cochainDifferential G.obj q).hom s₀ = 0 from hs₀] at h1
    have h2 : (G.obj.map (inv (w.app (q + 1))).op) ((G.obj.map (w.app (q + 1)).op)
        ((V.cochainDifferential G.obj q).hom s)) = (V.cochainDifferential G.obj q).hom s := by
      simp only [← ConcreteCategory.comp_apply, Category.assoc, ← Functor.map_comp, ← op_comp,
        IsIso.inv_hom_id, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
    rw [SemiSimplicialObject.IsCocycle, ← h2, ← h1, map_zero]
  have hclass : hV₀.isHypercover.cohomologyClass G q s₀ hs₀ = hV.cohomologyClass G q s hs :=
    (hV₀.isHypercover.cohomologyClass_congr G q hws.symm hs₀ (hs.restrict w)).trans
      (hV.cohomologyClass_restrict hV₀.isHypercover w G q s hs)
  rw [hclass]
  -- the restriction of the class to the limit is the class of a cocycle on `V₀ ×_{Dᵢ} X`, which
  -- is a coboundary on a refinement `U'`
  have := isAffineHom_π_app D' c' hc i
  have : CompactSpace (((Functor.const I).obj c'.pt).obj i) := ‹CompactSpace c.pt.left›
  have : QuasiSeparatedSpace (((Functor.const I).obj c'.pt).obj i) :=
    ‹QuasiSeparatedSpace c.pt.left›
  have hV₀X := hV₀.baseChange (c'.π.app i)
  have hs₀X := hs₀.restrictAlongBaseChange c.pt.hom (π.app i) (c'.π.app i) (hP i).symm (𝟙 _) F
  have h0 : hV₀X.isHypercover.cohomologyClass _ q _ hs₀X = 0 := by
    rw [← cohomologyRestrictOver_cohomologyClass c.pt.hom (π.app i) (c'.π.app i) (hP i).symm
      (𝟙 _) F hV₀.isHypercover hV₀X.isHypercover q s₀ hs₀]
    exact hy
  obtain ⟨U', hU', f, hf⟩ := Scheme.exists_isCoboundary_of_isQcqsHypercover Λ _ q hV₀X _ hs₀X h0
  let f' : U' ⟶ V.baseChange (c'.π.app i) := baseChangeComp (c'.π.app i) f w
  let σ := restrictAlongBaseChange c.pt.hom (π.app i) (c'.π.app i) (hP i).symm f' F q s
  have hfσ : (((c.pt.hom)^*[ModuleCat.{u + 1} Λ].obj F).obj.map (f.app q).op)
      (restrictAlongBaseChange c.pt.hom (π.app i) (c'.π.app i) (hP i).symm (𝟙 _) F q s₀) = σ := by
    rw [← hws]
    simp only [restrictAlongBaseChange, σ]
    rw [ModuleSheaf.map_restrictAlong, ModuleSheaf.restrictAlong_map]
    have hm : ((f.app q).left ≫ baseChangeProj (c'.π.app i) (𝟙 (V₀.baseChange (c'.π.app i))) q) ≫
        (w.app q).left = baseChangeProj (c'.π.app i) f' q := by
      rw [baseChangeProj_baseChangeComp, baseChangeProj_id, baseChangeProj_eq]
    rw [ModuleSheaf.restrictAlong_congr _ _ _ _ _ _ hm]
  -- the truncation of `U'` descends, together with the morphism `U' ⟶ V ×_{Dᵢ} X`
  obtain ⟨k, ⟨d⟩⟩ := exists_truncatedDescent hc U'
    (fun n ↦ ⟨hU'.compactSpace n, hU'.quasiSeparatedSpace n⟩) (q + 1)
  let e₀ : IsCofiltered.min k i ⟶ i := IsCofiltered.minToRight k i
  let d₀ := d.baseChange (IsCofiltered.minToLeft k i)
  let f₀ := baseChangeLift (c'.π.app i) f' (c'.π.app (IsCofiltered.min k i)) (D'.map e₀)
    (c'.w e₀)
  obtain ⟨k₁, g₁, ⟨Ψ₁⟩⟩ := d₀.exists_hom hc (V.baseChange (D'.map e₀)) f₀
  obtain ⟨k₂, g₂, hΨ₂⟩ := Ψ₁.exists_isCompatible hc
  obtain ⟨k₃, g₃, hk₃⟩ :=
    ((d₀.baseChange g₁).baseChange g₂).exists_isHypercover hc hU'.isHypercover
  let d₃ := ((d₀.baseChange g₁).baseChange g₂).baseChange (𝟙 k₃ ≫ g₃)
  let Ψ₃ := (Ψ₁.baseChange g₂).baseChange (𝟙 k₃ ≫ g₃)
  have hΨ₃ : Ψ₃.IsCompatible := hΨ₂.baseChange _
  let V₃ := d₃.T.cosk
  have hV₃ : V₃.IsHypercover (D'.obj k₃).smallEtaleTopology := hk₃ k₃ (𝟙 _)
  have hW₃ : ∀ n, q + 1 ≤ n → ((((V.baseChange (D'.map e₀)).baseChange (D'.map g₁)).baseChange
      (D'.map g₂)).baseChange (D'.map (𝟙 k₃ ≫ g₃))).HasLifts n := fun n h ↦
    ((((hVl n h).baseChange _).baseChange _).baseChange _).baseChange _ |>.hasLifts
  let Φ := Ψ₃.toCosk hΨ₃ hW₃
  let tot : D'.obj k₃ ⟶ D'.obj i :=
    ((D'.map (𝟙 k₃ ≫ g₃) ≫ D'.map g₂) ≫ D'.map g₁) ≫ D'.map e₀
  let φtot : k₃ ⟶ i := (𝟙 k₃ ≫ g₃) ≫ g₂ ≫ g₁ ≫ e₀
  have hφtot : D'.map φtot = tot := by simp only [φtot, tot, Functor.map_comp, Category.assoc]
  have hπtot : tot ≫ π.app i = π.app k₃ := hφtot ▸ hπ φtot
  let φ₃ : V₃ ⟶ V.baseChange tot := baseChangeTrans _ (D'.map e₀)
    (baseChangeTrans _ (D'.map g₁) (baseChangeTrans (D'.map (𝟙 k₃ ≫ g₃)) (D'.map g₂) Φ))
  let s₃ := restrictAlongBaseChange (π.app k₃) (π.app i) tot hπtot φ₃ F q s
  -- `V₃` agrees with `U'` in degrees `≤ q + 1`
  have hqc (n : ℕ) (hn : n ≤ q + 1) : Scheme.Etale.qcqs _ (V₃.obj n) :=
    (Scheme.Etale.qcqs _).prop_of_iso (d₃.T.coskIso n hn).symm (d₃.qcqs n hn)
  have hpb (n : ℕ) (hn : n ≤ q + 1) : IsPullback (baseChangeProj (c'.π.app k₃) d₃.toCosk n)
      (U'.obj n).hom (V₃.obj n).hom (c'.π.app k₃) := by
    have := d₃.isIso_toCosk_app n hn
    refine IsPullback.of_iso_pullback ⟨baseChangeProj_w _ _ _⟩
      (Scheme.Etale.leftIso (asIso (d₃.toCosk.app n))) rfl ?_
    exact MorphismProperty.Over.w (d₃.toCosk.app n)
  -- the restriction of `s₃` to the limit is `σ`
  have hs₃ : restrictAlongBaseChange c.pt.hom (π.app k₃) (c'.π.app k₃) (hP k₃).symm d₃.toCosk F
      q s₃ = σ := by
    simp only [s₃, σ, restrictAlongBaseChange]
    rw [ModuleSheaf.restrictAlong_restrictAlong,
      ModuleSheaf.restrictAlong_congr_hom F (π.app i) c.pt.hom _
        (show c'.π.app k₃ ≫ tot = c'.π.app i by rw [← hφtot]; exact c'.w φtot)]
    have hm : baseChangeProj (c'.π.app k₃) d₃.toCosk q ≫ baseChangeProj tot φ₃ q =
        baseChangeProj (c'.π.app i) f' q := by
      have e1 := Ψ₃.baseChangeProj_toCosk hΨ₃ hW₃ q (Nat.le_succ q)
      simp only [φ₃, tot, baseChangeProj_baseChangeTrans, Category.assoc]
      rw [baseChangeProj_eq (D'.map (𝟙 k₃ ≫ g₃)) Φ q]
      calc _ = (baseChangeProj (c'.π.app k₃) d₃.toCosk q ≫ (Φ.app q).left) ≫
            pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ :=
            (Category.assoc _ _ _).symm
        _ = _ := by
          rw [e1]
          simp only [baseChangeProj_baseChangeLift_assoc]
          exact baseChangeProj_baseChangeLift _ _ _ _ _ q
    rw [ModuleSheaf.restrictAlong_congr _ _ _ _ _ _ hm]
  cases q with
  | zero =>
    have hσ : σ = 0 := hfσ.symm.trans hf
    obtain ⟨_, _⟩ := hqc 0 (Nat.zero_le _)
    obtain ⟨k₄, g₄, hk₄⟩ := ModuleSheaf.exists_restrictAlong_eq_zero_of_isLimit hc π c.pt.hom hP
      F (V₃.obj 0) _ (hpb 0 (Nat.zero_le _)) s₃ (hs₃.trans hσ)
    let V₄ := V₃.baseChange (D'.map g₄)
    refine ⟨k₄, g₄ ≫ φtot, final hV hs (g₄ ≫ φtot) (hV₃.baseChange _) (D'.map g₄ ≫ tot)
      ((D'.map_comp _ _).trans (congrArg (D'.map g₄ ≫ ·) hφtot))
      (baseChangeTrans (D'.map g₄) tot (baseChangeComp (D'.map g₄) (𝟙 V₄) φ₃)) ?_⟩
    change restrictAlongBaseChange _ _ _ _ _ F 0 s = 0
    rw [restrictAlongBaseChange_trans (π.app k₃) (π.app i) tot hπtot φ₃ F (π.app k₄) (D'.map g₄)
      (hπ g₄)]
    exact hk₄ (𝟙 _) g₄ (Category.id_comp _) _ _ _
  | succ p =>
    obtain ⟨t, ht⟩ := hf
    rw [hfσ] at ht
    obtain ⟨_, _⟩ := hqc p (by omega)
    obtain ⟨K, h₄, hK⟩ := ModuleSheaf.exists_restrictAlong_eq_of_isLimit hc π c.pt.hom hP F
      (V₃.obj p) _ (hpb p (by omega)) t
    let V₄ := V₃.baseChange (D'.map (𝟙 K ≫ h₄))
    have hV₄ : V₄.IsHypercover (D'.obj K).smallEtaleTopology := hV₃.baseChange _
    let l₄ : U' ⟶ V₄.baseChange (c'.π.app K) := baseChangeLift (c'.π.app k₃) d₃.toCosk
      (c'.π.app K) (D'.map (𝟙 K ≫ h₄)) (c'.w _)
    obtain ⟨t₄, ht₄⟩ := hK (𝟙 K) (V₄.obj p) (baseChangeProj _ (𝟙 V₄) p) (baseChangeProj_w _ _ p)
      (baseChangeProj _ l₄ p) (baseChangeProj_w _ _ p)
      (by rw [baseChangeProj_id]; exact baseChangeProj_baseChangeLift _ _ _ _ _ p)
    let φ₄ : V₄ ⟶ V.baseChange (D'.map (𝟙 K ≫ h₄) ≫ tot) :=
      baseChangeTrans _ tot (baseChangeComp _ (𝟙 V₄) φ₃)
    have hπ₄ : (D'.map (𝟙 K ≫ h₄) ≫ tot) ≫ π.app i = π.app K := by
      rw [Category.assoc, hπtot, hπ]
    let s₄ := restrictAlongBaseChange (π.app K) (π.app i) _ hπ₄ φ₄ F (p + 1) s
    let G₄ := (π.app K)^*[ModuleCat.{u + 1} Λ].obj F
    let e₄ := (V₄.cochainDifferential G₄.obj p).hom t₄ - s₄
    have he₄ : restrictAlongBaseChange c.pt.hom (π.app K) (c'.π.app K) (hP K).symm l₄ F (p + 1)
        e₄ = 0 := by
      rw [map_sub, ← cochainDifferential_restrictAlongBaseChange,
        show restrictAlongBaseChange c.pt.hom (π.app K) (c'.π.app K) (hP K).symm l₄ F p t₄ = t
          from ht₄, ht, sub_eq_zero, ← hs₃]
      simp only [s₄, φ₄]
      rw [restrictAlongBaseChange_trans (π.app k₃) (π.app i) tot hπtot φ₃ F (π.app K) _ (hπ _),
        restrictAlongBaseChange_baseChangeLift]
    have hqc₄ : Scheme.Etale.qcqs _ (V₄.obj (p + 1)) :=
      Scheme.Etale.qcqs_baseChange _ (hqc (p + 1) (Nat.le_succ _))
    obtain ⟨_, _⟩ := hqc₄
    have hpb₄ : IsPullback (baseChangeProj (c'.π.app K) l₄ (p + 1)) (U'.obj (p + 1)).hom
        (V₄.obj (p + 1)).hom (c'.π.app K) := by
      have := isPullback_lift_of_isPullback (𝟙 K ≫ h₄) (hpb (p + 1) (Nat.le_succ _))
      rw [show baseChangeProj (c'.π.app K) l₄ (p + 1) = pullback.lift _ _ _ from
        baseChangeProj_baseChangeMk _ _ _ _ _]
      exact this
    obtain ⟨k₅, g₅, hk₅⟩ := ModuleSheaf.exists_restrictAlong_eq_zero_of_isLimit hc π c.pt.hom hP
      F (V₄.obj (p + 1)) _ hpb₄ e₄ he₄
    let V₅ := V₄.baseChange (D'.map g₅)
    let t₅ := restrictAlongBaseChange (π.app k₅) (π.app K) (D'.map g₅) (hπ g₅) (𝟙 V₅) F p t₄
    refine ⟨k₅, g₅ ≫ (𝟙 K ≫ h₄) ≫ φtot, final hV hs _ (hV₄.baseChange _)
      (D'.map g₅ ≫ D'.map (𝟙 K ≫ h₄) ≫ tot)
      ((D'.map_comp _ _).trans (congrArg (D'.map g₅ ≫ ·)
        ((D'.map_comp _ _).trans (congrArg (D'.map (𝟙 K ≫ h₄) ≫ ·) hφtot))))
      (baseChangeTrans (D'.map g₅) _ (baseChangeComp (D'.map g₅) (𝟙 V₅) φ₄)) ⟨t₅, ?_⟩⟩
    rw [cochainDifferential_restrictAlongBaseChange, restrictAlongBaseChange_trans (π.app K)
      (π.app i) _ hπ₄ φ₄ F (π.app k₅) (D'.map g₅) (hπ g₅)]
    have : (V₄.cochainDifferential G₄.obj p).hom t₄ = e₄ + s₄ := (sub_add_cancel _ _).symm
    rw [this, map_add, hk₅ (𝟙 _) g₅ (Category.id_comp _) _ _ _, zero_add]

end AlgebraicGeometry.Etale
