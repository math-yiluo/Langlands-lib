/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQcqsPushforwardContinuity
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-! # Continuity of derived closed costalks -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private noncomputable def triangleComparison
    {C A I : Type*} [Category* C] [Category* A] [Category I]
    [HasShift C ℤ] [Abelian A] [HasColimitsOfShape I A]
    (T : I ⥤ Triangle C) (c : Cocone T) (F : C ⥤ A) [F.ShiftSequence ℤ] (n : ℤ)
    (π : Triangle C ⥤ C) :
    colimit (T ⋙ π ⋙ F.shift n) ⟶ (F.shift n).obj (π.obj c.pt) :=
  colimit.desc _ ((π ⋙ F.shift n).mapCocone c)

private theorem triangleComparison_isIso
    {C A I : Type*} [Category* C] [Category* A] [Category I]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [Abelian A] [HasColimitsOfShape I A] [HasExactColimitsOfShape I A]
    (T : I ⥤ Triangle C) (c : Cocone T)
    (hT : ∀ s, T.obj s ∈ distTriang C) (hc : c.pt ∈ distTriang C)
    (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]
    (m n : ℤ) (h : m + 1 = n)
    [IsIso (triangleComparison T c F m Triangle.π₂)]
    [IsIso (triangleComparison T c F m Triangle.π₃)]
    [IsIso (triangleComparison T c F n Triangle.π₂)]
    [IsIso (triangleComparison T c F n Triangle.π₃)] :
    IsIso (triangleComparison T c F n Triangle.π₁) := by
  let A₀ := T ⋙ Triangle.π₂ ⋙ F.shift m
  let A₁ := T ⋙ Triangle.π₃ ⋙ F.shift m
  let A₂ := T ⋙ Triangle.π₁ ⋙ F.shift n
  let A₃ := T ⋙ Triangle.π₂ ⋙ F.shift n
  let A₄ := T ⋙ Triangle.π₃ ⋙ F.shift n
  let d₀ : A₀ ⟶ A₁ :=
    Functor.whiskerRight (Functor.whiskerLeft T Triangle.π₂Toπ₃) (F.shift m)
  let d₁ : A₁ ⟶ A₂ :=
    { app s := F.homologySequenceδ (T.obj s) m n h
      naturality _ _ f := F.homologySequenceδ_naturality (T.map f) m n h }
  let d₂ : A₂ ⟶ A₃ :=
    Functor.whiskerRight (Functor.whiskerLeft T Triangle.π₁Toπ₂) (F.shift n)
  let d₃ : A₃ ⟶ A₄ :=
    Functor.whiskerRight (Functor.whiskerLeft T Triangle.π₂Toπ₃) (F.shift n)
  have z₀ : d₀ ≫ d₁ = 0 := by
    ext s
    exact F.comp_homologySequenceδ (T.obj s) (hT s) m n h
  have z₁ : d₁ ≫ d₂ = 0 := by
    ext s
    exact F.homologySequenceδ_comp (T.obj s) (hT s) m n h
  have z₂ : d₂ ≫ d₃ = 0 := by
    ext s
    exact F.homologySequence_comp (T.obj s) (hT s) n
  have e₀ : (ShortComplex.mk d₀ d₁ z₀).Exact :=
    (ShortComplex.exact_iff_evaluation _).2
      (fun s ↦ F.homologySequence_exact₃ (T.obj s) (hT s) m n h)
  have e₁ : (ShortComplex.mk d₁ d₂ z₁).Exact :=
    (ShortComplex.exact_iff_evaluation _).2
      (fun s ↦ F.homologySequence_exact₁ (T.obj s) (hT s) m n h)
  have e₂ : (ShortComplex.mk d₂ d₃ z₂).Exact :=
    (ShortComplex.exact_iff_evaluation _).2
      (fun s ↦ F.homologySequence_exact₂ (T.obj s) (hT s) n)
  let R := ComposableArrows.mk₄ (colim.map d₀) (colim.map d₁)
    (colim.map d₂) (colim.map d₃)
  have hR : R.Exact :=
    ComposableArrows.exact_of_δ₀ (e₀.map colim).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀ (e₁.map colim).exact_toComposableArrows
        (e₂.map colim).exact_toComposableArrows)
  let R' := ComposableArrows.mk₄ ((F.shift m).map c.pt.mor₂)
    (F.homologySequenceδ c.pt m n h) ((F.shift n).map c.pt.mor₁)
    ((F.shift n).map c.pt.mor₂)
  have hR' : R'.Exact :=
    ComposableArrows.exact_of_δ₀
      (F.homologySequence_exact₃ c.pt hc m n h).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (F.homologySequence_exact₁ c.pt hc m n h).exact_toComposableArrows
        (F.homologySequence_exact₂ c.pt hc n).exact_toComposableArrows)
  let φ : R ⟶ R' := ComposableArrows.homMk₄
    (triangleComparison T c F m Triangle.π₂)
    (triangleComparison T c F m Triangle.π₃)
    (triangleComparison T c F n Triangle.π₁)
    (triangleComparison T c F n Triangle.π₂)
    (triangleComparison T c F n Triangle.π₃)
    (by
      change colimMap d₀ ≫ triangleComparison T c F m Triangle.π₃ =
        triangleComparison T c F m Triangle.π₂ ≫ (F.shift m).map c.pt.mor₂
      apply colimit.hom_ext
      intro s
      dsimp only [A₀, A₁, A₂, A₃, A₄]
      simp only [triangleComparison, ι_colimMap_assoc, colimit.ι_desc,
        colimit.ι_desc_assoc]
      change (F.shift m).map (T.obj s).mor₂ ≫
          (F.shift m).map (c.ι.app s).hom₃ =
        (F.shift m).map (c.ι.app s).hom₂ ≫ (F.shift m).map c.pt.mor₂
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (F.shift m).map (c.ι.app s).comm₂)
    (by
      change colimMap d₁ ≫ triangleComparison T c F n Triangle.π₁ =
        triangleComparison T c F m Triangle.π₃ ≫ F.homologySequenceδ c.pt m n h
      apply colimit.hom_ext
      intro s
      dsimp only [A₀, A₁, A₂, A₃, A₄]
      simp only [triangleComparison, ι_colimMap_assoc, colimit.ι_desc,
        colimit.ι_desc_assoc]
      exact (F.homologySequenceδ_naturality (c.ι.app s) m n h).symm)
    (by
      change colimMap d₂ ≫ triangleComparison T c F n Triangle.π₂ =
        triangleComparison T c F n Triangle.π₁ ≫ (F.shift n).map c.pt.mor₁
      apply colimit.hom_ext
      intro s
      dsimp only [A₀, A₁, A₂, A₃, A₄]
      simp only [triangleComparison, ι_colimMap_assoc, colimit.ι_desc,
        colimit.ι_desc_assoc]
      change (F.shift n).map (T.obj s).mor₁ ≫
          (F.shift n).map (c.ι.app s).hom₂ =
        (F.shift n).map (c.ι.app s).hom₁ ≫ (F.shift n).map c.pt.mor₁
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (F.shift n).map (c.ι.app s).comm₁)
    (by
      change colimMap d₃ ≫ triangleComparison T c F n Triangle.π₃ =
        triangleComparison T c F n Triangle.π₂ ≫ (F.shift n).map c.pt.mor₂
      apply colimit.hom_ext
      intro s
      dsimp only [A₀, A₁, A₂, A₃, A₄]
      simp only [triangleComparison, ι_colimMap_assoc, colimit.ι_desc,
        colimit.ι_desc_assoc]
      change (F.shift n).map (T.obj s).mor₂ ≫
          (F.shift n).map (c.ι.app s).hom₃ =
        (F.shift n).map (c.ι.app s).hom₂ ≫ (F.shift n).map c.pt.mor₂
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (F.shift n).map (c.ι.app s).comm₂)
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hR hR' φ
    (by change Epi (triangleComparison T c F m Triangle.π₂); infer_instance)
    (by change IsIso (triangleComparison T c F m Triangle.π₃); infer_instance)
    (by change IsIso (triangleComparison T c F n Triangle.π₂); infer_instance)
    (by change Mono (triangleComparison T c F n Triangle.π₃); infer_instance)

private theorem comparison_ofNatIso
    {C A I : Type*} [Category* C] [Category* A] [Category I]
    [HasColimitsOfShape I A] (D : I ⥤ C) (c : Cocone D)
    {F G : C ⥤ A} (e : F ≅ G)
    [IsIso (colimit.desc (D ⋙ F) (F.mapCocone c))] :
    IsIso (colimit.desc (D ⋙ G) (G.mapCocone c)) := by
  have heq : colimMap (Functor.whiskerLeft D e.hom) ≫
      colimit.desc (D ⋙ G) (G.mapCocone c) =
    colimit.desc (D ⋙ F) (F.mapCocone c) ≫ e.hom.app c.pt := by
    apply colimit.hom_ext
    intro s
    simp only [ι_colimMap_assoc, colimit.ι_desc, colimit.ι_desc_assoc]
    exact (e.hom.naturality (c.ι.app s)).symm
  have hi : IsIso (colimMap (Functor.whiskerLeft D e.hom)) :=
    inferInstanceAs (IsIso (colim.map (Functor.whiskerLeft D e.hom)))
  have : IsIso (colimMap (Functor.whiskerLeft D e.hom) ≫
      colimit.desc (D ⋙ G) (G.mapCocone c)) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_left (colimMap (Functor.whiskerLeft D e.hom))
    (colimit.desc (D ⋙ G) (G.mapCocone c))

private noncomputable def localizationTriangleFunctor
    {C : Type*} [Category* C] [HasShift C ℤ]
    (F G : C ⥤ C) (f : F ⟶ 𝟭 C) (g : 𝟭 C ⟶ G)
    (δ : G ⟶ F ⋙ shiftFunctor C (1 : ℤ)) : C ⥤ Triangle C where
  obj K := Triangle.mk (f.app K) (g.app K) (δ.app K)
  map k :=
    { hom₁ := F.map k
      hom₂ := k
      hom₃ := G.map k
      comm₁ := (f.naturality k).symm
      comm₂ := (g.naturality k).symm
      comm₃ := (δ.naturality k).symm }
  map_id K := by ext <;> simp [Triangle.mk]
  map_comp k l := by ext <;> simp

/-- Colimits of complexes with a common strict lower bound retain that bound.
Source: the degreewise colimit construction for homological complexes, used in
Hemo--Richarz--Scholbach, Lemma 5.3(2).
(auxiliary; not a blueprint node)

Proof: evaluation at any degree below the bound preserves the colimit. Every
object of that evaluated diagram is zero, hence its colimit is zero. -/
theorem colimit_isStrictlyGE
    {C : Type*} [Category* C] [Abelian C]
    {I : Type*} [Category I] [HasColimitsOfShape I C]
    (N : I ⥤ CochainComplex C ℤ) (a : ℤ)
    (hN : ∀ s, (N.obj s).IsStrictlyGE a) : (colimit N).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro r hr
  exact (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) r)
    (colimit.isColimit N)).isZero_pt ((N ⋙ HomologicalComplex.eval C (.up ℤ) r).isZero
      (fun s ↦ by
        have := hN s
        exact (N.obj s).isZero_of_isStrictlyGE a r hr))

private noncomputable def canonicalContinuityIsColimit
    {A I : Type*} [Category* A] [Abelian A] [Category I]
    [HasColimitsOfShape I A] (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    (hD : ∀ s, (D.obj s).IsStrictlyGE a) :
    IsColimit (condensedContinuityCocone D a) := by
  let π := Functor.whiskerLeft D ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A)
  have hπ (s : I) : IsIso (π.app s) := by
    have := hD s
    exact inferInstanceAs (IsIso ((D.obj s).πTruncGE a))
  have : IsIso π := NatIso.isIso_of_isIso_app π
  exact (IsColimit.precomposeHomEquiv (asIso π) (colimit.cocone _)).2
    (colimit.isColimit _)

private theorem comparison_of_colimitCocone
    {C A I : Type*} [Category* C] [Category* A] [Category I]
    [HasColimitsOfShape I A] (D : I ⥤ C) (c d : Cocone D)
    (hc : IsColimit c) (hd : IsColimit d) (F : C ⥤ A)
    [IsIso (colimit.desc (D ⋙ F) (F.mapCocone c))] :
    IsIso (colimit.desc (D ⋙ F) (F.mapCocone d)) := by
  have heq : colimit.desc (D ⋙ F) (F.mapCocone d) =
      colimit.desc (D ⋙ F) (F.mapCocone c) ≫ F.map (hc.desc d) := by
    apply colimit.hom_ext
    intro s
    simp only [colimit.ι_desc_assoc, colimit.ι_desc]
    change F.map (d.ι.app s) = F.map (c.ι.app s) ≫ F.map (hc.desc d)
    rw [← F.map_comp, hc.fac]
  have : IsIso (hc.desc d) := by
    change IsIso ((IsColimit.coconePointUniqueUpToIso hc hd).hom)
    infer_instance
  rw [heq]
  infer_instance

-- Use the existing closed-structure and coefficient-pullback APIs without unfolding them.
attribute [local irreducible] CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint

noncomputable local instance hasZeroMorphisms_condensedRingObj_condensedClosedCostalkDerived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :
    HasZeroMorphisms (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := inferInstance

set_option synthInstance.maxSize 4096 in
/-- Derived closed costalks commute with uniformly bounded-below filtered colimits.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(2), final paragraph, using (3.4)
and Lemma 5.3(1).
(auxiliary; not a blueprint node)

Proof: let k be the complementary open immersion. It is quasi-compact because T
is noetherian. Apply the functorial recollement triangle i_*Ri! -> id -> Rk_*k*
to the diagram and its good-truncated colimit. All three functors preserve a
common cohomological lower bound. Exact filtered colimits produce the colimit
long exact sequence on cohomology. The middle comparison is invertible because
cohomology commutes with filtered colimits; the third is invertible by Lemma
5.3(1) applied to k, and the exact colimit-preserving restriction k*. The five
lemma makes the first comparison invertible. The closed pushforward i_* is
exact, fully faithful, and preserves colimits (its right adjoint is H), and thus
reflects the resulting cohomology comparison on Z. Uniqueness of right adjoints
identifies the H in the statement with the exceptional inverse image supplied
by recollement, compatibly with units and counits. Naturality identifies the
comparison with condensedContinuityComparison, including its good-truncation
projection. Empty closed or open parts give the same argument with zero terms. -/
theorem condensed_closed_costalk_derived_continuity
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (H : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    [H.Additive] (adj : CondensedRing.lowerStar Λ i ⊣ H)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ℤ)
    (a : ℤ) (hD : ∀ s, (D.obj s).IsStrictlyGE a) (q : ℤ) :
    IsIso (condensedContinuityComparison D a
      (DerivedCategory.Q ⋙ H.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor _ q)) := by
  classical
  let A := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)
  let B := Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)
  have : HasColimitsOfShape I A := inferInstance
  have : HasExactColimitsOfShape I A := inferInstance
  have : HasColimitsOfShape I B := inferInstance
  have : HasExactColimitsOfShape I B := inferInstance
  have : HasColimitsOfShape I (CochainComplex A ℤ) := inferInstance
  have : HasColimitsOfShape I (CochainComplex B ℤ) := inferInstance
  -- Use the colimits of the ambient categories directly, including for composite diagrams.
  have (E : I ⥤ A) : HasColimit E := HasColimitsOfShape.has_colimit E
  have (E : I ⥤ B) : HasColimit E := HasColimitsOfShape.has_colimit E
  have (E : I ⥤ CochainComplex A ℤ) : HasColimit E := HasColimitsOfShape.has_colimit E
  let W : T.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : TopologicalSpace.NoetherianSpace W :=
    W.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact W.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hk : Set.range W.ι = (Set.range i)ᶜ := W.range_ι
  have hrec := CondensedRing.condensed_open_closed_recollement Λ i W.ι hk
  obtain ⟨hclosed, hr⟩ := hrec
  let _ := hclosed
  have hFull := hr.2.2.2.2.2.2.2.2.2.1
  have hFaith := hr.2.2.2.2.2.2.2.2.2.2.1
  have hs := hr.2.2.2.2.2.2.2.2.2.2.2.2
  rcases hs with ⟨H₀, hAdd, hLim, ash, aj, bj, ai, bi, hjs, his, hdata⟩
  let _ := hAdd
  let _ := hLim
  let _ := hjs
  let _ := his
  let _ := hFull
  let _ := hFaith
  have htri := hdata.2.2.2.2.2.2.2.2.2.2.2.2
  let ε := htri.choose_spec.choose
  have hClosed := htri.choose_spec.choose_spec.2.2.2.1
  let C := Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)
  have : HasColimitsOfShape I C := inferInstance
  have : HasColimitsOfShape I (CochainComplex C ℤ) := inferInstance
  have (E : I ⥤ CochainComplex C ℤ) : HasColimit E := HasColimitsOfShape.has_colimit E
  let kstar : A ⥤ C := CondensedRing.upperStar Λ W.ι
  let kpush : C ⥤ A := CondensedRing.lowerStar Λ W.ι
  let ipush : B ⥤ A := CondensedRing.lowerStar Λ i
  let rawi := H₀.rightDerivedFunctorPlus ⋙ ipush.mapDerivedCategoryPlus
  let rawk := kstar.mapDerivedCategoryPlus ⋙ kpush.rightDerivedFunctorPlus
  let loc := localizationTriangleFunctor rawi rawk bi.counit bj.unit ε
  let loc' := loc ⋙ (DerivedCategory.Plus.ι (C := A)).mapTriangle
  let d := condensedContinuityCocone D a
  have hd : IsColimit d := canonicalContinuityIsColimit D a hD
  have hda : d.pt.IsStrictlyGE a :=
    colimit_isStrictlyGE (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A) a
      (fun s ↦ inferInstanceAs (CochainComplex.IsStrictlyGE ((D.obj s).truncGE a) a))
  let Dp : I ⥤ CochainComplex.Plus A :=
    (CochainComplex.plus A).lift D (fun s ↦ ⟨a, hD s⟩)
  let dp : Cocone Dp :=
    { pt := ⟨d.pt, ⟨a, hda⟩⟩
      ι :=
        { app s := ⟨d.ι.app s⟩
          naturality _ _ f := by
            apply ObjectProperty.hom_ext
            exact (d.w f).trans (Category.comp_id _).symm } }
  let TT := Dp ⋙ DerivedCategory.Plus.Q ⋙ loc'
  let tc : Cocone TT := loc'.mapCocone (DerivedCategory.Plus.Q.mapCocone dp)
  have hTT (s : I) : TT.obj s ∈ distTriang (DerivedCategory A) :=
    (DerivedCategory.Plus.ι (C := A)).map_distinguished _ (hClosed _)
  have htc : tc.pt ∈ distTriang (DerivedCategory A) :=
    (DerivedCategory.Plus.ι (C := A)).map_distinguished _ (hClosed _)
  let F := DerivedCategory.homologyFunctor A 0
  let eQ : CochainComplex.Plus.ι A ⋙ DerivedCategory.Q ≅
      DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι :=
    (DerivedCategory.Plus.QCompιIso A).symm
  have hid (r : ℤ) : IsIso (triangleComparison TT tc F r Triangle.π₂) := by
    let C := HomologicalComplex.homologyFunctor A (.up ℤ) r
    have hb : IsIso (colimit.desc (D ⋙ C) (C.mapCocone d)) := by
      change IsIso ((IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
        (isColimitOfPreserves C hd)).hom)
      infer_instance
    let e : DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ⋙
        DerivedCategory.homologyFunctor A r ≅ CochainComplex.Plus.ι A ⋙ C :=
      Functor.isoWhiskerRight eQ.symm (DerivedCategory.homologyFunctor A r) ≪≫
        Functor.isoWhiskerLeft (CochainComplex.Plus.ι A)
          (DerivedCategory.homologyFunctorFactors A r)
    have hb' : IsIso (colimit.desc (Dp ⋙ CochainComplex.Plus.ι A ⋙ C)
        ((CochainComplex.Plus.ι A ⋙ C).mapCocone dp)) := hb
    exact comparison_ofNatIso Dp dp e.symm
  have hkComp (r : ℤ) : IsIso (triangleComparison TT tc F r Triangle.π₃) := by
    let K : CochainComplex A ℤ ⥤ CochainComplex C ℤ :=
      kstar.mapHomologicalComplex (.up ℤ)
    let R : I ⥤ CochainComplex C ℤ := D ⋙ K
    let cd := K.mapCocone d
    have hR (s : I) : (R.obj s).IsStrictlyGE a := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro t ht
      exact kstar.map_isZero ((D.obj s).isZero_of_isStrictlyGE a t ht)
    have : PreservesColimitsOfShape I kstar :=
      (CondensedRing.upperStarLowerStarAdjunction Λ W.ι).leftAdjoint_preservesColimits
        |>.preservesColimitsOfShape
    have hcd : IsColimit cd := isColimitOfPreserves K hd
    let V := DerivedCategory.Q ⋙ kpush.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor A r
    have hb : IsIso (colimit.desc (R ⋙ V)
        (V.mapCocone (condensedContinuityCocone R a))) :=
      condensed_qcqs_pushforward_continuity Λ W.ι R a
        (fun s t ht ↦ by have := hR s; exact (R.obj s).isZero_of_isGE a t ht) r
    have hbc : IsIso (colimit.desc (R ⋙ V) (V.mapCocone cd)) :=
      comparison_of_colimitCocone R (condensedContinuityCocone R a) cd
        (canonicalContinuityIsColimit R a hR) hcd V
    let e : DerivedCategory.Plus.Q ⋙ rawk ⋙ DerivedCategory.Plus.ι ⋙
        DerivedCategory.homologyFunctor A r ≅ CochainComplex.Plus.ι A ⋙ K ⋙ V :=
      Functor.isoWhiskerLeft (DerivedCategory.Plus.Q ⋙ kstar.mapDerivedCategoryPlus)
          (Functor.isoWhiskerRight kpush.rightDerivedFunctorPlusCompatibility
            (DerivedCategory.homologyFunctor A r)) ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft DerivedCategory.Plus.Q
            kstar.mapDerivedCategoryPlusCompatibility)
          (kpush.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor A r) ≪≫
        Functor.isoWhiskerRight eQ.symm
          (kstar.mapDerivedCategory ⋙ kpush.rightDerivedFunctor ⋙
            DerivedCategory.homologyFunctor A r) ≪≫
        Functor.isoWhiskerLeft (CochainComplex.Plus.ι A)
          (Functor.isoWhiskerRight kstar.mapDerivedCategoryFactors
            (kpush.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor A r))
    have hbc' : IsIso (colimit.desc (Dp ⋙ CochainComplex.Plus.ι A ⋙ K ⋙ V)
        ((CochainComplex.Plus.ι A ⋙ K ⋙ V).mapCocone dp)) := hbc
    exact comparison_ofNatIso Dp dp e.symm
  have hiComp : IsIso (triangleComparison TT tc F q Triangle.π₁) :=
    triangleComparison_isIso TT tc hTT htc F (q - 1) q (by omega)
  let e : DerivedCategory.Plus.Q ⋙ rawi ⋙ DerivedCategory.Plus.ι ⋙
      DerivedCategory.homologyFunctor A q ≅ CochainComplex.Plus.ι A ⋙
        DerivedCategory.Q ⋙ H.rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor B q ⋙ ipush :=
    Functor.isoWhiskerLeft (DerivedCategory.Plus.Q ⋙ H₀.rightDerivedFunctorPlus)
        (ipush.mapDerivedCategoryPlusHomologyFunctorIso q).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft DerivedCategory.Plus.Q H₀.rightDerivedFunctorPlusCompatibility)
        (DerivedCategory.homologyFunctor B q ⋙ ipush) ≪≫
      Functor.isoWhiskerRight eQ.symm
        (H₀.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q ⋙ ipush) ≪≫
      Functor.isoWhiskerLeft (CochainComplex.Plus.ι A ⋙ DerivedCategory.Q)
        (Functor.isoWhiskerRight (Functor.rightDerivedFunctorNatIso (ash.rightAdjointUniq adj))
          (DerivedCategory.homologyFunctor B q ⋙ ipush))
  have hraw : IsIso (colimit.desc (Dp ⋙ DerivedCategory.Plus.Q ⋙ rawi ⋙
      DerivedCategory.Plus.ι ⋙ DerivedCategory.homologyFunctor A q)
    ((DerivedCategory.Plus.Q ⋙ rawi ⋙ DerivedCategory.Plus.ι ⋙
      DerivedCategory.homologyFunctor A q).mapCocone dp)) := hiComp
  have hpush : IsIso (colimit.desc (D ⋙ DerivedCategory.Q ⋙ H.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor B q ⋙ ipush)
    ((DerivedCategory.Q ⋙ H.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q ⋙
      ipush).mapCocone d)) := comparison_ofNatIso Dp dp e
  let V := DerivedCategory.Q ⋙ H.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q
  have : PreservesColimitsOfShape I ipush :=
    ash.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have hh : IsIso (ipush.map (colimit.desc (D ⋙ V) (V.mapCocone d))) := by
    have hh' : IsIso (colimit.post (D ⋙ V) ipush ≫
        ipush.map (colimit.desc (D ⋙ V) (V.mapCocone d))) := by
      rw [colimit.post_desc]
      exact hpush
    exact IsIso.of_isIso_comp_left (colimit.post (D ⋙ V) ipush) _
  change IsIso (colimit.desc (D ⋙ V) (V.mapCocone d))
  exact isIso_of_reflects_iso _ ipush

end AlgebraicGeometry.ProEtale
