/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeEtaleCohomology
public import WeilConjectures.CategoryTheory.Sites.WithSection.TorsorWithSection
public import WeilConjectures.CategoryTheory.Sites.ContractedProductPresentation
public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorClassNaturality
import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorForgetNormalization
import Mathlib.CategoryTheory.Preadditive.Comma
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions

/-!
# Relative first cohomology and torsors with an open section

## References

* Stacks Project, Cohomology on Sites, Tag 03AJ
* Stacks Project, Tags 0G71 and 0G78
* Stacks Project, Tag 03AJ, relative refinement
* Stacks Project, Tag 03AJ, canonical extension class
* Stacks Project, Tag 03AJ, relative cone construction
* Stacks Project, Tag 013T and the relative refinement of Tag 03AJ
* Stacks Project, Tag 013T and Tag 03AJ, relative refinement
* Tag 03AJ, relative refinement
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The restriction square for a morphism of sheaf complexes commutes. -/
theorem relativeSectionMap_square (T : Scheme.{u}) (U : T.Etale)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (f : I ⟶ J) :
    HomologicalComplex.extendMap
        (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex _).map f)
        ComplexShape.embeddingUpNat ≫ relativeSectionRestriction T U J =
      relativeSectionRestriction T U I ≫ HomologicalComplex.extendMap
        (((etaleSectionFunctor U).mapHomologicalComplex _).map f)
        ComplexShape.embeddingUpNat := by
  dsimp only [relativeSectionRestriction]
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
  congr 1
  apply HomologicalComplex.hom_ext
  intro n
  change (f.f n).hom.app _ ≫ (J.X n).obj.map _ =
    (I.X n).obj.map _ ≫ (f.f n).hom.app _
  exact ((f.f n).hom.naturality _).symm

/-- The map of actual relative complexes induced by a coefficient-complex map. -/
noncomputable def relativeSectionMap (T : Scheme.{u}) (U : T.Etale)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (f : I ⟶ J) : relativeSectionComplex T U I ⟶ relativeSectionComplex T U J :=
  relativeFiberMap (relativeSectionRestriction T U I) (relativeSectionRestriction T U J)
    (HomologicalComplex.extendMap
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex _).map f)
      ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap (((etaleSectionFunctor U).mapHomologicalComplex _).map f)
      ComplexShape.embeddingUpNat) (relativeSectionMap_square T U f)

/-- The restriction square for scheme pullback, followed by a coefficient map. -/
theorem relativeTransfer_square {T T' : Scheme.{u}} (h : T' ⟶ T) (W : T.Opens)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (a : I ⟶ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J) :
    HomologicalComplex.extendMap (globalResolutionSectionTransfer h I J a)
        ComplexShape.embeddingUpNat ≫
        relativeSectionRestriction T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) J =
      relativeSectionRestriction T (Scheme.Etale.mk W.ι) I ≫
        HomologicalComplex.extendMap (openResolutionSectionTransfer h I J a W)
          ComplexShape.embeddingUpNat := by
  dsimp only [relativeSectionRestriction]
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
  congr 1
  have hT : (MorphismProperty.Over.mkIdTerminal @Etale T).from (Scheme.Etale.mk W.ι) =
      MorphismProperty.Over.homMk W.ι (Category.comp_id _) :=
    (MorphismProperty.Over.mkIdTerminal @Etale T).hom_ext _ _
  have hT' : (MorphismProperty.Over.mkIdTerminal @Etale T').from
      (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) =
      MorphismProperty.Over.homMk (h ⁻¹ᵁ W).ι (Category.comp_id _) :=
    (MorphismProperty.Over.mkIdTerminal @Etale T').hom_ext _ _
  rw [hT, hT']
  exact (resolutionSectionTransfer_naturality h I J a _ _ _ _
    (terminalSectionPullback_naturality h W)).symm

/-- Pullback on the shifted restriction cone, computed on a resolution comparison. -/
noncomputable def relativeTransfer {T T' : Scheme.{u}} (h : T' ⟶ T) (W : T.Opens)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (a : I ⟶ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J) :
    relativeSectionComplex T (Scheme.Etale.mk W.ι) I ⟶
      relativeSectionComplex T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) J :=
  relativeFiberMap _ _
    (HomologicalComplex.extendMap (globalResolutionSectionTransfer h I J a)
      ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap (openResolutionSectionTransfer h I J a W)
      ComplexShape.embeddingUpNat) (relativeTransfer_square h W I J a)

/-- Forgetting the specified open section, with the normalized ordinary H1 comparison. -/
noncomputable def relativeForgetH1 (T : Scheme.{u}) (W : T.Opens)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (c : ResolutionSectionCanonicalComparison G I) :
    relativeCohomology T (Scheme.Etale.mk W.ι) I 1 → Sheaf.H G 1 :=
  fun x ↦ c.globalEquiv 1
    (((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).extendHomologyIso ComplexShape.embeddingUpNat (rfl : (1 : ℤ) = 1)).hom
        (HomologicalComplex.homologyMap
          (relativeForgetComplex T (Scheme.Etale.mk W.ι) I.cocomplex) 1 x))

set_option backward.isDefEq.respectTransparency false in
private lemma fiberMap_comp
    {A B A' B' A'' B'' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (r'' : A'' ⟶ B'')
    (a : A ⟶ A') (b : B ⟶ B') (a' : A' ⟶ A'') (b' : B' ⟶ B'')
    (h : a ≫ r' = r ≫ b) (h' : a' ≫ r'' = r' ≫ b') :
    relativeFiberMap r r'' (a ≫ a') (b ≫ b')
        (by rw [Category.assoc, h', ← Category.assoc, h, Category.assoc]) =
      relativeFiberMap r r' a b h ≫ relativeFiberMap r' r'' a' b' h' := by
  unfold relativeFiberMap
  rw [← Functor.map_comp, ← HomologicalComplex.homotopyCofiber.mapArrowHom_comp]
  congr 2

set_option backward.isDefEq.respectTransparency false in
private lemma sectionMap_comp (T : Scheme.{u}) (U : T.Etale)
    {I J K : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (a : I ⟶ J) (b : J ⟶ K) :
    relativeSectionMap T U (a ≫ b) = relativeSectionMap T U a ≫ relativeSectionMap T U b := by
  unfold relativeSectionMap
  rw [← fiberMap_comp]
  simp only [Functor.map_comp, HomologicalComplex.extendMap_comp]

set_option backward.isDefEq.respectTransparency false in
private lemma fiberMap_comp_zero
    {A B A' B' A'' B'' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (r'' : A'' ⟶ B'')
    (a : A ⟶ A') (b : B ⟶ B') (a' : A' ⟶ A'') (b' : B' ⟶ B'')
    (h : a ≫ r' = r ≫ b) (h' : a' ≫ r'' = r' ≫ b')
    (ha : a ≫ a' = 0) (hb : b ≫ b' = 0) :
    relativeFiberMap r r' a b h ≫ relativeFiberMap r' r'' a' b' h' = 0 := by
  unfold relativeFiberMap
  rw [← Functor.map_comp, ← HomologicalComplex.homotopyCofiber.mapArrowHom_comp]
  have hz : (Arrow.homMk a b h : Arrow.mk r ⟶ Arrow.mk r') ≫
      (Arrow.homMk a' b' h' : Arrow.mk r' ⟶ Arrow.mk r'') = 0 := by
    apply Arrow.hom_ext <;> assumption
  rw [hz]
  have hc : HomologicalComplex.homotopyCofiber.mapArrowHom r r''
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) 0 = 0 := by
    apply HomologicalComplex.hom_ext
    intro n
    apply HomologicalComplex.homotopyCofiber.ext_from_X r (n + 1) n rfl <;>
      simp [HomologicalComplex.homotopyCofiber.mapArrowHom]
  rw [hc]
  exact Functor.map_zero _ _ _

/-- Relative complex maps preserve a zero composite. -/
theorem relativeSectionMap_comp_zero (T : Scheme.{u}) (U : T.Etale)
    {I J K : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (a : I ⟶ J) (b : J ⟶ K) (hab : a ≫ b = 0) :
    relativeSectionMap T U a ≫ relativeSectionMap T U b = 0 := by
  apply fiberMap_comp_zero <;>
    simp only [← HomologicalComplex.extendMap_comp, ← Functor.map_comp, hab,
      Functor.map_zero, HomologicalComplex.extendMap_zero]

/-- Apply the relative shifted-cone construction to a short complex of resolutions. -/
noncomputable def relativeShortComplex (T : Scheme.{u}) (U : T.Etale)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)) :
    ShortComplex (CochainComplex AddCommGrpCat.{u + 1} ℤ) :=
  ShortComplex.mk (relativeSectionMap T U S.f) (relativeSectionMap T U S.g)
    (relativeSectionMap_comp_zero T U S.f S.g S.zero)

set_option backward.isDefEq.respectTransparency false in
private lemma extendedSections_split (T : Scheme.{u}) (U : T.Etale)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : ∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
    (q : ℤ) : Nonempty ((S.map
      ((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ) ⋙
        ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1})).map
          (HomologicalComplex.eval _ (.up ℤ) q)).Splitting := by
  classical
  let F := etaleSectionFunctor U
  let E := ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}
  let R := S.map (F.mapHomologicalComplex (.up ℕ) ⋙ E)
  change Nonempty (R.map (HomologicalComplex.eval _ (.up ℤ) q)).Splitting
  by_cases hq : ∃ n : ℕ, (n : ℤ) = q
  · obtain ⟨n, rfl⟩ := hq
    let e : R.map (HomologicalComplex.eval _ (.up ℤ) (n : ℤ)) ≅
        (S.map (HomologicalComplex.eval _ (.up ℕ) n)).map F :=
      ShortComplex.isoMk
        (HomologicalComplex.extendXIso _ _ rfl)
        (HomologicalComplex.extendXIso _ _ rfl)
        (HomologicalComplex.extendXIso _ _ rfl)
        (by
          change _ ≫ F.map (S.f.f n) =
            (HomologicalComplex.extendMap ((F.mapHomologicalComplex (.up ℕ)).map S.f)
              ComplexShape.embeddingUpNat).f (n : ℤ) ≫ _
          erw [HomologicalComplex.extendMap_f _ _ (rfl :
            ComplexShape.embeddingUpNat.f n = (n : ℤ))]
          simp)
        (by
          change _ ≫ F.map (S.g.f n) =
            (HomologicalComplex.extendMap ((F.mapHomologicalComplex (.up ℕ)).map S.g)
              ComplexShape.embeddingUpNat).f (n : ℤ) ≫ _
          erw [HomologicalComplex.extendMap_f _ _ (rfl :
            ComplexShape.embeddingUpNat.f n = (n : ℤ))]
          simp)
    exact ⟨((hs n).some.map F).ofIso e.symm⟩
  · have hz (I : CochainComplex
        (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
        IsZero ((E.obj ((F.mapHomologicalComplex (.up ℕ)).obj I)).X q) :=
      HomologicalComplex.isZero_extend_X _ _ _ (by simpa using hq)
    exact ⟨{
      r := 0
      s := 0
      f_r := (hz S.X₁).eq_of_src _ _
      s_g := (hz S.X₃).eq_of_src _ _
      id := (hz S.X₂).eq_of_src _ _ }⟩

private noncomputable def sumRow (S R : ShortComplex AddCommGrpCat.{u + 1}) :
    ShortComplex AddCommGrpCat.{u + 1} :=
  ShortComplex.mk (biprod.map S.f R.f) (biprod.map S.g R.g) (by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [biprod.map])

private noncomputable def sumRowSplitting (S R : ShortComplex AddCommGrpCat.{u + 1})
    (s : S.Splitting) (t : R.Splitting) : (sumRow S R).Splitting where
  r := biprod.map s.r t.r
  s := biprod.map s.s t.s
  f_r := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [sumRow, biprod.map]
  s_g := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [sumRow, biprod.map]
  id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [sumRow, biprod.map, Category.assoc, s.id, t.id]

/-- Split horseshoe rows remain short exact after relative sections. -/
theorem relativeShortComplex_shortExact (T : Scheme.{u}) (U : T.Etale)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : (∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))) :
    (relativeShortComplex T U S).ShortExact := by
  classical
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let A := (S.map
    ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ) ⋙
      ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1})).map
        (HomologicalComplex.eval _ (.up ℤ) (n + -1 + 1))
  let B := (S.map ((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ) ⋙
      ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1})).map
        (HomologicalComplex.eval _ (.up ℤ) (n + -1))
  let e (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod
      (relativeSectionRestriction T U I) (n + -1) (n + -1 + 1) rfl
  let iso : (relativeShortComplex T U S).map (HomologicalComplex.eval _ (.up ℤ) n) ≅
      sumRow A B := ShortComplex.isoMk (e S.X₁) (e S.X₂) (e S.X₃)
        (coneMap_XIso _ _ _ _ (relativeSectionMap_square T U S.f) (n + -1)).symm
        (coneMap_XIso _ _ _ _ (relativeSectionMap_square T U S.g) (n + -1)).symm
  exact ShortComplex.shortExact_of_iso iso.symm
    (sumRowSplitting A B
      (extendedSections_split T (Scheme.Etale.mk (𝟙 T)) S hs (n + -1 + 1)).some
      (extendedSections_split T U S hs (n + -1)).some).shortExact

/-- The canonical relative connecting map in any split horseshoe model.
Its sign is the homology-sequence sign, not an independently chosen homomorphism. -/
noncomputable def relativeConnecting (T : Scheme.{u}) (U : T.Etale)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : (∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))) (q : ℤ) :
    (relativeSectionComplex T U S.X₃).homology q ⟶
      (relativeSectionComplex T U S.X₁).homology (q + 1) :=
  (relativeShortComplex_shortExact T U S hs).δ q (q + 1) rfl

set_option backward.isDefEq.respectTransparency false in
private lemma coneMap_fst
    {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) :
    HomologicalComplex.homotopyCofiber.mapArrowHom r r'
        (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h) ≫
      CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (CochainComplex.mappingCone.fst r') =
    CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (CochainComplex.mappingCone.fst r) ≫ a⟦(1 : ℤ)⟧' := by
  rw [← CochainComplex.HomComplex.Cocycle.equivHomShift_symm_precomp,
    ← CochainComplex.HomComplex.Cocycle.equivHomShift_symm_postcomp]
  congr 1
  apply CochainComplex.HomComplex.Cocycle.ext
  apply CochainComplex.HomComplex.Cochain.ext
  intro i j hij
  change ((CochainComplex.HomComplex.Cochain.ofHom _).comp
      (CochainComplex.mappingCone.fst r').1 (zero_add 1)).v i j hij =
    ((CochainComplex.mappingCone.fst r).1.comp
      (CochainComplex.HomComplex.Cochain.ofHom a) (add_zero 1)).v i j hij
  simp only [CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]
  obtain rfl := hij
  apply HomologicalComplex.homotopyCofiber.ext_from_X r (i + 1) i rfl <;>
    simp [CochainComplex.mappingCone.fst,
      HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom r' _ (i + 1) i rfl]

set_option backward.isDefEq.respectTransparency false in
private lemma resolutionTransfer_comp_square {T T' : Scheme.{u}} (h : T' ⟶ T)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    {I' J' : CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (f : I ⟶ J) (f' : I' ⟶ J')
    (a : I ⟶ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj I')
    (b : J ⟶ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J')
    (comm : a ≫ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).map f' =
      f ≫ b) (A : T.Etale) (B : T'.Etale)
    (k : B ⟶ (MorphismProperty.Over.pullback @Etale ⊤ h).obj A) :
    resolutionSectionTransfer h I I' a A B k ≫
        ((etaleSectionFunctor B).mapHomologicalComplex (.up ℕ)).map f' =
      ((etaleSectionFunctor A).mapHomologicalComplex (.up ℕ)).map f ≫
        resolutionSectionTransfer h J J' b A B k := by
  apply HomologicalComplex.hom_ext
  intro n
  have hc := congrArg (fun v ↦ (v.f n).hom.app (op A)) comm
  change (a.f n).hom.app (op A) ≫ (f'.f n).hom.app _ =
    (f.f n).hom.app (op A) ≫ (b.f n).hom.app (op A) at hc
  change ((a.f n).hom.app (op A) ≫ (I'.X n).obj.map k.op) ≫
    (f'.f n).hom.app (op B) =
      (f.f n).hom.app (op A) ≫ (b.f n).hom.app (op A) ≫ (J'.X n).obj.map k.op
  rw [Category.assoc, (f'.f n).hom.naturality, ← Category.assoc, hc, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private lemma transfer_comp_square {T T' : Scheme.{u}} (h : T' ⟶ T) (W : T.Opens)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    {I' J' : CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (f : I ⟶ J) (f' : I' ⟶ J')
    (a : I ⟶ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj I')
    (b : J ⟶ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J')
    (comm : a ≫ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).map f' =
      f ≫ b) :
    relativeTransfer h W I I' a ≫ relativeSectionMap T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) f' =
      relativeSectionMap T (Scheme.Etale.mk W.ι) f ≫ relativeTransfer h W J J' b := by
  unfold relativeTransfer relativeSectionMap
  rw [← fiberMap_comp, ← fiberMap_comp]
  congr 1
  · rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
    exact congrArg (fun v ↦ HomologicalComplex.extendMap v ComplexShape.embeddingUpNat)
      (resolutionTransfer_comp_square h f f' a b comm _ _ _)
  · rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
    exact congrArg (fun v ↦ HomologicalComplex.extendMap v ComplexShape.embeddingUpNat)
      (resolutionTransfer_comp_square h f f' a b comm _ _ _)

/-- Relative connecting maps are natural under scheme pullback and coefficient maps.
This includes identity scheme pullback, and hence independence of horseshoe choices. -/
theorem relativeConnecting_pullback_naturality {T T' : Scheme.{u}} (h : T' ⟶ T)
    (W : T.Opens)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (S' : ShortComplex
      (CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : (∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting)))
    (hs' : (∀ n : ℕ, Nonempty ((S'.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting)))
    (a : S ⟶ S'.map ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)))
    (q : ℤ) :
    relativeConnecting T (Scheme.Etale.mk W.ι) S hs q ≫
        HomologicalComplex.homologyMap (relativeTransfer h W S.X₁ S'.X₁ a.τ₁) (q + 1) =
      HomologicalComplex.homologyMap (relativeTransfer h W S.X₃ S'.X₃ a.τ₃) q ≫
        relativeConnecting T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) S' hs' q := by
  let m : relativeShortComplex T (Scheme.Etale.mk W.ι) S ⟶
      relativeShortComplex T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) S' := {
    τ₁ := relativeTransfer h W S.X₁ S'.X₁ a.τ₁
    τ₂ := relativeTransfer h W S.X₂ S'.X₂ a.τ₂
    τ₃ := relativeTransfer h W S.X₃ S'.X₃ a.τ₃
    comm₁₂ := transfer_comp_square h W S.f S'.f a.τ₁ a.τ₂ a.comm₁₂
    comm₂₃ := transfer_comp_square h W S.g S'.g a.τ₂ a.τ₃ a.comm₂₃ }
  exact HomologicalComplex.HomologySequence.δ_naturality m
    (relativeShortComplex_shortExact T (Scheme.Etale.mk W.ι) S hs)
    (relativeShortComplex_shortExact T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) S' hs') q (q + 1) rfl

/-- The relative boundary is natural for coefficient-sequence comparison maps. -/
theorem relativeConnecting_coefficient_naturality (T : Scheme.{u}) (U : T.Etale)
    (S S' : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : (∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting)))
    (hs' : (∀ n : ℕ, Nonempty ((S'.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting)))
    (a : S ⟶ S') (q : ℤ) :
    relativeConnecting T U S hs q ≫
        HomologicalComplex.homologyMap (relativeSectionMap T U a.τ₁) (q + 1) =
      HomologicalComplex.homologyMap (relativeSectionMap T U a.τ₃) q ≫
        relativeConnecting T U S' hs' q := by
  let m : relativeShortComplex T U S ⟶ relativeShortComplex T U S' := {
    τ₁ := relativeSectionMap T U a.τ₁
    τ₂ := relativeSectionMap T U a.τ₂
    τ₃ := relativeSectionMap T U a.τ₃
    comm₁₂ := by
      change relativeSectionMap T U a.τ₁ ≫ relativeSectionMap T U S'.f =
        relativeSectionMap T U S.f ≫ relativeSectionMap T U a.τ₂
      rw [← sectionMap_comp, ← sectionMap_comp, a.comm₁₂]
    comm₂₃ := by
      change relativeSectionMap T U a.τ₂ ≫ relativeSectionMap T U S'.g =
        relativeSectionMap T U S.g ≫ relativeSectionMap T U a.τ₃
      rw [← sectionMap_comp, ← sectionMap_comp, a.comm₂₃] }
  exact HomologicalComplex.HomologySequence.δ_naturality m
    (relativeShortComplex_shortExact T U S hs)
    (relativeShortComplex_shortExact T U S' hs') q (q + 1) rfl

end AlgebraicGeometry.Etale
