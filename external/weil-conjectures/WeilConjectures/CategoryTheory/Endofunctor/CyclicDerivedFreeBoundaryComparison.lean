/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedFreeHomCoordinates
public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedOffDiagonalPresentation

/-! # Comparison of the free and off-diagonal boundaries

Source: Stacks Tags 0149, 0152, and the normalized cyclic free resolution.
(blueprint: lem-sf-cyclic-free-boundary-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w wF

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence] [IsGrothendieckAbelian.{v} C]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]

namespace BoundaryComparison

private abbrev underlying (K : CochainComplex (IsoAlgebra F) ℤ) :=
  ((forget F).mapHomologicalComplex (.up ℤ)).obj K

private abbrev freeComplex := (Free.functor F).mapHomologicalComplex (.up ℤ)

private abbrev freeCounit (K : CochainComplex (IsoAlgebra F) ℤ) :=
  ((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K

private def freeAdjunct {J A : CochainComplex (IsoAlgebra F) ℤ}
    (u : underlying F J ⟶ underlying F A) : (freeComplex F).obj (underlying F J) ⟶ A :=
  (freeComplex F).map u ≫ freeCounit F A

omit [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)] in
private theorem freeAdjunct_zero {J A : CochainComplex (IsoAlgebra F) ℤ}
    (u : underlying F J ⟶ underlying F A) (n : ℤ) :
    Sigma.ι (Free.obj F (J.X n).carrier) 0 ≫
      (forget F).map ((freeAdjunct F u).f n) = u.f n := by
  change Sigma.ι _ 0 ≫ (Free.map (u.f n)).hom.f ≫
    (Free.desc (A.X n) (𝟙 _)).hom.f = _
  rw [← Category.assoc, Free.map_hom_f, Sigma.ι_map, Free.objMap_zero]
  simp only [Category.assoc, Free.ι_desc_hom_f]
  exact Category.comp_id _

private theorem comparison (r : CyclicDerivedFreeResolution F)
    (S : ShortComplex (CochainComplex (IsoAlgebra F) ℤ))
    (u : underlying F S.X₃ ⟶ underlying F S.X₁)
    (s : underlying F S.X₃ ⟶ underlying F S.X₂)
    (hs : s ≫ ((forget F).mapHomologicalComplex (.up ℤ)).map S.g = 𝟙 _)
    (he : ∀ n : ℤ,
      F.map (@id ((S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier) (s.f n)) ≫
          (S.X₂.X n).str.hom =
        ((S.X₃.X n).str.hom ≫
          @id ((S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier) (s.f n)) +
        (F.map (@id ((S.X₃.X n).carrier ⟶ (S.X₁.X n).carrier) (u.f n)) ≫
          (S.X₁.X n).str.hom ≫
            @id ((S.X₁.X n).carrier ⟶ (S.X₂.X n).carrier) ((forget F).map (S.f.f n)))) :
    (r.d.mapHomologicalComplex (.up ℤ)).app S.X₃ ≫ freeAdjunct F s =
        freeAdjunct F u ≫ S.f ∧
      freeAdjunct F s ≫ S.g = freeCounit F S.X₃ := by
  constructor
  · ext n
    apply Free.hom_ext
    change Sigma.ι _ 0 ≫ ((forget F).map (r.d.app (S.X₃.X n)) ≫
        (forget F).map ((freeAdjunct F s).f n)) =
      Sigma.ι _ 0 ≫ ((forget F).map ((freeAdjunct F u).f n) ≫
        (forget F).map (S.f.f n))
    rw [← Category.assoc]
    erw [r.summand, Preadditive.sub_comp]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    have hθ0 : (r.theta (S.X₃.X n) 0).hom = 𝟙 _ := r.theta_eq _ _
    erw [hθ0, Category.id_comp]
    erw [freeAdjunct_zero,
      ← Category.assoc (Sigma.ι (Free.obj F (S.X₃.X n).carrier) 0), freeAdjunct_zero]
    change @id ((S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier) (s.f n) -
        @id ((S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier)
          ((r.theta (S.X₃.X n) (-1)).inv ≫
            Sigma.ι (Free.obj F (S.X₃.X n).carrier) (-1) ≫
            (forget F).map ((freeAdjunct F s).f n)) =
      @id ((S.X₃.X n).carrier ⟶ (S.X₁.X n).carrier) (u.f n) ≫
        @id ((S.X₁.X n).carrier ⟶ (S.X₂.X n).carrier) ((forget F).map (S.f.f n))
    have hrec := Free.map_ι_comp_comp_str ((freeAdjunct F s).f n) (-1)
    have hθ := Free.map_hom_comp_str (S.X₃.X n) (𝟙 _) (-1)
    rw [← r.theta_eq, ← r.theta_eq] at hθ
    change F.map (r.theta (S.X₃.X n) (-1)).hom ≫ (S.X₃.X n).str.hom =
      (Free.objSucc F (S.X₃.X n).carrier (-1)).hom ≫
        (r.theta (S.X₃.X n) 0).hom at hθ
    erw [hθ0, Category.comp_id] at hθ
    have hinv : F.map (r.theta (S.X₃.X n) (-1)).inv ≫
        (Free.objSucc F (S.X₃.X n).carrier (-1)).hom = (S.X₃.X n).str.hom := by
      erw [← hθ, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
    change F.map (Sigma.ι _ (-1) ≫ (forget F).map ((freeAdjunct F s).f n)) ≫
        (S.X₂.X n).str.hom =
      (Free.objSucc F (S.X₃.X n).carrier (-1)).hom ≫
        Sigma.ι (Free.obj F (S.X₃.X n).carrier) 0 ≫
          (forget F).map ((freeAdjunct F s).f n) at hrec
    erw [freeAdjunct_zero] at hrec
    have hback :
        F.map ((r.theta (S.X₃.X n) (-1)).inv ≫
          Sigma.ι (Free.obj F (S.X₃.X n).carrier) (-1) ≫
          (forget F).map ((freeAdjunct F s).f n)) ≫ (S.X₂.X n).str.hom =
        (S.X₃.X n).str.hom ≫ s.f n := by
      erw [F.map_comp, Category.assoc, hrec, ← Category.assoc, hinv]
    apply F.map_injective
    apply (cancel_mono (S.X₂.X n).str.hom).1
    erw [F.map_sub, Preadditive.sub_comp, hback, he, F.map_comp, Category.assoc,
      (S.f.f n).hom.h]
    exact add_sub_cancel_left _ _
  · ext n
    apply Free.hom_ext
    change Sigma.ι _ 0 ≫ ((forget F).map ((freeAdjunct F s).f n) ≫
      (forget F).map (S.g.f n)) = _
    erw [← Category.assoc, freeAdjunct_zero]
    change s.f n ≫ (forget F).map (S.g.f n) =
      Sigma.ι (Free.obj F (S.X₃.X n).carrier) 0 ≫
        Sigma.desc (Free.hom (S.X₃.X n) (𝟙 _))
    rw [Sigma.ι_comp_desc]
    exact congrArg (fun t ↦ t.f n) hs

private lemma cyclicFree_derived_counit (K : CochainComplex (IsoAlgebra F) ℤ) :
    (cyclicDerivedFreeAdjunction F).counit.app (DerivedCategory.Q.obj K) =
      (cyclicDerivedFreeComparison F K).hom ≫
        DerivedCategory.Q.map
          (((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K) := by
  let : CatCommSq ((Free.functor F).mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q (Free.functor F).mapDerivedCategory :=
    ⟨(Free.functor F).mapDerivedCategoryFactors.symm⟩
  let : CatCommSq ((forget F).mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q (forget F).mapDerivedCategory :=
    ⟨(forget F).mapDerivedCategoryFactors.symm⟩
  have h := Adjunction.Localization.η_app
    ((Free.adjunction F).mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q DerivedCategory.Q (HomologicalComplex.quasiIso (IsoAlgebra F) (.up ℤ))
    (Free.functor F).mapDerivedCategory (forget F).mapDerivedCategory K
  have hU : (CatCommSq.iso ((forget F).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (forget F).mapDerivedCategory).inv.app K =
      (forget F).mapDerivedCategoryFactors.hom.app K := rfl
  have hI : (CatCommSq.iso ((Free.functor F).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (Free.functor F).mapDerivedCategory).inv.app
        (((forget F).mapHomologicalComplex (.up ℤ)).obj K) =
      (Free.functor F).mapDerivedCategoryFactors.hom.app
        (((forget F).mapHomologicalComplex (.up ℤ)).obj K) := rfl
  rw [hU, hI] at h
  have hc : ((Free.adjunction F).mapHomologicalComplex (.up ℤ)).counit.app K =
      ((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K := by
    ext n
    exact (Free.adjunction F).mapHomologicalComplex_counit_app_f (.up ℤ) K n
  rw [hc] at h
  simpa only [cyclicDerivedFreeAdjunction, Adjunction.mapExactDerivedCategory,
    Adjunction.localization, Adjunction.mkOfUnitCounit, cyclicDerivedFreeComparison,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using h

private def underlyingClass {J A : CochainComplex (IsoAlgebra F) ℤ}
    (u : underlying F J ⟶ underlying F A) :
    (forget F).mapDerivedCategory.obj (DerivedCategory.Q.obj J) ⟶
      (forget F).mapDerivedCategory.obj (DerivedCategory.Q.obj A) :=
  (forget F).mapDerivedCategoryFactors.hom.app J ≫ DerivedCategory.Q.map u ≫
    (forget F).mapDerivedCategoryFactors.inv.app A

private theorem freeAdjunct_localization {J A : CochainComplex (IsoAlgebra F) ℤ}
    (u : underlying F J ⟶ underlying F A) :
    (cyclicDerivedFreeComparison F J).hom ≫ DerivedCategory.Q.map (freeAdjunct F u) =
      (Free.functor F).mapDerivedCategory.map (underlyingClass F u) ≫
        (cyclicDerivedFreeAdjunction F).counit.app (DerivedCategory.Q.obj A) := by
  rw [cyclicFree_derived_counit]
  simp only [underlyingClass, Functor.map_comp, cyclicDerivedFreeComparison, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  erw [← (Free.functor F).mapDerivedCategory.map_comp_assoc
      ((forget F).mapDerivedCategoryFactors.inv.app A)
      ((forget F).mapDerivedCategoryFactors.hom.app A),
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
    (Free.functor F).mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [freeAdjunct, Functor.map_comp]

private def pairing (r : CyclicDerivedFreeResolution F)
    {J A : DerivedCategory (IsoAlgebra F)}
    (u : (forget F).mapDerivedCategory.obj J ⟶ (forget F).mapDerivedCategory.obj A) :
    J ⟶ A⟦(1 : ℤ)⟧ :=
  r.delta.app J ≫
    ((Free.functor F).mapDerivedCategory.map u ≫
      (cyclicDerivedFreeAdjunction F).counit.app A)⟦(1 : ℤ)⟧'

private theorem pairing_naturality (r : CyclicDerivedFreeResolution F)
    {J A J' A' : DerivedCategory (IsoAlgebra F)} (a : J' ⟶ J) (c : A ⟶ A')
    (u : (forget F).mapDerivedCategory.obj J ⟶ (forget F).mapDerivedCategory.obj A) :
    a ≫ pairing F r u ≫ c⟦(1 : ℤ)⟧' =
      pairing F r ((forget F).mapDerivedCategory.map a ≫ u ≫
        (forget F).mapDerivedCategory.map c) := by
  simp only [pairing, Category.assoc]
  rw [← Functor.map_comp, Category.assoc]
  erw [← (cyclicDerivedFreeAdjunction F).counit.naturality c]
  erw [r.delta.naturality_assoc a]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]

-- The comparison of short exact sequences fixes the boundary, including its sign.
private theorem pairing_boundary (r : CyclicDerivedFreeResolution F)
    (S : ShortComplex (CochainComplex (IsoAlgebra F) ℤ)) (hS : S.ShortExact)
    (u : underlying F S.X₃ ⟶ underlying F S.X₁)
    (s : underlying F S.X₃ ⟶ underlying F S.X₂)
    (hs : s ≫ ((forget F).mapHomologicalComplex (.up ℤ)).map S.g = 𝟙 _)
    (he : ∀ n : ℤ,
      F.map (@id ((S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier) (s.f n)) ≫
          (S.X₂.X n).str.hom =
        ((S.X₃.X n).str.hom ≫
          @id ((S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier) (s.f n)) +
        (F.map (@id ((S.X₃.X n).carrier ⟶ (S.X₁.X n).carrier) (u.f n)) ≫
          (S.X₁.X n).str.hom ≫
            @id ((S.X₁.X n).carrier ⟶ (S.X₂.X n).carrier) ((forget F).map (S.f.f n)))) :
    pairing F r (underlyingClass F u) = DerivedCategory.triangleOfSESδ hS := by
  obtain ⟨h₁, h₂⟩ := comparison F r S u s hs he
  let t : ShortComplex.mk ((r.d.mapHomologicalComplex (.up ℤ)).app S.X₃)
      (freeCounit F S.X₃) (r.zero S.X₃) ⟶ S :=
    { τ₁ := freeAdjunct F u
      τ₂ := freeAdjunct F s
      τ₃ := 𝟙 _
      comm₁₂ := h₁.symm
      comm₂₃ := by simpa only [Category.comp_id] using h₂ }
  have h := DerivedCategory.triangleOfSESδ_naturality (r.shortExact S.X₃) hS t
  change DerivedCategory.triangleOfSESδ (r.shortExact S.X₃) ≫
      (DerivedCategory.Q.map (freeAdjunct F u))⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map (𝟙 S.X₃) ≫ DerivedCategory.triangleOfSESδ hS at h
  simpa only [pairing, ← freeAdjunct_localization,
    Functor.map_comp, ← Category.assoc, CyclicDerivedFreeResolution.delta_fac,
    Functor.map_id, Category.id_comp] using h

private def unshiftBoundary {A N : DerivedCategory (IsoAlgebra F)}
    (c : A⟦(1 : ℤ)⟧ ⟶ N) : A ⟶ N⟦(-1 : ℤ)⟧ :=
  (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).inv.app A ≫ c⟦(-1 : ℤ)⟧'

omit [HasDerivedCategory.{w} C] [IsGrothendieckAbelian.{v} C] in
private theorem unshiftBoundary_shift {A N : DerivedCategory (IsoAlgebra F)}
    (c : A⟦(1 : ℤ)⟧ ⟶ N) :
    (unshiftBoundary F c)⟦(1 : ℤ)⟧' ≫
      (shiftEquiv _ (1 : ℤ)).counitIso.hom.app N = c := by
  change (shiftEquiv _ (1 : ℤ)).functor.map
      ((shiftEquiv _ (1 : ℤ)).unitIso.hom.app A ≫
        (shiftEquiv _ (1 : ℤ)).inverse.map c) ≫ _ = c
  rw [Functor.map_comp, Category.assoc]
  erw [(shiftEquiv _ (1 : ℤ)).counitIso.hom.naturality c]
  rw [← Category.assoc]
  erw [(shiftEquiv _ (1 : ℤ)).functor_unitIso_comp]
  exact Category.id_comp _

omit [IsGrothendieckAbelian.{v} C] in
private theorem offDiagonalClass_unshift
    {S : ShortComplex (CochainComplex (IsoAlgebra F) ℤ)}
    (u : underlying F S.X₃ ⟶ underlying F S.X₁)
    {N : DerivedCategory (IsoAlgebra F)}
    (c : (DerivedCategory.Q.obj S.X₁)⟦(1 : ℤ)⟧ ⟶ N) :
    cyclicDerivedOffDiagonalClass F u ≫
        ((forget F).mapDerivedCategory.map c)⟦(-1 : ℤ)⟧' ≫
        ((forget F).mapDerivedCategory.commShiftIso (-1 : ℤ)).inv.app N =
      underlyingClass F u ≫ (forget F).mapDerivedCategory.map (unshiftBoundary F c) := by
  simp only [cyclicDerivedOffDiagonalClass, underlyingClass, unshiftBoundary,
    Functor.map_comp, Category.assoc]
  erw [← ((forget F).mapDerivedCategory.commShiftIso (-1 : ℤ)).hom.naturality_assoc c]
  simp

end BoundaryComparison

/-- The normalized SES boundary of the free resolution computes the uniquely
presented off-diagonal boundary. This only identifies two concrete morphisms; it
does not assert additivity, naturality, or any exactness statement.

Proof: take a strict presentation S of u. Let e be the free adjunct of the chosen
underlying splitting s, and let f₀ be the adjunct of its off-diagonal entry.
On summand zero, e d = j f₀ follows by inserting the inverse triangular action:
the difference between s and its translate is exactly the inclusion composed
with the off-diagonal entry. Also p e = epsilon because p s = 1. The free
adjunction shows these identities hold on all summands, so f₀,e,1 define a
morphism of short exact sequences. Naturality of triangleOfSESδ gives the
presented boundary as delta_free followed by f₀[1]. The standard localization
comparisons, differential_fac, delta_fac, and the two adjunctions defining
cyclicDerivedFreeShiftedHomEquiv turn this expression into the displayed one.
Use naturality of delta to transport the presentation's endpoint isomorphisms.
Finally cyclicDerivedOffDiagonalBoundary_eq identifies the presented morphism
with the specified boundary. The computation uses the normalized SES sign,
and works for unbounded complexes and independent localizations.
Source: parent calculus step 2, Stacks 0152 and parent presentation step 8
(blueprint: lem-sf-cyclic-free-boundary-comparison). -/
theorem cyclicDerivedFreeBoundary_comparison (R : CyclicDerivedFreeResolution F)
    {M N : DerivedCategory (IsoAlgebra F)} (u : CyclicDerivedHom F M N (-1)) :
    cyclicDerivedOffDiagonalBoundary F u =
      R.delta.app M ≫ (cyclicDerivedFreeShiftedHomEquiv F M N).symm u := by
  obtain ⟨S, hS, u₀, s, a, c, hs, he, hu, hf⟩ :=
    cyclicDerivedOffDiagonalBoundary_presentation F u
  have hp := BoundaryComparison.pairing_naturality F R a.hom
    (BoundaryComparison.unshiftBoundary F c.hom) (BoundaryComparison.underlyingClass F u₀)
  rw [BoundaryComparison.pairing_boundary F R S hS u₀ s hs he] at hp
  have hu' :
      (forget F).mapDerivedCategory.map a.hom ≫ BoundaryComparison.underlyingClass F u₀ ≫
        (forget F).mapDerivedCategory.map (BoundaryComparison.unshiftBoundary F c.hom) =
      u ≫ ((forget F).mapDerivedCategory.commShiftIso (-1 : ℤ)).inv.app N := by
    rw [hu]
    simp only [Category.assoc, BoundaryComparison.offDiagonalClass_unshift]
  rw [hf]
  have hvalue : a.hom ≫ DerivedCategory.triangleOfSESδ hS ≫ c.hom =
      BoundaryComparison.pairing F R
        (u ≫ ((forget F).mapDerivedCategory.commShiftIso (-1 : ℤ)).inv.app N) ≫
          (shiftEquiv _ (1 : ℤ)).counitIso.hom.app N := by
    rw [← hu', ← hp]
    simp only [Category.assoc, BoundaryComparison.unshiftBoundary_shift]
  rw [hvalue]
  simp [BoundaryComparison.pairing, cyclicDerivedFreeShiftedHomEquiv,
    cyclicDerivedFreeShiftAdjunction, Iso.homCongr, Adjunction.homEquiv_counit,
    Category.assoc]
  rfl

end CategoryTheory.Endofunctor.IsoAlgebra
