/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedHomData
import WeilConjectures.CategoryTheory.Endofunctor.FreeDerivedWeilResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Strict presentations of the cyclic connecting morphism

Source: the free-resolution comparison and off-diagonal construction in steps 6--8 of
`lem-sf-cyclic-derived-hom-exact-sequence`; Stacks Project, Derived Categories,
Tags 0152 and 070I (blueprint: lem-sf-cyclic-derived-off-diagonal-presentation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w wF

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]

/-- A strict off-diagonal extension, together with isomorphisms identifying its two
endpoints with M and N. Both the underlying shifted morphism and the native connecting
morphism are prescribed; a presentation includes the sign of the canonical SES boundary.
Source: Stacks Tag 0152 and node steps 6--8
(blueprint: lem-sf-cyclic-derived-off-diagonal-presentation). -/
def CyclicDerivedOffDiagonalPresentation
    {M N : DerivedCategory (IsoAlgebra F)} (u : CyclicDerivedHom F M N (-1))
    (f : M ⟶ N) : Prop :=
  ∃ (S : ShortComplex (CochainComplex (IsoAlgebra F) ℤ)) (hS : S.ShortExact)
    (u₀ : ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj S.X₃ ⟶
      ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj S.X₁)
    (s : ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj S.X₃ ⟶
      ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj S.X₂)
    (a : M ≅ DerivedCategory.Q.obj S.X₃)
    (c : (DerivedCategory.Q.obj S.X₁)⟦(1 : ℤ)⟧ ≅ N),
    s ≫ ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).map S.g = 𝟙 _ ∧
    (∀ n : ℤ,
      F.map (@id ((S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier) (s.f n)) ≫
          (S.X₂.X n).str.hom =
        ((S.X₃.X n).str.hom ≫
          @id ((S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier) (s.f n)) +
        (F.map (@id ((S.X₃.X n).carrier ⟶ (S.X₁.X n).carrier) (u₀.f n)) ≫
          (S.X₁.X n).str.hom ≫
            @id ((S.X₁.X n).carrier ⟶ (S.X₂.X n).carrier) ((forget F).map (S.f.f n)))) ∧
    u = (forget F).mapDerivedCategory.map a.hom ≫ cyclicDerivedOffDiagonalClass F u₀ ≫
      ((forget F).mapDerivedCategory.map c.hom)⟦(-1 : ℤ)⟧' ∧
    f = a.hom ≫ DerivedCategory.triangleOfSESδ hS ≫ c.hom

private abbrev complexOfAction (Y : CochainComplex C ℤ)
    (τ : (F.mapHomologicalComplex (.up ℤ)).obj Y ≅ Y) :
    CochainComplex (IsoAlgebra F) ℤ where
  X i := IsoAlgebra.mk (Y.X i) (HomologicalComplex.eval C (.up ℤ) i |>.mapIso τ)
  d i j := ObjectProperty.homMk
    { f := Y.d i j
      h := (τ.hom.comm i j).symm }
  shape i j hij := by
    apply (forget F).map_injective
    exact Y.shape i j hij
  d_comp_d' i j k hij hjk := by
    apply (forget F).map_injective
    exact Y.d_comp_d i j k

private abbrev underlying (K : CochainComplex (IsoAlgebra F) ℤ) : CochainComplex C ℤ :=
  ((forget F).mapHomologicalComplex (.up ℤ)).obj K

private def complexAction (K : CochainComplex (IsoAlgebra F) ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (underlying F K) ≅ underlying F K :=
  (NatIso.mapHomologicalComplex (strNatIso F) (.up ℤ)).app K

private def triangularAction (A J : CochainComplex (IsoAlgebra F) ℤ)
    (u : underlying F J ⟶ underlying F A) :
    (F.mapHomologicalComplex (.up ℤ)).obj (underlying F A ⊞ underlying F J) ≅
      underlying F A ⊞ underlying F J :=
  (F.mapHomologicalComplex (.up ℤ)).mapBiprod _ _ ≪≫
    biprod.mapIso (complexAction F A) (complexAction F J) ≪≫
    Biprod.unipotentLower ((complexAction F J).inv ≫
      (F.mapHomologicalComplex (.up ℤ)).map u ≫ (complexAction F A).hom)

omit [F.IsEquivalence] [HasDerivedCategory C] [HasDerivedCategory (IsoAlgebra F)] in
private theorem triangularAction_inl (A J : CochainComplex (IsoAlgebra F) ℤ)
    (u : underlying F J ⟶ underlying F A) :
    (F.mapHomologicalComplex (.up ℤ)).map (biprod.inl : underlying F A ⟶ _) ≫
      (triangularAction F A J u).hom = (complexAction F A).hom ≫ biprod.inl := by
  simp [triangularAction, Biprod.unipotentLower, Biprod.ofComponents,
    ← Category.assoc, ← Functor.map_comp]

omit [F.IsEquivalence] [HasDerivedCategory C] [HasDerivedCategory (IsoAlgebra F)] in
private theorem triangularAction_snd (A J : CochainComplex (IsoAlgebra F) ℤ)
    (u : underlying F J ⟶ underlying F A) :
    (triangularAction F A J u).hom ≫ (biprod.snd : _ ⟶ underlying F J) =
      (F.mapHomologicalComplex (.up ℤ)).map biprod.snd ≫ (complexAction F J).hom := by
  simp [triangularAction, Biprod.unipotentLower, Biprod.ofComponents,
    Category.assoc]

omit [F.IsEquivalence] [HasDerivedCategory C] [HasDerivedCategory (IsoAlgebra F)] in
private theorem triangularAction_inr (A J : CochainComplex (IsoAlgebra F) ℤ)
    (u : underlying F J ⟶ underlying F A) :
    (F.mapHomologicalComplex (.up ℤ)).map (biprod.inr : underlying F J ⟶ _) ≫
      (triangularAction F A J u).hom =
      (complexAction F J).hom ≫ biprod.inr +
        (F.mapHomologicalComplex (.up ℤ)).map u ≫ (complexAction F A).hom ≫
          biprod.inl := by
  simpa [triangularAction, Biprod.unipotentLower, Biprod.ofComponents,
    ← Category.assoc, ← Functor.map_comp, Preadditive.comp_add] using
    add_comm ((F.mapHomologicalComplex (.up ℤ)).map u ≫
      (complexAction F A).hom ≫ biprod.inl) ((complexAction F J).hom ≫ biprod.inr)

private abbrev triangularComplex (A J : CochainComplex (IsoAlgebra F) ℤ)
    (u : underlying F J ⟶ underlying F A) : CochainComplex (IsoAlgebra F) ℤ :=
  complexOfAction F _ (triangularAction F A J u)

private def triangularInclusion (A J : CochainComplex (IsoAlgebra F) ℤ)
    (u : underlying F J ⟶ underlying F A) : A ⟶ triangularComplex F A J u where
  f n := ObjectProperty.homMk
    { f := (biprod.inl : underlying F A ⟶ underlying F A ⊞ underlying F J).f n
      h := congrArg (fun f ↦ f.f n) (triangularAction_inl F A J u) }
  comm' i j hij := by
    apply (forget F).map_injective
    exact (biprod.inl : underlying F A ⟶ underlying F A ⊞ underlying F J).comm i j

private def triangularProjection (A J : CochainComplex (IsoAlgebra F) ℤ)
    (u : underlying F J ⟶ underlying F A) : triangularComplex F A J u ⟶ J where
  f n := ObjectProperty.homMk
    { f := (biprod.snd : underlying F A ⊞ underlying F J ⟶ underlying F J).f n
      h := (congrArg (fun f ↦ f.f n) (triangularAction_snd F A J u)).symm }
  comm' i j hij := by
    apply (forget F).map_injective
    exact (biprod.snd : underlying F A ⊞ underlying F J ⟶ underlying F J).comm i j

private def triangularSequence (A J : CochainComplex (IsoAlgebra F) ℤ)
    (u : underlying F J ⟶ underlying F A) :
    ShortComplex (CochainComplex (IsoAlgebra F) ℤ) :=
  ShortComplex.mk (triangularInclusion F A J u) (triangularProjection F A J u) (by
    apply ((forget F).mapHomologicalComplex (.up ℤ)).map_injective
    change (biprod.inl : underlying F A ⟶ _) ≫ (biprod.snd : _ ⟶ underlying F J) = 0
    simp)

omit [HasDerivedCategory C] [HasDerivedCategory (IsoAlgebra F)] in
/-- Any chain-level off-diagonal entry gives an actual short exact sequence of fixed
pairs with a split underlying chain sequence and exactly that off-diagonal entry.
Proof: give UA ⊕ UJ the invertible triangular action. Its inclusion and projection are
equivariant. Forgetting identifies their sequence with the standard split biproduct
sequence, and faithful exact forgetting reflects exactness, monomorphisms and epimorphisms.
Source: step 7 of the parent node, the triangular construction preceding Stacks Tag 0152
(blueprint: lem-sf-cyclic-derived-off-diagonal-presentation). -/
theorem exists_cyclicDerivedStrictExtension (A J : CochainComplex (IsoAlgebra F) ℤ)
    (u : ((forget F).mapHomologicalComplex (.up ℤ)).obj J ⟶
      ((forget F).mapHomologicalComplex (.up ℤ)).obj A) :
    ∃ (E : CochainComplex (IsoAlgebra F) ℤ) (f : A ⟶ E) (g : E ⟶ J)
      (w : f ≫ g = 0), (ShortComplex.mk f g w).ShortExact ∧
      ∃ s : ((forget F).mapHomologicalComplex (.up ℤ)).obj J ⟶
          ((forget F).mapHomologicalComplex (.up ℤ)).obj E,
        s ≫ ((forget F).mapHomologicalComplex (.up ℤ)).map g = 𝟙 _ ∧
        ∀ n : ℤ,
          F.map (@id ((J.X n).carrier ⟶ (E.X n).carrier) (s.f n)) ≫
              (E.X n).str.hom =
            ((J.X n).str.hom ≫ @id ((J.X n).carrier ⟶ (E.X n).carrier) (s.f n)) +
              (F.map (@id ((J.X n).carrier ⟶ (A.X n).carrier) (u.f n)) ≫
                (A.X n).str.hom ≫
                  @id ((A.X n).carrier ⟶ (E.X n).carrier) ((forget F).map (f.f n))) := by
  let U := (forget F).mapHomologicalComplex (.up ℤ)
  let S := triangularSequence F A J u
  have hsplit : (S.map U).Splitting :=
    ShortComplex.Splitting.ofHasBinaryBiproduct (underlying F A) (underlying F J)
  have hshort : S.ShortExact :=
    ShortComplex.ShortExact.mk' ((S.exact_map_iff_of_faithful U).mp hsplit.exact)
      (U.mono_of_mono_map hsplit.mono_f) (U.epi_of_epi_map hsplit.epi_g)
  refine ⟨S.X₂, S.f, S.g, S.zero, hshort, biprod.inr, ?_, ?_⟩
  · change (biprod.inr : underlying F J ⟶ _) ≫ biprod.snd = 𝟙 _
    simp
  · intro n
    exact congrArg (fun f ↦ f.f n) (triangularAction_inr F A J u)

/-- Every underlying shifted morphism admits a strict off-diagonal presentation.
Proof: choose K-injective representatives for M and N[-1]. Forgetting
preserves K-injectives, so the localized underlying morphism is represented by a chain
map. Apply the triangular extension construction, then transport its endpoints by the
chosen model isomorphisms and the canonical shift cancellation.
Source: steps 6--7 of the parent node, Stacks Tags 070I and 0152
(blueprint: lem-sf-cyclic-derived-off-diagonal-presentation). -/
theorem exists_cyclicDerivedOffDiagonalPresentation [IsGrothendieckAbelian.{v} C]
    {M N : DerivedCategory (IsoAlgebra F)} (u : CyclicDerivedHom F M N (-1)) :
    ∃ f : M ⟶ N, CyclicDerivedOffDiagonalPresentation F u f := by
  have : IsGrothendieckAbelian.{v} (IsoAlgebra F) := isGrothendieckAbelian F
  let KM := DerivedCategory.Q.objPreimage M
  let KN := DerivedCategory.Q.objPreimage (N⟦(-1 : ℤ)⟧)
  obtain ⟨J, hJ, sJ, _, hsJ⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective KM
  obtain ⟨A, hA, sA, _, hsA⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective KN
  have := hJ
  have := hA
  have := hsJ
  have := hsA
  let U := (forget F).mapDerivedCategory
  let Uc := (forget F).mapHomologicalComplex (.up ℤ)
  let a : M ≅ DerivedCategory.Q.obj J :=
    (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫ asIso (DerivedCategory.Q.map sJ)
  let c : (DerivedCategory.Q.obj A)⟦(1 : ℤ)⟧ ≅ N :=
    (shiftFunctor _ (1 : ℤ)).mapIso
      ((asIso (DerivedCategory.Q.map sA)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso _) ≪≫
      (shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by omega)).app N
  let k : U.obj (DerivedCategory.Q.obj A) ≅
      (U.obj ((DerivedCategory.Q.obj A)⟦(1 : ℤ)⟧))⟦(-1 : ℤ)⟧ :=
    U.mapIso ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).symm.app
      (DerivedCategory.Q.obj A)) ≪≫
        (U.commShiftIso (-1 : ℤ)).app ((DerivedCategory.Q.obj A)⟦(1 : ℤ)⟧)
  let a' : U.obj M ≅ DerivedCategory.Q.obj (Uc.obj J) :=
    U.mapIso a ≪≫ (forget F).mapDerivedCategoryFactors.app J
  let c' : DerivedCategory.Q.obj (Uc.obj A) ≅ (U.obj N)⟦(-1 : ℤ)⟧ :=
    ((forget F).mapDerivedCategoryFactors.app A).symm ≪≫ k ≪≫
      (shiftFunctor _ (-1 : ℤ)).mapIso (U.mapIso c)
  have : CochainComplex.IsKInjective (Uc.obj A) := inferInstance
  obtain ⟨u₀, hu₀⟩ := CochainComplex.IsKInjective.exists_Q_map_eq (Uc.obj J) (Uc.obj A)
    (a'.inv ≫ u ≫ c'.inv)
  obtain ⟨E, f, g, w, hS, s, hs, he⟩ := exists_cyclicDerivedStrictExtension F A J u₀
  refine ⟨a.hom ≫ DerivedCategory.triangleOfSESδ hS ≫ c.hom,
    ShortComplex.mk f g w, hS, u₀, s, a, c, hs, he, ?_, rfl⟩
  dsimp [cyclicDerivedOffDiagonalClass]
  rw [hu₀]
  simp [a', c', k, U, Category.assoc]

section Comparison

set_option backward.defeqAttrib.useBackward true

variable [IsGrothendieckAbelian.{v} C]

-- Reuse the proved chain resolution independently of the two chosen derived universes.
private structure CyclicResolution where
  θ : ∀ (M : IsoAlgebra F) (n : ℤ), Free.obj F M.carrier n ≅ M.carrier
  d : forget F ⋙ Free.functor F ⟶ forget F ⋙ Free.functor F
  theta_eq : ∀ M n, (θ M n).hom = Free.hom M (𝟙 M.carrier) n
  summand : ∀ M n,
    Sigma.ι (Free.obj F M.carrier) n ≫ (forget F).map (d.app M) =
      Sigma.ι (Free.obj F M.carrier) n -
        (θ M n).hom ≫ (θ M (n - 1)).inv ≫ Sigma.ι (Free.obj F M.carrier) (n - 1)
  zero : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
    (d.mapHomologicalComplex (.up ℤ)).app K ≫
      ((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K = 0
  shortExact : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
    (ShortComplex.mk ((d.mapHomologicalComplex (.up ℤ)).app K)
      (((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K)
      (zero K)).ShortExact

omit [HasDerivedCategory C] [HasDerivedCategory (IsoAlgebra F)] in
private theorem exists_cyclicResolution : Nonempty (CyclicResolution F) := by
  let : IsGrothendieckAbelian.{v} (IsoAlgebra F) := isGrothendieckAbelian F
  let : HasDerivedCategory.{v} C := HasDerivedCategory.ofIsGrothendieckAbelian C
  let : HasDerivedCategory.{v} (IsoAlgebra F) :=
    HasDerivedCategory.ofIsGrothendieckAbelian (IsoAlgebra F)
  obtain ⟨θ, d, hθ, hd, _, hz, hs, _⟩ := exists_freeDerivedWeilResolution F
  exact ⟨⟨θ, d, hθ, by simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using hd,
    hz, hs⟩⟩

private abbrev freeComplex := (Free.functor F).mapHomologicalComplex (.up ℤ)

private abbrev freeCounit (K : CochainComplex (IsoAlgebra F) ℤ) :=
  ((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K

private def freeAdjunct {J A : CochainComplex (IsoAlgebra F) ℤ}
    (u : underlying F J ⟶ underlying F A) : (freeComplex F).obj (underlying F J) ⟶ A :=
  (freeComplex F).map u ≫ freeCounit F A

omit [HasDerivedCategory C] [HasDerivedCategory (IsoAlgebra F)] in
private theorem freeAdjunct_zero {J A : CochainComplex (IsoAlgebra F) ℤ}
    (u : underlying F J ⟶ underlying F A) (n : ℤ) :
    Sigma.ι (Free.obj F (J.X n).carrier) 0 ≫
      (forget F).map ((freeAdjunct F u).f n) = u.f n := by
  change Sigma.ι _ 0 ≫ (Free.map (u.f n)).hom.f ≫
    (Free.desc (A.X n) (𝟙 _)).hom.f = _
  rw [← Category.assoc, Free.map_hom_f, Sigma.ι_map, Free.objMap_zero]
  simp only [Category.assoc, Free.ι_desc_hom_f]
  exact Category.comp_id _

omit [HasDerivedCategory C] [HasDerivedCategory (IsoAlgebra F)] in
private theorem CyclicResolution.comparison (r : CyclicResolution F)
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
    have hθ0 : (r.θ (S.X₃.X n) 0).hom = 𝟙 _ := r.theta_eq _ _
    simp only [hθ0, Category.id_comp, Category.assoc]
    erw [freeAdjunct_zero,
      ← Category.assoc (Sigma.ι (Free.obj F (S.X₃.X n).carrier) 0), freeAdjunct_zero]
    change @id ((S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier) (s.f n) -
        @id ((S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier)
          ((r.θ (S.X₃.X n) (-1)).inv ≫
            Sigma.ι (Free.obj F (S.X₃.X n).carrier) (-1) ≫
            (forget F).map ((freeAdjunct F s).f n)) =
      @id ((S.X₃.X n).carrier ⟶ (S.X₁.X n).carrier) (u.f n) ≫
        @id ((S.X₁.X n).carrier ⟶ (S.X₂.X n).carrier) ((forget F).map (S.f.f n))
    have hrec := Free.map_ι_comp_comp_str ((freeAdjunct F s).f n) (-1)
    have hθ := Free.map_hom_comp_str (S.X₃.X n) (𝟙 _) (-1)
    rw [← r.theta_eq, ← r.theta_eq] at hθ
    change F.map (r.θ (S.X₃.X n) (-1)).hom ≫ (S.X₃.X n).str.hom =
      (Free.objSucc F (S.X₃.X n).carrier (-1)).hom ≫
        (r.θ (S.X₃.X n) 0).hom at hθ
    erw [hθ0, Category.comp_id] at hθ
    have hinv : F.map (r.θ (S.X₃.X n) (-1)).inv ≫
        (Free.objSucc F (S.X₃.X n).carrier (-1)).hom = (S.X₃.X n).str.hom := by
      erw [← hθ, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
    change F.map (Sigma.ι _ (-1) ≫ (forget F).map ((freeAdjunct F s).f n)) ≫
        (S.X₂.X n).str.hom =
      (Free.objSucc F (S.X₃.X n).carrier (-1)).hom ≫
        Sigma.ι (Free.obj F (S.X₃.X n).carrier) 0 ≫
          (forget F).map ((freeAdjunct F s).f n) at hrec
    erw [freeAdjunct_zero] at hrec
    have hback :
        F.map ((r.θ (S.X₃.X n) (-1)).inv ≫
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

private def freeLocalization (K : CochainComplex (IsoAlgebra F) ℤ) :
    ((forget F).mapDerivedCategory ⋙ (Free.functor F).mapDerivedCategory).obj
        (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ)).obj K) :=
  (Free.functor F).mapDerivedCategory.mapIso
      ((forget F).mapDerivedCategoryFactors.app K) ≪≫
    (Free.functor F).mapDerivedCategoryFactors.app (underlying F K)

private def freeComparison :
    DerivedCategory.Q ⋙
        ((forget F).mapDerivedCategory ⋙ (Free.functor F).mapDerivedCategory) ≅
      (forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (freeLocalization F) (fun f ↦ by
    dsimp [freeLocalization]
    erw [Category.assoc, ← (Free.functor F).mapDerivedCategory.map_comp_assoc,
      (forget F).mapDerivedCategoryFactors_hom_naturality,
      (Free.functor F).mapDerivedCategory.map_comp,
      Category.assoc, (Free.functor F).mapDerivedCategoryFactors_hom_naturality]
    rfl)

private def CyclicResolution.connecting (r : CyclicResolution F) : DerivedCategory.Q ⟶
    ((forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙
      shiftFunctor (DerivedCategory (IsoAlgebra F)) (1 : ℤ) where
  app K := DerivedCategory.triangleOfSESδ (r.shortExact K)
  naturality K L f := by
    let S (K : CochainComplex (IsoAlgebra F) ℤ) :=
      ShortComplex.mk ((r.d.mapHomologicalComplex (.up ℤ)).app K)
        (freeCounit F K) (r.zero K)
    let t : S K ⟶ S L :=
      { τ₁ := ((forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ)).map f
        τ₂ := ((forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ)).map f
        τ₃ := f
        comm₁₂ := (r.d.mapHomologicalComplex (.up ℤ)).naturality f
        comm₂₃ := ((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).naturality f }
    exact (DerivedCategory.triangleOfSESδ_naturality
      (r.shortExact K) (r.shortExact L) t).symm

-- Descend the natural chain boundary into the chosen fixed-pair derived category.
private def CyclicResolution.δ (r : CyclicResolution F) :
    𝟭 (DerivedCategory (IsoAlgebra F)) ⟶
      ((forget F).mapDerivedCategory ⋙ (Free.functor F).mapDerivedCategory) ⋙
        shiftFunctor (DerivedCategory (IsoAlgebra F)) (1 : ℤ) :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (IsoAlgebra F) (.up ℤ))
    (DerivedCategory (IsoAlgebra F))).preimage
      (r.connecting F ≫ Functor.whiskerRight (freeComparison F).inv (shiftFunctor _ (1 : ℤ)))

private theorem CyclicResolution.δ_Q (r : CyclicResolution F)
    (K : CochainComplex (IsoAlgebra F) ℤ) :
    (r.δ F).app (DerivedCategory.Q.obj K) ≫ (freeLocalization F K).hom⟦(1 : ℤ)⟧' =
      DerivedCategory.triangleOfSESδ (r.shortExact K) := by
  let τ : DerivedCategory.Q ⋙ 𝟭 (DerivedCategory (IsoAlgebra F)) ⟶
      DerivedCategory.Q ⋙
        (((forget F).mapDerivedCategory ⋙ (Free.functor F).mapDerivedCategory) ⋙
          shiftFunctor (DerivedCategory (IsoAlgebra F)) (1 : ℤ)) :=
    r.connecting F ≫
      Functor.whiskerRight (freeComparison F).inv (shiftFunctor _ (1 : ℤ))
  have h := congr_app ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (IsoAlgebra F) (.up ℤ))
    (DerivedCategory (IsoAlgebra F))).map_preimage τ) K
  change (r.δ F).app (DerivedCategory.Q.obj K) =
    DerivedCategory.triangleOfSESδ (r.shortExact K) ≫
      (freeLocalization F K).inv⟦(1 : ℤ)⟧' at h
  rw [h, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
    Category.comp_id]

private def freeDerivedCounit :
    (forget F).mapDerivedCategory ⋙ (Free.functor F).mapDerivedCategory ⟶
      𝟭 (DerivedCategory (IsoAlgebra F)) :=
  (Free.adjunction F).mapExactDerivedCategory.counit

private theorem freeDerivedCounit_Q (K : CochainComplex (IsoAlgebra F) ℤ) :
    (freeDerivedCounit F).app (DerivedCategory.Q.obj K) =
      (freeLocalization F K).hom ≫ DerivedCategory.Q.map (freeCounit F K) := by
  let : CatCommSq ((Free.functor F).mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q (Free.functor F).mapDerivedCategory :=
    ⟨(Free.functor F).mapDerivedCategoryFactors.symm⟩
  let : CatCommSq ((forget F).mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q (forget F).mapDerivedCategory :=
    ⟨(forget F).mapDerivedCategoryFactors.symm⟩
  have h := Adjunction.localization_counit_app
    ((Free.adjunction F).mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso (IsoAlgebra F) (.up ℤ))
    (Free.functor F).mapDerivedCategory (forget F).mapDerivedCategory K
  have hU : (CatCommSq.iso ((forget F).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (forget F).mapDerivedCategory).inv.app K =
      (forget F).mapDerivedCategoryFactors.hom.app K := rfl
  have hI : (CatCommSq.iso ((Free.functor F).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (Free.functor F).mapDerivedCategory).inv.app
        (underlying F K) =
      (Free.functor F).mapDerivedCategoryFactors.hom.app (underlying F K) := rfl
  have hc : ((Free.adjunction F).mapHomologicalComplex (.up ℤ)).counit.app K =
      freeCounit F K := by
    ext n
    exact (Free.adjunction F).mapHomologicalComplex_counit_app_f (.up ℤ) K n
  rw [hU, hI, hc] at h
  simpa only [freeDerivedCounit, Adjunction.mapExactDerivedCategory, freeLocalization,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using h

private def underlyingClass {J A : CochainComplex (IsoAlgebra F) ℤ}
    (u : underlying F J ⟶ underlying F A) :
    (forget F).mapDerivedCategory.obj (DerivedCategory.Q.obj J) ⟶
      (forget F).mapDerivedCategory.obj (DerivedCategory.Q.obj A) :=
  (forget F).mapDerivedCategoryFactors.hom.app J ≫ DerivedCategory.Q.map u ≫
    (forget F).mapDerivedCategoryFactors.inv.app A

private theorem freeAdjunct_localization {J A : CochainComplex (IsoAlgebra F) ℤ}
    (u : underlying F J ⟶ underlying F A) :
    (freeLocalization F J).hom ≫ DerivedCategory.Q.map (freeAdjunct F u) =
      (Free.functor F).mapDerivedCategory.map (underlyingClass F u) ≫
        (freeDerivedCounit F).app (DerivedCategory.Q.obj A) := by
  rw [freeDerivedCounit_Q]
  simp only [underlyingClass, Functor.map_comp, freeLocalization, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  erw [← (Free.functor F).mapDerivedCategory.map_comp_assoc
      ((forget F).mapDerivedCategoryFactors.inv.app A)
      ((forget F).mapDerivedCategoryFactors.hom.app A),
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
    (Free.functor F).mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [freeAdjunct, Functor.map_comp]

private def CyclicResolution.pairing (r : CyclicResolution F)
    {J A : DerivedCategory (IsoAlgebra F)}
    (u : (forget F).mapDerivedCategory.obj J ⟶ (forget F).mapDerivedCategory.obj A) :
    J ⟶ A⟦(1 : ℤ)⟧ :=
  (r.δ F).app J ≫
    ((Free.functor F).mapDerivedCategory.map u ≫ (freeDerivedCounit F).app A)⟦(1 : ℤ)⟧'

private theorem CyclicResolution.pairing_naturality (r : CyclicResolution F)
    {J A J' A' : DerivedCategory (IsoAlgebra F)} (a : J' ⟶ J) (c : A ⟶ A')
    (u : (forget F).mapDerivedCategory.obj J ⟶ (forget F).mapDerivedCategory.obj A) :
    a ≫ r.pairing F u ≫ c⟦(1 : ℤ)⟧' =
      r.pairing F ((forget F).mapDerivedCategory.map a ≫ u ≫
        (forget F).mapDerivedCategory.map c) := by
  simp only [CyclicResolution.pairing, Category.assoc]
  rw [← Functor.map_comp, Category.assoc]
  erw [← (freeDerivedCounit F).naturality c]
  erw [(r.δ F).naturality_assoc a]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]

-- The comparison of short exact sequences fixes the boundary, including its sign.
private theorem CyclicResolution.pairing_boundary (r : CyclicResolution F)
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
    r.pairing F (underlyingClass F u) = DerivedCategory.triangleOfSESδ hS := by
  obtain ⟨h₁, h₂⟩ := r.comparison F S u s hs he
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
  simpa only [CyclicResolution.pairing, ← freeAdjunct_localization,
    Functor.map_comp, ← Category.assoc, CyclicResolution.δ_Q,
    Functor.map_id, Category.id_comp] using h

private def unshiftBoundary {A N : DerivedCategory (IsoAlgebra F)}
    (c : A⟦(1 : ℤ)⟧ ⟶ N) : A ⟶ N⟦(-1 : ℤ)⟧ :=
  (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).inv.app A ≫ c⟦(-1 : ℤ)⟧'

omit [HasDerivedCategory C] [IsGrothendieckAbelian.{v} C] in
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

end Comparison

/-- Two strict off-diagonal presentations of the same shifted morphism have the same
native connecting morphism.

Proof: use the natural two-term free resolution of J. For a splitting s of the
underlying projection of a presented extension, let e be its free adjunct and let f₀
be the free adjunct of the off-diagonal map u₀. Evaluation on summand zero, with the
inverse triangular action, gives e d = j f₀ and p e = ε. These two equations define a
map from the free short exact sequence to the presented one. Naturality of the
canonical SES boundary gives δ_S = δ_free ≫ f₀[1], with the canonical shift
cancellation. Passing to the free/forgetful derived adjunction identifies f₀ with
the prescribed underlying shifted morphism. Thus every presentation computes the
same adjunct formula δ_M ≫ adjunct(u)[1], followed by cancellation of the opposite
shifts. Naturality of the free triangle handles the endpoint isomorphisms in the
presentation. Both presented morphisms equal this formula. The free resolution is
unbounded, so no cohomological bound is used.

Source: step 8 of lem-sf-cyclic-derived-hom-exact-sequence and Stacks Tag 0152,
using the explicit free-resolution summand formula.
(blueprint: lem-sf-cyclic-derived-off-diagonal-presentation). -/
theorem cyclicDerivedOffDiagonalPresentation_unique [IsGrothendieckAbelian.{v} C]
    {M N : DerivedCategory (IsoAlgebra F)} {u : CyclicDerivedHom F M N (-1)}
    {f g : M ⟶ N} (hf : CyclicDerivedOffDiagonalPresentation F u f)
    (hg : CyclicDerivedOffDiagonalPresentation F u g) : f = g := by
  obtain ⟨r⟩ := exists_cyclicResolution F
  have hvalue (f : M ⟶ N) (hf : CyclicDerivedOffDiagonalPresentation F u f) :
      f = r.pairing F
        (u ≫ ((forget F).mapDerivedCategory.commShiftIso (-1 : ℤ)).inv.app N) ≫
          (shiftEquiv _ (1 : ℤ)).counitIso.hom.app N := by
    obtain ⟨S, hS, u₀, s, a, c, hs, he, hu, rfl⟩ := hf
    have hp := r.pairing_naturality F a.hom (unshiftBoundary F c.hom)
      (underlyingClass F u₀)
    rw [r.pairing_boundary F S hS u₀ s hs he] at hp
    have hu' :
        (forget F).mapDerivedCategory.map a.hom ≫ underlyingClass F u₀ ≫
          (forget F).mapDerivedCategory.map (unshiftBoundary F c.hom) =
        u ≫ ((forget F).mapDerivedCategory.commShiftIso (-1 : ℤ)).inv.app N := by
      rw [hu]
      simp only [Category.assoc, offDiagonalClass_unshift]
    rw [← hu', ← hp]
    simp only [Category.assoc, unshiftBoundary_shift]
  exact (hvalue f hf).trans (hvalue g hg).symm

/-- Every underlying shifted morphism determines exactly one native morphism represented
by a strict off-diagonal extension. The strict extension itself is not claimed unique.
Proof: combine the explicit triangular construction on K-injective representatives with
the free-resolution comparison of any two presentations.
Source: steps 6--8 of the parent node and Stacks Tags 070I and 0152
(blueprint: lem-sf-cyclic-derived-off-diagonal-presentation). -/
theorem exists_unique_cyclicDerivedOffDiagonalPresentation [IsGrothendieckAbelian.{v} C]
    {M N : DerivedCategory (IsoAlgebra F)} (u : CyclicDerivedHom F M N (-1)) :
    ∃! f : M ⟶ N, CyclicDerivedOffDiagonalPresentation F u f := by
  obtain ⟨f, hf⟩ := exists_cyclicDerivedOffDiagonalPresentation F u
  exact ⟨f, hf, fun g hg ↦ cyclicDerivedOffDiagonalPresentation_unique F hg hf⟩

/-- The uniquely specified native morphism represented by the off-diagonal extension.
Only its unique value is chosen, not a complex, resolution, or extension witness.
Source: the unique-value characterization above, Stacks Tag 0152
(blueprint: lem-sf-cyclic-derived-off-diagonal-presentation). -/
def cyclicDerivedOffDiagonalBoundary [IsGrothendieckAbelian.{v} C]
    {M N : DerivedCategory (IsoAlgebra F)} (u : CyclicDerivedHom F M N (-1)) : M ⟶ N :=
  Classical.choose (exists_unique_cyclicDerivedOffDiagonalPresentation F u)

/-- The boundary has its prescribed strict presentation.
Source: the unique-value characterization, Stacks Tag 0152
(blueprint: lem-sf-cyclic-derived-off-diagonal-presentation). -/
theorem cyclicDerivedOffDiagonalBoundary_presentation [IsGrothendieckAbelian.{v} C]
    {M N : DerivedCategory (IsoAlgebra F)} (u : CyclicDerivedHom F M N (-1)) :
    CyclicDerivedOffDiagonalPresentation F u (cyclicDerivedOffDiagonalBoundary F u) :=
  (Classical.choose_spec (exists_unique_cyclicDerivedOffDiagonalPresentation F u)).1

/-- Any strict presentation computes the specified boundary.
Source: uniqueness in the presentation characterization, Stacks Tag 0152
(blueprint: lem-sf-cyclic-derived-off-diagonal-presentation). -/
theorem cyclicDerivedOffDiagonalBoundary_eq [IsGrothendieckAbelian.{v} C]
    {M N : DerivedCategory (IsoAlgebra F)} {u : CyclicDerivedHom F M N (-1)} {f : M ⟶ N}
    (h : CyclicDerivedOffDiagonalPresentation F u f) :
    cyclicDerivedOffDiagonalBoundary F u = f :=
  ((Classical.choose_spec (exists_unique_cyclicDerivedOffDiagonalPresentation F u)).2 f h).symm

end CategoryTheory.Endofunctor.IsoAlgebra
