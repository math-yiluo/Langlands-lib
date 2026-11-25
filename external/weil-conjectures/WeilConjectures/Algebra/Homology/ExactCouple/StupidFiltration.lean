/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.ExactCouple.Triangulated
public import WeilConjectures.Algebra.Homology.ExactCouple.Convergence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# The spectral sequence `E₁^{r, s} = R^r v(K^s) ⟹ H^{r + s}(R⁺v(K))`

Let `v : A ⥤ B` be an additive functor between abelian categories, where `A` has enough
injectives, and let `K` be a bounded below cochain complex in `A`. We construct the spectral
sequence

`E₁^{r, s} = R^r v(K^s) ⟹ H^{r + s}(R⁺v(K))`

of blueprint `thm-sp-if-e1`, whose differential `d₁ : E₁^{r, s} ⟶ E₁^{r, s + 1}` is
`R^r v(d_K)`.

## The construction

The blueprint constructs this spectral sequence from a Cartan–Eilenberg resolution of `K`,
filtered by the second degree. We use the equivalent construction by the *stupid filtration*:
the stupid truncations `σ_{≥ s} K` give degreewise split short exact sequences of complexes

`0 ⟶ σ_{≥ s + 1} K ⟶ σ_{≥ s} K ⟶ K^s[-s] ⟶ 0`,

hence a tower of distinguished triangles in the bounded below homotopy category
(`CochainComplex.stupidTower`). Its image under the localization functor and the triangulated
functor `R⁺v : D⁺(A) ⥤ D⁺(B)` is a tower of distinguished triangles in `D⁺(B)`
(`CategoryTheory.Functor.stupidFiltrationTower`), and the long exact cohomology sequences of
these triangles form an exact couple (`CategoryTheory.Functor.stupidFiltrationExactCouple`)
indexed by the filtration degree `s` and the total degree `n`, with

`D^{s, n} = Hⁿ(R⁺v(σ_{≥ s} K))` and `E^{s, n} = Hⁿ(R⁺v(K^s[-s])) ≅ R^{n - s} v(K^s)`.

(Applying a Cartan–Eilenberg resolution `I^{•, •}` of `K` and filtering `v(Tot I)` by the second
degree gives exactly the same exact couple: the second filtration of `Tot I` is a resolution of
the stupid filtration of `K`.) The spectral sequence of this couple, starting on page `1`, has
`E₁^{s, n} ≅ R^{n - s} v(K^s)` (`CategoryTheory.Functor.stupidFiltrationE₁Iso`), its differential
`d₁ : E₁^{s, n} ⟶ E₁^{s + 1, n + 1}` is `R^{n - s} v(d_K)`
(`CategoryTheory.Functor.stupidFiltrationE₁Iso_inv_comp_d_comp_hom`), and it converges to the
cohomology `Hⁿ(R⁺v(K))` of the derived functor, filtered by the images of
`Hⁿ(R⁺v(σ_{≥ s} K))` (`CategoryTheory.Functor.stupidFiltrationExactCouple_convergesTo`). The
abutment `Hⁿ(R⁺v(K))` only depends on `K` (and not on any choice of resolutions).

In the notation `E₁^{r, s}` of the blueprint, `r = n - s` is the degree of the derived functor
and `s` is the degree in `K`.

## Main definitions

- `CochainComplex.stupidTower`: the tower of distinguished triangles of stupid truncations.
- `CategoryTheory.Functor.stupidFiltrationExactCouple`: the exact couple.
- `CategoryTheory.Functor.stupidFiltrationSpectralSequence`: its spectral sequence.
- `CategoryTheory.Functor.stupidFiltrationE₁Iso`: `E₁^{s, n} ≅ R^{n - s} v(K^s)`.

## Main statements

- `CategoryTheory.Functor.isZero_stupidFiltrationExactCouple_E`: `E₁^{s, n} = 0` for `n < s`.
- `CategoryTheory.Functor.stupidFiltrationE₁Iso_inv_comp_d_comp_hom`: `d₁ = R^r v(d_K)`.
- `CategoryTheory.Functor.stupidFiltrationExactCouple_convergesTo`: convergence to
  `Hⁿ(R⁺v(K))`.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)
  [P.IsTriangulated]

/-- The lift of a triangle of `C` whose objects satisfy `P` to a triangle in the full
triangulated subcategory `P.FullSubcategory`. -/
noncomputable def liftTriangle (T : Triangle C) (h₁ : P T.obj₁) (h₂ : P T.obj₂)
    (h₃ : P T.obj₃) : Triangle P.FullSubcategory :=
  Triangle.mk (X := ⟨T.obj₁, h₁⟩) (Y := ⟨T.obj₂, h₂⟩) (Z := ⟨T.obj₃, h₃⟩)
    (ObjectProperty.homMk T.mor₁) (ObjectProperty.homMk T.mor₂)
    (ObjectProperty.homMk (T.mor₃ ≫ (P.ι.commShiftIso (1 : ℤ)).inv.app ⟨T.obj₁, h₁⟩))

/-- The lift of a distinguished triangle to a full triangulated subcategory is
distinguished. -/
lemma liftTriangle_distinguished (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : P T.obj₁)
    (h₂ : P T.obj₂) (h₃ : P T.obj₃) : P.liftTriangle T h₁ h₂ h₃ ∈ distTriang _ :=
  isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [liftTriangle, Functor.mapTriangle]) (by simp [liftTriangle, Functor.mapTriangle])
    (by
      dsimp [liftTriangle, Functor.mapTriangle]
      simp only [Category.assoc,
        CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
      erw [Iso.inv_hom_id_app, Category.comp_id]))

end CategoryTheory.ObjectProperty

namespace CategoryTheory.SingleFunctors

section Lift

variable {C D E : Type*} [Category C] [Category D] [Category E] [HasShift D ℤ] [HasShift E ℤ]

/-- The image under the fully faithful functor `G` of the inverse of the shift isomorphisms of
the single functors `SingleFunctors.lift F G Φ hΦ`. -/
lemma map_lift_shiftIso_inv_app (F : SingleFunctors C E ℤ) (G : D ⥤ E) [G.CommShift ℤ]
    [G.Full] [G.Faithful] (Φ : ℤ → C ⥤ D) (hΦ : ∀ a, Φ a ⋙ G ≅ F.functor a)
    (n a a' : ℤ) (h : n + a = a') (X : C) :
    G.map (((lift F G Φ hΦ).shiftIso n a a' h).inv.app X) =
      (hΦ a).hom.app X ≫ (F.shiftIso n a a' h).inv.app X ≫
        (shiftFunctor E n).map ((hΦ a').inv.app X) ≫ (G.commShiftIso n).inv.app _ := by
  rw [← cancel_epi (G.map (((lift F G Φ hΦ).shiftIso n a a' h).hom.app X)), ← G.map_comp,
    Iso.hom_inv_id_app, G.map_id, map_lift_shiftIso_hom_app]
  simp [← Functor.map_comp_assoc]
  rfl

end Lift

section ShiftSequence

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [HasShift D ℤ]
  (F : SingleFunctors C D ℤ) (H : D ⥤ E) [H.ShiftSequence ℤ]

/-- For single functors `F` and a functor `H` with a shift sequence, the isomorphism
`Hⁿ(F_t X) ≅ Hⁿ'(F_{t'} X)` when `m + t = t'` and `m + n = n'`, induced by
`F_t X ≅ (F_{t'} X)⟦m⟧`. -/
noncomputable def shiftSequenceIso (t t' m n n' : ℤ) (ht : m + t = t') (hn : m + n = n') :
    F.functor t ⋙ H.shift n ≅ F.functor t' ⋙ H.shift n' :=
  Functor.isoWhiskerRight (F.shiftIso m t t' ht).symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (H.shiftIso m n n' hn)

lemma shiftSequenceIso_hom_app (t t' m n n' : ℤ) (ht : m + t = t') (hn : m + n = n') (X : C) :
    (F.shiftSequenceIso H t t' m n n' ht hn).hom.app X =
      (H.shift n).map ((F.shiftIso m t t' ht).inv.app X) ≫
        (H.shiftIso m n n' hn).hom.app ((F.functor t').obj X) := by
  simp [shiftSequenceIso]

/-- The isomorphisms `SingleFunctors.shiftSequenceIso` are compatible with composition. -/
lemma shiftSequenceIso_trans (t t' t'' m m' mm' n n' n'' : ℤ) (ht : m + t = t')
    (ht' : m' + t' = t'') (hn : m + n = n') (hn' : m' + n' = n'') (hm : m' + m = mm') :
    F.shiftSequenceIso H t t' m n n' ht hn ≪≫ F.shiftSequenceIso H t' t'' m' n' n'' ht' hn' =
      F.shiftSequenceIso H t t'' mm' n n'' (by omega) (by omega) := by
  ext X
  simp only [Iso.trans_hom, NatTrans.comp_app, shiftSequenceIso_hom_app,
    F.shiftIso_add'_inv_app m m' mm' hm t t' t'' ht ht',
    H.shiftIso_add'_hom_app m m' mm' hm n n' n'' hn hn', Functor.map_comp, Category.assoc]
  congr 1
  rw [← Functor.map_comp_assoc (H.shift n) ((shiftFunctorAdd' D m' m mm' hm).inv.app _),
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  exact (H.shiftIso_hom_naturality_assoc m n n' hn _ _).symm

end ShiftSequence

end CategoryTheory.SingleFunctors

namespace CategoryTheory.TriangleTower

variable {T : Type*} [Category* T] [HasZeroObject T] [HasShift T ℤ] [Preadditive T]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] (P : TriangleTower T)

/-- Transport of a family of morphisms `P.X q ⟶ Z` along an equality of indices. -/
lemma eqToHom_X_comp {Z : T} (f : ∀ q, P.X q ⟶ Z) (q q' : ℤ) (h : q = q') :
    eqToHom (congrArg P.X h) ≫ f q' = f q := by
  subst h
  simp

variable {C : Type*} [Category* C] [Abelian C] (H : T ⥤ C) [H.ShiftSequence ℤ]

/-- The composite `g ∘ f : Hⁿ(Y q) ⟶ Hⁿ⁺¹(Y (q - 1))` in the exact couple of a tower is induced
by the composite `Y q ⟶ X (q - 1)⟦1⟧ ⟶ Y (q - 1)⟦1⟧`. -/
lemma couplef_comp_coupleg (q q' n n' : ℤ) (hq : q' = q - 1) (hn : n + 1 = n') :
    P.couplef H (q, n) (q', n') ≫ P.coupleg H (q', n') (q', n') =
      H.shiftMap (P.mor₃ q ≫ (eqToHom (congrArg P.X hq.symm) ≫ P.mor₂ q')⟦(1 : ℤ)⟧') n n'
        (by omega) := by
  subst hq hn
  rw [couplef_self _ _ _ _ _ rfl, coupleg_self, eqToHom_refl, Category.id_comp, H.shiftMap_comp]
  rfl

section Map

variable {T' : Type*} [Category* T'] [HasZeroObject T'] [HasShift T' ℤ] [Preadditive T']
  [∀ n : ℤ, (shiftFunctor T' n).Additive] [Pretriangulated T']
  (G : T ⥤ T') [G.CommShift ℤ] [G.IsTriangulated]

/-- The connecting morphisms of the image of a tower under a triangulated functor `G`, followed
by the image of a morphism, are the images of the corresponding composites. -/
lemma map_mor₃_comp_shift_map {Z : T} (q : ℤ) (f : P.X (q - 1) ⟶ Z) :
    (P.map G).mor₃ q ≫ (G.map f)⟦(1 : ℤ)⟧' =
      G.map (P.mor₃ q ≫ f⟦(1 : ℤ)⟧') ≫ (G.commShiftIso (1 : ℤ)).hom.app Z := by
  simp [Functor.commShiftIso_hom_naturality]

end Map

end CategoryTheory.TriangleTower

/-- The image in the homotopy category of bounded below complexes of the inverse of the shift
isomorphisms of the single functors. -/
lemma HomotopyCategory.Plus.ι_map_singleFunctors_shiftIso_inv_app {A : Type*} [Category* A]
    [Abelian A] (n a a' : ℤ) (h : n + a = a') (X : A) :
    (HomotopyCategory.Plus.ι A).map
        (((HomotopyCategory.Plus.singleFunctors A).shiftIso n a a' h).inv.app X) =
      (HomotopyCategory.quotient A _).map
          (((CochainComplex.singleFunctors A).shiftIso n a a' h).inv.app X) ≫
        ((HomotopyCategory.quotient A _).commShiftIso n).hom.app _ ≫
        ((HomotopyCategory.Plus.ι A).commShiftIso n).inv.app
          ((HomotopyCategory.Plus.singleFunctor A a').obj X) := by
  dsimp only [HomotopyCategory.Plus.singleFunctors]
  rw [SingleFunctors.map_lift_shiftIso_inv_app]
  simp only [HomotopyCategory.singleFunctors, ObjectProperty.ι_obj, Functor.comp_obj,
    ObjectProperty.lift_obj_obj, Iso.refl_hom, NatTrans.id_app,
    SingleFunctors.postcomp_shiftIso_inv_app,
    Iso.refl_inv, Category.assoc, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The isomorphism `(K.stupidTrunc e).X i' ≅ K.X i'` is the component of the inclusion
`K.stupidTrunc e ⟶ K`. -/
lemma HomologicalComplex.stupidTruncXIso_hom_eq_ιStupidTrunc_f {C : Type*} [Category* C]
    [HasZeroMorphisms C] [HasZeroObject C] {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} (L : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncGE]
    {i : ι} {i' : ι'} (hi : e.f i = i') :
    (L.stupidTruncXIso e hi).hom = (L.ιStupidTrunc e).f i' := by
  subst hi
  dsimp [HomologicalComplex.ιStupidTrunc]
  rw [HomologicalComplex.ιStupidTruncf_eq]
  simp [HomologicalComplex.stupidTruncXIso]

namespace CochainComplex

variable {A : Type*} [Category* A] [Abelian A] (K : CochainComplex A ℤ)

instance (s : ℤ) : (K.stupidFiltrationGE.obj ⟨s⟩).IsStrictlyGE s :=
  inferInstanceAs
    (CochainComplex.IsStrictlyGE (K.stupidTrunc (ComplexShape.embeddingUpIntGE s)) s)

instance (s : ℤ) :
    IsIso ((K.stupidFiltrationGE.map (homOfLE (show s ≤ s + 1 by omega)).op).f (s + 1)) :=
  K.isIso_stupidFiltrationGE_map_f s (s + 1) _ (s + 1) (Or.inl le_rfl)

/-- The stupid truncation `σ_{≥ s} K`, as an object of the bounded below homotopy
category. -/
noncomputable def stupidFiltrationGEPlus (s : ℤ) : HomotopyCategory.Plus A :=
  ⟨(HomotopyCategory.quotient A _).obj (K.stupidFiltrationGE.obj ⟨s⟩), by
    rw [HomotopyCategory.plus_quotient_obj_iff]
    exact ⟨s, inferInstance⟩⟩

/-- The distinguished triangle `σ_{≥ s + 1} K ⟶ σ_{≥ s} K ⟶ K^s[-s] ⟶ (σ_{≥ s + 1} K)[1]` in
the bounded below homotopy category, given by the degreewise split short exact sequence of
stupid truncations. -/
noncomputable def stupidTrianglePlus (s₀ s₁ : ℤ) (h : s₀ + 1 = s₁) :
    Triangle (HomotopyCategory.Plus A) :=
  (HomotopyCategory.plus A).liftTriangle
    (CochainComplex.trianglehOfDegreewiseSplit (K.shortComplexStupidFiltrationGE s₀ s₁ h)
      (K.shortComplexStupidFiltrationGESplitting s₀ s₁ h))
    (K.stupidFiltrationGEPlus s₁).2 (K.stupidFiltrationGEPlus s₀).2
    ((HomotopyCategory.Plus.singleFunctor A s₀).obj (K.X s₀)).2

lemma stupidTrianglePlus_distinguished (s₀ s₁ : ℤ) (h : s₀ + 1 = s₁) :
    K.stupidTrianglePlus s₀ s₁ h ∈ distTriang _ :=
  ObjectProperty.liftTriangle_distinguished _ _
    (HomotopyCategory.trianglehOfDegreewiseSplit_distinguished _ _) _ _ _

/-- The tower of distinguished triangles of the stupid filtration of a cochain complex `K`,
in the bounded below homotopy category: `X q = σ_{≥ -q} K` and `Y q = K^{-q}[q]`. -/
noncomputable def stupidTower : TriangleTower (HomotopyCategory.Plus A) where
  X q := K.stupidFiltrationGEPlus (-q)
  Y q := (HomotopyCategory.Plus.singleFunctor A (-q)).obj (K.X (-q))
  mor₁ q := (K.stupidTrianglePlus (-q) (-(q - 1)) (by omega)).mor₁
  mor₂ q := (K.stupidTrianglePlus (-q) (-(q - 1)) (by omega)).mor₂
  mor₃ q := (K.stupidTrianglePlus (-q) (-(q - 1)) (by omega)).mor₃
  distinguished q := K.stupidTrianglePlus_distinguished _ _ _

lemma stupidTower_mor₁ (q : ℤ) :
    K.stupidTower.mor₁ q = ObjectProperty.homMk ((HomotopyCategory.quotient A _).map
      (K.stupidFiltrationGE.map (homOfLE (show -q ≤ -(q - 1) by omega)).op)) :=
  rfl

lemma stupidTower_mor₂ (q : ℤ) :
    K.stupidTower.mor₂ q = ObjectProperty.homMk ((HomotopyCategory.quotient A _).map
      (K.shortComplexStupidFiltrationGE (-q) (-(q - 1)) (by omega)).g) :=
  rfl

lemma stupidTower_mor₃ (q : ℤ) :
    K.stupidTower.mor₃ q = ObjectProperty.homMk
      ((trianglehOfDegreewiseSplit (K.shortComplexStupidFiltrationGE (-q) (-(q - 1)) (by omega))
          (K.shortComplexStupidFiltrationGESplitting (-q) (-(q - 1)) (by omega))).mor₃ ≫
        ((HomotopyCategory.Plus.ι A).commShiftIso (1 : ℤ)).inv.app
          (K.stupidFiltrationGEPlus (-(q - 1)))) :=
  rfl

/-- The inclusions `σ_{≥ s₁} K ⟶ σ_{≥ s₀} K ⟶ K` compose to the inclusion `σ_{≥ s₁} K ⟶ K`. -/
lemma stupidFiltrationGE_map_ιStupidTrunc (s₀ s₁ : ℤ) (h : s₀ ≤ s₁) :
    K.stupidFiltrationGE.map (homOfLE h).op ≫ K.ιStupidTrunc (ComplexShape.embeddingUpIntGE s₀) =
      K.ιStupidTrunc (ComplexShape.embeddingUpIntGE s₁) :=
  K.mapStupidTruncGE_fac _

/-- The differential of `σ_{≥ s} K` in degrees `s ⟶ s + 1`, read through the identifications
of the stupid truncations with `K` in these degrees, is the differential of `K`. -/
lemma stupidTruncXIso_inv_d_comp (s : ℤ) :
    (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE s) (i := 0) (by simp)).inv ≫
      (K.stupidFiltrationGE.obj ⟨s⟩).d s (s + 1) ≫
        inv ((K.stupidFiltrationGE.map (homOfLE (show s ≤ s + 1 by omega)).op).f (s + 1)) ≫
          (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE (s + 1)) (i := 0) (by simp)).hom =
      K.d s (s + 1) := by
  have h₁ := HomologicalComplex.congr_hom (K.stupidFiltrationGE_map_ιStupidTrunc s (s + 1)
    (by omega)) (s + 1)
  have h₂ := (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE s)).comm s (s + 1)
  rw [HomologicalComplex.comp_f] at h₁
  rw [HomologicalComplex.stupidTruncXIso_hom_eq_ιStupidTrunc_f, ← h₁, IsIso.inv_hom_id_assoc]
  erw [← h₂]
  rw [← HomologicalComplex.stupidTruncXIso_hom_eq_ιStupidTrunc_f K _ (i := 0) (by simp),
    Iso.inv_hom_id_assoc]

/-- The composite `K^{s₀}[-s₀] ⟶ (σ_{≥ s₁} K)[1] ⟶ K^{s₁}[-s₁][1]` of the connecting morphism of
the degreewise split short exact sequence of stupid truncations with the projection is induced by
the differential `d : K^{s₀} ⟶ K^{s₁}`, without sign. -/
lemma homOfDegreewiseSplit_stupidFiltrationGE_comp (s₀ s₁ s₂ : ℤ) (h : s₀ + 1 = s₁)
    (h' : s₁ + 1 = s₂) :
    homOfDegreewiseSplit (K.shortComplexStupidFiltrationGE s₀ s₁ h)
        (K.shortComplexStupidFiltrationGESplitting s₀ s₁ h) ≫
      (K.shortComplexStupidFiltrationGE s₁ s₂ h').g⟦(1 : ℤ)⟧' =
      (HomologicalComplex.single A (.up ℤ) s₀).map (K.d s₀ s₁) ≫
        ((CochainComplex.singleFunctors A).shiftIso 1 s₀ s₁ (by omega)).inv.app (K.X s₁) := by
  subst h h'
  apply HomologicalComplex.from_single_hom_ext
  simp only [shiftFunctor_obj_X', shortComplexStupidFiltrationGE_g, stupidFiltrationGEObjToSingle,
    Functor.comp_obj, evaluation_obj_obj, HomologicalComplex.comp_f, homOfDegreewiseSplit_f,
    cocycleOfDegreewiseSplit, shortComplexStupidFiltrationGESplitting, homOfLE_leOfHom,
    Functor.comp_map, ComplexShape.Embedding.stupidTruncGEFiltration_map, evaluation_obj_map,
    ComplexShape.Embedding.Subset.mapStupidTruncGE_app, HomComplex.Cocycle.mk_coe,
    HomComplex.Cochain.mk_v, ↓reduceDIte, eqToHom_refl, Category.id_comp, add_eq_left,
    one_ne_zero, Category.assoc, shiftFunctor_map_f', HomologicalComplex.mkHomToSingle_f,
    singleFunctors, NatIso.ofComponents_inv_app, HomologicalComplex.Hom.isoOfComponents_inv_f,
    eqToIso.inv]
  have key := K.stupidTruncXIso_inv_d_comp s₀
  simp only [Functor.comp_obj, evaluation_obj_obj, homOfLE_leOfHom, Functor.comp_map,
    ComplexShape.Embedding.stupidTruncGEFiltration_map, evaluation_obj_map,
    ComplexShape.Embedding.Subset.mapStupidTruncGE_app] at key
  erw [reassoc_of% key]
  rw [HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, Iso.cancel_iso_hom_left]
  congr 1
  simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]

/-- In the tower of stupid truncations, the composite `K^{-q}[q] ⟶ (σ_{≥ -q + 1} K)[1] ⟶
K^{-q + 1}[q - 1][1]` is induced by the differential of `K`. -/
lemma stupidTower_mor₃_comp_mor₂ (q : ℤ) :
    K.stupidTower.mor₃ q ≫ (K.stupidTower.mor₂ (q - 1))⟦(1 : ℤ)⟧' =
      (HomotopyCategory.Plus.singleFunctor A (-q)).map (K.d (-q) (-(q - 1))) ≫
        ((HomotopyCategory.Plus.singleFunctors A).shiftIso 1 (-q) (-(q - 1)) (by omega)).inv.app
          (K.X (-(q - 1))) := by
  apply (HomotopyCategory.Plus.ι A).map_injective
  have h₁ := (HomotopyCategory.quotient A (.up ℤ)).commShiftIso_hom_naturality
    (K.shortComplexStupidFiltrationGE (-(q - 1)) (-(q - 1 - 1)) (by omega)).g (1 : ℤ)
  have h₂ := congrArg (HomotopyCategory.quotient A (.up ℤ)).map
    (K.homOfDegreewiseSplit_stupidFiltrationGE_comp (-q) (-(q - 1)) (-(q - 1 - 1)) (by omega)
      (by omega))
  simp only [Functor.map_comp] at h₂
  have key := h₂ =≫ ((HomotopyCategory.quotient A (.up ℤ)).commShiftIso (1 : ℤ)).hom.app
    (K.shortComplexStupidFiltrationGE (-(q - 1)) (-(q - 1 - 1)) (by omega)).X₃
  rw [Category.assoc, h₁, Category.assoc] at key
  rw [Functor.map_comp, Functor.map_comp,
    HomotopyCategory.Plus.ι_map_singleFunctors_shiftIso_inv_app,
    ← cancel_mono (((HomotopyCategory.Plus.ι A).commShiftIso (1 : ℤ)).hom.app _),
    Category.assoc, Functor.commShiftIso_hom_naturality, stupidTower_mor₃, stupidTower_mor₂]
  simp only [ObjectProperty.ι_map, ObjectProperty.homMk_hom, Category.assoc]
  erw [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact (Category.assoc _ _ _).trans key

/-- The inclusion `σ_{≥ s} K ⟶ K` in the bounded below homotopy category, for a bounded below
complex `K`. -/
noncomputable def stupidFiltrationGEPlusι (K : CochainComplex.Plus A) (s : ℤ) :
    K.obj.stupidFiltrationGEPlus s ⟶ (HomotopyCategory.Plus.quotient A).obj K :=
  ObjectProperty.homMk ((HomotopyCategory.quotient A _).map
    (K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE s)))

lemma stupidTower_mor₁_comp_stupidFiltrationGEPlusι (K : CochainComplex.Plus A) (q : ℤ) :
    K.obj.stupidTower.mor₁ q ≫ stupidFiltrationGEPlusι K (-q) =
      stupidFiltrationGEPlusι K (-(q - 1)) := by
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, stupidTower_mor₁]
  simp only [stupidFiltrationGEPlusι, ObjectProperty.homMk_hom]
  rw [← Functor.map_comp]
  exact congrArg _ (K.obj.stupidFiltrationGE_map_ιStupidTrunc _ _ _)

instance (K : CochainComplex.Plus A) (s : ℤ) [K.obj.IsStrictlyGE s] :
    IsIso (stupidFiltrationGEPlusι K s) := by
  rw [← ObjectProperty.isIso_hom_iff]
  dsimp [stupidFiltrationGEPlusι]
  infer_instance

end CochainComplex

namespace CategoryTheory.Functor

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] (v : A ⥤ B) [v.Additive]

instance (K : CochainComplex A ℤ) (s : ℤ) :
    (DerivedCategory.Plus.Qh.obj (K.stupidFiltrationGEPlus s)).IsGE s := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((DerivedCategory.quotientCompQhIso A).symm.app (K.stupidFiltrationGE.obj ⟨s⟩)) s

variable (A) in
/-- The isomorphism `HomotopyCategory.Plus.singleFunctor A t ⋙ DerivedCategory.Plus.Qh ≅
DerivedCategory.Plus.singleFunctor A t`. -/
noncomputable def plusSingleFunctorCompQhIso (t : ℤ) :
    HomotopyCategory.Plus.singleFunctor A t ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.singleFunctor A t :=
  ((Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).whiskeringRight A).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.Plus.QhCompιIsoιCompQh A) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (HomotopyCategory.Plus.singleFunctorCompιIso A t) _ ≪≫
      (DerivedCategory.singleFunctorIsoCompQh A t).symm ≪≫
      (DerivedCategory.Plus.singleFunctorιIso A t).symm)

instance (t : ℤ) (X : A) :
    (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor A t).obj X)).IsGE t := by
  have : ((DerivedCategory.Plus.singleFunctor A t).obj X).IsGE t := inferInstance
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff] at this ⊢
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (DerivedCategory.Plus.ι.mapIso ((plusSingleFunctorCompQhIso A t).app X).symm) t

/-- The tower of distinguished triangles `R⁺v(σ_{≥ -q} K)` in `D⁺(B)`, image under the
right derived functor `R⁺v` of the tower of stupid truncations of `K`. -/
noncomputable def stupidFiltrationTower (K : CochainComplex A ℤ) :
    TriangleTower (DerivedCategory.Plus B) :=
  (K.stupidTower.map DerivedCategory.Plus.Qh).map v.rightDerivedFunctorPlus

/-- **The exact couple of the stupid filtration.** For an additive functor `v : A ⥤ B` (where
`A` has enough injectives) and a cochain complex `K`, the exact couple indexed by the filtration
degree `s` and the total degree `n` with `D^{s, n} = Hⁿ(R⁺v(σ_{≥ s} K))` and
`E^{s, n} = Hⁿ(R⁺v(K^s[-s])) ≅ R^{n - s} v(K^s)`, given by the long exact cohomology sequences of
the distinguished triangles `R⁺v(σ_{≥ s + 1} K) ⟶ R⁺v(σ_{≥ s} K) ⟶ R⁺v(K^s[-s]) ⟶`.
Its spectral sequence is `E₁^{r, s} = R^r v(K^s) ⟹ H^{r + s}(R⁺v(K))`.

This replaces the Cartan–Eilenberg resolution filtered by the second degree of the blueprint by
the stupid filtration of `K`, which gives the same exact couple (see the module docstring).

(blueprint: `thm-sp-if-e1`) -/
noncomputable def stupidFiltrationExactCouple (K : CochainComplex A ℤ) :
    ExactCouple B ((-1, 0) : ℤ × ℤ) (1, 1) 0 :=
  (v.stupidFiltrationTower K).exactCoupleNeg (DerivedCategory.Plus.homologyFunctor B 0)

/-- **The spectral sequence `E₁^{r, s} = R^r v(K^s) ⟹ H^{r + s}(R⁺v(K))`**, starting on page
`1`: the spectral sequence of `CategoryTheory.Functor.stupidFiltrationExactCouple`. Its entry
of index `(s, n)` (filtration degree `s`, total degree `n`) on page `1` is
`R^{n - s} v(K^s)` (`CategoryTheory.Functor.stupidFiltrationE₁Iso`).

(blueprint: `thm-sp-if-e1`) -/
noncomputable def stupidFiltrationSpectralSequence (K : CochainComplex A ℤ) :
    SpectralSequence B (ExactCouple.pageShape ((-1, 0) : ℤ × ℤ) (1, 1) 0 1) 1 :=
  (v.stupidFiltrationExactCouple K).spectralSequence 1

lemma stupidFiltrationSpectralSequence_page_one (K : CochainComplex A ℤ) :
    (v.stupidFiltrationSpectralSequence K).page 1 le_rfl =
      (v.stupidFiltrationExactCouple K).dComplex :=
  rfl

lemma stupidFiltrationExactCouple_D (K : CochainComplex A ℤ) (p n : ℤ) :
    (v.stupidFiltrationExactCouple K).D (p, n) =
      (DerivedCategory.Plus.homologyFunctor B n).obj (v.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Qh.obj (K.stupidFiltrationGEPlus (-(-p))))) :=
  rfl

lemma stupidFiltrationExactCouple_E (K : CochainComplex A ℤ) (p n : ℤ) :
    (v.stupidFiltrationExactCouple K).E (p, n) =
      (DerivedCategory.Plus.homologyFunctor B n).obj
        (v.rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Qh.obj
            ((HomotopyCategory.Plus.singleFunctor A (-(-p))).obj (K.X (-(-p)))))) :=
  rfl

/-- The single functors `X ↦ R⁺v(X[-t])` from `A` to `D⁺(B)`. -/
noncomputable abbrev rightDerivedSingleFunctors : SingleFunctors A (DerivedCategory.Plus B) ℤ :=
  ((HomotopyCategory.Plus.singleFunctors A).postcomp DerivedCategory.Plus.Qh).postcomp
    v.rightDerivedFunctorPlus

/-- The isomorphism `Hʳ(R⁺v(X[0])) ≅ R^r v(X)`, natural in `X`. -/
noncomputable def rightDerivedSingleFunctorsZeroIso (r : ℕ) :
    v.rightDerivedSingleFunctors.functor 0 ⋙
        (DerivedCategory.Plus.homologyFunctor B 0).shift (r : ℤ) ≅
      v.rightDerived r :=
  Functor.associator (HomotopyCategory.Plus.singleFunctor A 0 ⋙ DerivedCategory.Plus.Qh)
      v.rightDerivedFunctorPlus (DerivedCategory.Plus.homologyFunctor B r) ≪≫
    Functor.isoWhiskerRight (plusSingleFunctorCompQhIso A 0) _ ≪≫
    v.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso r

/-- The isomorphism `Hⁿ(R⁺v(X[-t])) ≅ R^r v(X)` for `n - t = r`, natural in `X`. -/
noncomputable def homologyRightDerivedSingleIso (t n : ℤ) (r : ℕ) (h : n - t = r) :
    v.rightDerivedSingleFunctors.functor t ⋙ (DerivedCategory.Plus.homologyFunctor B 0).shift n ≅
      v.rightDerived r :=
  v.rightDerivedSingleFunctors.shiftSequenceIso _ t 0 (-t) n r (by omega) (by omega) ≪≫
    v.rightDerivedSingleFunctorsZeroIso r

/-- The isomorphisms `Hⁿ(R⁺v(X[-t])) ≅ R^r v(X)` are compatible with the isomorphisms
`Hⁿ(R⁺v(X[-t])) ≅ Hⁿ⁺¹(R⁺v(X[-t-1]))`. -/
lemma homologyRightDerivedSingleIso_symm_trans (t t' n n' : ℤ) (r : ℕ) (h : n - t = r)
    (h' : n' - t' = r) (ht : 1 + t = t') (hn : 1 + n = n') :
    (v.homologyRightDerivedSingleIso t n r h).symm ≪≫
        v.rightDerivedSingleFunctors.shiftSequenceIso _ t t' 1 n n' ht hn ≪≫
          v.homologyRightDerivedSingleIso t' n' r h' = Iso.refl _ := by
  ext X
  have e := congrArg (fun e ↦ e.hom.app X) (SingleFunctors.shiftSequenceIso_trans
    v.rightDerivedSingleFunctors (DerivedCategory.Plus.homologyFunctor B 0) t t' 0 1 (-t') (-t)
    n n' r ht (by omega) hn (by omega) (by omega))
  simp only [Iso.trans_hom, NatTrans.comp_app] at e
  simp only [homologyRightDerivedSingleIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app, Category.assoc]
  rw [reassoc_of% e, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]

/-- **The `E₁`-term of the spectral sequence of the stupid filtration**:
`E₁^{s, n} ≅ R^r v(K^s)` for `r = n - s`.

(blueprint: `thm-sp-if-e1`) -/
noncomputable def stupidFiltrationE₁Iso (K : CochainComplex A ℤ) (s n : ℤ) (r : ℕ)
    (h : n - s = r) :
    (v.stupidFiltrationExactCouple K).E (s, n) ≅ (v.rightDerived r).obj (K.X s) :=
  (v.homologyRightDerivedSingleIso (-(-s)) n r (by omega)).app (K.X (-(-s))) ≪≫
    (v.rightDerived r).mapIso (K.XIsoOfEq (neg_neg s))

/-- The `E₁`-term `E₁^{s, n}` of the spectral sequence of the stupid filtration vanishes for
`n < s`.

(blueprint: `thm-sp-if-e1`) -/
lemma isZero_stupidFiltrationExactCouple_E (K : CochainComplex A ℤ) (s n : ℤ) (h : n < s) :
    IsZero ((v.stupidFiltrationExactCouple K).E (s, n)) :=
  isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE v
    (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor A (-(-s))).obj
      (K.X (-(-s))))) (-(-s)) (q := n) (by omega)

/-- In the tower `R⁺v(σ_{≥ -q} K)`, the composite `R⁺v(K^{-q}[q]) ⟶ R⁺v(σ_{≥ -q + 1} K)[1] ⟶
R⁺v(K^{-q + 1}[q - 1])[1]` is induced by the differential of `K`. -/
lemma stupidFiltrationTower_mor₃_comp_mor₂ (K : CochainComplex A ℤ) (q q' : ℤ)
    (hq : q' = q - 1) :
    (v.stupidFiltrationTower K).mor₃ q ≫ (eqToHom (congrArg (v.stupidFiltrationTower K).X
        hq.symm) ≫ (v.stupidFiltrationTower K).mor₂ q')⟦(1 : ℤ)⟧' =
      (v.rightDerivedSingleFunctors.functor (-q)).map (K.d (-q) (-q')) ≫
        (v.rightDerivedSingleFunctors.shiftIso 1 (-q) (-q') (by omega)).inv.app (K.X (-q')) := by
  subst hq
  rw [eqToHom_refl, Category.id_comp]
  dsimp only [stupidFiltrationTower]
  rw [TriangleTower.map_mor₂, TriangleTower.map_mor₂, TriangleTower.map_mor₃_comp_shift_map,
    TriangleTower.map_mor₃_comp_shift_map, CochainComplex.stupidTower_mor₃_comp_mor₂]
  simp only [Functor.map_comp, Category.assoc, SingleFunctors.postcomp_shiftIso_inv_app]
  rfl

lemma stupidFiltrationExactCouple_d_eq (K : CochainComplex A ℤ) (s n : ℤ) :
    (v.stupidFiltrationExactCouple K).d (s, n) (s + 1, n + 1) =
      ((DerivedCategory.Plus.homologyFunctor B 0).shift n).map
          ((v.rightDerivedSingleFunctors.functor (-(-s))).map (K.d (-(-s)) (-(-(s + 1))))) ≫
        (v.rightDerivedSingleFunctors.shiftSequenceIso (DerivedCategory.Plus.homologyFunctor B 0)
          (-(-s)) (-(-(s + 1))) 1 n (n + 1) (by omega) (by omega)).hom.app
            (K.X (-(-(s + 1)))) := by
  rw [ExactCouple.d_eq _ _ (s + 1, n + 1) _ (by ext <;> simp)]
  simp only [stupidFiltrationExactCouple, TriangleTower.exactCoupleNeg_f,
    TriangleTower.exactCoupleNeg_g, TriangleTower.negFstEquiv_symm_apply]
  rw [TriangleTower.couplef_comp_coupleg _ _ (-s) (-(s + 1)) n (n + 1) (by omega) rfl,
    stupidFiltrationTower_mor₃_comp_mor₂ v K (-s) (-(s + 1)) (by omega), Functor.shiftMap_comp',
    SingleFunctors.shiftSequenceIso_hom_app]
  rfl

/-- **The differential `d₁` of the spectral sequence of the stupid filtration.** Under the
isomorphisms `E₁^{s, n} ≅ R^r v(K^s)` and `E₁^{s + 1, n + 1} ≅ R^r v(K^{s + 1})` (with
`r = n - s`), the differential `d₁ : E₁^{s, n} ⟶ E₁^{s + 1, n + 1}` of the first page is
`R^r v(d_K)`, with sign `+1`.

(blueprint: `thm-sp-if-e1`) -/
theorem stupidFiltrationE₁Iso_inv_comp_d_comp_hom (K : CochainComplex A ℤ) (s n : ℤ) (r : ℕ)
    (h : n - s = r) :
    (v.stupidFiltrationE₁Iso K s n r h).inv ≫
        (v.stupidFiltrationExactCouple K).d (s, n) (s + 1, n + 1) ≫
          (v.stupidFiltrationE₁Iso K (s + 1) (n + 1) r (by omega)).hom =
      (v.rightDerived r).map (K.d s (s + 1)) := by
  have e := congrArg (fun e ↦ e.hom.app (K.X (-(-(s + 1)))))
    (v.homologyRightDerivedSingleIso_symm_trans (-(-s)) (-(-(s + 1))) n (n + 1) r (by omega)
      (by omega) (by omega) (by omega))
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app] at e
  rw [stupidFiltrationExactCouple_d_eq]
  simp only [stupidFiltrationE₁Iso, Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc]
  erw [← (v.homologyRightDerivedSingleIso (-(-s)) n r (by omega)).inv.naturality_assoc,
    reassoc_of% e]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simp [HomologicalComplex.XIsoOfEq_inv_comp_d, HomologicalComplex.d_comp_XIsoOfEq_hom]

/-- The maps `Hⁿ(R⁺v(σ_{≥ p} K)) ⟶ Hⁿ(R⁺v(K))` to the abutment, induced by the inclusions
`σ_{≥ p} K ⟶ K`. -/
noncomputable def stupidFiltrationAbutmentι (K : CochainComplex.Plus A) (p n : ℤ) :
    (v.stupidFiltrationExactCouple K.obj).D (p, n) ⟶
      (DerivedCategory.Plus.homologyFunctor B n).obj
        (v.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) :=
  ((DerivedCategory.Plus.homologyFunctor B 0).shift n).map (v.rightDerivedFunctorPlus.map
    (DerivedCategory.Plus.Qh.map (CochainComplex.stupidFiltrationGEPlusι K (-(-p))) ≫
      (DerivedCategory.Plus.quotientCompQhIso A).hom.app K))

lemma stupidFiltrationAbutmentι_comp (K : CochainComplex.Plus A) (p n : ℤ) :
    (v.stupidFiltrationExactCouple K.obj).α (p + 1, n) (p, n) ≫
      v.stupidFiltrationAbutmentι K p n = v.stupidFiltrationAbutmentι K (p + 1) n := by
  have h := (v.stupidFiltrationTower K.obj).eqToHom_X_comp
    (fun q ↦ v.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Qh.map (CochainComplex.stupidFiltrationGEPlusι K (-q))))
    (-(p + 1)) (-p - 1) (by omega)
  simp only [stupidFiltrationExactCouple, TriangleTower.exactCoupleNeg_α,
    TriangleTower.negFstEquiv_symm_apply, stupidFiltrationAbutmentι]
  rw [TriangleTower.coupleα_eq _ _ (-(p + 1)) (-p) n (by omega), ← Functor.map_comp,
    Category.assoc]
  congr 1
  simp only [stupidFiltrationTower, TriangleTower.map_mor₁, ← Functor.map_comp]
  have h' := h =≫ v.rightDerivedFunctorPlus.map
    ((DerivedCategory.Plus.quotientCompQhIso A).hom.app K)
  simp only [Category.assoc, ← Functor.map_comp] at h'
  rw [← Functor.map_comp_assoc, CochainComplex.stupidTower_mor₁_comp_stupidFiltrationGEPlusι]
  exact h'

/-- The filtration of the abutment `Hⁿ(R⁺v(K))` by the images of the maps
`Hⁿ(R⁺v(σ_{≥ p} K)) ⟶ Hⁿ(R⁺v(K))`. -/
noncomputable def stupidFiltrationAbutmentFiltration (K : CochainComplex.Plus A) (n : ℤ) :
    DecreasingFiltration ((DerivedCategory.Plus.homologyFunctor B n).obj
        (v.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K))) :=
  (v.stupidFiltrationExactCouple K.obj).abutmentFiltration (v.stupidFiltrationAbutmentι K)
    (v.stupidFiltrationAbutmentι_comp K) n

/-- **Convergence of the spectral sequence `E₁^{r, s} = R^r v(K^s) ⟹ H^{r + s}(R⁺v(K))`.**
For a bounded below complex `K`, the spectral sequence of the stupid filtration converges to the
cohomology `Hⁿ(R⁺v(K))` of the right derived functor of `K` (which does not depend on any
choices), filtered by the images of the maps `Hⁿ(R⁺v(σ_{≥ p} K)) ⟶ Hⁿ(R⁺v(K))`.

(blueprint: `thm-sp-if-e1`) -/
theorem stupidFiltrationExactCouple_convergesTo (K : CochainComplex.Plus A) :
    (v.stupidFiltrationExactCouple K.obj).ConvergesTo (v.stupidFiltrationAbutmentι K)
      (v.stupidFiltrationAbutmentFiltration K) := by
  obtain ⟨a, ha⟩ := K.2
  refine (v.stupidFiltrationExactCouple K.obj).convergesTo_abutmentFiltration _
    (v.stupidFiltrationAbutmentι_comp K)
    (fun n ↦ ⟨a, fun p hp ↦ ?_⟩) (fun n ↦ ⟨n + 1, fun p hp ↦ ?_⟩)
  · have : K.obj.IsStrictlyGE (-(-p)) := K.obj.isStrictlyGE_of_ge (-(-p)) a (by omega)
    dsimp only [stupidFiltrationAbutmentι]
    infer_instance
  · exact isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE v
      (DerivedCategory.Plus.Qh.obj (K.obj.stupidFiltrationGEPlus (-(-p)))) (-(-p)) (q := n)
      (by omega)

end CategoryTheory.Functor
