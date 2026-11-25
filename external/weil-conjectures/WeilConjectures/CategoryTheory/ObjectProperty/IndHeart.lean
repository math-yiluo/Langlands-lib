/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
public import Mathlib.CategoryTheory.Comma.Final
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Ind-objects of a Serre-type subcategory

Let `C` be a Grothendieck abelian category and `P` a class of objects of `C` (the constructible
sheaves) containing zero and closed under kernels, cokernels and extensions, such that for `M`
in `P`, every morphism `M[0] ⟶ B[n]` in `D(C)` to a filtered colimit `B = colim Bᵢ` factors
through some `Bᵢ[n]` (`DerivedCategory.HomFactorsThroughFilteredColimits`). We show (blueprint
`proposition-ind-constructible-sheaves` (2)) that the ind-objects `ind P` are closed under kernels,
cokernels, extensions and direct sums
(`CategoryTheory.ObjectProperty.isClosedUnder_ind_of_homFactorsThroughFilteredColimits`):

* `proposition-ind-constructible-sheaves`: the objects of `P` are finitely presentable
  (`DerivedCategory.HomFactorsThroughFilteredColimits.isFinitelyPresentable`); injectivity of
  `colim Hom(M, Bᵢ) ⟶ Hom(M, colim Bᵢ)` comes from surjectivity applied to the kernels of
  `M ⟶ Bⱼ`;
* `proposition-ind-constructible-sheaves`: any presentation of an object of `ind P` is final in
  the category of morphisms from objects of `P`
  (`CategoryTheory.ObjectProperty.ColimitOfShape.final_toCostructuredArrow`), so that a morphism
  between objects of `ind P` is a filtered colimit of morphisms between objects of `P`
  (`CategoryTheory.ObjectProperty.exists_colimitOfShape_hom`);
* `proposition-ind-constructible-sheaves`: filtered colimits being exact, kernels and cokernels are
  computed termwise (`CategoryTheory.ObjectProperty.ind_isClosedUnderKernels`,
  `CategoryTheory.ObjectProperty.ind_isClosedUnderCokernels`);
* `proposition-ind-constructible-sheaves--3`: `ind P` is closed under binary biproducts and, using
  `ind (ind P) = ind P`, under direct sums
  (`CategoryTheory.ObjectProperty.ind_isClosedUnderColimitsOfShape_discrete`);
* `proposition-ind-constructible-sheaves--7`: an extension of `B = colim Cₖ` by `N` is the filtered
colimit of
  its pullbacks to the `Cₖ`; an extension of `C` in `P` by `N = colim Dᵢ` is, by the case
  `n = -1` of the factorization property applied to its class `C[0] ⟶ N[0][1]`, a pushout of an
  extension of `C` by some `Dᵢ` (`CategoryTheory.ObjectProperty.ind_isClosedUnderExtensions`).
-/

@[expose] public section

universe w v u

open CategoryTheory Category Limits


namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

namespace HomFactorsThroughFilteredColimits

attribute [local instance] IsFiltered.isConnected

variable {X : C}
  (hX : DerivedCategory.HomFactorsThroughFilteredColimits.{w} ((singleFunctor C 0).obj X))
include hX

/-- The case `n = 0` of `HomFactorsThroughFilteredColimits`, in `C`: a morphism from `X` to a
filtered colimit factors through some term of the diagram. -/
lemma exists_hom {I : Type w} [SmallCategory I] [IsFiltered I] {F : I ⥤ C} {c : Cocone F}
    (hc : IsColimit c) (f : X ⟶ c.pt) : ∃ (i : I) (g : X ⟶ F.obj i), g ≫ c.ι.app i = f := by
  obtain ⟨i, g, hg⟩ := hX I F c hc 0 ((singleFunctor C 0).map f)
  refine ⟨i, (singleFunctor C 0).preimage g, (singleFunctor C 0).map_injective ?_⟩
  simp [hg]

/-- Blueprint `proposition-ind-constructible-sheaves`: if morphisms out of `X[0]` factor through
filtered colimits, then `X` is finitely presentable. Injectivity of
`colim Hom(X, Bᵢ) ⟶ Hom(X, colim Bᵢ)` follows from surjectivity applied to the filtered diagram
of the kernels of `X ⟶ Bⱼ`, whose colimit is `X` by exactness of filtered colimits. -/
lemma isFinitelyPresentable [IsGrothendieckAbelian.{w} C] : IsFinitelyPresentable.{w} X := by
  rw [isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  refine ⟨fun I _ _ ↦ ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨Types.FilteredColimit.isColimitOf' _ _
    (fun f ↦ ?_) (fun i x y hxy ↦ ?_)⟩⟩⟩⟩
  · obtain ⟨i, g, hg⟩ := exists_hom hX hc f
    exact ⟨i, g, hg.symm⟩
  · open IsGrothendieckAbelian.IsPresentable.injectivity₀ in
    let x' : X ⟶ F.obj i := x
    let y' : X ⟶ F.obj i := y
    let z : X ⟶ F.obj i := x' - y'
    have hz : z ≫ c.ι.app i = 0 := by
      simpa [z, sub_eq_zero] using hxy
    have := epi_f hc hz
    have : Mono (f z) := colim.map_mono' (kernel.ι (g z)) (colimit.isColimit _)
      (isColimitConstCocone _ _) _ (fun j ↦ (hf z j).trans (comp_id _).symm)
    have := isIso_of_mono_of_epi (f z)
    obtain ⟨j, a, ha⟩ : ∃ (j : Under i) (a : X ⟶ (kernel (g z)).obj j),
        a ≫ colimit.ι (kernel (g z)) j = inv (f z) :=
      exists_hom hX (colimit.isColimit (kernel (g z))) (inv (f z))
    refine ⟨j.right, j.hom, ?_⟩
    have h₁ : a ≫ (kernel.ι (g z)).app j = 𝟙 X := by
      rw [← hf, ← assoc, ha, IsIso.inv_hom_id]
    have h₂ := NatTrans.congr_app (kernel.condition (g z)) j
    simp only [NatTrans.comp_app, NatTrans.app_zero, g_app] at h₂
    have h₃ : z ≫ F.map j.hom = 0 := by
      rw [← id_comp (z ≫ _), ← h₁, assoc]
      exact (congrArg (a ≫ ·) h₂).trans comp_zero
    simpa [z, x', y', sub_eq_zero] using h₃

end HomFactorsThroughFilteredColimits


open Pretriangulated in
/-- A distinguished triangle `X[0] ⟶ Y[0] ⟶ Z[0] ⟶ X[0][1]` in `D(C)` whose first two
morphisms come from morphisms in `C` gives a short exact sequence `0 ⟶ X ⟶ Y ⟶ Z ⟶ 0`. -/
lemma shortExact_of_distTriang_singleFunctor {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (δ : (singleFunctor C 0).obj Z ⟶ ((singleFunctor C 0).obj X)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((singleFunctor C 0).map f) ((singleFunctor C 0).map g) δ ∈ distTriang _) :
    (ShortComplex.mk f g ((singleFunctor C 0).map_injective (by
      rw [Functor.map_comp, Functor.map_zero]
      exact comp_distTriang_mor_zero₁₂ _ hT))).ShortExact := by
  let e := singleFunctorCompHomologyFunctorIso C 0
  refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk (e.app X) (e.app Y) (e.app Z)
    (e.hom.naturality f).symm (e.hom.naturality g).symm) (ShortComplex.ShortExact.mk'
      (HomologySequence.exact₂ _ hT 0) ?_ ?_)
  · exact (HomologySequence.mono_homologyMap_mor₁_iff _ hT (-1) 0).2
      ((isZero_of_isGE ((singleFunctor C 0).obj Z) 0 (-1) (by lia)).eq_of_src _ _)
  · exact (HomologySequence.epi_homologyMap_mor₂_iff _ hT 0 1).2
      ((isZero_of_isLE ((singleFunctor C 0).obj X) 0 1 (by lia)).eq_of_tgt _ _)


open Pretriangulated in
/-- Blueprint `proposition-ind-constructible-sheaves--7`: if morphisms out of `X₃[0]` factor through
filtered colimits, an extension `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `X₁ = colim Dᵢ` filtered receives a
morphism from an extension `0 ⟶ Dᵢ ⟶ E ⟶ X₃ ⟶ 0`, for some `i`: the extension class
`X₃[0] ⟶ X₁[0][1]` factors through `Dᵢ[0][1]`, and its cone is an extension of `X₃` by `Dᵢ`. -/
lemma HomFactorsThroughFilteredColimits.exists_shortExact {S : ShortComplex C}
    (hS : S.ShortExact)
    (hX : DerivedCategory.HomFactorsThroughFilteredColimits.{w} ((singleFunctor C 0).obj S.X₃))
    {I : Type w} [SmallCategory I] [IsFiltered I] (p : ColimitPresentation I S.X₁) :
    ∃ (i : I) (E : C) (j : p.diag.obj i ⟶ E) (q : E ⟶ S.X₃) (w : j ≫ q = 0) (h : E ⟶ S.X₂),
      (ShortComplex.mk j q w).ShortExact ∧ j ≫ h = p.ι.app i ≫ S.f ∧ h ≫ S.g = q := by
  let e := (singleFunctors C).shiftIso 1 (-1) 0 (by norm_num)
  obtain ⟨i, g, hg⟩ := hX I p.diag p.cocone p.isColimit (-1) (hS.singleδ ≫ e.hom.app S.X₁)
  let g' : (singleFunctor C 0).obj S.X₃ ⟶ ((singleFunctor C 0).obj (p.diag.obj i))⟦(1 : ℤ)⟧ :=
    g ≫ e.inv.app (p.diag.obj i)
  have hδ : hS.singleδ = g' ≫ ((singleFunctor C 0).map (p.ι.app i))⟦(1 : ℤ)⟧' := by
    rw [← cancel_mono (e.hom.app S.X₁), hg]
    have := e.hom.naturality (p.ι.app i)
    dsimp at this
    simp [g', this]
  obtain ⟨Z, u, v, hT⟩ := distinguished_cocone_triangle₂ g'
  obtain ⟨b, hb₁, hb₂⟩ : ∃ b : Z ⟶ (singleFunctor C 0).obj S.X₂,
      u ≫ b = (singleFunctor C 0).map (p.ι.app i) ≫ (singleFunctor C 0).map S.f ∧
      v = b ≫ (singleFunctor C 0).map S.g := by
    obtain ⟨b, hb₁, hb₂⟩ := complete_distinguished_triangle_morphism₂ _ _ hT
      hS.singleTriangle_distinguished ((singleFunctor C 0).map (p.ι.app i)) (𝟙 _)
      (hδ.symm.trans (id_comp _).symm)
    exact ⟨b, hb₁, (comp_id _).symm.trans hb₂⟩
  have : Z.IsLE 0 := TStructure.t.isLE₂ _ hT 0
    (inferInstanceAs (((singleFunctor C 0).obj _).IsLE 0))
    (inferInstanceAs (((singleFunctor C 0).obj _).IsLE 0))
  have : Z.IsGE 0 := TStructure.t.isGE₂ _ hT 0
    (inferInstanceAs (((singleFunctor C 0).obj _).IsGE 0))
    (inferInstanceAs (((singleFunctor C 0).obj _).IsGE 0))
  obtain ⟨E, ⟨eZ⟩⟩ := Z.exists_iso_singleFunctor_obj_of_isGE_of_isLE 0
  refine ⟨i, E, (singleFunctor C 0).preimage (u ≫ eZ.hom),
    (singleFunctor C 0).preimage (eZ.inv ≫ v), (singleFunctor C 0).map_injective ?_,
    (singleFunctor C 0).preimage (eZ.inv ≫ b), shortExact_of_distTriang_singleFunctor _ _ g' ?_,
    (singleFunctor C 0).map_injective ?_, (singleFunctor C 0).map_injective ?_⟩
  · simp only [Functor.map_comp, Functor.map_preimage, Functor.map_zero, assoc,
      Iso.hom_inv_id_assoc]
    exact comp_distTriang_mor_zero₁₂ _ hT
  · rw [Functor.map_preimage, Functor.map_preimage]
    exact isomorphic_distinguished _ hT _
      (Triangle.isoMk _ _ (Iso.refl _) eZ.symm (Iso.refl _)
        (by exact (by simp : (u ≫ eZ.hom) ≫ eZ.inv = 𝟙 _ ≫ u))
        (by exact (by simp : (eZ.inv ≫ v) ≫ 𝟙 _ = eZ.inv ≫ v))
        (by exact (by simp : g' ≫ (𝟙 ((singleFunctor C 0).obj (p.diag.obj i)))⟦(1 : ℤ)⟧' =
          𝟙 _ ≫ g')))
  · simpa using hb₁
  · simpa using hb₂.symm

end DerivedCategory


namespace CategoryTheory.Limits.ColimitPresentation

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

/-- The pointwise biproduct of two colimit presentations indexed by the same category is a
colimit presentation of the biproduct. -/
@[simps]
noncomputable def biprod {K : Type*} [Category* K] {X Y : C} (pX : ColimitPresentation K X)
    (pY : ColimitPresentation K Y) : ColimitPresentation K (X ⊞ Y) where
  diag :=
    { obj k := pX.diag.obj k ⊞ pY.diag.obj k
      map t := biprod.map (pX.diag.map t) (pY.diag.map t) }
  ι := { app k := biprod.map (pX.ι.app k) (pY.ι.app k) }
  isColimit :=
    { desc s := biprod.desc
        (pX.isColimit.desc (Cocone.mk s.pt
          { app k := biprod.inl ≫ s.ι.app k
            naturality k k' t := by simp [← s.w t] }))
        (pY.isColimit.desc (Cocone.mk s.pt
          { app k := biprod.inr ≫ s.ι.app k
            naturality k k' t := by simp [← s.w t] }))
      fac s k := by
        ext
        · simpa using pX.isColimit.fac _ k
        · simpa using pY.isColimit.fac _ k
      uniq s m hm := by
        ext
        · refine pX.isColimit.hom_ext fun k ↦ ?_
          rw [biprod.inl_desc, pX.isColimit.fac]
          simpa using biprod.inl ≫= hm k
        · refine pY.isColimit.hom_ext fun k ↦ ?_
          rw [biprod.inr_desc, pY.isColimit.fac]
          simpa using biprod.inr ≫= hm k }

end CategoryTheory.Limits.ColimitPresentation


namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Given a morphism from a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ S₃ ⟶ 0` to a short exact
sequence `0 ⟶ S₁ ⟶ S₂ ⟶ S₃ ⟶ 0` which is the identity on `S₃`, the object `S₂` is the cokernel
of `X₁ ⟶ S₁ ⊞ X₂` (i.e. `S` is the pushout of the first sequence along `X₁ ⟶ S₁`). -/
noncomputable def ShortExact.isColimitCokernelCoforkBiprodDesc {S : ShortComplex C}
    (hS : S.ShortExact) {X₁ X₂ : C} {j : X₁ ⟶ X₂} {q : X₂ ⟶ S.X₃} {w : j ≫ q = 0}
    (hT : (ShortComplex.mk j q w).ShortExact) (a : X₁ ⟶ S.X₁) (h : X₂ ⟶ S.X₂)
    (w₁ : j ≫ h = a ≫ S.f) (w₂ : h ≫ S.g = q) :
    IsColimit (CokernelCofork.ofπ (f := biprod.lift (-a) j) (biprod.desc S.f h)
      (by simp [w₁])) := by
  have := hS.mono_f
  have : Epi q := hT.epi_g
  let U := ShortComplex.mk (biprod.lift (-a) j) (biprod.desc S.f h) (by simp [w₁])
  have hU : U.Exact := by
    rw [exact_iff_exact_up_to_refinements]
    intro A x hx
    have hx' : (x ≫ biprod.snd) ≫ h = -((x ≫ biprod.fst) ≫ S.f) := by
      refine eq_neg_of_add_eq_zero_right ?_
      simpa [U, biprod.desc_eq] using hx
    have hq : (x ≫ biprod.snd) ≫ q = 0 := by
      rw [← w₂, ← assoc, hx']
      simp
    obtain ⟨A', π, hπ, d, hd⟩ := hT.exact.exact_up_to_refinements (x ≫ biprod.snd) hq
    refine ⟨A', π, hπ, d, biprod.hom_ext _ _ ?_ (by simpa [U] using hd)⟩
    rw [← cancel_mono S.f]
    simp only [assoc] at hx' hd
    simp only [U, assoc, biprod.lift_fst_assoc, Preadditive.neg_comp, ← w₁, ← reassoc_of% hd, hx',
      Preadditive.comp_neg, neg_neg]
  have : Epi U.g := by
    rw [epi_iff_surjective_up_to_refinements]
    intro A y
    obtain ⟨A₁, π₁, hπ₁, e, he⟩ := surjective_up_to_refinements_of_epi q (y ≫ S.g)
    obtain ⟨A₂, π₂, hπ₂, n, hn⟩ := hS.exact.exact_up_to_refinements (π₁ ≫ y - e ≫ h) (by
      simp [he, w₂])
    refine ⟨A₂, π₂ ≫ π₁, epi_comp _ _, biprod.lift n (π₂ ≫ e), ?_⟩
    rw [assoc, ← sub_add_cancel (π₂ ≫ π₁ ≫ y) (π₂ ≫ e ≫ h), ← Preadditive.comp_sub, hn]
    simp [U]
  exact hU.gIsCokernel

end CategoryTheory.ShortComplex

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

attribute [local instance] Cardinal.fact_isRegular_aleph0 in
/-- If the objects of `P` are finitely presentable, a presentation of `X` as a filtered colimit
of objects of `P` is final in the category of all morphisms from objects of `P` to `X`. -/
lemma ColimitOfShape.final_toCostructuredArrow (hP : P ≤ isFinitelyPresentable.{w} C)
    {J : Type w} [SmallCategory J] [IsFiltered J] {X : C} (p : P.ColimitOfShape J X) :
    p.toCostructuredArrow.Final := by
  have : IsCardinalFiltered J Cardinal.aleph0.{w} := by
    rwa [isCardinalFiltered_aleph0_iff]
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun g ↦ ?_, fun {g j} g₁ g₂ ↦ ?_⟩
  · have : IsFinitelyPresentable.{w} (P.ι.obj g.left) := hP _ g.left.property
    obtain ⟨j, a, ha⟩ := IsFinitelyPresentable.exists_hom_of_isColimit p.isColimit g.hom
    exact ⟨j, ⟨CostructuredArrow.homMk (ObjectProperty.homMk a) ha⟩⟩
  · have : IsFinitelyPresentable.{w} g.left.obj := hP _ g.left.property
    obtain ⟨k, a, h⟩ := IsCardinalPresentable.exists_eq_of_isColimit' Cardinal.aleph0.{w}
      p.isColimit g₁.left.hom g₂.left.hom
      ((CostructuredArrow.w g₁).trans (CostructuredArrow.w g₂).symm)
    exact ⟨k, a, by cat_disch⟩

/-- Blueprint `proposition-ind-constructible-sheaves` (the category `P_f`): if the objects of `P`
are finitely presentable, a morphism `f : X ⟶ Y` between filtered colimits of objects of `P` is a
filtered colimit of morphisms between objects of `P`, indexed by the category of squares from
morphisms of the given presentations to `f`. -/
lemma exists_colimitOfShape_hom (hP : P ≤ isFinitelyPresentable.{w} C) [LocallySmall.{w} C]
    {X Y : C} (f : X ⟶ Y) (hX : ind.{w} P X) (hY : ind.{w} P Y) :
    ∃ (K : Type w) (_ : SmallCategory K) (_ : IsFiltered K) (pX : P.ColimitOfShape K X)
      (pY : P.ColimitOfShape K Y) (α : pX.diag ⟶ pY.diag),
      ∀ k, α.app k ≫ pY.ι.app k = pX.ι.app k ≫ f := by
  obtain ⟨I, _, _, pX, hpX⟩ := hX
  obtain ⟨J, _, _, pY, hpY⟩ := hY
  let qX : P.ColimitOfShape I X := ⟨pX, hpX⟩
  let qY : P.ColimitOfShape J Y := ⟨pY, hpY⟩
  have := qY.final_toCostructuredArrow hP
  let L := qX.toCostructuredArrow ⋙ CostructuredArrow.map f
  let K := Comma L qY.toCostructuredArrow
  have : Small.{w} K := small_of_injective
    (f := fun k : K ↦ (⟨k.left, k.right, k.hom⟩ : Σ i j, L.obj i ⟶ qY.toCostructuredArrow.obj j))
    (by
      rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h
      cases h
      rfl)
  have := essentiallySmall_of_small_of_locallySmall.{w} K
  let e := equivSmallModel.{w} K
  have : IsFiltered (SmallModel.{w} K) := IsFiltered.of_equivalence e
  refine ⟨SmallModel.{w} K, inferInstance, inferInstance,
    (qX.reindex (Comma.fst _ _)).reindex e.inverse,
    (qY.reindex (Comma.snd _ _)).reindex e.inverse,
    e.inverse.whiskerLeft
      { app k := k.hom.left.hom
        naturality k k' φ := congr_arg (fun ψ ↦ ψ.left.hom) φ.w }, fun k ↦ ?_⟩
  exact CostructuredArrow.w (e.inverse.obj k).hom

section Abelian

variable [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- Blueprint `proposition-ind-constructible-sheaves`: if the objects of `P` are finitely
presentable and `P` is closed under kernels, then so is `ind P`, filtered colimits being exact. -/
lemma ind_isClosedUnderKernels (hP : P ≤ isFinitelyPresentable.{w} C)
    [P.IsClosedUnderKernels] : (ind.{w} P).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, ⟨hX, hY⟩⟩
    obtain ⟨K, _, _, pX, pY, α, hα⟩ := exists_colimitOfShape_hom hP f hX hY
    let φ : colimit (kernel α) ⟶ _ := IsColimit.map (colimit.isColimit _) pX.cocone (kernel.ι α)
    have hφ (j : K) : colimit.ι (kernel α) j ≫ φ = (kernel.ι α).app j ≫ pX.ι.app j :=
      IsColimit.ι_map _ _ _ _
    let T := colim.mapShortComplex (ShortComplex.mk _ _ (kernel.condition α))
      (colimit.isColimit _) pX.cocone pY.cocone φ f hφ (fun j ↦ (hα j).symm)
    have hS : T.Exact := colim.exact_mapShortComplex
      ((ShortComplex.mk _ _ (kernel.condition α)).exact_of_f_is_kernel (kernelIsKernel α))
      (colimit.isColimit _) pX.isColimit pY.isColimit φ f hφ (fun j ↦ (hα j).symm)
    have : Mono T.f := colim.map_mono' (kernel.ι α) (colimit.isColimit _) pX.isColimit φ hφ
    refine (ind.{w} P).prop_of_iso
      (IsLimit.conePointUniqueUpToIso hS.fIsKernel hk) ⟨K, inferInstance, inferInstance,
        ColimitPresentation.colimit (kernel α), fun j ↦ ?_⟩
    exact P.prop_of_isLimit_kernelFork
      (KernelFork.mapIsLimit _ (kernelIsKernel α) ((evaluation K C).obj j))
      (pX.prop_diag_obj j) (pY.prop_diag_obj j)

/-- Blueprint `proposition-ind-constructible-sheaves`: if the objects of `P` are finitely
presentable and `P` is closed under cokernels, then so is `ind P`. -/
lemma ind_isClosedUnderCokernels (hP : P ≤ isFinitelyPresentable.{w} C)
    [P.IsClosedUnderCokernels] : (ind.{w} P).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, ⟨hX, hY⟩⟩
    obtain ⟨K, _, _, pX, pY, α, hα⟩ := exists_colimitOfShape_hom hP f hX hY
    let φ : _ ⟶ colimit (cokernel α) :=
      IsColimit.map pY.isColimit (colimit.cocone _) (cokernel.π α)
    have hφ (j : K) : pY.ι.app j ≫ φ = (cokernel.π α).app j ≫ colimit.ι (cokernel α) j :=
      IsColimit.ι_map pY.isColimit (colimit.cocone _) (cokernel.π α) j
    let T := colim.mapShortComplex (ShortComplex.mk _ _ (cokernel.condition α))
      pX.isColimit pY.cocone (colimit.cocone _) f φ (fun j ↦ (hα j).symm) hφ
    have hS : T.Exact := colim.exact_mapShortComplex
      ((ShortComplex.mk _ _ (cokernel.condition α)).exact_of_g_is_cokernel
        (cokernelIsCokernel α))
      pX.isColimit pY.isColimit (colimit.isColimit _) f φ (fun j ↦ (hα j).symm) hφ
    have : Epi T.g := colim.map_epi' (cokernel.π α) pY.cocone (colimit.isColimit _) φ hφ
    refine (ind.{w} P).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso hS.gIsCokernel hk) ⟨K, inferInstance, inferInstance,
        ColimitPresentation.colimit (cokernel α), fun j ↦ ?_⟩
    exact P.prop_of_isColimit_cokernelCofork
      (CokernelCofork.mapIsColimit _ (cokernelIsCokernel α) ((evaluation K C).obj j))
      (pX.prop_diag_obj j) (pY.prop_diag_obj j)

/-- If the objects of `P` are finitely presentable and `P` is closed under extensions, then
`ind P` is closed under binary biproducts: two filtered colimits may be indexed by the same
category, and the pointwise biproduct of colimit cocones is a colimit cocone. -/
lemma ind_biprod (hP : P ≤ isFinitelyPresentable.{w} C) [P.IsClosedUnderExtensions]
    {X Y : C} (hX : ind.{w} P X) (hY : ind.{w} P Y) : ind.{w} P (X ⊞ Y) := by
  obtain ⟨K, _, _, pX, pY, -, -⟩ := exists_colimitOfShape_hom hP (0 : X ⟶ Y) hX hY
  exact ⟨K, inferInstance, inferInstance, pX.biprod pY.toColimitPresentation,
    fun k ↦ P.prop_biprod (pX.prop_diag_obj k) (pY.prop_diag_obj k)⟩

instance [P.ContainsZero] : (ind.{w} P).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ, hPZ⟩ := P.exists_prop_of_containsZero
    exact ⟨Z, hZ, le_ind _ _ hPZ⟩

/-- Blueprint `proposition-ind-constructible-sheaves--3`: if the objects of `P` are finitely
presentable and `P` contains zero and is closed under extensions, then `ind P` is closed under
direct sums: a direct sum is the filtered colimit of its finite subsums, which lie in `ind P` by
`ind_biprod`, and `ind (ind P) = ind P`. -/
lemma ind_isClosedUnderColimitsOfShape_discrete (hP : P ≤ isFinitelyPresentable.{w} C)
    [P.ContainsZero] [P.IsClosedUnderExtensions] (J : Type w) :
    (ind.{w} P).IsClosedUnderColimitsOfShape (Discrete J) := by
  classical
  have : (ind.{w} P).IsClosedUnderBinaryCoproducts := .mk' (by
    rintro _ ⟨F, hF⟩
    exact (ind.{w} P).prop_of_iso (biprod.isoCoprod _ _ ≪≫
      (HasColimit.isoOfNatIso (diagramIsoPair F)).symm)
      (ind_biprod hP (hF ⟨.left⟩) (hF ⟨.right⟩)))
  have : (ind.{w} P).IsClosedUnderFiniteCoproducts := .mk'
  refine ⟨fun X ⟨h⟩ ↦ ?_⟩
  rw [← ind_ind hP]
  exact (ind.{w} (ind.{w} P)).prop_of_iso
    (IsColimit.coconePointUniqueUpToIso
      (CoproductsFromFiniteFiltered.liftToFinsetColimitCocone h.diag).isColimit h.isColimit)
    ⟨Finset (Discrete J), inferInstance, inferInstance, ColimitPresentation.colimit _,
      fun S ↦ (ind.{w} P).prop_coproduct fun x ↦ h.prop_diag_obj _⟩

attribute [local instance] IsFiltered.isConnected in
/-- Blueprint `proposition-ind-constructible-sheaves--7` (pullback step): let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`
be short exact with `X₃ = colim Cₖ` in `ind P`. If the pullbacks `X₂ ×_{X₃} Y` along all morphisms
`Y ⟶ X₃` with `Y` in `P` lie in `ind P`, then so does `X₂`, which is the filtered colimit of the
pullbacks `X₂ ×_{X₃} Cₖ` by exactness of filtered colimits. -/
lemma ind_X₂_of_shortExact_of_pullback (hP : P ≤ isFinitelyPresentable.{w} C)
    {S : ShortComplex C} (hS : S.ShortExact) (hX₃ : ind.{w} P S.X₃)
    (h : ∀ ⦃Y : C⦄ (c : Y ⟶ S.X₃), P Y → ind.{w} P (pullback S.g c)) : ind.{w} P S.X₂ := by
  obtain ⟨I, _, _, p, hp⟩ := hX₃
  have := hS.epi_g
  let F : I ⥤ C :=
    { obj k := pullback S.g (p.ι.app k)
      map t := pullback.map _ _ _ _ (𝟙 _) (p.diag.map t) (𝟙 _) (by simp)
        (by rw [comp_id, p.w])
      map_id k := by
        ext <;> simp
      map_comp t t' := by
        ext
        · simp only [assoc, pullback.lift_fst, comp_id]
        · simp only [assoc, Functor.map_comp, pullback.lift_snd, pullback.lift_snd_assoc] }
  let T : ShortComplex (I ⥤ C) :=
    { X₁ := (Functor.const I).obj S.X₁
      X₂ := F
      X₃ := p.diag
      f :=
        { app k := pullback.lift (f := S.g) (g := p.ι.app k) S.f 0 (by simp)
          naturality k k' t := by
            ext
            · simp only [F, Functor.const_obj_map, assoc, pullback.lift_fst, comp_id]
              exact id_comp _
            · simp only [F, assoc, pullback.lift_snd, pullback.lift_snd_assoc, zero_comp,
                comp_zero] }
      g :=
        { app k := pullback.snd _ _
          naturality k k' t := by simp only [F, pullback.lift_snd] }
      zero := by
        ext k
        exact pullback.lift_snd _ _ _ }
  have hT : T.Exact := (ShortComplex.exact_iff_evaluation _).2
    fun k ↦ (hS.pullback (p.ι.app k)).exact
  have (k : I) : Mono (T.f.app k) := (hS.pullback (p.ι.app k)).mono_f
  have := NatTrans.mono_of_mono_app T.f
  let c : Cocone F :=
    { pt := S.X₂
      ι :=
        { app k := pullback.fst _ _
          naturality k k' t := by
            simp only [F, pullback.lift_fst, Functor.const_obj_map] } }
  let φ₁ : S.X₁ ⟶ colimit F := IsColimit.map (isColimitConstCocone I S.X₁) (colimit.cocone F) T.f
  have hφ₁ (k : I) : φ₁ = T.f.app k ≫ colimit.ι F k :=
    (id_comp _).symm.trans
      (IsColimit.ι_map (isColimitConstCocone I S.X₁) (colimit.cocone F) T.f k)
  let φ₃ : colimit F ⟶ S.X₃ := IsColimit.map (colimit.isColimit F) p.cocone T.g
  have hφ₃ (k : I) : colimit.ι F k ≫ φ₃ = T.g.app k ≫ p.ι.app k := IsColimit.ι_map _ _ _ _
  have hφ₁' (k : I) : (constCocone I S.X₁).ι.app k ≫ φ₁ = T.f.app k ≫ colimit.ι F k :=
    (id_comp _).trans (hφ₁ k)
  have hU : (colim.mapShortComplex T (isColimitConstCocone I S.X₁) (colimit.cocone F) p.cocone
      φ₁ φ₃ hφ₁' hφ₃).ShortExact :=
    .mk' (colim.exact_mapShortComplex hT (isColimitConstCocone I S.X₁) (colimit.isColimit F)
      p.isColimit φ₁ φ₃ hφ₁' hφ₃)
      (colim.map_mono' T.f (isColimitConstCocone I S.X₁) (colimit.isColimit F) φ₁ hφ₁')
      (colim.map_epi' T.g (colimit.cocone F) p.isColimit φ₃ hφ₃)
  have comm₁ : φ₁ ≫ colimit.desc F c = S.f := by
    obtain ⟨k⟩ := IsFiltered.nonempty (C := I)
    rw [hφ₁ k, assoc, colimit.ι_desc]
    exact pullback.lift_fst _ _ _
  have comm₂ : colimit.desc F c ≫ S.g = φ₃ := colimit.hom_ext fun k ↦ by
    rw [colimit.ι_desc_assoc, hφ₃]
    exact pullback.condition
  let ψ : colim.mapShortComplex T (isColimitConstCocone I S.X₁) (colimit.cocone F) p.cocone
      φ₁ φ₃ hφ₁' hφ₃ ⟶ S :=
    { τ₁ := 𝟙 S.X₁
      τ₂ := colimit.desc F c
      τ₃ := 𝟙 S.X₃
      comm₁₂ := (id_comp _).trans comm₁.symm
      comm₂₃ := comm₂.trans (comp_id _).symm }
  have : IsIso ψ.τ₁ := inferInstanceAs (IsIso (𝟙 _))
  have : IsIso ψ.τ₃ := inferInstanceAs (IsIso (𝟙 _))
  have : IsIso ((colimit.isColimit F).desc (Cocone.mk _ c.ι)) :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ ψ hU hS
  rw [← ind_ind hP]
  exact ⟨I, inferInstance, inferInstance, ⟨F, c.ι, IsColimit.ofPointIso (colimit.isColimit F)⟩,
    fun k ↦ h (p.ι.app k) (hp k)⟩

variable [HasDerivedCategory C]

/-- Blueprint `proposition-ind-constructible-sheaves--7` (case of a constructible quotient): let
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be short exact with `X₁` in `ind P` and `X₃` in `P`, such that morphisms
out of `X₃[0]` factor through filtered colimits. Then `X₂` is the pushout of an extension
`0 ⟶ Dᵢ ⟶ E ⟶ X₃ ⟶ 0` along `Dᵢ ⟶ X₁` (`E` lies in `P`), hence the cokernel of
`Dᵢ ⟶ X₁ ⊞ E`, which lies in `ind P`. -/
lemma ind_X₂_of_shortExact_of_prop (hP : P ≤ isFinitelyPresentable.{w} C)
    [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions] {S : ShortComplex C}
    (hS : S.ShortExact) (hX₁ : ind.{w} P S.X₁) (hX₃ : P S.X₃)
    (hfac : DerivedCategory.HomFactorsThroughFilteredColimits.{w}
      ((DerivedCategory.singleFunctor C 0).obj S.X₃)) :
    ind.{w} P S.X₂ := by
  obtain ⟨I, _, _, p, hp⟩ := hX₁
  obtain ⟨i, E, j, q, w, h, hjq, hj, hq⟩ :=
    DerivedCategory.HomFactorsThroughFilteredColimits.exists_shortExact hS hfac p
  have := ind_isClosedUnderCokernels hP
  exact (ind.{w} P).prop_of_isColimit_cokernelCofork
    (hS.isColimitCokernelCoforkBiprodDesc hjq (p.ι.app i) h hj hq) (le_ind _ _ (hp i))
    (ind_biprod hP ⟨I, inferInstance, inferInstance, p, hp⟩
      (le_ind _ _ (P.prop_X₂_of_shortExact hjq (hp i) hX₃)))

/-- Blueprint `proposition-ind-constructible-sheaves--7`: if the objects of `P` are finitely
presentable, `P` is closed under cokernels and extensions, and morphisms out of objects `M[0]` with
`M` in `P` factor through filtered colimits (in all degrees, here degree `-1`, i.e. `Ext¹`), then
`ind P` is closed under extensions. -/
lemma ind_isClosedUnderExtensions (hP : P ≤ isFinitelyPresentable.{w} C)
    [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    (hfac : ∀ M, P M → DerivedCategory.HomFactorsThroughFilteredColimits.{w}
      ((DerivedCategory.singleFunctor C 0).obj M)) :
    (ind.{w} P).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ :=
    ind_X₂_of_shortExact_of_pullback hP hS h₃ fun Y c hY ↦
      ind_X₂_of_shortExact_of_prop hP (hS.pullback c) h₁ hY (hfac Y hY)

/-- If morphisms out of `M[0]` factor through filtered colimits for all `M` in `P`, the objects
of `P` are finitely presentable (blueprint `proposition-ind-constructible-sheaves`). -/
lemma le_isFinitelyPresentable_of_homFactorsThroughFilteredColimits
    (hfac : ∀ M, P M → DerivedCategory.HomFactorsThroughFilteredColimits.{w}
      ((DerivedCategory.singleFunctor C 0).obj M)) :
    P ≤ isFinitelyPresentable.{w} C :=
  fun M hM ↦ (hfac M hM).isFinitelyPresentable

/-- Blueprints `proposition-ind-constructible-sheaves` (2), `proposition-ind-constructible-sheaves`,
`proposition-ind-constructible-sheaves`, `proposition-ind-constructible-sheaves--3`,
`proposition-ind-constructible-sheaves` and `proposition-ind-constructible-sheaves--7`: let `P` be a
class of objects of a Grothendieck abelian category, containing zero and closed under kernels,
cokernels and extensions, such that morphisms out of `M[0]` (`M` in `P`) to `B[n]` factor through
filtered colimits `B = colim Bᵢ`. Then the ind-objects of `P` are closed under kernels, cokernels,
extensions and direct sums. -/
theorem isClosedUnder_ind_of_homFactorsThroughFilteredColimits [P.ContainsZero]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    (hfac : ∀ M, P M → DerivedCategory.HomFactorsThroughFilteredColimits.{w}
      ((DerivedCategory.singleFunctor C 0).obj M)) :
    (ind.{w} P).IsClosedUnderKernels ∧ (ind.{w} P).IsClosedUnderCokernels ∧
      (ind.{w} P).IsClosedUnderExtensions ∧
      ∀ J : Type w, (ind.{w} P).IsClosedUnderColimitsOfShape (Discrete J) :=
  have hP := le_isFinitelyPresentable_of_homFactorsThroughFilteredColimits hfac
  ⟨ind_isClosedUnderKernels hP, ind_isClosedUnderCokernels hP, ind_isClosedUnderExtensions hP hfac,
    ind_isClosedUnderColimitsOfShape_discrete hP⟩

end Abelian

end CategoryTheory.ObjectProperty
