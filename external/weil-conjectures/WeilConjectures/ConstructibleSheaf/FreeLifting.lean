/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import WeilConjectures.Algebra.Homology.ResolutionByClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyTrivial
public import WeilConjectures.AlgebraicGeometry.GenericFiniteness
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.CategoryTheory.ConcreteCategory.FinitelyGenerated
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.OpenClosed.Conservative
public import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Supported
public import WeilConjectures.SixFunctors.OpenClosed.Vanishing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Lifting sections of étale sheaves along epimorphisms

An epimorphism of étale sheaves is locally surjective: a section of the target over a
quasi-compact étale `X`-scheme `W` lifts, after refining `W` by finitely many affine étale
`X`-schemes jointly covering it.

## Main statements

- `AlgebraicGeometry.Etale.exists_affine_refinement`: a covering sieve of a quasi-compact
  object of the small étale site contains a finite family of affine étale `X`-schemes jointly
  covering it.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Etale

variable {X : Scheme.{u}}

/-- **Finite affine refinement of an étale covering sieve.** A covering sieve `S` of an object
`W` of the small étale site of `X` with quasi-compact `W` contains finitely many arrows
`φ k : V k ⟶ W` from affine étale `X`-schemes whose images cover `W`. -/
lemma exists_affine_refinement {W : X.Etale} [CompactSpace W.left] (S : Sieve W)
    (hS : S ∈ X.smallEtaleTopology W) :
    ∃ (n : ℕ) (V : Fin n → X.Etale) (φ : ∀ k, V k ⟶ W), (∀ k, S (φ k)) ∧
      (∀ k, IsAffine (V k).left) ∧ ⋃ k, Set.range (φ k).left = Set.univ := by
  rw [Scheme.mem_smallEtaleTopology_iff] at hS
  choose V g hg hx using hS
  choose v hv using hx
  have hU (w : W.left) : ∃ U ∈ (V w).left.affineOpens, v w ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hvU, -⟩ :=
      (V w).left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (v w)) isOpen_univ
    exact ⟨U, hU, hvU⟩
  choose U hUa hvU using hU
  let V' (w : W.left) : X.Etale := Scheme.Etale.mk ((U w).ι ≫ (V w).hom)
  let ψ (w : W.left) : V' w ⟶ V w := MorphismProperty.Over.homMk (U w).ι rfl
  let φ (w : W.left) : V' w ⟶ W := ψ w ≫ g w
  have hφ (w : W.left) : (φ w).left = (U w).ι ≫ (g w).left := rfl
  let O (w : W.left) : Set W.left := Set.range (φ w).left
  have hO (w : W.left) : IsOpen (O w) := (φ w).left.isOpenMap.isOpen_range
  have hwO (w : W.left) : w ∈ O w := ⟨⟨v w, hvU w⟩, by
    rw [hφ, Scheme.Hom.comp_apply]
    exact hv w⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun w _ ↦ Set.mem_iUnion.2 ⟨w, hwO w⟩)
  let e := t.equivFin.symm
  refine ⟨t.card, fun k ↦ V' (e k), fun k ↦ φ (e k), fun k ↦ S.downward_closed (hg _) _,
    fun k ↦ hUa (e k), ?_⟩
  refine Set.eq_univ_of_forall fun w ↦ ?_
  obtain ⟨w', hw', hw⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ w))
  refine Set.mem_iUnion.2 ⟨e.symm ⟨w', hw'⟩, ?_⟩
  have : (e (e.symm ⟨w', hw'⟩) : W.left) = w' := by rw [Equiv.apply_symm_apply]
  change w ∈ O (e (e.symm ⟨w', hw'⟩) : W.left)
  rw [this]
  exact hw

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- `Sheaf.freeYonedaHomEquiv` is natural in the target. -/
lemma freeYonedaHomEquiv_comp {W : X.Etale} {M : ModuleCat.{u + 1} Λ}
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (α : Sheaf.freeYoneda X.smallEtaleTopology W M ⟶ F) (f : F ⟶ G) :
    Sheaf.freeYonedaHomEquiv (α ≫ f) = Sheaf.freeYonedaHomEquiv α ≫ f.hom.app (op W) := by
  simp only [Sheaf.freeYonedaHomEquiv, Equiv.trans_apply]
  have h := (sheafificationAdjunction X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)).homEquiv_naturality_right
    (X := Presheaf.freeYoneda W M) α f
  erw [h, Presheaf.freeYonedaHomEquiv_comp]
  rfl

/-- **Local lifting along an epimorphism.** Let `p : A ⟶ G` be an epimorphism of étale sheaves
of `Λ`-modules and `s : Λ[W] ⟶ G` a map from the free sheaf on a quasi-compact étale
`X`-scheme `W`. Then there are finitely many affine étale `X`-schemes `V k` with maps
`φ k : V k ⟶ W` whose images cover `W`, and lifts `t k : Λ[V k] ⟶ A` of the restrictions of
`s` to the `V k`. -/
lemma exists_lift_freeYoneda {A G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (p : A ⟶ G) [Epi p] (W : X.Etale) [CompactSpace W.left]
    (s : Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ) ⟶ G) :
    ∃ (n : ℕ) (V : Fin n → X.Etale) (φ : ∀ k, V k ⟶ W)
      (t : ∀ k, Sheaf.freeYoneda X.smallEtaleTopology (V k) (ModuleCat.of Λ Λ) ⟶ A),
      (∀ k, IsAffine (V k).left) ∧ ⋃ k, Set.range (φ k).left = Set.univ ∧
      ∀ k, Sheaf.freeYonedaHomEquiv (t k ≫ p) =
        Sheaf.freeYonedaHomEquiv s ≫ G.obj.map (φ k).op := by
  have : Sheaf.IsLocallySurjective p :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := p)).2 inferInstance
  let x := (Sheaf.freeYonedaHomEquiv s).hom (1 : Λ)
  obtain ⟨n, V, φ, hφ, hV, hcov⟩ := exists_affine_refinement _
    (Presheaf.imageSieve_mem X.smallEtaleTopology p.hom (U := op W) x)
  choose a ha using hφ
  refine ⟨n, V, φ, fun k ↦ Sheaf.freeYonedaHomEquiv.symm
    (ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ (a k))), hV, hcov, fun k ↦ ?_⟩
  rw [freeYonedaHomEquiv_comp, Equiv.apply_symm_apply]
  ext
  simpa [x] using ha k

omit [CommRing Λ] in
/-- A property of objects of an abelian category which contains the zero objects and is closed
under isomorphisms and binary biproducts is closed under finite coproducts. -/
lemma _root_.CategoryTheory.ObjectProperty.isClosedUnderFiniteCoproducts_of_biprod
    {C : Type*} [Category* C] [Abelian C] (P : ObjectProperty C) [P.ContainsZero]
    [P.IsClosedUnderIsomorphisms] (h : ∀ X Y, P X → P Y → P (X ⊞ Y)) :
    P.IsClosedUnderFiniteCoproducts := by
  have : P.IsClosedUnderBinaryCoproducts := ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
    rintro _ ⟨F, hF⟩
    exact P.prop_of_iso ((biprod.isoCoprod _ _) ≪≫ (HasColimit.isoOfNatIso (diagramIsoPair F)).symm)
      (h _ _ (hF _) (hF _)))
  exact .mk'

/-- **Lifting along epimorphisms by free sheaves.** Let `S` be a property of étale sheaves of
`Λ`-modules closed under finite coproducts and containing the free sheaves `Λ[W]` on the affine
étale `X`-schemes `W`, and let `T` be a property such that every sheaf `G` in `T` is a quotient
of a finite coproduct of such free sheaves, that is, receives a jointly epimorphic finite
family of maps from them. Then `S` lifts along epimorphisms onto `T`: sections
lift locally along an epimorphism (`AlgebraicGeometry.Etale.exists_lift_freeYoneda`), and the
local pieces again form a finite coproduct of free sheaves on affine étale `X`-schemes. -/
theorem liftsAlongEpi_of_exists_epi_sigma_freeYoneda
    (S T : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [S.IsClosedUnderFiniteCoproducts]
    (hS : ∀ W : X.Etale, IsAffine W.left →
      S (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ)))
    (hgen : ∀ G, T G → ∃ (n : ℕ) (W : Fin n → X.Etale)
      (s : ∀ i, Sheaf.freeYoneda X.smallEtaleTopology (W i) (ModuleCat.of Λ Λ) ⟶ G),
      (∀ i, IsAffine (W i).left) ∧ ∀ ⦃F⦄ (f : G ⟶ F), (∀ i, s i ≫ f = 0) → f = 0) :
    ChainComplex.LiftsAlongEpi S T := by
  intro A B G p _ g hG
  obtain ⟨n, W, s, hWa, hepi⟩ := hgen G hG
  have : Epi (pullback.snd p g) := inferInstance
  choose m V φ t hV hcov ht using fun i ↦ exists_lift_freeYoneda (pullback.snd p g) (W i) (s i)
  have : HasFiniteCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := inferInstance
  have := hasColimitsOfShape_discrete (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (Σ i, Fin (m i))
  let free (Z : X.Etale) := Sheaf.freeYoneda X.smallEtaleTopology Z (ModuleCat.of Λ Λ)
  let e : ∐ (fun j : Σ i, Fin (m i) ↦ free (V j.1 j.2)) ⟶ G := Sigma.desc fun j ↦
    Sheaf.freeYonedaHomEquiv.symm (Sheaf.freeYonedaHomEquiv (s j.1) ≫ G.obj.map (φ j.1 j.2).op)
  have he (j : Σ i, Fin (m i)) : t j.1 j.2 ≫ pullback.snd p g = Sigma.ι _ j ≫ e := by
    apply Sheaf.freeYonedaHomEquiv.injective
    rw [ht, Sigma.ι_comp_desc, Equiv.apply_symm_apply]
  refine ⟨_, e, Sigma.desc (fun j ↦ t j.1 j.2) ≫ pullback.fst p g,
    S.prop_coproduct (fun j ↦ hS _ (hV _ _)), ?_, ?_⟩
  · refine Preadditive.epi_of_cancel_zero _ fun {F} f hf ↦ ?_
    have hs (i : Fin n) : s i ≫ f = 0 := by
      apply Sheaf.freeYonedaHomEquiv.injective
      rw [freeYonedaHomEquiv_comp, ← comp_zero (f := s i), freeYonedaHomEquiv_comp]
      refine F.property.hom_ext_ofArrows (φ i)
        ((Scheme.ofArrows_mem_smallEtaleTopology_iff _).2 (hcov i)) fun k ↦ ?_
      have h₁ := congrArg Sheaf.freeYonedaHomEquiv
        (Sigma.ι (fun j : Σ i, Fin (m i) ↦ free (V j.1 j.2)) ⟨i, k⟩ ≫= hf)
      rw [comp_zero, ← Category.assoc, Sigma.ι_comp_desc, freeYonedaHomEquiv_comp,
        Equiv.apply_symm_apply] at h₁
      simp only [Category.assoc, ← NatTrans.naturality] at h₁ ⊢
      rw [h₁]
      calc Sheaf.freeYonedaHomEquiv (0 : free (V i k) ⟶ F)
          = Sheaf.freeYonedaHomEquiv ((0 : free (V i k) ⟶ F) ≫ (0 : F ⟶ F)) := by rw [comp_zero]
        _ = _ := freeYonedaHomEquiv_comp _ _
        _ = 0 := by simp
    exact hepi f hs
  · ext j
    simp only [Sigma.ι_comp_desc_assoc, Category.assoc, pullback.condition]
    rw [← Category.assoc, he, Category.assoc]

omit [CommRing Λ] in
/-- A colimit of flat objects of shape `J`, for colimits of shape `J` exact, is flat: tensoring
with it is the colimit of the left exact functors of tensoring with the terms. -/
lemma _root_.CategoryTheory.ObjectProperty.flat_colimit {A : Type*} [Category* A] [Abelian A]
    [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A] {J : Type*} [Category* J]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A] (F : J ⥤ A)
    (hF : ∀ j, ObjectProperty.flat (F.obj j)) : ObjectProperty.flat (colimit F) := by
  have (j : J) : PreservesFiniteLimits (tensorLeft (F.obj j)) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits (F.obj j)).1 (hF j)
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  have : PreservesColimit F (MonoidalCategory.curriedTensor A) :=
    MonoidalCategory.Limits.preservesColimit_curriedTensor _
  have e : tensorLeft (colimit F) ≅ (F ⋙ MonoidalCategory.curriedTensor A).flip ⋙ colim :=
    preservesColimitIso (MonoidalCategory.curriedTensor A) F ≪≫ colimitIsoFlipCompColim _
  have : PreservesFiniteLimits ((F ⋙ MonoidalCategory.curriedTensor A).flip) :=
    preservesFiniteLimits_of_evaluation _ (fun j ↦
      inferInstanceAs (PreservesFiniteLimits (tensorLeft (F.obj j))))
  exact preservesFiniteLimits_of_natIso e.symm

/-- **Free sheaves are flat.** The free étale sheaf of `Λ`-modules `Λ[W]` on an étale
`X`-scheme `W` is flat: its stalks are filtered colimits of free `Λ`-modules. -/
theorem flat_freeYoneda (W : X.Etale) :
    ObjectProperty.flat (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ)) := by
  rw [flat_iff_forall_flat_sheafFiber_obj]
  intro Ω _ _ s
  let Φ := (Scheme.pointSmallEtale s).ulift.{u + 1}
  refine ObjectProperty.prop_of_iso _
    ((Φ.presheafToSheafCompSheafFiberIso _).app (Presheaf.freeYoneda W (ModuleCat.of Λ Λ))).symm
    (ObjectProperty.flat_colimit _ fun j ↦ ?_)
  have hunit : ObjectProperty.flat (ModuleCat.of Λ Λ) :=
    ObjectProperty.flat_of_tensorIso (λ_ (𝟙_ (ModuleCat.{u + 1} Λ)))
  let f (_ : ULift.{u + 1} ((yoneda.obj W).obj (op j.unop.1))) := ModuleCat.of Λ Λ
  exact ObjectProperty.prop_of_iso _ (Sigma.whiskerEquiv Equiv.ulift (fun _ ↦ Iso.refl _))
    (ObjectProperty.flat_coproduct f fun _ ↦ hunit)

/-- **Base change of free sheaves.** For a morphism `g : Y ⟶ X` and an étale `X`-scheme `W`,
the pullback `g^* Λ[W]` is the free sheaf `Λ[W ×_X Y]` on the base change of `W`: both
corepresent `F ↦ F(W ×_X Y) = (g_* F)(W)`.
(blueprint: `lem-weil-pbc-modulecat-upperstar-free-yoneda`) -/
noncomputable def upperStarFreeYonedaIso {Y : Scheme.{u}} (g : Y ⟶ X) (W : X.Etale) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj
        (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ)) ≅
      Sheaf.freeYoneda Y.smallEtaleTopology (g.Etale.obj W) (ModuleCat.of Λ Λ) :=
  let e (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj
        (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ)) ⟶ F) ≃
      (Sheaf.freeYoneda Y.smallEtaleTopology (g.Etale.obj W) (ModuleCat.of Λ Λ) ⟶ F) :=
    let e₁ := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).homEquiv
      (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ)) F
    let e₂ := Sheaf.freeYonedaHomEquiv (J := X.smallEtaleTopology) (X := W)
      (M := ModuleCat.of Λ Λ) (F := (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).obj F)
    let e₃ := Sheaf.freeYonedaHomEquiv (J := Y.smallEtaleTopology) (X := g.Etale.obj W)
      (M := ModuleCat.of Λ Λ) (F := F)
    { toFun f := e₃.symm (e₂ (e₁ f))
      invFun f := e₁.symm (e₂.symm (e₃ f))
      left_inv f := by simp
      right_inv f := by simp }
  have he {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : _ ⟶ F) (h : F ⟶ F') :
      e F' (f ≫ h) = e F f ≫ h := by
    apply Sheaf.freeYonedaHomEquiv.injective
    dsimp only [e, Equiv.coe_fn_mk]
    rw [Equiv.apply_symm_apply, freeYonedaHomEquiv_comp, Equiv.apply_symm_apply,
      Adjunction.homEquiv_naturality_right, freeYonedaHomEquiv_comp]
    rfl
  Coyoneda.ext _ _ (fun f ↦ e _ f) (fun f ↦ (e _).symm f) (fun f ↦ by simp)
    (fun f ↦ by simp) (fun f h ↦ by
      apply (e _).injective
      rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply])

section TrivialCover

variable {U : Scheme.{u}} (S : Type u)

instance etale_sigmaDesc_id : AlgebraicGeometry.Etale (Sigma.desc fun _ : S ↦ 𝟙 U) :=
  IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance

/-- The trivial finite étale cover `∐_{s ∈ S} U ⟶ U`, as an object of the small étale site. -/
noncomputable abbrev trivialCover : U.Etale := Scheme.Etale.mk (Sigma.desc fun _ : S ↦ 𝟙 U)

/-- The inclusion of the `s`-th copy of `U` into the trivial cover. -/
noncomputable def trivialCoverι (s : S) : Scheme.Etale.mk (𝟙 U) ⟶ trivialCover (U := U) S :=
  MorphismProperty.Over.homMk (Sigma.ι (fun _ : S ↦ U) s) (by simp)

variable {S}

/-- A sheaf on the small étale site of `U` turns the trivial cover `∐_{s ∈ S} U` into the
product of copies of its global sections: maps into the sections over `∐_{s ∈ S} U` are the
families of maps into the sections over the copies of `U`, since these cover `∐_{s ∈ S} U` and
pairwise intersect in the empty scheme. -/
lemma bijective_comp_map_trivialCoverι {A : Type*} [Category* A]
    (F : Sheaf U.smallEtaleTopology A) (E : A) :
    Function.Bijective (fun (x : E ⟶ F.obj.obj (op (trivialCover S))) (s : S) ↦
      x ≫ F.obj.map (trivialCoverι S s).op) := by
  have hcov : Sieve.ofArrows _ (trivialCoverι (U := U) S) ∈
      U.smallEtaleTopology (trivialCover S) := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun p ↦ Set.mem_iUnion.2 ?_
    obtain ⟨⟨s, x⟩, rfl⟩ := (sigmaMk fun _ : S ↦ U).surjective p
    exact ⟨s, x, by rw [sigmaMk_mk]; rfl⟩
  have h := (Presieve.isSheafFor_arrows_iff _ _).1
    ((F.property E).isSheafFor (Presieve.ofArrows _ (trivialCoverι S)) hcov)
  refine ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨t, -, ht⟩ := h (fun s ↦ x ≫ F.obj.map (trivialCoverι S s).op) (by
      intro i j Z gi gj hij
      change (x ≫ F.obj.map _) ≫ F.obj.map gi.op = (x ≫ F.obj.map _) ≫ F.obj.map gj.op
      simp only [Category.assoc, ← Functor.map_comp, ← op_comp, hij])
    exact (ht x fun _ ↦ rfl).trans (ht y fun s ↦ (congrFun hxy s).symm).symm
  · obtain ⟨t, ht, -⟩ := h z (by
      intro i j Z gi gj hij
      have hl : gi.left ≫ Sigma.ι (fun _ : S ↦ U) i = gj.left ≫ Sigma.ι (fun _ : S ↦ U) j :=
        congrArg (fun f ↦ f.left) hij
      by_cases hij' : i = j
      · subst hij'
        have : gi = gj :=
          MorphismProperty.Over.Hom.ext ((cancel_mono (Sigma.ι (fun _ : S ↦ U) i)).1 hl)
        rw [this]
      · have : IsEmpty Z.left := isEmpty_of_commSq_sigmaι_of_ne
          ⟨hl⟩ hij'
        refine F.property.hom_ext_ofArrows (I := PEmpty.{1}) (X := fun _ ↦ Z) (fun _ ↦ 𝟙 Z)
          ((Scheme.ofArrows_mem_smallEtaleTopology_iff _).2
            (Set.eq_univ_of_forall fun z ↦ isEmptyElim z)) fun i ↦ i.elim)
    exact ⟨t, funext ht⟩

/-- Maps out of a coproduct are families of maps. -/
noncomputable def _root_.CategoryTheory.Limits.sigmaDescEquiv {C : Type*} [Category* C] {S : Type*}
    {A B : C} [HasCoproduct fun _ : S ↦ A] : (S → (A ⟶ B)) ≃ ((∐ fun _ : S ↦ A) ⟶ B) where
  toFun f := Sigma.desc f
  invFun g s := Sigma.ι (fun _ : S ↦ A) s ≫ g
  left_inv f := by simp
  right_inv g := Sigma.hom_ext _ _ fun s ↦ by simp

variable (Λ) in
/-- The free sheaf on the trivial cover `∐_{s ∈ S} U` is the constant sheaf with value
`∐_{s ∈ S} Λ`: both corepresent `G ↦ ∏_{s ∈ S} G(U)`. -/
noncomputable def freeYonedaTrivialCoverIso [Finite S] :
    Sheaf.freeYoneda U.smallEtaleTopology (trivialCover S) (ModuleCat.of Λ Λ) ≅
      (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (∐ fun _ : S ↦ ModuleCat.of Λ Λ) :=
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 U)) := MorphismProperty.Over.mkIdTerminal _ _
  let adj := constantSheafAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT
  let e (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      (Sheaf.freeYoneda U.smallEtaleTopology (trivialCover S) (ModuleCat.of Λ Λ) ⟶ G) ≃
        ((constantSheaf _ _).obj (∐ fun _ : S ↦ ModuleCat.of Λ Λ) ⟶ G) :=
    Sheaf.freeYonedaHomEquiv.trans ((Equiv.ofBijective _
      (bijective_comp_map_trivialCoverι G (ModuleCat.of Λ Λ))).trans
        (sigmaDescEquiv.trans (adj.homEquiv _ _).symm))
  have he {G G' : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : _ ⟶ G) (h : G ⟶ G') :
      e G' (f ≫ h) = e G f ≫ h := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right]
    dsimp only [e, Equiv.trans_apply]
    erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    refine Sigma.hom_ext _ _ fun s ↦ ?_
    simp only [sigmaDescEquiv, Equiv.coe_fn_mk, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc,
      Equiv.ofBijective_apply, freeYonedaHomEquiv_comp, Category.assoc]
    erw [h.hom.naturality]
  Coyoneda.ext _ _ (fun f ↦ e _ f) (fun f ↦ (e _).symm f) (fun f ↦ by simp)
    (fun f ↦ by simp) (fun f h ↦ by
      apply (e _).injective
      rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply])

end TrivialCover

section FiniteEtale

variable {U : Scheme.{u}}

/-- Free sheaves on isomorphic étale `U`-schemes are isomorphic. -/
noncomputable def freeYonedaMapIso {A B : U.Etale} (i : A ≅ B) :
    Sheaf.freeYoneda U.smallEtaleTopology A (ModuleCat.of Λ Λ) ≅
      Sheaf.freeYoneda U.smallEtaleTopology B (ModuleCat.of Λ Λ) :=
  let e (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      (Sheaf.freeYoneda U.smallEtaleTopology A (ModuleCat.of Λ Λ) ⟶ G) ≃
        (Sheaf.freeYoneda U.smallEtaleTopology B (ModuleCat.of Λ Λ) ⟶ G) :=
    Sheaf.freeYonedaHomEquiv.trans
      ((Iso.homCongr (Iso.refl _) (G.obj.mapIso i.op).symm).trans Sheaf.freeYonedaHomEquiv.symm)
  have he {G G' : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : _ ⟶ G) (h : G ⟶ G') :
      e G' (f ≫ h) = e G f ≫ h := by
    apply Sheaf.freeYonedaHomEquiv.injective
    simp only [e, Equiv.trans_apply, Equiv.apply_symm_apply, freeYonedaHomEquiv_comp,
      Iso.homCongr_apply, Iso.refl_inv, Category.id_comp, Iso.symm_hom, Functor.mapIso_inv,
      Category.assoc]
    erw [h.hom.naturality]
  Coyoneda.ext _ _ (fun f ↦ e _ f) (fun f ↦ (e _).symm f) (fun f ↦ by simp)
    (fun f ↦ by simp) (fun f h ↦ by
      apply (e _).injective
      rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply])

/-- The free sheaf on an étale `U`-scheme isomorphic to a trivial cover is constant. -/
lemma isConstant_freeYoneda_of_iso {S : Type u} [Finite S] {V : U.Etale}
    (i : V ≅ trivialCover S) :
    (Sheaf.freeYoneda U.smallEtaleTopology V (ModuleCat.of Λ Λ)).IsConstant
      U.smallEtaleTopology :=
  Sheaf.isConstant_of_iso _ (freeYonedaMapIso i ≪≫ freeYonedaTrivialCoverIso Λ)

/-- The base change of an étale `U`-scheme `V` along `g`, when it is a trivial cover, as an
isomorphism of étale `U'`-schemes. -/
noncomputable def etaleObjIsoTrivialCover {U' : Scheme.{u}} {g : U' ⟶ U} {V : U.Etale}
    {S : Type u} {fst : (∐ fun _ : S ↦ U') ⟶ V.left}
    (h : IsPullback fst (Sigma.desc fun _ ↦ 𝟙 U') V.hom g) :
    g.Etale.obj V ≅ trivialCover S :=
  MorphismProperty.Over.isoMk h.isoPullback.symm (by simp; rfl)

/-- **Free sheaves on finite étale schemes are finite locally constant.** For a finite étale
`U`-scheme `V`, the free sheaf `Λ[V]` is finite locally constant: étale-locally `V` is a trivial
cover (`AlgebraicGeometry.Scheme.FiniteEtale.exists_etale_isPullback_sigma`), on which the free
sheaf is constant, and its stalks are free of finite rank, the geometric fibres of `V` being
finite. -/
theorem isFiniteLocallyConstantSheaf_freeYoneda_of_isFinite (V : U.Etale) [IsFinite V.hom] :
    Scheme.IsFiniteLocallyConstantSheaf
      (Sheaf.freeYoneda U.smallEtaleTopology V (ModuleCat.of Λ Λ)) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hloc : Scheme.IsLocallyConstantSheaf
      (Sheaf.freeYoneda U.smallEtaleTopology V (ModuleCat.of Λ Λ)) := by
    choose U' g hg S hS fst hy hpb using fun y : U ↦
      Scheme.FiniteEtale.exists_etale_isPullback_sigma (⟨V, ‹_›⟩ : U.FiniteEtale) y
    let 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage U :=
      Scheme.Cover.mkOfCovers U U' g (fun y ↦ ⟨y, hy y⟩) hg
    refine ⟨⟨⟨𝒰, fun y ↦ (Scheme.isConstant_over_iff_upperStar _ _ _).2 ?_⟩⟩⟩
    have := isConstant_freeYoneda_of_iso (Λ := Λ) (etaleObjIsoTrivialCover (hpb y))
    exact (Sheaf.isConstant_congr (U' y).smallEtaleTopology
      (upperStarFreeYonedaIso (Λ := Λ) (g y) V).symm :)
  have hfin : Scheme.IsFiniteSheaf
      (Sheaf.freeYoneda U.smallEtaleTopology V (ModuleCat.of Λ Λ)) := ⟨fun Ω _ _ s ↦ by
    obtain ⟨ι, _, -, ⟨e⟩⟩ := V.hom.exists_overIso_sigma_of_isSepClosed s
    let i : s.Etale.obj V ≅ trivialCover ι :=
      MorphismProperty.Over.isoMk ((Over.forget _).mapIso e) (Over.w e.hom)
    have : Module.Finite Λ ((∐ fun _ : ι ↦ ModuleCat.of.{u + 1} Λ Λ : ModuleCat.{u + 1} Λ)) :=
      have := Classical.decEq (ULift.{u + 1} ι)
      have : Finite (ULift.{u + 1} ι) := Finite.of_equiv ι Equiv.ulift.symm
      (Module.Finite.equiv_iff ((Sigma.whiskerEquiv (f := fun _ : ULift.{u + 1} ι ↦
        ModuleCat.of.{u + 1} Λ Λ) (g := fun _ : ι ↦ ModuleCat.of.{u + 1} Λ Λ) Equiv.ulift
        (fun _ ↦ Iso.refl _)).symm ≪≫ ModuleCat.coprodIsoDirectSum.{u + 1, u + 1, u + 1}
        (fun _ : ULift.{u + 1} ι ↦ ModuleCat.of.{u + 1} Λ Λ)).toLinearEquiv).mpr
          (Module.Finite.instDirectSum (R := Λ) (fun _ : ULift.{u + 1} ι ↦ Λ))
    have h := (((ModuleCat.isFinitelyGenerated_iff _).2 this).of_iso
      ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiberConstantSheafIso _).symm).of_iso
      ((Scheme.pointSmallEtale (𝟙 _)).sheafFiber.mapIso
        ((upperStarFreeYonedaIso (Λ := Λ) s V ≪≫ freeYonedaMapIso (Λ := Λ) i ≪≫
          freeYonedaTrivialCoverIso Λ).symm) ≪≫
        (Etale.upperStarCompSheafFiberIso _ s (𝟙 _)).app _)
    rwa [Category.id_comp] at h⟩
  exact { toIsLocallyConstantSheaf := hloc, toIsFiniteSheaf := hfin }

end FiniteEtale

/-- **Generic finiteness of étale morphisms** [Stacks 03I1, 02NW]. Let `Z` be a nonempty scheme
with Noetherian underlying space and `W` an affine étale `Z`-scheme. Over some nonempty open
`U ⊆ Z` the morphism `W ⟶ Z` is finite: over the generic point `η` of an irreducible open
`U₀`, the fibre of `W` is finite, and by Zariski's Main Theorem `W` is open in a scheme `T` finite
over `U₀`; the closure of `W` in `T` meets its complement only over a closed subset of `U₀` not
containing `η`, and over the complement `U` of that subset `W` is closed in `T`, hence finite
over `U`. -/
theorem exists_isFinite_etale_obj {Z : Scheme.{u}} [TopologicalSpace.NoetherianSpace Z]
    [Nonempty Z] (W : Z.Etale) [IsAffine W.left] :
    ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ IsFinite (U.ι.Etale.obj W).hom := by
  let f : W.left ⟶ Z := W.hom
  have : LocallyQuasiFinite f := inferInstance
  have : LocallyOfFiniteType f := inferInstance
  obtain ⟨U, hU, hfin⟩ := f.exists_isFinite_morphismRestrict_of_noetherianSpace
  refine ⟨U, hU, ?_⟩
  change IsFinite (pullback.snd W.hom U.ι)
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
  infer_instance

/-- **Generic local constancy of free sheaves.** Let `Z` be a nonempty scheme with Noetherian
underlying space and `Λ` finite. The free étale sheaf `Λ[W]` on an affine étale `Z`-scheme `W`
is finite locally constant on some nonempty open `U ⊆ Z`: over a nonempty open `U` the morphism
`W ⟶ Z` is finite étale (`AlgebraicGeometry.Etale.exists_isFinite_etale_obj`), the restriction
of `Λ[W]` to `U` is the free sheaf on `W ×_Z U` (`AlgebraicGeometry.Etale.upperStarFreeYonedaIso`),
and the free sheaf on a finite étale scheme is finite locally constant
(`AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_freeYoneda_of_isFinite`). -/
theorem exists_isFiniteLocallyConstantSheaf_freeYoneda [Finite Λ] {Z : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace Z] [Nonempty Z] (W : Z.Etale) [IsAffine W.left] :
    ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ Scheme.IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
        (Sheaf.freeYoneda Z.smallEtaleTopology W (ModuleCat.of Λ Λ))) := by
  obtain ⟨U, hU, hfin⟩ := exists_isFinite_etale_obj W
  refine ⟨U, hU, ?_⟩
  have := isFiniteLocallyConstantSheaf_freeYoneda_of_isFinite (Λ := Λ) (U.ι.Etale.obj W)
  exact Scheme.IsFiniteLocallyConstantSheaf.of_iso (upperStarFreeYonedaIso U.ι W).symm

/-- **Free sheaves on affine étale schemes are constructible** [Stacks 03SA, 095M]. Let `X` be
a scheme with Noetherian underlying space and `Λ` finite. The free étale sheaf `Λ[W] = j_{W!} Λ_W`
on an affine étale `X`-scheme `W` is constructible. By Noetherian induction it is finite
locally constant on a nonempty open `U`
(`AlgebraicGeometry.Etale.exists_isFiniteLocallyConstantSheaf_freeYoneda`) and, by base change
(`AlgebraicGeometry.Etale.upperStarFreeYonedaIso`), its restriction to the closed complement of
`U` is the free sheaf on an affine étale scheme over a smaller closed subset. -/
theorem isConstructibleSheaf_freeYoneda [Finite Λ] [TopologicalSpace.NoetherianSpace X]
    (W : X.Etale) [IsAffine W.left] :
    Scheme.IsConstructibleSheaf (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ)) := by
  -- Noetherian induction on the closed subsets `C` of `X` containing the image of a closed
  -- subscheme `Z`
  suffices h : ∀ C : TopologicalSpace.Closeds X, ∀ (Z : Scheme.{u}) (i : Z ⟶ X)
      [IsClosedImmersion i], Set.range i.base ⊆ C → ∀ (W : Z.Etale) [IsAffine W.left],
      Scheme.IsConstructibleSheaf (Sheaf.freeYoneda Z.smallEtaleTopology W (ModuleCat.of Λ Λ)) by
    exact h ⊤ X (𝟙 X) (Set.subset_univ _) W
  intro C
  induction C using WellFoundedLT.induction with
  | _ C ih =>
  intro Z i _ hZC W _
  have : TopologicalSpace.NoetherianSpace (Set.range i.base) := inferInstance
  have : TopologicalSpace.NoetherianSpace Z :=
    (TopologicalSpace.noetherianSpace_iff_of_homeomorph
      i.isClosedEmbedding.isEmbedding.toHomeomorph).2 inferInstance
  by_cases hZ : IsEmpty Z
  · exact Scheme.IsConstructibleSheaf.of_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty _)
  rw [not_isEmpty_iff] at hZ
  obtain ⟨U, hU, hlc⟩ := exists_isFiniteLocallyConstantSheaf_freeYoneda (Λ := Λ) W
  let i' := Scheme.Opens.closedComplement U
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (U : Set Z))
  have hij : Set.range i'.base = (Set.range U.ι.base)ᶜ := by
    rw [Scheme.Opens.range_closedComplement, Scheme.Opens.range_ι]
  rw [Scheme.isConstructibleSheaf_iff_upperStar U.ι i' hij]
  refine ⟨hlc.isConstructibleSheaf, ?_⟩
  have : IsAffine (i'.Etale.obj W).left :=
    have : IsAffine ((𝟭 Scheme).obj W.left) := ‹IsAffine W.left›
    isAffine_of_isAffineHom (pullback.fst W.hom i')
  let C' : TopologicalSpace.Closeds X :=
    ⟨Set.range (i' ≫ i).base, (i' ≫ i).isClosedEmbedding.isClosed_range⟩
  have hC' : C' < C := by
    refine lt_of_le_of_ne (fun x hx ↦ ?_) fun h ↦ ?_
    · obtain ⟨z, rfl⟩ := hx
      exact hZC ⟨_, rfl⟩
    · obtain ⟨u, hu⟩ := hU
      have hx : i.base u ∈ (C : Set X) := hZC ⟨u, rfl⟩
      rw [← h] at hx
      obtain ⟨z, hz⟩ := hx
      rw [Scheme.Hom.comp_apply] at hz
      have := i.isClosedEmbedding.injective hz
      have hz' : u ∈ Set.range i'.base := ⟨z, this⟩
      rw [hij] at hz'
      exact hz' ⟨⟨u, hu⟩, rfl⟩
  have := ih C' hC' _ (i' ≫ i) subset_rfl (i'.Etale.obj W)
  exact Scheme.IsConstructibleSheaf.of_iso (upperStarFreeYonedaIso i' W).symm

section Generation

/-- Maps from the free sheaf on the étale `Z`-scheme `V ⟶ Y ⟶ Z` are maps from the free sheaf
on `V` into the pullback along the étale `e : Y ⟶ Z`: both are sections over `V`. -/
noncomputable def freeYonedaEtaleHomEquiv {Y Z : Scheme.{u}} (e : Y ⟶ Z) (he : Etale e)
    (V : Y.Etale) (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.freeYoneda Z.smallEtaleTopology ((MorphismProperty.Over.map ⊤ he).obj V)
        (ModuleCat.of Λ Λ) ⟶ G) ≃
      (Sheaf.freeYoneda Y.smallEtaleTopology V (ModuleCat.of Λ Λ) ⟶
        (Etale.upperStar (ModuleCat.{u + 1} Λ) e).obj G) :=
  Sheaf.freeYonedaHomEquiv.trans ((Iso.homCongr (Iso.refl _)
    (((sheafToPresheaf _ _).mapIso
      ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) e he).app G)).symm.app
        (op V))).trans Sheaf.freeYonedaHomEquiv.symm)

lemma freeYonedaEtaleHomEquiv_comp {Y Z : Scheme.{u}} (e : Y ⟶ Z) (he : Etale e)
    (V : Y.Etale) {G F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (s : Sheaf.freeYoneda Z.smallEtaleTopology ((MorphismProperty.Over.map ⊤ he).obj V)
        (ModuleCat.of Λ Λ) ⟶ G) (f : G ⟶ F) :
    freeYonedaEtaleHomEquiv e he V F (s ≫ f) =
      freeYonedaEtaleHomEquiv e he V G s ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) e).map f := by
  apply Sheaf.freeYonedaHomEquiv.injective
  simp only [freeYonedaEtaleHomEquiv, Equiv.trans_apply, freeYonedaHomEquiv_comp]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have := congrArg (fun φ ↦ φ.hom.app (op V))
    ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) e he).inv.naturality f)
  erw [Iso.homCongr_apply, Iso.homCongr_apply]
  simp only [Iso.refl_inv, Category.id_comp, Category.assoc]
  congr 1

omit [CommRing Λ] in
lemma freeYonedaHomEquiv_zero [CommRing Λ] {W : X.Etale}
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} :
    Sheaf.freeYonedaHomEquiv
      (0 : Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ) ⟶ F) = 0 := by
  calc Sheaf.freeYonedaHomEquiv (0 : Sheaf.freeYoneda X.smallEtaleTopology W
        (ModuleCat.of Λ Λ) ⟶ F)
      = Sheaf.freeYonedaHomEquiv ((0 : Sheaf.freeYoneda X.smallEtaleTopology W
          (ModuleCat.of Λ Λ) ⟶ F) ≫ (0 : F ⟶ F)) := by rw [comp_zero]
    _ = _ := freeYonedaHomEquiv_comp _ _
    _ = 0 := by simp

/-- **Generation of a constant sheaf with finitely generated value.** If `H` is isomorphic to a
constant sheaf with finitely generated value, finitely many maps from the free sheaf on the
terminal object detect the vanishing of maps out of `H`. -/
lemma exists_detecting_freeYoneda_of_iso_constantSheaf {Y : Scheme.{u}}
    {H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {N : ModuleCat.{u + 1} Λ}
    [Module.Finite Λ N]
    (i : (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N ≅ H) :
    ∃ (n : ℕ) (σ : Fin n → (Sheaf.freeYoneda Y.smallEtaleTopology (Scheme.Etale.mk (𝟙 Y))
        (ModuleCat.of Λ Λ) ⟶ H)),
      ∀ ⦃F⦄ (g : H ⟶ F), (∀ k, σ k ≫ g = 0) → g = 0 := by
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 Y)) := MorphismProperty.Over.mkIdTerminal _ _
  let adj := constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := Λ) (M := N)
  let c : N ⟶ H.obj.obj (op (Scheme.Etale.mk (𝟙 Y))) := adj.homEquiv _ _ i.hom
  refine ⟨n, fun k ↦ Sheaf.freeYonedaHomEquiv.symm
    (ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ (c (v k)))), fun F g hg ↦ ?_⟩
  suffices h : i.hom ≫ g = 0 by
    rw [← cancel_epi i.hom, h, comp_zero]
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  ext1
  refine LinearMap.ext_on_range hv fun k ↦ ?_
  have := congrArg (fun φ : Sheaf.freeYoneda Y.smallEtaleTopology (Scheme.Etale.mk (𝟙 Y))
      (ModuleCat.of Λ Λ) ⟶ F ↦ (Sheaf.freeYonedaHomEquiv φ).hom (1 : Λ)) (hg k)
  simp only [freeYonedaHomEquiv_comp, Equiv.apply_symm_apply, freeYonedaHomEquiv_zero] at this
  have h0 : (adj.homEquiv N F) 0 = 0 := by
    rw [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  rw [h0]
  simpa [c] using this

lemma freeYonedaEtaleHomEquiv_zero {Y Z : Scheme.{u}} (e : Y ⟶ Z) (he : Etale e) (V : Y.Etale)
    {F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)} :
    freeYonedaEtaleHomEquiv e he V F
      (0 : Sheaf.freeYoneda Z.smallEtaleTopology ((MorphismProperty.Over.map ⊤ he).obj V)
        (ModuleCat.of Λ Λ) ⟶ F) = 0 := by
  calc freeYonedaEtaleHomEquiv e he V F 0
      = freeYonedaEtaleHomEquiv e he V F (0 ≫ (0 : F ⟶ F)) := by rw [comp_zero]
    _ = _ := freeYonedaEtaleHomEquiv_comp e he V _ _
    _ = 0 := by simp

/-- **Vanishing is detected on a jointly surjective family.** A morphism of étale sheaves of
`Λ`-modules whose pullbacks along a family of morphisms covering the base vanish is zero: its
kernel inclusion becomes invertible after each pullback. -/
lemma eq_zero_of_upperStar_map_eq_zero {Z : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}}
    (a : ∀ i, Y i ⟶ Z) (ha : ∀ z : Z, ∃ (i : ι) (y : Y i), (a i).base y = z)
    {G F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : G ⟶ F)
    (hf : ∀ i, (Etale.upperStar (ModuleCat.{u + 1} Λ) (a i)).map f = 0) : f = 0 := by
  have : IsIso (kernel.ι f) := by
    refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective _ a ha _ fun i ↦ ?_
    have h : (Etale.upperStar (ModuleCat.{u + 1} Λ) (a i)).map (kernel.ι f) =
        (PreservesKernel.iso (Etale.upperStar (ModuleCat.{u + 1} Λ) (a i)) f).hom ≫
          (kernelIsoOfEq (hf i)).hom ≫ kernel.ι _ := by simp
    rw [h]
    infer_instance
  rw [← cancel_epi (kernel.ι f), kernel.condition, comp_zero]

/-- If the pullback of `G` along an étale `e : A ⟶ Z` from a nonempty scheme is constant and
finite, finitely many maps from the free sheaf on `A` detect the vanishing of `e^* f`. -/
lemma exists_detecting_freeYoneda_of_isConstant {Z A : Scheme.{u}} (e : A ⟶ Z) (he : Etale e)
    [Nonempty A] (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hc : ((Etale.upperStar (ModuleCat.{u + 1} Λ) e).obj G).IsConstant A.smallEtaleTopology)
    (hfin : Scheme.IsFiniteSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) e).obj G)) :
    ∃ (n : ℕ) (s : Fin n → (Sheaf.freeYoneda Z.smallEtaleTopology
        ((MorphismProperty.Over.map ⊤ he).obj (Scheme.Etale.mk (𝟙 A))) (ModuleCat.of Λ Λ) ⟶ G)),
      ∀ ⦃F⦄ (f : G ⟶ F), (∀ k, s k ≫ f = 0) →
        (Etale.upperStar (ModuleCat.{u + 1} Λ) e).map f = 0 := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨N, ⟨iN⟩⟩ := hc.mem_essImage
  obtain ⟨x⟩ := ‹Nonempty A›
  have : Module.Finite Λ N := by
    rw [← ModuleCat.isFinitelyGenerated_iff]
    exact (hfin.isFinitelyGenerated_sheafFiber _ (A.algClosurePoint x)).of_iso
      ((Scheme.pointSmallEtale (A.algClosurePoint x)).sheafFiber.mapIso iN.symm ≪≫
        (Scheme.pointSmallEtale (A.algClosurePoint x)).sheafFiberConstantSheafIso N)
  obtain ⟨n, σ, hσ⟩ := exists_detecting_freeYoneda_of_iso_constantSheaf iN
  refine ⟨n, fun k ↦ (freeYonedaEtaleHomEquiv e he _ G).symm (σ k), fun F f hf ↦ hσ _ fun k ↦ ?_⟩
  have := congrArg (freeYonedaEtaleHomEquiv e he _ F) (hf k)
  rwa [freeYonedaEtaleHomEquiv_comp, Equiv.apply_symm_apply,
    freeYonedaEtaleHomEquiv_zero e he _] at this

/-- A finite locally constant restriction to a quasi-compact open `U` is trivialised by finitely
many étale maps from nonempty affine schemes whose images cover `U`. -/
lemma exists_etale_isConstant_cover {Z : Scheme.{u}} (U : Z.Opens)
    (hU : IsCompact (U : Set Z)) (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj G)] :
    ∃ (n : ℕ) (A : Fin n → Scheme.{u}) (e : ∀ l, A l ⟶ Z) (_ : ∀ l, Etale (e l)),
      (∀ l, IsAffine (A l) ∧ Nonempty (A l)) ∧
      (∀ l, ((Etale.upperStar (ModuleCat.{u + 1} Λ) (e l)).obj G).IsConstant
        (A l).smallEtaleTopology ∧
        Scheme.IsFiniteSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (e l)).obj G)) ∧
      (U : Set Z) ⊆ ⋃ l, Set.range (e l) := by
  let L := (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj G
  obtain ⟨⟨𝒰, hc⟩⟩ := Scheme.IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := L)
  have hy (u : U.toScheme) := 𝒰.exists_eq u
  choose i y hy using hy
  have hA (u : U.toScheme) := exists_isAffineOpen_mem_and_subset (x := y u) (U := ⊤) trivial
  choose A hA hyA _ using hA
  let e (u : U.toScheme) : (A u).toScheme ⟶ Z := (A u).ι ≫ 𝒰.f (i u) ≫ U.ι
  have he (u : U.toScheme) : Etale (e u) := by dsimp [e]; infer_instance
  have hcon (u : U.toScheme) : ((Etale.upperStar (ModuleCat.{u + 1} Λ) (e u)).obj G).IsConstant
      (A u).toScheme.smallEtaleTopology := by
    have h₁ := (Scheme.isConstant_over_iff_upperStar _ _ L).1 (hc (i u))
    have : ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f (i u))).obj L).IsConstant
        (𝒰.X (i u)).smallEtaleTopology := h₁
    have h₂ := Sheaf.IsConstant.upperStar (ModuleCat.{u + 1} Λ) (A u).ι
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f (i u))).obj L)
    have : ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f (i u)) ⋙
        Etale.upperStar (ModuleCat.{u + 1} Λ) (A u).ι).obj L).IsConstant
        (A u).toScheme.smallEtaleTopology := h₂
    exact Sheaf.isConstant_congr _ (((Etale.upperStarComp _ (A u).ι (𝒰.f (i u))).app L).symm ≪≫
      ((Etale.upperStarComp _ ((A u).ι ≫ 𝒰.f (i u)) U.ι).app G).symm)
  have hfin (u : U.toScheme) :
      Scheme.IsFiniteSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (e u)).obj G) := by
    have := Scheme.IsFiniteSheaf.upperStar ((A u).ι ≫ 𝒰.f (i u)) L
    exact Scheme.IsFiniteSheaf.of_iso
      (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) ((A u).ι ≫ 𝒰.f (i u))).obj L)
      ((Etale.upperStarComp _ ((A u).ι ≫ 𝒰.f (i u)) U.ι).app G).symm
  have hopen (u : U.toScheme) : IsOpen (Set.range (e u)) := (e u).isOpenMap.isOpen_range
  have hmem (u : U.toScheme) : u.1 ∈ Set.range (e u) :=
    ⟨⟨y u, hyA u⟩, by simp [e, hy u]⟩
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun u : U.toScheme ↦ Set.range (e u)) hopen
    (fun z hz ↦ Set.mem_iUnion.2 ⟨⟨z, hz⟩, hmem ⟨z, hz⟩⟩)
  let r := t.equivFin.symm
  refine ⟨t.card, fun l ↦ (A (r l)).toScheme, fun l ↦ e (r l), fun l ↦ he _,
    fun l ↦ ⟨hA _, ⟨⟨y (r l), hyA (r l)⟩⟩⟩, fun l ↦ ⟨hcon _, hfin _⟩, fun z hz ↦ ?_⟩
  obtain ⟨u, hu, hzu⟩ := Set.mem_iUnion₂.1 (ht hz)
  refine Set.mem_iUnion.2 ⟨r.symm ⟨u, hu⟩, ?_⟩
  have : (r (r.symm ⟨u, hu⟩) : U.toScheme) = u := by rw [Equiv.apply_symm_apply]
  change z ∈ Set.range (e (r (r.symm ⟨u, hu⟩) : U.toScheme))
  rw [this]
  exact hzu

/-- For a closed immersion `i`, the unit `G ⟶ i_* i^* G` is an epimorphism: its cokernel
vanishes on the open complement, where `i_* i^* G` does, and on `Z'`, where the unit becomes
invertible. -/
lemma epi_upperStarLowerStarAdjunction_unit_app {Z Z' : Scheme.{u}} (i : Z' ⟶ Z)
    [IsClosedImmersion i] (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Epi ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app G) := by
  let adj := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i
  let U : Z.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hij : Set.range i = (Set.range U.ι)ᶜ := by simp [U]
  refine Preadditive.epi_of_isZero_cokernel _
    (Etale.isZero_of_isZero_upperStar (j := U.ι) i hij ?_ ?_)
  · refine IsZero.of_iso ?_ (PreservesCokernel.iso (Etale.upperStar _ U.ι) (adj.unit.app G))
    refine IsZero.of_epi (cokernel.π _) ?_
    exact Etale.isZero_upperStar_lowerStar_of_disjoint_range _ U.ι i
      (by rw [Scheme.Opens.range_ι]; exact disjoint_compl_left) _
  · refine IsZero.of_iso ?_ (PreservesCokernel.iso (Etale.upperStar _ i) (adj.unit.app G))
    have h := adj.left_triangle_components G
    have : IsIso ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).map (adj.unit.app G)) := by
      have : IsIso ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).map (adj.unit.app G) ≫
          adj.counit.app _) := by rw [h]; exact IsIso.id _
      exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
    exact isZero_cokernel_of_epi _

/-- **Lifting generators from a closed subscheme.** For a closed immersion `i : Z' ⟶ Z` and a map
`t : Λ[W'] ⟶ i^* G` from the free sheaf on a quasi-compact étale `Z'`-scheme, finitely many maps
from free sheaves on affine étale `Z`-schemes detect the vanishing of `t ≫ i^* f`: étale
`Z'`-schemes are covered by base changes of étale `Z`-schemes, and sections of `i_* i^* G` lift
locally to `G`, the unit being an epimorphism. -/
lemma exists_detecting_of_isClosedImmersion {Z Z' : Scheme.{u}} (i : Z' ⟶ Z)
    [IsClosedImmersion i] (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (W' : Z'.Etale) [CompactSpace W'.left]
    (t : Sheaf.freeYoneda Z'.smallEtaleTopology W' (ModuleCat.of Λ Λ) ⟶
      (Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj G) :
    ∃ (n : ℕ) (V : Fin n → Z.Etale)
      (u : ∀ k, Sheaf.freeYoneda Z.smallEtaleTopology (V k) (ModuleCat.of Λ Λ) ⟶ G),
      (∀ k, IsAffine (V k).left) ∧ ∀ ⦃F⦄ (f : G ⟶ F), (∀ k, u k ≫ f = 0) →
        t ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) i).map f = 0 := by
  let adj := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i
  let η := adj.unit.app G
  have : Epi η := epi_upperStarLowerStarAdjunction_unit_app i G
  have hls : Sheaf.IsLocallySurjective η :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := η)).2 inferInstance
  let H := (Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj G
  let s := (Sheaf.freeYonedaHomEquiv t).hom (1 : Λ)
  let T : Sieve W' :=
    { arrows := fun P g ↦ ∃ (V : Z.Etale) (_ : IsAffine V.left) (a : G.obj.obj (op V))
        (ψ : P ⟶ i.Etale.obj V),
          (H.obj.map g.op).hom s = (H.obj.map ψ.op).hom ((η.hom.app (op V)).hom a)
      downward_closed := by
        rintro P Q g ⟨V, hV, a, ψ, h⟩ g'
        refine ⟨V, hV, a, g' ≫ ψ, ?_⟩
        simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, h] }
  have hT : T ∈ Z'.smallEtaleTopology W' := by
    refine Z'.smallEtaleTopology.transitive (Functor.is_cover_of_isCoverDense i.Etale _ W') T ?_
    rintro P g₁ ⟨⟨Y, lift, map, fac⟩⟩
    let sY := (H.obj.map map.op).hom s
    let S : Presieve Y := fun V h ↦ IsAffine V.left ∧
      Presheaf.imageSieve η.hom (U := Y) sY h
    have hS : Sieve.generate S ∈ Z.smallEtaleTopology Y := by
      have hI := Presheaf.imageSieve_mem Z.smallEtaleTopology η.hom (U := op Y) sY
      rw [Scheme.mem_smallEtaleTopology_iff] at hI ⊢
      intro y
      obtain ⟨V₂, h, hh, ⟨q, rfl⟩⟩ := hI y
      obtain ⟨V₃, hV₃, hq, -⟩ := exists_isAffineOpen_mem_and_subset (x := q) (U := ⊤) trivial
      let V₃' : Z.Etale := Scheme.Etale.mk (V₃.ι ≫ V₂.hom)
      let h' : V₃' ⟶ Y := MorphismProperty.Over.homMk V₃.ι rfl ≫ h
      refine ⟨V₃', h', Sieve.le_generate S V₃' h'
        ⟨hV₃, (Presheaf.imageSieve η.hom sY).downward_closed hh _⟩,
        ⟨⟨q, hq⟩, rfl⟩⟩
    refine Z'.smallEtaleTopology.superset_covering ?_
      (Z'.smallEtaleTopology.pullback_stable lift
        ((Scheme.Hom.coverPreserving_etale i).cover_preserve hS))
    rintro P' h₂ ⟨V₄, h₄, k, ⟨V₃, a', h', ⟨hV₃, ⟨a, ha⟩⟩, rfl⟩, eq⟩
    refine ⟨V₃, hV₃, a, k ≫ i.Etale.map a', ?_⟩
    have e₁ : h₂ ≫ g₁ = (k ≫ i.Etale.map a') ≫ i.Etale.map h' ≫ map := by
      rw [← fac, ← Category.assoc, eq, Functor.map_comp]
      simp only [Category.assoc]
    rw [e₁]
    simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    exact congrArg (fun z ↦ (H.obj.map k.op).hom ((H.obj.map (i.Etale.map a').op).hom z)) ha.symm
  obtain ⟨n, V', φ, hφT, -, hcov⟩ := exists_affine_refinement T hT
  choose V hV a ψ hc using hφT
  refine ⟨n, V, fun k ↦ Sheaf.freeYonedaHomEquiv.symm
    (ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ (a k))), hV, fun F f hf ↦ ?_⟩
  have hfa (k : Fin n) : (f.hom.app (op (V k))).hom (a k) = 0 := by
    have := congrArg (fun φ : Sheaf.freeYoneda Z.smallEtaleTopology (V k) (ModuleCat.of Λ Λ) ⟶ F ↦
      (Sheaf.freeYonedaHomEquiv φ).hom (1 : Λ)) (hf k)
    simpa [freeYonedaHomEquiv_comp, freeYonedaHomEquiv_zero] using this
  let H' := (Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj F
  let φf := (Etale.upperStar (ModuleCat.{u + 1} Λ) i).map f
  have key (k : Fin n) :
      (H'.obj.map (φ k).op).hom ((φf.hom.app (op W')).hom s) = 0 := by
    have e₁ := congrArg (fun z ↦ z s) (congrArg ModuleCat.Hom.hom (φf.hom.naturality (φ k).op))
    have e₂ := congrArg (fun z ↦ z ((η.hom.app (op (V k))).hom (a k)))
      (congrArg ModuleCat.Hom.hom (φf.hom.naturality (ψ k).op))
    have e₃ := congrArg (fun z ↦ z (a k)) (congrArg ModuleCat.Hom.hom
      (congrArg (fun φ ↦ φ.hom.app (op (V k))) (adj.unit.naturality f)))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e₁ e₂ e₃
    rw [← e₁, hc k, e₂]
    have e₄ : (φf.hom.app (op (i.Etale.obj (V k)))).hom ((η.hom.app (op (V k))).hom (a k)) =
        ((adj.unit.app F).hom.app (op (V k))).hom ((f.hom.app (op (V k))).hom (a k)) := by
      exact e₃.symm
    rw [e₄, hfa k, map_zero, map_zero]
  apply Sheaf.freeYonedaHomEquiv.injective
  rw [freeYonedaHomEquiv_comp, freeYonedaHomEquiv_zero]
  refine H'.property.hom_ext_ofArrows φ ((Scheme.ofArrows_mem_smallEtaleTopology_iff _).2 hcov)
    fun k ↦ ?_
  ext1
  refine LinearMap.ext_ring ?_
  simpa using key k

end Generation

/-- A morphism vanishing after pullback to a closed subscheme and along finitely many morphisms
whose images cover its complement vanishes. -/
lemma eq_zero_of_upperStar_map_eq_zero_of_isClosedImmersion {Z Z' : Scheme.{u}} (i' : Z' ⟶ Z)
    {n : ℕ} {A : Fin n → Scheme.{u}} (e : ∀ l, A l ⟶ Z)
    (hcov : ∀ z : Z, z ∈ Set.range i' ∨ ∃ l, z ∈ Set.range (e l))
    {G F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : G ⟶ F)
    (h₁ : ∀ l, (Etale.upperStar (ModuleCat.{u + 1} Λ) (e l)).map f = 0)
    (h₂ : (Etale.upperStar (ModuleCat.{u + 1} Λ) i').map f = 0) : f = 0 := by
  refine eq_zero_of_upperStar_map_eq_zero
    (Y := fun o : ULift.{u} (Option (Fin n)) ↦ Option.elim o.down Z' A)
    (fun o ↦ match o with
      | ⟨none⟩ => i'
      | ⟨some l⟩ => e l) (fun z ↦ ?_) f ?_
  · rcases hcov z with ⟨y, hy⟩ | ⟨l, y, hy⟩
    · exact ⟨⟨none⟩, y, hy⟩
    · exact ⟨⟨some l⟩, y, hy⟩
  · rintro ⟨_ | l⟩
    · exact h₂
    · exact h₁ l

/-- **Constructible sheaves are generated by finitely many sections** [Stacks 095M; SGA 4½,
Rapport, 4.6]. Let `X` be Noetherian and `Λ` finite. A constructible sheaf `G` of `Λ`-modules
on `X_ét` receives a jointly epimorphic finite family of maps from free sheaves `Λ[W i]` on
affine étale `X`-schemes. -/
theorem exists_jointlyEpi_freeYoneda [Finite Λ] [TopologicalSpace.NoetherianSpace X]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsConstructibleSheaf G] :
    ∃ (n : ℕ) (W : Fin n → X.Etale)
      (s : ∀ i, Sheaf.freeYoneda X.smallEtaleTopology (W i) (ModuleCat.of Λ Λ) ⟶ G),
      (∀ i, IsAffine (W i).left) ∧ ∀ ⦃F⦄ (f : G ⟶ F), (∀ i, s i ≫ f = 0) → f = 0 := by
  suffices h : ∀ C : TopologicalSpace.Closeds X, ∀ (Z : Scheme.{u}) (i : Z ⟶ X)
      [IsClosedImmersion i], Set.range i.base ⊆ C →
      ∀ (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsConstructibleSheaf G],
      ∃ (ι : Type) (_ : Finite ι) (W : ι → Z.Etale)
        (s : ∀ j, Sheaf.freeYoneda Z.smallEtaleTopology (W j) (ModuleCat.of Λ Λ) ⟶ G),
        (∀ j, IsAffine (W j).left) ∧ ∀ ⦃F⦄ (f : G ⟶ F), (∀ j, s j ≫ f = 0) → f = 0 by
    obtain ⟨ι, _, W, s, hW, hs⟩ := h ⊤ X (𝟙 X) (Set.subset_univ _) G
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
    exact ⟨n, fun k ↦ W (e.symm k), fun k ↦ s (e.symm k), fun k ↦ hW _,
      fun F f hf ↦ hs f fun j ↦ by obtain ⟨k, rfl⟩ := e.symm.surjective j; exact hf k⟩
  intro C
  induction C using WellFoundedLT.induction with
  | _ C ih =>
  intro Z i _ hZC G _
  have : TopologicalSpace.NoetherianSpace (Set.range i.base) := inferInstance
  have : TopologicalSpace.NoetherianSpace Z :=
    (TopologicalSpace.noetherianSpace_iff_of_homeomorph
      i.isClosedEmbedding.isEmbedding.toHomeomorph).2 inferInstance
  by_cases hZ : IsEmpty Z
  · exact ⟨PEmpty, inferInstance, PEmpty.elim, fun j ↦ j.elim, fun j ↦ j.elim,
      fun F f _ ↦ (Scheme.Etale.isZero_sheaf_of_isEmpty G).eq_of_src _ _⟩
  rw [not_isEmpty_iff] at hZ
  obtain ⟨U, hUd, hlc⟩ := Scheme.IsConstructibleSheaf.exists_dense_open G
  obtain ⟨n₁, A, e, he, haff, hcf, hcovU⟩ := exists_etale_isConstant_cover U
    (TopologicalSpace.NoetherianSpace.isCompact _) G
  have (l : Fin n₁) : Nonempty (A l) := (haff l).2
  choose m s₁ hs₁ using fun l ↦
    exists_detecting_freeYoneda_of_isConstant (e l) (he l) G (hcf l).1 (hcf l).2
  let i' := Scheme.Opens.closedComplement U
  have hij : Set.range i'.base = (Set.range U.ι.base)ᶜ := by
    rw [Scheme.Opens.range_closedComplement, Scheme.Opens.range_ι]
  have hU : (U : Set Z).Nonempty := hUd.nonempty
  let C' : TopologicalSpace.Closeds X :=
    ⟨Set.range (i' ≫ i).base, (i' ≫ i).isClosedEmbedding.isClosed_range⟩
  have hC' : C' < C := by
    refine lt_of_le_of_ne (fun x hx ↦ ?_) fun h ↦ ?_
    · obtain ⟨z, rfl⟩ := hx
      exact hZC ⟨_, rfl⟩
    · obtain ⟨u, hu⟩ := hU
      have hx : i.base u ∈ (C : Set X) := hZC ⟨u, rfl⟩
      rw [← h] at hx
      obtain ⟨z, hz⟩ := hx
      rw [Scheme.Hom.comp_apply] at hz
      have := i.isClosedEmbedding.injective hz
      have hz' : u ∈ Set.range i'.base := ⟨z, this⟩
      rw [hij] at hz'
      exact hz' ⟨⟨u, hu⟩, rfl⟩
  have : Scheme.IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) i').obj G) :=
    Scheme.IsConstructibleSheaf.upperStar i' G
  obtain ⟨ι₂, _, W', t, hW', ht⟩ := ih C' hC' _ (i' ≫ i) subset_rfl
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) i').obj G)
  have (k : ι₂) : CompactSpace (W' k).left := by have := hW' k; infer_instance
  choose p V u hV hu using fun k ↦ exists_detecting_of_isClosedImmersion i' G (W' k) (t k)
  let W : (Σ l, Fin (m l)) ⊕ (Σ k, Fin (p k)) → Z.Etale :=
    Sum.elim (fun j ↦ (MorphismProperty.Over.map ⊤ (he j.1)).obj (Scheme.Etale.mk (𝟙 (A j.1))))
      (fun j ↦ V j.1 j.2)
  refine ⟨_, inferInstance, W,
    fun j ↦ Sum.rec (motive := fun j ↦
      Sheaf.freeYoneda Z.smallEtaleTopology (W j) (ModuleCat.of Λ Λ) ⟶ G)
      (fun j ↦ s₁ j.1 j.2) (fun j ↦ u j.1 j.2) j, ?_, ?_⟩
  · rintro (j | j)
    · exact (haff j.1).1
    · exact hV j.1 j.2
  intro F f hf
  refine eq_zero_of_upperStar_map_eq_zero_of_isClosedImmersion i' e (fun z ↦ ?_) f
    (fun l ↦ hs₁ l f fun k ↦ hf (.inl ⟨l, k⟩))
    (ht _ fun k ↦ hu k f fun q ↦ hf (.inr ⟨k, q⟩))
  by_cases hz : z ∈ (U : Set Z)
  · obtain ⟨l, hl⟩ := Set.mem_iUnion.1 (hcovU hz)
    exact .inr ⟨l, hl⟩
  · refine .inl ?_
    rw [hij, Scheme.Opens.range_ι]
    exact hz

end AlgebraicGeometry.Etale
