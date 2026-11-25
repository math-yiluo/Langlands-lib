/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower

/-!
# Cohomological range of homotopy limits of towers
-/

@[expose] public section

open CategoryTheory Category Limits Opposite Pretriangulated

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C] {J : Type*} [Category* J]
  [HasLimitsOfShape J C] [HasExactLimitsOfShape J C]

/-- If limits of shape `J` are exact, the homology of short complexes commutes with limits of
shape `J`. -/
instance preservesLimitsOfShape_homologyFunctor :
    PreservesLimitsOfShape J (homologyFunctor C) where
  preservesLimit {F} := by
    let S := (functorEquivalence J C).inverse.obj F
    let τ (j : J) : (lim : (J ⥤ C) ⥤ C) ⟶ (evaluation J C).obj j :=
      { app G := limit.π G j }
    have hτ (j : J) : homologyMap ((limitCone F).π.app j) =
        (S.mapHomologyIso lim).hom ≫ limit.π S.homology j ≫
          (S.mapHomologyIso ((evaluation J C).obj j)).inv := by
      refine Eq.trans ?_ (congrArg (fun x ↦ (S.mapHomologyIso lim).hom ≫ x ≫
        (S.mapHomologyIso ((evaluation J C).obj j)).inv) (NatTrans.app_homology (τ j) S)).symm
      simp only [Iso.hom_inv_id_assoc, assoc, Iso.hom_inv_id, comp_id]
      rfl
    let e : S.homology ≅ F ⋙ homologyFunctor C :=
      NatIso.ofComponents (fun j ↦ (S.mapHomologyIso ((evaluation J C).obj j)).symm)
        (fun {j j'} f ↦ by
          have h := NatTrans.app_homology ((evaluation J C).map f) S
          dsimp at h ⊢
          rw [h]
          simp only [assoc, Iso.hom_inv_id, comp_id]
          rfl)
    refine preservesLimit_of_preserves_limit_cone (isLimitLimitCone F)
      (IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv e _).symm (limit.isLimit _))
        (Cone.ext (S.mapHomologyIso lim).symm fun j ↦ ?_))
    simp only [Functor.mapCone_π_app, homologyFunctor_map, hτ, Iso.symm_hom,
      Iso.inv_hom_id_assoc]
    rfl

end CategoryTheory.ShortComplex

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C]

/-- If products of shape `J` are exact, the cohomology functors of the derived category commute
with products of shape `J`: products in `D(C)` are computed termwise on complexes. -/
instance preservesLimitsOfShape_discrete_homologyFunctor (J : Type*)
    [HasLimitsOfShape (Discrete J) C] [HasExactLimitsOfShape (Discrete J) C] (n : ℤ) :
    PreservesLimitsOfShape (Discrete J) (homologyFunctor C n) where
  preservesLimit {G} := by
    let K : Discrete J ⥤ CochainComplex C ℤ :=
      Discrete.functor fun j ↦ Q.objPreimage (G.obj ⟨j⟩)
    let e : K ⋙ Q ≅ G := Discrete.natIso fun j ↦ Q.objObjPreimageIso (G.obj j)
    have : PreservesLimit K (Q ⋙ homologyFunctor C n) :=
      preservesLimit_of_natIso _ (homologyFunctorFactors C n).symm
    have : PreservesLimit (K ⋙ Q) (homologyFunctor C n) :=
      preservesLimit_of_preserves_limit_cone (isLimitOfPreserves Q (limit.isLimit K))
        (isLimitOfPreserves (Q ⋙ homologyFunctor C n) (limit.isLimit K))
    exact preservesLimit_of_iso_diagram _ e

variable [HasLimitsOfShape (Discrete ℕ) C] [HasExactLimitsOfShape (Discrete ℕ) C]
  {F : ℕᵒᵖ ⥤ DerivedCategory C} {c : Cone F}

/-- The cohomology of a product `∏ Fₙ` in the derived category vanishes in degree `i` if the
cohomology of every `Fₙ` does. -/
lemma isZero_homologyFunctor_obj_of_isLimit {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P)
    (i : ℤ) (h : ∀ n : ℕ, IsZero ((homologyFunctor C i).obj (F.obj (op n)))) :
    IsZero ((homologyFunctor C i).obj P.pt) := by
  have hP' := isLimitOfPreserves (homologyFunctor C i) hP
  exact (IsZero.iff_id_eq_zero _).2 (hP'.hom_ext fun ⟨n⟩ ↦ (h n).eq_of_tgt _ _)

/-- Let `c` be a homotopy limit cone over a tower `F` in `D(C)`, for an abelian category `C`
with exact countable products. If `Hⁱ(Fₙ) = 0` for all `n` and `H^{i-1}(1 - t)` is an
epimorphism on `∏ Fₙ`, then `Hⁱ(c.pt) = 0`: in the Milnor triangle, the connecting map
`H^{i-1}(∏ Fₙ) ⟶ Hⁱ(c.pt)` is both surjective and zero. -/
lemma isZero_homologyFunctor_obj_of_isHomotopyLimit (hc : IsHomotopyLimit c)
    {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P) (i : ℤ)
    (h : ∀ n : ℕ, IsZero ((homologyFunctor C i).obj (F.obj (op n))))
    (hepi : Epi ((homologyFunctor C (i - 1)).map (𝟙 P.pt - towerShift hP))) :
    IsZero ((homologyFunctor C i).obj c.pt) := by
  obtain ⟨δ, hT⟩ := hc.exists_distTriang hP
  have h₂ := isZero_homologyFunctor_obj_of_isLimit hP i h
  have hδ := (HomologySequence.exact₁ _ hT (i - 1) i (by lia)).epi_f (h₂.eq_of_tgt _ _)
  have h0 : HomologySequence.δ _ (i - 1) i (by lia) = 0 :=
    (HomologySequence.epi_homologyMap_mor₂_iff _ hT (i - 1) i (by lia)).1 hepi
  dsimp at hδ h0
  rw [h0] at hδ
  exact @IsZero.of_epi_zero _ _ _ _ _ hδ

/-- **Cohomological range of a derived limit.** Let `C` be an abelian category with exact
countable products in which `1 - t` is an epimorphism on `∏ Gₙ` for every tower `G` with
epimorphic transitions (the Mittag-Leffler condition; this holds for sheaves on a replete site,
e.g. the pro-étale site). If every term of a tower `F` in `D(C)` lies in degrees `[a, b]` and
the transitions are surjective on `H^b`, then the derived limit of `F` lies in degrees `[a, b]`.
-/
theorem isGE_and_isLE_of_isHomotopyLimit (hc : IsHomotopyLimit c) (a b : ℤ)
    (hF : ∀ n : ℕ, (F.obj (op n)).IsGE a ∧ (F.obj (op n)).IsLE b)
    (hb : ∀ n : ℕ, Epi ((homologyFunctor C b).map (F.map (homOfLE n.le_succ).op)))
    (hML : ∀ (G : ℕᵒᵖ ⥤ C) {P : Fan fun n : ℕ ↦ G.obj (op n)} (_ : IsLimit P)
      (t : P.pt ⟶ P.pt), (∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ G.map (homOfLE n.le_succ).op) →
      (∀ n : ℕ, Epi (G.map (homOfLE n.le_succ).op)) → Epi (𝟙 P.pt - t)) :
    c.pt.IsGE a ∧ c.pt.IsLE b := by
  let hP := productIsProduct fun n : ℕ ↦ F.obj (op n)
  have hzero (i : ℤ) (hi : ∀ n : ℕ, IsZero ((homologyFunctor C (i - 1)).obj (F.obj (op n)))) :
      Epi ((homologyFunctor C (i - 1)).map (𝟙 _ - towerShift hP)) :=
    ⟨fun _ _ _ ↦ (isZero_homologyFunctor_obj_of_isLimit hP (i - 1) hi).eq_of_src _ _⟩
  constructor
  · rw [isGE_iff]
    intro i hi
    refine isZero_homologyFunctor_obj_of_isHomotopyLimit hc hP i
      (fun n ↦ isZero_of_isGE _ a i hi (hX := (hF n).1)) (hzero i fun n ↦ ?_)
    exact isZero_of_isGE _ a (i - 1) (by lia) (hX := (hF n).1)
  · rw [isLE_iff]
    intro i hi
    refine isZero_homologyFunctor_obj_of_isHomotopyLimit hc hP i
      (fun n ↦ isZero_of_isLE _ b i hi (hX := (hF n).2)) ?_
    obtain hi' | rfl := lt_or_eq_of_le (show b ≤ i - 1 by lia)
    · exact hzero i fun n ↦ isZero_of_isLE _ b (i - 1) hi' (hX := (hF n).2)
    · let H := homologyFunctor C (i - 1)
      rw [H.map_sub, H.map_id]
      refine hML (F ⋙ H) (P := Fan.mk (H.obj _) fun n ↦ H.map (Pi.π _ n))
        (isLimitFanMkObjOfIsLimit H _ _ hP) _ (fun n ↦ ?_) hb
      dsimp only [Fan.mk, Fan.proj, Functor.comp_map, Discrete.natTrans_app]
      rw [← H.map_comp, ← H.map_comp]
      exact congrArg H.map (towerShift_proj hP n)

end DerivedCategory
