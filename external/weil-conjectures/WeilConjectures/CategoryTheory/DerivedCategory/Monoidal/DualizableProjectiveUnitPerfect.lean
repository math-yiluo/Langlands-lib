/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingle

/-!
# Dualizable objects of `D(C)` are bounded complexes of finite projective objects

Let `C` be a braided monoidal closed Grothendieck abelian category with functorial flat
resolutions, whose unit `𝟙` is projective, with morphisms from `𝟙` finite on coproducts and on
tensor products (`CategoryTheory.UnitFactorsThroughFiniteCoproducts`,
`CategoryTheory.UnitTensorFinite`). We prove that every dualizable object `K` of `D(C)` is
isomorphic to a bounded complex of finite projective objects, that is, of retracts of finite
direct sums `𝟙ʳ` (`DerivedCategory.exists_iso_Q_obj_of_isDualizable`).

## Strategy

By `DerivedCategory.exists_retract_of_exactPairing_of_projective_unit`, a dualizable `K` is a
retract of a bounded complex whose terms are quotients of some `𝟙ʳ`. Hence `K` is bounded, its
top homology is a quotient of some `𝟙ʳ`, and, its dual being bounded as well, `K` has finite Tor
amplitude. We argue by induction on the length of the interval `[a, b]`, where `K` vanishes above
`b` and `K ⊗ G[0]` vanishes below `a` for every `G : C`.

* If `a = b`, then `K = H[-a]`, where `H` is a quotient of `𝟙ʳ` such that `H[0]` is dualizable of
  Tor amplitude `[0, 0]`. Its dual `X` then vanishes above `0`, so `Hom(H[0], G[1])`, which is
  `Hom(𝟙, G[1] ⊗ X)`, vanishes; the surjection `𝟙ʳ ⟶ H` splits, and `H` is finite projective.
* If `a < b`, a map `𝟙ʳ[-b] ⟶ K` which is surjective on `Hᵇ` has a dualizable cone `C'` vanishing
  above `b - 1` with the same lower Tor bound `a`. By induction `C'` is a bounded complex of
  finite projective objects, and so is `K`, an extension of `C'` by `𝟙ʳ[-b]`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

open Pretriangulated

section FinProjComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [HasDerivedCategory.{w} C]

attribute [local instance] Abelian.hasFiniteBiproducts

variable (C) in
/-- The objects of `D(C)` isomorphic to the image of a bounded complex of finite projective
objects, that is, of retracts of finite direct sums `𝟙ʳ` (`CategoryTheory.finProj`). -/
def finProjComplex : ObjectProperty (DerivedCategory C) :=
  fun K ↦ ∃ (P : CochainComplex C ℤ) (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
    (∀ n, finProj C (P.X n)) ∧ Nonempty (K ≅ Q.obj P)

instance : (finProjComplex C).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨P, a, b, h₁, h₂, h₃, ⟨e'⟩⟩ ↦ ⟨P, a, b, h₁, h₂, h₃, ⟨e.symm ≪≫ e'⟩⟩

/-- A finite projective object placed in degree `n` is a bounded complex of finite projective
objects. -/
lemma finProjComplex_singleFunctor_obj {X : C} (hX : finProj C X) (n : ℤ) :
    finProjComplex C ((singleFunctor C n).obj X) := by
  refine ⟨(HomologicalComplex.single C (.up ℤ) n).obj X, n, n,
    inferInstanceAs (CochainComplex.IsStrictlyGE ((CochainComplex.singleFunctor C n).obj X) n),
    inferInstanceAs (CochainComplex.IsStrictlyLE ((CochainComplex.singleFunctor C n).obj X) n),
    fun i ↦ ?_, ⟨(singleFunctorIsoCompQ C n).app X⟩⟩
  by_cases hi : i = n
  · subst hi
    exact finProj_of_iso (HomologicalComplex.singleObjXSelf _ _ X).symm hX
  · exact finProj_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)

/-- A zero object of `D(C)` is a bounded complex of finite projective objects. -/
lemma finProjComplex_of_isZero {K : DerivedCategory C} (hK : IsZero K) : finProjComplex C K :=
  (finProjComplex C).prop_of_iso
    (((singleFunctor C 0).map_isZero (isZero_zero C)).iso hK)
    (finProjComplex_singleFunctor_obj (finProj_of_isZero (isZero_zero C)) 0)

/-- Bounded complexes of finite projective objects are stable under shifts. -/
lemma finProjComplex.shift {K : DerivedCategory C} (hK : finProjComplex C K) (n : ℤ) :
    finProjComplex C (K⟦n⟧) := by
  obtain ⟨P, a, b, _, _, hP, ⟨e⟩⟩ := hK
  exact ⟨P⟦n⟧, a - n, b - n, P.isStrictlyGE_shift a n (a - n) (by omega),
    P.isStrictlyLE_shift b n (b - n) (by omega),
    fun i ↦ finProj_of_iso (P.shiftFunctorObjXIso n i (i + n) rfl).symm (hP _),
    ⟨(shiftFunctor _ n).mapIso e ≪≫ ((Q.commShiftIso n).app P).symm⟩⟩

/-- The mapping cone of a morphism of bounded complexes of finite projective objects is a
bounded complex of finite projective objects. -/
lemma finProjComplex_Q_obj_mappingCone {P₁ P₂ : CochainComplex C ℤ} (φ : P₁ ⟶ P₂)
    (a₁ b₁ a₂ b₂ : ℤ) [P₁.IsStrictlyGE a₁] [P₁.IsStrictlyLE b₁] [P₂.IsStrictlyGE a₂]
    [P₂.IsStrictlyLE b₂] (h₁ : ∀ i, finProj C (P₁.X i)) (h₂ : ∀ i, finProj C (P₂.X i)) :
    finProjComplex C (Q.obj (CochainComplex.mappingCone φ)) := by
  have : (CochainComplex.mappingCone φ).IsStrictlyLE (max (b₁ - 1) b₂) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨P₁.isZero_of_isStrictlyLE b₁ _ (by omega), P₂.isZero_of_isStrictlyLE b₂ _ (by omega)⟩
  exact ⟨_, min (a₁ - 1) a₂, max (b₁ - 1) b₂,
    CochainComplex.isStrictlyGE_mappingCone φ a₁ a₂ _, inferInstance,
    fun i ↦ finProj_of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl).symm
      (finProj_biprod (h₁ (i + 1)) (h₂ i)), ⟨Iso.refl _⟩⟩

/-- **Bounded complexes of finite projective objects are stable under extensions.** In a
distinguished triangle `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` with `K₁` and `K₃` bounded complexes of finite
projective objects, so is `K₂`, provided the unit is projective: the map `K₃ ⟶ K₁[1]` lifts to a
morphism of complexes, its source being K-projective, and `K₂[1]` is its mapping cone. -/
lemma finProjComplex_obj₂_of_distTriang [Projective (𝟙_ C)] (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (h₁ : finProjComplex C T.obj₁) (h₃ : finProjComplex C T.obj₃) :
    finProjComplex C T.obj₂ := by
  obtain ⟨P₁, a₁, b₁, _, _, hP₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨P₃, a₃, b₃, _, _, hP₃, ⟨e₃⟩⟩ := h₃
  have : ∀ n, Projective (P₃.X n) := fun n ↦ (hP₃ n).projective
  have : P₃.IsKProjective := CochainComplex.isKProjective_of_projective _ b₃
  have := P₁.isStrictlyGE_shift a₁ 1 (a₁ - 1) (by omega)
  have := P₁.isStrictlyLE_shift b₁ 1 (b₁ - 1) (by omega)
  obtain ⟨ψ, hψ⟩ := CochainComplex.IsKProjective.exists_Q_map_eq P₃ (P₁⟦(1 : ℤ)⟧)
    (e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧' ≫ ((Q.commShiftIso (1 : ℤ)).app P₁).inv)
  have hcomm : Q.map ψ ≫ ((Q.commShiftIso (1 : ℤ)).app P₁).hom ≫ e₁.inv⟦(1 : ℤ)⟧' =
      e₃.inv ≫ T.mor₃ := by
    rw [hψ]
    simp [← Functor.map_comp]
  obtain ⟨f, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _
    (mappingCone_triangle_distinguished ψ)
    (Pretriangulated.rot_of_distTriang _ (Pretriangulated.rot_of_distTriang _ hT))
    (Arrow.isoMk e₃.symm (((Q.commShiftIso (1 : ℤ)).app P₁) ≪≫ (shiftFunctor _ 1).mapIso e₁.symm)
      hcomm.symm)
  have hcone := finProjComplex_Q_obj_mappingCone ψ a₃ b₃ (a₁ - 1) (b₁ - 1) hP₃
    fun i ↦ finProj_of_iso (P₁.shiftFunctorObjXIso 1 i (i + 1) rfl).symm (hP₁ (i + 1))
  exact (finProjComplex C).prop_of_iso ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).app _)
    (((finProjComplex C).prop_of_iso (Triangle.π₃.mapIso f) hcone).shift (-1))

end FinProjComplex

section Dualizable

open MonoidalClosed

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]

attribute [local instance] Abelian.hasFiniteBiproducts

/-- A bounded complex of finite projective objects is dualizable in `D(C)`. -/
lemma finProjComplex.isDualizable {K : DerivedCategory C} (hK : finProjComplex C K) :
    IsDualizable K := by
  obtain ⟨P, a, b, _, _, hP, ⟨e⟩⟩ := hK
  exact IsDualizable.of_iso e.symm (isDualizable_Q_obj P a b fun n ↦ (hP n).isDualizable)

/-- A flat object placed in degree `n` has Tor amplitude in `[n, n]`. -/
lemma torAmplitudeIn_singleFunctor_obj_of_flat' {F : C} (hF : ObjectProperty.flat F) (n : ℤ) :
    torAmplitudeIn C n n ((singleFunctor C n).obj F) := by
  have : CochainComplex.IsStrictlyGE ((HomologicalComplex.single C (.up ℤ) n).obj F) n :=
    inferInstanceAs (CochainComplex.IsStrictlyGE ((CochainComplex.singleFunctor C n).obj F) n)
  have : CochainComplex.IsStrictlyLE ((HomologicalComplex.single C (.up ℤ) n).obj F) n :=
    inferInstanceAs (CochainComplex.IsStrictlyLE ((CochainComplex.singleFunctor C n).obj F) n)
  refine (torAmplitudeIn C n n).prop_of_iso ((singleFunctorIsoCompQ C n).app F).symm
    (torAmplitudeIn_Q_obj_of_flat _ n n fun i ↦ ?_)
  by_cases hi : i = n
  · subst hi
    exact ObjectProperty.prop_of_iso _ (HomologicalComplex.singleObjXSelf _ _ F).symm hF
  · exact ObjectProperty.flat_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)

/-- A dualizable object of `D(C)` is bounded: it is a retract of a bounded complex
(`DerivedCategory.exists_retract_of_exactPairing_of_projective_unit`). -/
lemma exists_isGE_isLE_of_isDualizable [Projective (𝟙_ C)]
    (hC : UnitFactorsThroughFiniteCoproducts C) (hT : UnitTensorFinite C)
    {K : DerivedCategory C} (hK : IsDualizable K) :
    ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b := by
  obtain ⟨_⟩ := hK
  obtain ⟨L, ι, _, a, b, _, _, -, w, hw⟩ := exists_retract_of_exactPairing_of_projective_unit
    hC hT K Kᘁ (Q.objPreimage K) (Q.objObjPreimageIso K).symm
  have h : homologyConcentratedIn a b K := (homologyConcentratedIn a b).prop_of_retract
    { i := w, r := Q.map ι ≫ (Q.objObjPreimageIso K).hom,
      retract := by simp [reassoc_of% hw] }
    ⟨inferInstance, inferInstance⟩
  exact ⟨a, b, h.1, h.2⟩

/-- If a dualizable object `K` of `D(C)` vanishes above `b`, its top homology `Hᵇ(K)` is a
quotient of a finite direct sum `𝟙ʳ`: `K` is a retract of a complex `L` vanishing above `b`
whose terms are quotients of finite direct sums `𝟙ʳ`, and `Hᵇ(L)` is a quotient of `Lᵇ`. -/
lemma exists_epi_homology_of_isDualizable [Projective (𝟙_ C)]
    (hC : UnitFactorsThroughFiniteCoproducts C) (hT : UnitTensorFinite C)
    {K : DerivedCategory C} (hK : IsDualizable K) (b : ℤ)
    [K.IsLE b] :
    ∃ (r : ℕ) (π : (⨁ fun _ : Fin r ↦ 𝟙_ C) ⟶ (homologyFunctor C b).obj K), Epi π := by
  obtain ⟨_⟩ := hK
  obtain ⟨M, _, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
  obtain ⟨L, ι, _, -, -, -, -, hL, w, hw⟩ :=
    exists_retract_of_exactPairing_of_projective_unit hC hT K Kᘁ M e
  have : L.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff L b).2 fun i hi ↦
    (M.isZero_of_isStrictlyLE b i hi).of_mono (ι.f i)
  obtain ⟨r, π, _⟩ := hL b
  have := L.isIso_iCycles b (b + 1) (by simp)
    ((L.isZero_of_isStrictlyLE b (b + 1) (by omega)).eq_of_tgt _ _)
  have : IsSplitEpi ((homologyFunctor C b).map (Q.map ι ≫ e.inv)) :=
    IsSplitEpi.mk' ⟨(homologyFunctor C b).map w, by
      rw [← Functor.map_comp, reassoc_of% hw, Iso.hom_inv_id, CategoryTheory.Functor.map_id]⟩
  exact ⟨r, π ≫ inv (L.iCycles b) ≫ L.homologyπ b ≫ ((homologyFunctorFactors C b).app L).inv ≫
    (homologyFunctor C b).map (Q.map ι ≫ e.inv), inferInstance⟩

/-- A dualizable object of `D(C)` vanishing above `b` has Tor amplitude in `[a, b]` for some
`a`: its dual is dualizable, hence bounded above. -/
lemma exists_torAmplitudeIn_of_isDualizable [Projective (𝟙_ C)]
    (hC : UnitFactorsThroughFiniteCoproducts C) (hT : UnitTensorFinite C)
    {K : DerivedCategory C} (hK : IsDualizable K)
    (b : ℤ) [K.IsLE b] : ∃ a, torAmplitudeIn C a b K := by
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ := nonempty_braidedCategory C
  let := BraidedCategory.exactPairing_swap K Kᘁ
  obtain ⟨-, b', -, hb'⟩ := exists_isGE_isLE_of_isDualizable hC hT (K := Kᘁ) ⟨⟨K⟩⟩
  exact ⟨-b', torAmplitudeIn_of_exactPairing_of_isLE (L := Kᘁ) b b'⟩

/-- **A quotient `H` of `𝟙ʳ` with `H[0]` dualizable of Tor amplitude `≥ 0` is finite
projective.** The Tor amplitude of `H[0]` is `[0, 0]`, so its dual `X` vanishes above `0`:
morphisms `X ⟶ Z` correspond to morphisms `𝟙 ⟶ H[0] ⊗ Z`. Hence for the kernel `G` of
`𝟙ʳ ⟶ H`, morphisms `H[0] ⟶ G[1]`, which correspond to morphisms `𝟙 ⟶ G[1] ⊗ X` into an object
vanishing above `-1`, are zero as `𝟙` is projective. So `𝟙ʳ ⟶ H` splits. -/
lemma finProj_of_isDualizable_singleFunctor_obj [Projective (𝟙_ C)]
    (hC : UnitFactorsThroughFiniteCoproducts C) (hT : UnitTensorFinite C)
    {H : C}
    (hH : IsDualizable ((singleFunctor C 0).obj H))
    (hGE : ∀ G : C, ((singleFunctor C 0).obj H ⊗ (singleFunctor C 0).obj G).IsGE 0)
    {r : ℕ} (π : (⨁ fun _ : Fin r ↦ 𝟙_ C) ⟶ H) [Epi π] : finProj C H := by
  set Y := (singleFunctor C 0).obj H
  obtain ⟨a, ha⟩ := exists_torAmplitudeIn_of_isDualizable hC hT hH 0
  have hY : torAmplitudeIn C 0 0 Y := fun G ↦ ⟨hGE G, (ha G).2⟩
  obtain ⟨_⟩ := hH
  have hU : (𝟙_ (DerivedCategory C)).IsLE 0 :=
    TStructure.t.isLE_of_iso (singleFunctorObjUnitIso C) 0
  -- the dual `X` of `H[0]` vanishes above `0`
  have hX : (Yᘁ).IsLE 0 := by
    refine (TStructure.t.isLE_iff_orthogonal 0 1 rfl _).2 fun Z f hZ ↦ ?_
    have : Z.IsGE 1 := hZ
    have := isGE_tensor_of_torAmplitudeIn hY Z 1
    have h : tensorLeftHomEquiv (𝟙_ _) Y Yᘁ Z ((ρ_ _).hom ≫ f) = 0 :=
      TStructure.t.zero _ 0 (0 + 1) (by omega)
    have h' : (ρ_ _).hom ≫ f = 0 := by
      rw [← (tensorLeftHomEquiv (𝟙_ _) Y Yᘁ Z).symm_apply_apply ((ρ_ _).hom ≫ f), h]
      simp [tensorLeftHomEquiv]
    rw [← cancel_epi (ρ_ _).hom, h', comp_zero]
  -- the extension `0 ⟶ G ⟶ 𝟙ʳ ⟶ H ⟶ 0` splits
  let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS : S.ShortExact := { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π) }
  have hδ : hS.singleδ = 0 := by
    let W := ((singleFunctor C 0).obj (kernel π))⟦(1 : ℤ)⟧
    have : W.IsLE (-1) := TStructure.t.isLE_shift _ 0 1 (-1) (by omega)
    have := isLE_tensor W Yᘁ (-1) 0
    have h : tensorRightHomEquiv (𝟙_ _) Y Yᘁ W ((λ_ Y).hom ≫ hS.singleδ) = 0 := by
      rw [← cancel_epi (singleFunctorObjUnitIso C).hom, comp_zero]
      exact eq_zero_of_isZero_homology_zero (𝟙_ C) _ (isZero_of_isLE _ (-1 + 0) 0 (by omega)) _
    have h' : (λ_ Y).hom ≫ hS.singleδ = 0 := by
      rw [← (tensorRightHomEquiv (𝟙_ _) Y Yᘁ W).symm_apply_apply ((λ_ Y).hom ≫ hS.singleδ), h]
      simp [tensorRightHomEquiv]
    rw [← cancel_epi (λ_ Y).hom, h', comp_zero]
  obtain ⟨s, hs⟩ := Triangle.coyoneda_exact₃ _ hS.singleTriangle_distinguished (𝟙 Y)
    (by simp [hδ])
  obtain ⟨s', rfl⟩ := (singleFunctor C 0).map_surjective s
  exact ⟨r, ⟨{ i := s', r := π, retract := (singleFunctor C 0).map_injective (by
    rw [Functor.map_comp, CategoryTheory.Functor.map_id]
    exact hs.symm) }⟩⟩

/-- If `K ⊗ G[0]` vanishes below `a` for every `G : C`, then so does `K`: take `G = 𝟙`. -/
lemma isGE_of_forall_isGE_tensor_singleFunctor_obj {K : DerivedCategory C} {a : ℤ}
    (hK : ∀ G : C, (K ⊗ (singleFunctor C 0).obj G).IsGE a) : K.IsGE a :=
  have := hK (𝟙_ C)
  TStructure.t.isGE_of_iso (whiskerLeftIso K (singleFunctorObjUnitIso C) ≪≫ ρ_ K) a

/-- The induction behind `DerivedCategory.exists_iso_Q_obj_of_isDualizable`: a dualizable object
`K` vanishing above `b`, such that `K ⊗ G[0]` vanishes below `a` for every `G : C`, is a bounded
complex of finite projective objects. By induction on `b - a`: if `a = b`, then `K = H[-a]` with
`H` finite projective (`DerivedCategory.finProj_of_isDualizable_singleFunctor_obj`); if `a < b`,
the cone of a map `𝟙ʳ[-b] ⟶ K` which is surjective on `Hᵇ` is dualizable, vanishes above `b - 1`
and has the same lower Tor bound `a`, and `K` is an extension of it by `𝟙ʳ[-b]`. -/
lemma finProjComplex_of_isDualizable_of_isLE [Projective (𝟙_ C)]
    (hC : UnitFactorsThroughFiniteCoproducts C) (hT : UnitTensorFinite C) (n : ℕ) :
    ∀ (K : DerivedCategory C) (a b : ℤ), b < a + n → IsDualizable K → K.IsLE b →
      (∀ G : C, (K ⊗ (singleFunctor C 0).obj G).IsGE a) → finProjComplex C K := by
  induction n with
  | zero =>
    intro K a b hab _ _ hGE
    have := isGE_of_forall_isGE_tensor_singleFunctor_obj hGE
    exact finProjComplex_of_isZero (TStructure.t.isZero K b a (by omega))
  | succ n ih =>
    intro K a b hab hK _ hGE
    by_cases hb : b < a + n
    · exact ih K a b hb hK inferInstance hGE
    have := isGE_of_forall_isGE_tensor_singleFunctor_obj hGE
    rcases n with _ | n
    · -- `K` is concentrated in degree `a`
      obtain rfl : b = a := by omega
      obtain ⟨H, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE K b
      let e' : (singleFunctor C 0).obj H ≅ K⟦b⟧ :=
        (((singleFunctors C).shiftIso b 0 b (by omega)).app H).symm ≪≫
          (shiftFunctor _ b).mapIso e.symm
      obtain ⟨r, π, _⟩ := exists_epi_homology_of_isDualizable hC hT hK b
      let eH : (homologyFunctor C b).obj K ≅ H :=
        (homologyFunctor C b).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso C b).app H
      have hH := finProj_of_isDualizable_singleFunctor_obj hC hT
        (IsDualizable.of_iso e'.symm (isDualizable_shift hK b)) (fun G ↦ ?_) (π ≫ eH.hom)
      · exact (finProjComplex C).prop_of_iso e.symm (finProjComplex_singleFunctor_obj hH b)
      · have := hGE G
        have : ((K ⊗ (singleFunctor C 0).obj G)⟦b⟧).IsGE 0 :=
          TStructure.t.isGE_shift _ b b 0 (by omega)
        have : ((tensorRight ((singleFunctor C 0).obj G) ⋙ shiftFunctor _ b).obj K).IsGE 0 :=
          this
        exact TStructure.t.isGE_of_iso (whiskerRightIso e' _ ≪≫
          ((tensorRight ((singleFunctor C 0).obj G)).commShiftIso b).app K).symm 0
    · -- kill the top homology `Hᵇ(K)` by a map `𝟙ʳ[-b] ⟶ K`
      obtain ⟨r, π, _⟩ := exists_epi_homology_of_isDualizable hC hT hK b
      let F := ⨁ fun _ : Fin r ↦ 𝟙_ C
      have : Projective F := projective_biproduct_const _ _
      have hF : finProj C F := ⟨r, ⟨Retract.refl _⟩⟩
      obtain ⟨f, hf⟩ := (homSingleEquivOfProjective F b K).surjective π
      obtain ⟨Z, g, h, hT'⟩ := distinguished_cocone_triangle f
      have h₁ := finProjComplex_singleFunctor_obj hF b
      have hZ : IsDualizable Z :=
        isDualizable_obj₃_of_distTriang (Triangle.mk f g h) hT' h₁.isDualizable hK
      have hf' : Epi ((homologyFunctor C b).map f) := by
        have : (homologyFunctor C b).map f =
            ((singleFunctorCompHomologyFunctorIso C b).app F).hom ≫ π := by
          rw [← hf]
          simp [homSingleToHomology]
        rw [this]
        infer_instance
      have hZle : Z.IsLE (b - 1) := by
        rw [isLE_iff]
        intro i hi
        have hepi : Epi ((homologyFunctor C i).map g) :=
          (HomologySequence.epi_homologyMap_mor₂_iff _ hT' i (i + 1) rfl).2
            ((isZero_of_isLE ((singleFunctor C b).obj F) b (i + 1) (by omega)).eq_of_tgt _ _)
        have hzero : (homologyFunctor C i).map g = 0 := by
          obtain rfl | hi' := eq_or_ne i b
          · exact (HomologySequence.epi_homologyMap_mor₁_iff _ hT' i).1 hf'
          · exact (isZero_of_isLE K b i (by omega)).eq_of_src _ _
        rw [hzero] at hepi
        exact IsZero.of_epi_zero ((homologyFunctor C i).obj K) ((homologyFunctor C i).obj Z)
      have hZge (G : C) : (Z ⊗ (singleFunctor C 0).obj G).IsGE a := by
        have hT₂ := (tensorRight ((singleFunctor C 0).obj G)).map_distinguished _
          (rot_of_distTriang _ hT')
        refine TStructure.t.isGE₂ _ hT₂ a (hGE G) ?_
        have : ((singleFunctor C (b - 1)).obj F ⊗ (singleFunctor C 0).obj G).IsGE (b - 1) :=
          (torAmplitudeIn_singleFunctor_obj_of_flat' (isDualizable_biproduct_unit r).flat
            (b - 1) G).1
        have : ((singleFunctor C (b - 1)).obj F ⊗ (singleFunctor C 0).obj G).IsGE a :=
          TStructure.t.isGE_of_ge _ a (b - 1) (by omega)
        exact TStructure.t.isGE_of_iso
          (whiskerRightIso (((singleFunctors C).shiftIso 1 (b - 1) b (by omega)).app F) _).symm a
      exact finProjComplex_obj₂_of_distTriang _ hT' h₁
        (ih Z a (b - 1) (by omega) hZ hZle hZge)

/-- **Dualizable objects are bounded complexes of finite projective objects.** Let `C` be a
braided monoidal closed Grothendieck abelian category with functorial flat resolutions, whose
unit `𝟙` is projective, with morphisms from `𝟙` finite on coproducts and on tensor products
(as for sheaves of modules on the pro-étale site of a weakly contractible affine scheme). Then
every dualizable object of `D(C)` is isomorphic to a bounded complex of retracts of finite direct
sums `𝟙ʳ` (the forward direction of Stacks 0FPV in this setting).

The object `K` is bounded, vanishing above some `b`, and has Tor amplitude in `[a, b]` for some
`a`; conclude by `DerivedCategory.finProjComplex_of_isDualizable_of_isLE`. -/
theorem exists_iso_Q_obj_of_isDualizable [Projective (𝟙_ C)]
    (hC : UnitFactorsThroughFiniteCoproducts C) (hT : UnitTensorFinite C)
    {K : DerivedCategory C} (hK : IsDualizable K) :
    ∃ (P : CochainComplex C ℤ) (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ n, finProj C (P.X n)) ∧ Nonempty (K ≅ Q.obj P) := by
  obtain ⟨-, b, -, hb⟩ := exists_isGE_isLE_of_isDualizable hC hT hK
  obtain ⟨a, ha⟩ := exists_torAmplitudeIn_of_isDualizable hC hT hK b
  exact finProjComplex_of_isDualizable_of_isLE hC hT (b - a + 1).toNat K a b (by omega) hK hb
    fun G ↦ (ha G).1

end Dualizable

end DerivedCategory
