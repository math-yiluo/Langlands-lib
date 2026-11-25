/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyColimitTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeGE
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Cohomology of a derived tensor product along a filtered colimit

Let `C` be a closed braided monoidal Grothendieck abelian category with functorial flat
resolutions, in which every object is flat (for instance sheaves of vector spaces). Let
`c` be a cocone in `D(C)` of a diagram `F` indexed by a category `J` along which colimits in `C`
are exact, such that all `F.obj j` and `c.pt` vanish in degrees `< a` and the cohomology objects
of `c` are colimits. Then for every `W ∈ D(C)` vanishing in degrees `< b`, the cohomology objects
of `c ⊗ᴸ W` are colimits
(`DerivedCategory.nonempty_isColimit_homologyFunctor_tensorRight_mapCocone`).

The proof:
* for `W = M[0]`, `- ⊗ᴸ M[0]` is the functor `D(- ⊗ M)` induced by the exact functor `- ⊗ M`
  (`DerivedCategory.tensorRightSingleFunctorIso`, `M[0]` being K-flat), so
  `Hᵠ(Y ⊗ᴸ M[0]) ≅ Hᵠ(Y) ⊗ M`, which commutes with colimits;
* the class of such `W` is stable under shifts and under extensions (five lemma for colimits,
  `DerivedCategory.nonempty_isColimit_homologyFunctor_mapCocone_π₂`, applied to `Y ⊗ᴸ -` of a
  distinguished triangle), hence contains bounded objects;
* for `W` bounded below, `Hᵠ(Y ⊗ᴸ τ^{≤ m} W) ≅ Hᵠ(Y ⊗ᴸ W)` for `Y` vanishing below `a` and
  `m ≥ q - a`, since `Y ⊗ᴸ τ^{≥ m + 1} W` vanishes below `a + m + 1` (Tor amplitude).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

section Single

variable (M : C)

/-- For a flat object `M`, the derived tensor product `Q(L) ⊗ᴸ M[0]` is the complex `L`
tensored termwise by `M`, naturally in the complex `L`. -/
noncomputable def qCompTensorRightSingleFunctorIso (hM : ObjectProperty.flat M) :
    Q ⋙ tensorRight ((singleFunctor C 0).obj M) ≅
      ((curriedTensor C).flip.obj M).mapHomologicalComplex (.up ℤ) ⋙ Q :=
  NatIso.ofComponents (fun L ↦ whiskerLeftIso (Q.obj L) ((singleFunctorIsoCompQ C 0).app M) ≪≫
      QObjTensorQObjIsoOfKFlatRight L ((HomologicalComplex.single C (.up ℤ) 0).obj M)
        ((CochainComplex.kFlat_single_obj_iff_flat M 0).2 hM) ≪≫
      Q.mapIso ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor C) M).app L))
    (fun {L L'} f ↦ by
      dsimp
      rw [whiskerLeftIso_hom, whiskerLeftIso_hom, ← whisker_exchange_assoc]
      erw [qObjTensorQObjIsoOfKFlatRight_hom_naturality_assoc]
      simp only [Category.assoc, ← Q.map_comp]
      congr 3
      exact (CochainComplex.map₂HomologicalComplexFlipObjSingleIso
        (curriedTensor C) M).hom.naturality f)

variable [PreservesFiniteLimits ((curriedTensor C).flip.obj M)]
  [PreservesFiniteColimits ((curriedTensor C).flip.obj M)]

/-- For a flat object `M`, the derived tensor product `- ⊗ᴸ M[0]` is the functor induced on
derived categories by the exact functor `- ⊗ M`. -/
noncomputable def tensorRightSingleFunctorIso (hM : ObjectProperty.flat M) :
    tensorRight ((singleFunctor C 0).obj M) ≅
      ((curriedTensor C).flip.obj M).mapDerivedCategory :=
  letI : Localization.Lifting Q (HomologicalComplex.quasiIso C (.up ℤ))
      (Q ⋙ tensorRight ((singleFunctor C 0).obj M))
      ((curriedTensor C).flip.obj M).mapDerivedCategory :=
    ⟨((curriedTensor C).flip.obj M).mapDerivedCategoryFactors ≪≫
      (qCompTensorRightSingleFunctorIso M hM).symm⟩
  Localization.liftNatIso Q (HomologicalComplex.quasiIso C (.up ℤ))
    (Q ⋙ tensorRight ((singleFunctor C 0).obj M)) (Q ⋙ tensorRight ((singleFunctor C 0).obj M))
    _ _ (Iso.refl _)

/-- For a flat object `M`, `Hᵠ(Y ⊗ᴸ M[0]) ≅ Hᵠ(Y) ⊗ M`, naturally in `Y`. -/
noncomputable def tensorRightSingleFunctorCompHomologyFunctorIso (hM : ObjectProperty.flat M)
    (q : ℤ) :
    tensorRight ((singleFunctor C 0).obj M) ⋙ homologyFunctor C q ≅
      homologyFunctor C q ⋙ (curriedTensor C).flip.obj M :=
  Functor.isoWhiskerRight (tensorRightSingleFunctorIso M hM) _ ≪≫
    (((curriedTensor C).flip.obj M).mapDerivedCategoryHomologyFunctorIso q).symm

end Single

variable {J : Type*} [Category J] {F : J ⥤ DerivedCategory C} (c : Cocone F)

/-- The property of `W ∈ D(C)` that the cohomology objects of `c ⊗ᴸ W` are colimits. -/
def HomologyTensorRightIsColimit (W : DerivedCategory C) : Prop :=
  ∀ q, Nonempty (IsColimit ((tensorRight W ⋙ homologyFunctor C q).mapCocone c))

variable {c}

lemma HomologyTensorRightIsColimit.of_iso {W W' : DerivedCategory C} (e : W ≅ W')
    (h : HomologyTensorRightIsColimit c W) : HomologyTensorRightIsColimit c W' := fun q ↦
  (h q).map fun h ↦ IsColimit.mapCoconeEquiv
    (Functor.isoWhiskerRight ((tensoringRight _).mapIso e) _) h

/-- Flat objects placed in degree `0` have the property `HomologyTensorRightIsColimit`, when
the cohomology objects of `c` are colimits. -/
lemma homologyTensorRightIsColimit_singleFunctor
    (hc : ∀ p, Nonempty (IsColimit ((homologyFunctor C p).mapCocone c)))
    (M : C) (hM : ObjectProperty.flat M)
    [PreservesColimitsOfShape J ((curriedTensor C).flip.obj M)] :
    HomologyTensorRightIsColimit c ((singleFunctor C 0).obj M) := fun q ↦ by
  have : PreservesFiniteLimits ((curriedTensor C).flip.obj M) := hM.tensorRight.1
  have : PreservesFiniteColimits ((curriedTensor C).flip.obj M) := hM.tensorRight.2
  obtain ⟨h⟩ := hc q
  have h' : IsColimit ((homologyFunctor C q ⋙ (curriedTensor C).flip.obj M).mapCocone c) :=
    IsColimit.ofIsoColimit (isColimitOfPreserves ((curriedTensor C).flip.obj M) h)
      (Functor.mapCoconeMapCocone c)
  exact ⟨IsColimit.mapCoconeEquiv (tensorRightSingleFunctorCompHomologyFunctorIso M hM q).symm h'⟩

/-- `HomologyTensorRightIsColimit` is stable under shifts. -/
lemma HomologyTensorRightIsColimit.shift {W : DerivedCategory C}
    (h : HomologyTensorRightIsColimit c W) (n : ℤ) :
    HomologyTensorRightIsColimit c (W⟦n⟧) := fun q ↦ by
  let e : tensorRight (W⟦n⟧) ≅ tensorRight W ⋙ shiftFunctor (DerivedCategory C) n :=
    NatIso.ofComponents (fun Y ↦ (((curriedTensor (DerivedCategory C)).obj Y).commShiftIso n).app W)
      (fun {Y Y'} f ↦ by
        have := Functor.CommShift₂.commShift_map (G := curriedTensor (DerivedCategory C))
          (h := .int) f
        exact (NatTrans.shift_app_comm ((curriedTensor (DerivedCategory C)).map f) n W).symm)
  exact (h (n + q)).map fun h ↦ IsColimit.mapCoconeEquiv
    (Functor.isoWhiskerLeft _ ((homologyFunctor C 0).shiftIso n q (n + q) rfl).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e.symm _) h

/-- For a triangle `Δ` of `D(C)`, the functor `Y ↦ Y ⊗ᴸ Δ`. -/
noncomputable def tensorLeftMapTriangle (Δ : Triangle (DerivedCategory C)) :
    DerivedCategory C ⥤ Triangle (DerivedCategory C) where
  obj Y := ((curriedTensor (DerivedCategory C)).obj Y).mapTriangle.obj Δ
  map {Y Y'} f :=
    letI := Functor.CommShift₂.commShift_map (G := curriedTensor (DerivedCategory C)) (h := .int) f
    (NatTrans.mapTriangle ((curriedTensor (DerivedCategory C)).map f)).app Δ
  map_id Y := by
    ext <;> simp
  map_comp f g := by
    ext <;> simp

variable [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]

/-- `HomologyTensorRightIsColimit` is stable under extensions. -/
lemma HomologyTensorRightIsColimit.ext₂ (Δ : Triangle (DerivedCategory C))
    (hΔ : Δ ∈ distTriang _) (h₁ : HomologyTensorRightIsColimit c Δ.obj₁)
    (h₃ : HomologyTensorRightIsColimit c Δ.obj₃) :
    HomologyTensorRightIsColimit c Δ.obj₂ :=
  nonempty_isColimit_homologyFunctor_mapCocone_π₂ (tensorLeftMapTriangle Δ)
    (fun Y ↦ ((curriedTensor (DerivedCategory C)).obj Y).map_distinguished Δ hΔ) c h₁ h₃

/-- Bounded objects whose cohomology objects are flat have the property
`HomologyTensorRightIsColimit`. -/
lemma homologyTensorRightIsColimit_of_isGE_of_isLE
    (hC : ∀ M : C, ObjectProperty.flat M)
    [∀ M : C, PreservesColimitsOfShape J ((curriedTensor C).flip.obj M)]
    (hc : ∀ p, Nonempty (IsColimit ((homologyFunctor C p).mapCocone c))) (b : ℤ) :
    ∀ (k : ℕ) (W : DerivedCategory C), W.IsGE b → W.IsLE (b + k) →
      HomologyTensorRightIsColimit c W := by
  have hsingle (n : ℤ) (M : C) :
      HomologyTensorRightIsColimit c ((singleFunctor C n).obj M) :=
    ((homologyTensorRightIsColimit_singleFunctor hc M (hC M)).shift (-n)).of_iso
      (((singleFunctors C).shiftIso (-n) n 0 (by simp)).app M)
  have hconc (W : DerivedCategory C) (n : ℤ) (h₁ : W.IsGE n) (h₂ : W.IsLE n) :
      HomologyTensorRightIsColimit c W := by
    obtain ⟨M, ⟨e⟩⟩ := W.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
    exact (hsingle n M).of_iso e.symm
  intro k
  induction k with
  | zero =>
    intro W h₁ h₂
    exact hconc W b h₁ (by simpa using h₂)
  | succ k ih =>
    intro W h₁ h₂
    refine HomologyTensorRightIsColimit.ext₂ _
      (TStructure.t.triangleLEGE_distinguished (b + k) (b + k + 1) rfl W) ?_ ?_
    · exact ih _ (inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLE (b + k)).obj W) b))
        (inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncLE (b + k)).obj W) (b + k)))
    · have : W.IsLE (b + k + 1) := by
        have := h₂
        push_cast at this
        rwa [← add_assoc] at this
      exact hconc _ (b + k + 1)
        (inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncGE (b + k + 1)).obj W) _))
        (inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE (b + k + 1)).obj W) _))

/-- Let `α : G₁ ⟶ G₂` be a natural transformation which is an isomorphism at the objects of a
cocone `c` and of its diagram. If `G₁` sends `c` to a colimit cocone, so does `G₂`. -/
noncomputable def _root_.CategoryTheory.Limits.IsColimit.mapCoconeOfNatTrans {D E : Type*}
    [Category D]
    [Category E] {K : J ⥤ D} {d : Cocone K} {G₁ G₂ : D ⥤ E} (α : G₁ ⟶ G₂)
    (hK : ∀ j, IsIso (α.app (K.obj j))) (hd : IsIso (α.app d.pt))
    (h : IsColimit (G₁.mapCocone d)) : IsColimit (G₂.mapCocone d) :=
  let e : K ⋙ G₁ ≅ K ⋙ G₂ :=
    NatIso.ofComponents (fun j ↦ asIso (α.app (K.obj j))) (fun f ↦ α.naturality _)
  (IsColimit.precomposeHomEquiv e (G₂.mapCocone d)).1 (IsColimit.ofIsoColimit h
    (Cocone.ext (asIso (α.app d.pt)) (fun j ↦ by simp [e])))

/-- **Cohomology of a derived tensor product along a filtered colimit**: if every object of `C`
is flat, `c` is a cocone in `D(C)` of objects vanishing below `a` whose cohomology objects are
colimits, and `W` is bounded below, then the cohomology objects of `c ⊗ᴸ W` are colimits. -/
theorem nonempty_isColimit_homologyFunctor_tensorRight_mapCocone
    (hC : ∀ M : C, ObjectProperty.flat M)
    [∀ M : C, PreservesColimitsOfShape J ((curriedTensor C).flip.obj M)] (a : ℤ)
    (hF : ∀ j, (F.obj j).IsGE a) (hc : c.pt.IsGE a)
    (hH : ∀ p, Nonempty (IsColimit ((homologyFunctor C p).mapCocone c)))
    (W : DerivedCategory C) (b : ℤ) [W.IsGE b] (q : ℤ) :
    Nonempty (IsColimit ((tensorRight W ⋙ homologyFunctor C q).mapCocone c)) := by
  -- the truncation `τ^{≤ m} W` with `q ≤ a + m`
  let m := max b (q - a)
  have hT := TStructure.t.triangleLEGE_distinguished m (m + 1) rfl W
  have hiso (Y : DerivedCategory C) (hY : Y.IsGE a) :
      IsIso ((homologyFunctor C q).map (Y ◁ (TStructure.t.truncLEι m).app W)) := by
    have hT' := ((curriedTensor (DerivedCategory C)).obj Y).map_distinguished _ hT
    have : (Y ⊗ (TStructure.t.truncGE (m + 1)).obj W).IsGE (a + (m + 1)) :=
      have : ((TStructure.t.truncGE (m + 1)).obj W).IsGE (m + 1) :=
        inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncGE (m + 1)).obj W) _)
      isGE_tensor_of_torAmplitudeGE_right (fun M ↦ by
          have := isGE_tensor_of_torAmplitudeGE_right
            (torAmplitudeGE_of_torAmplitudeIn (torAmplitudeIn_singleFunctor_obj_of_flat (hC M)))
            ((TStructure.t.truncGE (m + 1)).obj W) (m + 1)
          rwa [add_zero] at this) Y a
    have h₁ : Mono ((homologyFunctor C q).map (Y ◁ (TStructure.t.truncLEι m).app W)) :=
      (HomologySequence.mono_homologyMap_mor₁_iff _ hT' (q - 1) q (by lia)).2
        ((isZero_of_isGE _ (a + (m + 1)) (q - 1) (by lia) (hX := this)).eq_of_src _ _)
    have h₂ : Epi ((homologyFunctor C q).map (Y ◁ (TStructure.t.truncLEι m).app W)) :=
      (HomologySequence.epi_homologyMap_mor₁_iff _ hT' q).2
        ((isZero_of_isGE _ (a + (m + 1)) q (by lia) (hX := this)).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m = b + k := ⟨(m - b).toNat, by lia⟩
  obtain ⟨h⟩ := homologyTensorRightIsColimit_of_isGE_of_isLE hC hH b k
    ((TStructure.t.truncLE m).obj W)
    (inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLE m).obj W) b))
    (hk ▸ inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncLE m).obj W) m)) q
  exact ⟨IsColimit.mapCoconeOfNatTrans
    (Functor.whiskerRight ((tensoringRight _).map ((TStructure.t.truncLEι m).app W)) _)
    (fun j ↦ hiso _ (hF j)) (hiso _ hc) h⟩

end DerivedCategory
