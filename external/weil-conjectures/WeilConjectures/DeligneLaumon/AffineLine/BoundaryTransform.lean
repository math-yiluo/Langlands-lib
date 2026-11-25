/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CurveEndpoints
public import WeilConjectures.WeilSheaf.FiniteEtale
public import WeilConjectures.WeilSheaf.LowerShriekPackage
public import WeilConjectures.WeilSheaf.ShiftedSheaf

/-!
# The Fourier transform of the boundary sheaf

Let `M` be a lisse Weil sheaf on a dense open `j : U₀ ↪ 𝔸¹` with finite complement, and let
`B = j_*M / j_!M` be its boundary sheaf. Then `FT_ψ(B) ≅ B'[1]` for a lisse Weil sheaf `B'` on
the dual line (Steps 1–3 of `lemma-fourier-transform-boundary-sequence`).

Let `i : Z₀ ↪ 𝔸¹` be the reduced closed complement of `U₀`, a finite étale `k₀`-scheme. Since `B`
vanishes on `U₀`, the open–closed triangle gives `B ≅ i_* E` with `E = i^* B`. Writing
`i' : Z₀ × 𝔸¹ ↪ 𝔸¹ × 𝔸¹` for the base change of `i` along the first projection, `q` for the
projection to `Z₀` and `π = pr₂ ∘ i' : Z₀ × 𝔸¹ ⟶ 𝔸¹`, which is finite étale, compact support
base change, the projection formula and the composition law give

`FT_ψ(i_* E) ≅ Rπ_!(q^*E ⊗ i'^*𝓚_ψ)[1]`.

As `π` is finite, `Rπ_!` of the sheaf `q^*E ⊗ i'^*𝓚_ψ` is the sheaf `π_*(q^*E ⊗ i'^*𝓚_ψ)` in
degree zero; it is lisse, since `q^*E ⊗ i'^*𝓚_ψ` is lisse and `π` becomes a trivial covering
after base change to `k̄`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.exists_isReduced_isClosedImmersion_range_eq_compl`:
  the reduced closed complement of `U₀`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.exists_isLisse_iso_fourierTransform_boundarySheaf'`:
  `FT_ψ(B) ≅ B'[1]` with `B'` lisse.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The tensor product of a lisse Weil sheaf `L` with a Weil sheaf `G` placed in degree zero is
the tensor product sheaf `L ⊗ G` placed in degree zero: the internal hom out of the lisse
`L^∨` is exact. -/
noncomputable def tensorLisseObjToComplexIso (L : WeilSheaf k₀ l X) (hL : L.IsLisse)
    (G : WeilSheaf k₀ l X) :
    (tensorLisse L hL).obj (WeilSheaf.toComplex.obj G) ≅
      WeilSheaf.toComplex.obj (L.tensorObj G hL) :=
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (L.dual hL).obj hL.dual
  ObjectProperty.isoMk _
    ((ProEtaleWeilSheaf.ihomFunctor k₀ l X (L.dual hL).obj).singleFunctorCompRightDerivedFunctorIso
      |>.app G.obj)

end WeilComplex

omit [Finite k₀] in
/-- The reduced closed complement `Z₀` of a dense open `U₀` of the affine line, a finite
reduced `k₀`-scheme. -/
lemma exists_isReduced_isClosedImmersion_range_eq_compl {U : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ affineLine k₀) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j] :
    ∃ (Z : Scheme.{u}) (_ : Z.Over (Spec (CommRingCat.of k₀))) (i : Z ⟶ affineLine k₀)
      (_ : IsClosedImmersion i) (_ : i.IsOver (Spec (CommRingCat.of k₀)))
      (_ : IsFinite (Z ↘ Spec (CommRingCat.of k₀))) (_ : IsReduced Z),
      Set.range i.base = (Set.range j.base)ᶜ := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  have : GeometricallyConnected (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) :=
    GeometricallyConnected.of_geometricallyIrreducible _
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩ :
      TopologicalSpace.Closeds (affineLine k₀))
  have hI : Set.range I.subschemeι.base = (Set.range j.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  let : I.subscheme.Over (Spec (CommRingCat.of k₀)) :=
    ⟨I.subschemeι ≫ affineLine k₀ ↘ Spec (CommRingCat.of k₀)⟩
  have : I.subschemeι.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have hfin : Finite I.subscheme := by
    have := (finite_compl_range_of_isDominant (k₀ := k₀) j).to_subtype
    rw [← hI] at this
    exact Finite.of_equiv _ (Equiv.ofInjective _ I.subschemeι.isClosedEmbedding.injective).symm
  have : LocallyOfFiniteType (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    show LocallyOfFiniteType (I.subschemeι ≫ affineLine k₀ ↘ _) from inferInstance
  have : LocallyQuasiFinite (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    .of_finite_preimage_singleton _ fun _ ↦ Set.toFinite _
  exact ⟨I.subscheme, inferInstance, I.subschemeι, inferInstance, inferInstance,
    IsFinite.of_locallyQuasiFinite _, inferInstance, hI⟩

namespace WeilSheaf

open WeilComplex

/-- **The transform of the direct image of a sheaf on a closed subscheme** (Steps 2–3 of
`lemma-fourier-transform-boundary-sequence`). Let `i : Z₀ ↪ 𝔸¹` be a closed immersion, `X'` the base
change of `i` along the first projection of `𝔸¹ × 𝔸¹`, with projections `q : X' ⟶ Z₀` and
`i' : X' ⟶ 𝔸¹ × 𝔸¹`, and `π = pr₂ ∘ i'` finite. For a Weil sheaf `E` on `Z₀`,
`FT_ψ(i_! E) ≅ (π_*(i'^* 𝓚_ψ ⊗ q^* E))[1]`: compact support base change, the projection formula
and the composition law give `FT_ψ(i_! E) ≅ Rπ_!(i'^*𝓚_ψ ⊗ q^*E)[1]`, and `Rπ_!` of a sheaf is
the sheaf `π_*` in degree zero since `π` is finite. -/
theorem nonempty_iso_fourierTransform_derivedLowerShriek_of_isPullback
    (ψ : AddChar k₀ (PadicAlgCl l))
    {Z X' : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [X'.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀))]
    (i : Z ⟶ affineLine k₀) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (q : X' ⟶ Z) [q.IsOver (Spec (CommRingCat.of k₀))]
    (i' : X' ⟶ affinePlane k₀) [i'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated i']
    [LocallyOfFiniteType i'] [QuasiCompact i']
    (π : X' ⟶ affineLine k₀) [π.IsOver (Spec (CommRingCat.of k₀))] [IsFinite π]
    (hπ : i' ≫ affinePlane.snd k₀ = π) (hP : IsPullback q i' i (affinePlane.fst k₀))
    (E : WeilSheaf k₀ l Z) :
    Nonempty ((fourierTransform ψ).obj
        ((derivedLowerShriek k₀ l i).obj (WeilSheaf.toComplex.obj E)) ≅
      WeilSheaf.toShiftedComplex.obj ((WeilSheaf.lowerStar π).obj
        (((WeilSheaf.upperStar i').obj (fourierKernel ψ)).tensorObj
          ((WeilSheaf.upperStar q).obj E)
          (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_fourierKernel ψ))))) := by
  have : QuasiCompact (affinePlane.fst k₀) := MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiSeparated (affinePlane.fst k₀) := MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiCompact (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (affinePlane.fst k₀ ≫ _))
  have : QuasiSeparated (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiSeparated (affinePlane.fst k₀ ≫ _))
  set K := (derivedLowerShriek k₀ l i).obj (WeilSheaf.toComplex.obj E)
  -- Step 2: base change, the projection formula and composition
  obtain ⟨e₂⟩ := nonempty_upperStarDerivedLowerShriekIso_of_isPullback hP
    (WeilSheaf.toComplex.obj E)
  obtain ⟨e₃⟩ := nonempty_tensorLisseDerivedLowerShriekIso i' (fourierKernel ψ)
    (isLisse_fourierKernel ψ) ((WeilComplex.upperStar q).obj (WeilSheaf.toComplex.obj E))
  obtain ⟨eC⟩ := nonempty_derivedLowerShriekCompIso (k₀ := k₀) (l := l) i'
    (affinePlane.snd k₀) π hπ
  let L : WeilSheaf k₀ l X' := (WeilSheaf.upperStar i').obj (fourierKernel ψ)
  have hL : L.IsLisse := ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_fourierKernel ψ)
  let E' : WeilSheaf k₀ l X' := (WeilSheaf.upperStar q).obj E
  let G : WeilSheaf k₀ l X' := L.tensorObj E' hL
  let e₅ : (WeilComplex.upperStar q).obj (WeilSheaf.toComplex.obj E) ≅
      WeilSheaf.toComplex.obj E' :=
    (toComplexCompUpperStarIso q).app _
  let Kπ := (derivedLowerShriek k₀ l π).obj (WeilSheaf.toComplex.obj G)
  let e : (fourierTransform ψ).obj K ≅ Kπ⟦(1 : ℤ)⟧ :=
    (shiftFunctor _ (1 : ℤ)).mapIso
      ((derivedLowerShriek k₀ l (affinePlane.snd k₀)).mapIso
          ((tensorLisse (fourierKernel ψ) (isLisse_fourierKernel ψ)).mapIso e₂ ≪≫ e₃) ≪≫
        (eC.app _).symm ≪≫
        (derivedLowerShriek k₀ l π).mapIso
          ((tensorLisse L hL).mapIso e₅ ≪≫ tensorLisseObjToComplexIso L hL E'))
  -- Step 3: `Rπ_! G` is the sheaf `π_* G` in degree zero
  have hneg (r : ℤ) (hr : r < 0) : IsZero ((homologySheaf r).obj Kπ) :=
    WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg (f := π) G hr
  have hpos (r : ℕ) (hr : 0 < r) : IsZero ((homologySheaf r).obj Kπ) :=
    isZero_higherLowerShriek_of_quasiFinite π r hr G
  obtain ⟨eP⟩ := nonempty_derivedLowerShriekIsoDerivedLowerStar (l := l) π
    (WeilSheaf.toComplex.obj G)
  let e₀ : (homologySheaf 0).obj Kπ ≅ (WeilSheaf.lowerStar π).obj G :=
    (homologySheaf 0).mapIso eP ≪≫ homologySheafZeroDerivedLowerStarIso π G
  have hFT (a : ℤ) (ha : a ≠ -1) :
      IsZero ((homologySheaf a).obj ((fourierTransform ψ).obj K)) := by
    refine IsZero.of_iso ?_ ((homologySheaf a).mapIso e ≪≫ homologySheafShiftIso Kπ 1 a (1 + a) rfl)
    rcases lt_or_gt_of_ne (show 1 + a ≠ 0 by omega) with h | h
    · exact hneg _ h
    · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h.le
      rw [hn]
      exact hpos n (by omega)
  obtain ⟨eF⟩ := nonempty_iso_toShiftedComplex _ hFT
  exact ⟨eF ≪≫ WeilSheaf.toShiftedComplex.mapIso ((homologySheaf (-1)).mapIso e ≪≫
    homologySheafShiftIso Kπ 1 (-1) 0 rfl ≪≫ e₀)⟩

/-- **The transform of a punctual sheaf, explicitly** (Steps 1–3 of
`lemma-fourier-transform-boundary-sequence`). Let `F` be a Weil sheaf on the affine line vanishing
on a dense open `U₀` with closed complement `i : Z₀ ↪ 𝔸¹`, and let `X'` be the base change of `i`
along the first projection of `𝔸¹ × 𝔸¹`, with projections `q : X' ⟶ Z₀` and `i' : X' ⟶ 𝔸¹ × 𝔸¹`, and
`π = pr₂ ∘ i'` finite. Then `FT_ψ(F) ≅ (π_*(i'^* 𝓚_ψ ⊗ q^* i^* F))[1]`: `F ≅ i_* i^* F`, compact
support base change, the projection formula and the composition law give
`FT_ψ(i_* E) ≅ Rπ_!(i'^*𝓚_ψ ⊗ q^*E)[1]`, and `Rπ_!` of a sheaf is the sheaf `π_*` in degree zero
since `π` is finite. -/
theorem nonempty_iso_fourierTransform_toComplex_of_isPullback
    (ψ : AddChar k₀ (PadicAlgCl l)) {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ affineLine k₀) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))]
    {Z X' : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [X'.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀))]
    (i : Z ⟶ affineLine k₀) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hi : Set.range i.base = (Set.range j.base)ᶜ)
    (q : X' ⟶ Z) [q.IsOver (Spec (CommRingCat.of k₀))]
    (i' : X' ⟶ affinePlane k₀) [i'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated i']
    [LocallyOfFiniteType i'] [QuasiCompact i']
    (π : X' ⟶ affineLine k₀) [π.IsOver (Spec (CommRingCat.of k₀))] [IsFinite π]
    (hπ : i' ≫ affinePlane.snd k₀ = π) (hP : IsPullback q i' i (affinePlane.fst k₀))
    (F : WeilSheaf k₀ l (affineLine k₀)) (hF : IsZero ((WeilSheaf.upperStar j).obj F)) :
    Nonempty ((fourierTransform ψ).obj (WeilSheaf.toComplex.obj F) ≅
      WeilSheaf.toShiftedComplex.obj ((WeilSheaf.lowerStar π).obj
        (((WeilSheaf.upperStar i').obj (fourierKernel ψ)).tensorObj
          ((WeilSheaf.upperStar q).obj ((WeilSheaf.upperStar i).obj F))
          (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_fourierKernel ψ))))) := by
  have : QuasiCompact (affinePlane.fst k₀) := MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiSeparated (affinePlane.fst k₀) := MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiCompact (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (affinePlane.fst k₀ ≫ _))
  have : QuasiSeparated (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiSeparated (affinePlane.fst k₀ ≫ _))
  -- Step 1: `F ≅ i_* i^* F`
  set K := WeilSheaf.toComplex.obj F
  obtain ⟨α, β, γ, hT⟩ := exists_distTriang_derivedLowerShriek_openClosed_comp j i hi (𝟙 _) j i
    (Category.comp_id _) (Category.comp_id _) K
  have h₁ : IsZero ((derivedLowerShriek k₀ l j).obj ((WeilComplex.upperStar j).obj K)) :=
    (derivedLowerShriek k₀ l j).map_isZero
      ((WeilSheaf.toComplex.map_isZero hF).of_iso ((toComplexCompUpperStarIso j).app F))
  have : IsIso β := (Triangle.isZero₁_iff_isIso₂ _ hT).1 h₁
  obtain ⟨eId⟩ := nonempty_derivedLowerShriekIdIso (k₀ := k₀) (l := l) (affineLine k₀) K
  let e₁ : K ≅ (derivedLowerShriek k₀ l i).obj ((WeilComplex.upperStar i).obj K) :=
    eId.symm ≪≫ asIso β
  exact ⟨(fourierTransform ψ).mapIso (e₁ ≪≫ (derivedLowerShriek k₀ l i).mapIso
      ((toComplexCompUpperStarIso i).app F)) ≪≫
    (nonempty_iso_fourierTransform_derivedLowerShriek_of_isPullback ψ i q i' π hπ hP
      ((WeilSheaf.upperStar i).obj F)).some⟩

/-- **The transform of a punctual sheaf** (Steps 1–3 of
`lemma-fourier-transform-boundary-sequence`). Let `F` be a Weil sheaf on the affine line vanishing
on a dense open `U₀`. Then `FT_ψ(F) ≅ B'[1]` for a lisse Weil sheaf `B'` on the dual line: with
`i : Z₀ ↪ 𝔸¹` the reduced closed complement of `U₀`, `F ≅ i_* i^* F` and
`B' = π_*(q^* i^* F ⊗ i'^* 𝓚_ψ)` for the finite étale projection `π : Z₀ × 𝔸¹ ⟶ 𝔸¹`
(`AlgebraicGeometry.WeilSheaf.nonempty_iso_fourierTransform_toComplex_of_isPullback`). -/
theorem exists_isLisse_iso_fourierTransform_of_isZero_upperStar
    (ψ : AddChar k₀ (PadicAlgCl l)) {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ affineLine k₀) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j]
    (F : WeilSheaf k₀ l (affineLine k₀)) (hF : IsZero ((WeilSheaf.upperStar j).obj F)) :
    ∃ B' : WeilSheaf k₀ l (affineLine k₀), B'.IsLisse ∧
      Nonempty ((fourierTransform ψ).obj (WeilSheaf.toComplex.obj F) ≅
        WeilSheaf.toShiftedComplex.obj B') := by
  obtain ⟨Z, _, i, _, _, _, _, hi⟩ := exists_isReduced_isClosedImmersion_range_eq_compl j
  let X' := pullback i (affinePlane.fst k₀)
  let q : X' ⟶ Z := pullback.fst i (affinePlane.fst k₀)
  let i' : X' ⟶ affinePlane k₀ := pullback.snd i (affinePlane.fst k₀)
  let : X'.Over (Spec (CommRingCat.of k₀)) := ⟨i' ≫ affinePlane k₀ ↘ Spec (CommRingCat.of k₀)⟩
  have : i'.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : q.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change q ≫ Z ↘ Spec (CommRingCat.of k₀) = i' ≫ affinePlane.fst k₀ ≫ _
    rw [← comp_over i (Spec (CommRingCat.of k₀)), ← Category.assoc, pullback.condition,
      Category.assoc]⟩
  let π : X' ⟶ affineLine k₀ := i' ≫ affinePlane.snd k₀
  have hP : IsPullback q π (Z ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    have := (IsPullback.of_hasPullback i (affinePlane.fst k₀)).paste_vert
      (IsPullback.of_hasPullback (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    rwa [comp_over] at this
  have : IsFinite π := MorphismProperty.of_isPullback hP inferInstance
  have : LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (i' ≫ _))
  obtain ⟨e⟩ := nonempty_iso_fourierTransform_toComplex_of_isPullback ψ j i hi q i' π rfl
    (IsPullback.of_hasPullback i (affinePlane.fst k₀)) F hF
  let L : WeilSheaf k₀ l X' := (WeilSheaf.upperStar i').obj (fourierKernel ψ)
  have hL : L.IsLisse := ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_fourierKernel ψ)
  let E : WeilSheaf k₀ l X' := (WeilSheaf.upperStar q).obj ((WeilSheaf.upperStar i).obj F)
  have hE : E.IsLisse :=
    ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_of_isFinite_of_isReduced _)
  let G : WeilSheaf k₀ l X' := L.tensorObj E hL
  have hG : G.IsLisse := ProEtale.IsAdicLisseSheaf.ihom (IsLisse.dual hL) hE
  exact ⟨(WeilSheaf.lowerStar π).obj G, isLisse_lowerStar_of_isPullback hP G hG, ⟨e⟩⟩

end WeilSheaf

end AlgebraicGeometry
