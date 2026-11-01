import Langlands.AlgebraicGeometry.Modules.BiCech.SectionsIso
import Langlands.AlgebraicGeometry.Modules.BiCech.Comparison
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Cohomology of an external tensor product of line bundles via Čech complexes

Let `X`, `Y` be quasi-compact schemes separated over `Spec R`, with fibre product `P`, and let
`L`, `M` be line bundles on `X`, `Y`. There are finite ordered affine covers `𝒰` of `X` and `𝒱`
of `Y` on whose members `L` and `M` have frames (`exists_frameCover`). For such covers the
cohomology `Hⁿ(P, p₁^* L ⊗ p₂^* M)` is the `n`-th cohomology of the tensor total complex of
the Čech cochain complexes `C(𝒰, L)` and `C(𝒱, M)`: by `BiCech.Comparison` it is the cohomology
of the global sections of the bi-Čech complex, which `BiCech.SectionsIso` identifies with that
total complex. The external tensor product is a line bundle, hence quasi-coherent, because the
cup of local frames is a local frame.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
  MonoidalCategory

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.BiCech

open CechResolution Scheme.Modules OModulePresheaf Langlands.AlgebraicGeometry.Picard

section Frames

variable {X : Scheme.{u}} {L : X.Modules}

/-- A locally free sheaf of rank one has a frame on a neighbourhood of every point. -/
lemma exists_isFrameOn_of_isLocallyFreeRankOne (hL : IsLocallyFreeRankOne L) (x : X) :
    ∃ (T : X.Opens) (_ : x ∈ T) (e : Γ(L, T)), IsFrameOn e T := by
  obtain ⟨T, hxT, ⟨eT⟩⟩ := hL x
  obtain ⟨e, he⟩ := exists_isFrameOn_of_pullback_iso_unit T
    (((Scheme.Modules.restrictFunctorIsoPullback T.ι).app L).symm ≪≫ eT)
  exact ⟨T, hxT, e, he⟩

/-- A quasi-compact scheme with a locally free sheaf of rank one has a finite ordered affine
cover on whose members the sheaf has frames. -/
theorem exists_frameCover [CompactSpace X] (hL : IsLocallyFreeRankOne L) :
    ∃ 𝒰 : X.OrderedAffineCover, ∀ i, ∃ e : Γ(L, 𝒰.U i), IsFrameOn e (𝒰.U i) := by
  classical
  let B : Set X.Opens := {U | IsAffineOpen U ∧ ∃ e : Γ(L, U), IsFrameOn e U}
  have hB : Opens.IsBasis B := by
    rw [Opens.isBasis_iff_nbhd]
    intro W x hx
    obtain ⟨T, hxT, e, he⟩ := exists_isFrameOn_of_isLocallyFreeRankOne hL x
    obtain ⟨U, hU, hxU, hUWT⟩ :=
      (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (show x ∈ W ⊓ T from ⟨hx, hxT⟩)
    exact ⟨U, ⟨hU, L.presheaf.map (homOfLE (hUWT.trans inf_le_right)).op e,
      (he.map _).mono (hUWT.trans inf_le_right)⟩, hxU, hUWT.trans inf_le_left⟩
  obtain ⟨Us, hUs, hfinite, hcover⟩ :=
    hB.exists_finite_of_isCompact (U := ⊤) (show IsCompact (⊤ : X.Opens).carrier from
      isCompact_univ)
  let : Fintype Us := hfinite.fintype
  let : LinearOrder Us :=
    LinearOrder.lift' (Fintype.equivFin Us) (Fintype.equivFin Us).injective
  exact ⟨{
    ι := Us
    U := Subtype.val
    isAffineOpen := fun i => (hUs i.property).1
    iSup_eq_top := by
      simpa only [sSup_eq_iSup'] using hcover.symm }, fun i => (hUs i.property).2⟩

/-- Frames on the members of a cover restrict to frames on all finite intersections. -/
lemma frames_inter {𝒰 : X.OrderedAffineCover} (h : ∀ i, ∃ e : Γ(L, 𝒰.U i), IsFrameOn e (𝒰.U i))
    (p : ℕ) (s : 𝒰.Idx p) : ∃ e : Γ(L, 𝒰.inter s), IsFrameOn e (𝒰.inter s) := by
  obtain ⟨e, he⟩ := h (s.1 0)
  exact ⟨L.presheaf.map (homOfLE (𝒰.inter_le s 0)).op e, (he.map _).mono (𝒰.inter_le s 0)⟩

/-- The external tensor product of locally free sheaves of rank one is locally free of rank
one. -/
lemma isLocallyFreeRankOne_extTensor {P Y : Scheme.{u}} (f : P ⟶ X) (g : P ⟶ Y) {M : Y.Modules}
    (hL : IsLocallyFreeRankOne L) (hM : IsLocallyFreeRankOne M) :
    IsLocallyFreeRankOne (extTensor f g L M) := by
  intro x
  obtain ⟨T, hxT, e, he⟩ := exists_isFrameOn_of_isLocallyFreeRankOne hL (f x)
  obtain ⟨T', hxT', e', he'⟩ := exists_isFrameOn_of_isLocallyFreeRankOne hM (g x)
  let W := f ⁻¹ᵁ T ⊓ g ⁻¹ᵁ T'
  have hε := isFrameOn_cup (le_refl W) he he'
  exact ⟨W, ⟨hxT, hxT'⟩, ⟨((Scheme.Modules.restrictFunctorIsoPullback W.ι).app _) ≪≫
    (hε.nonempty_pullback_iso_unit W le_rfl le_rfl).some⟩⟩

end Frames

section Product

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {πP : P ⟶ Spec R} (hπ : p₁ ≫ πX = πP)
  (hP : IsPullback p₁ p₂ πX πY) {L : X.Modules} {M : Y.Modules}

include hπ hP in
/-- For covers on whose members `L` and `M` have frames, `Hⁿ(P, p₁^* L ⊗ p₂^* M)` is the
`n`-th cohomology of the tensor total complex of the Čech cochain complexes. -/
theorem nonempty_relativeCohomology_extTensor_iso [IsSeparated πX] [IsSeparated πY]
    [IsSeparated πP] (hL : IsLocallyFreeRankOne L) (hM : IsLocallyFreeRankOne M)
    (𝒰 : X.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
    (hfX : ∀ i, ∃ e : Γ(L, 𝒰.U i), IsFrameOn e (𝒰.U i))
    (hfY : ∀ j, ∃ e : Γ(M, 𝒱.U j), IsFrameOn e (𝒱.U j)) (n : ℕ) :
    Nonempty ((DerivedSections.relativeCohomology πP n).obj (extTensor p₁ p₂ L M) ≅
      (totCech πX πY 𝒰 𝒱 L M).homology n) := by
  have : (extTensor p₁ p₂ L M).IsQuasicoherent :=
    (isLocallyFreeRankOne_extTensor p₁ p₂ hL hM).isQuasicoherent
  obtain ⟨e⟩ := nonempty_relativeCohomology_iso_bicech_homology πP (prodBiCover p₁ p₂ 𝒰 𝒱)
    (extTensor p₁ p₂ L M)
    (fun s t => Picard.FieldTwoAxisH1Injectivity.isAffineOpen_prodOpen hP
      (isAffineOpen_inter πX 𝒰 s) (isAffineOpen_inter πY 𝒱 t)) n
  exact ⟨e ≪≫ (HomologicalComplex.homologyFunctor _ _ n).mapIso
    (sectionsIso hπ hP 𝒰 𝒱 L M (fun p s => isAffineOpen_inter πX 𝒰 s)
      (fun q t => isAffineOpen_inter πY 𝒱 t) (frames_inter hfX) (frames_inter hfY)).symm⟩

end Product

section OverProduct

variable {K : Type u} [CommRing K] (X Y : Over (Spec (CommRingCat.of K)))

/-- The projections of a product in `Over (Spec K)` form a pullback square of schemes. -/
lemma isPullback_overProd :
    IsPullback (Limits.prod.fst : X ⨯ Y ⟶ X).left (Limits.prod.snd : X ⨯ Y ⟶ Y).left X.hom
      Y.hom :=
  Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk Limits.prod.fst Limits.prod.snd)
    (prodIsProd X Y)

lemma isSeparated_overProd [IsSeparated X.hom] [IsSeparated Y.hom] :
    IsSeparated (X ⨯ Y).hom := by
  have : IsSeparated (Limits.prod.fst : X ⨯ Y ⟶ X).left :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (isPullback_overProd X Y).flip
      inferInstance
  rw [← Over.w (Limits.prod.fst : X ⨯ Y ⟶ X)]
  infer_instance

/-- For quasi-compact schemes `X`, `Y` separated over `Spec K` and line bundles `L`, `M`, there
are finite ordered affine covers `𝒰`, `𝒱` such that `Hⁿ(X ×_K Y, p₁^* L ⊗ p₂^* M)` is the
`n`-th cohomology of the tensor total complex of `C(𝒰, L)` and `C(𝒱, M)`. -/
theorem exists_nonempty_relativeCohomology_overProd_iso [IsSeparated X.hom] [IsSeparated Y.hom]
    [CompactSpace X.left] [CompactSpace Y.left] (L : LineBundle X.left) (M : LineBundle Y.left)
    (n : ℕ) :
    ∃ (𝒰 : X.left.OrderedAffineCover) (𝒱 : Y.left.OrderedAffineCover),
      Nonempty ((DerivedSections.relativeCohomology (X ⨯ Y).hom n).obj
          (Langlands.Scheme.Modules.tensorObj
            ((Scheme.Modules.pullback (Limits.prod.fst : X ⨯ Y ⟶ X).left).obj L.obj)
            ((Scheme.Modules.pullback (Limits.prod.snd : X ⨯ Y ⟶ Y).left).obj M.obj)) ≅
        (HomologicalComplex.mapBifunctor (cechCochainComplex X.hom 𝒰 L.obj)
          (cechCochainComplex Y.hom 𝒱 M.obj) (curriedTensor (ModuleCat.{u} (CommRingCat.of K)))
          (ComplexShape.up ℕ)).homology n) := by
  obtain ⟨𝒰, h𝒰⟩ := exists_frameCover L.property
  obtain ⟨𝒱, h𝒱⟩ := exists_frameCover M.property
  have := isSeparated_overProd X Y
  exact ⟨𝒰, 𝒱, nonempty_relativeCohomology_extTensor_iso (Over.w _) (isPullback_overProd X Y)
    L.property M.property 𝒰 𝒱 h𝒰 h𝒱 n⟩

end OverProduct

end Langlands.AlgebraicGeometry.Modules.BiCech
