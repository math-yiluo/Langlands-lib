import Langlands.AlgebraicGeometry.Picard.LinearSystemGluing
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected
import Langlands.AlgebraicGeometry.GeometricallyIntegralConnected

/-! # The glued universal divisor and the universal property of the glued scheme

The local universal divisors glue to an ideal sheaf on `Y ×_S G` over the glued scheme `G`.
Every divisor of the linear system over a locally noetherian test is the pullback of the glued
divisor along exactly one point of `G` (the local points on a test cover glue), the glued
divisor is relative effective Cartier, and its class is `[m] + [n]` for a class `n` on `G`
(by descent along `p_* O = O`). Morphism properties local on the target and stable under base
change pass from the local families to `G`. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemGluing

open PicardHilbertPiecesReduction (mapX mapX_comp mapX_congr mapX_fst mapX_snd mapX_snd_assoc dcl dcl_congr
  pb_comp_apply pb_iso_inv_hom pb_mapX_fst)
open Langlands.AbelianScheme.SmoothFamilyOpenCover (SubOpens isBasis_subOpens basisCover
  basisCover_trans_ι range_comp_ι_subset idx le_idx)

section Classes

/-- Picard classes are trivial on small opens. -/
lemma exists_open_pullback_eq_zero {T : Scheme.{u}} (x : Group T) (z : T) :
    ∃ U : T.Opens, z ∈ U ∧ Group.pullback U.ι x = 0 := by
  let N := Group.lineBundleRepresentative T x
  obtain ⟨O, hzO, t, ht⟩ := SectionZeroIdeal.exists_affine_frame N z
  obtain ⟨eO⟩ := ht.nonempty_pullback_iso_unit O.1 le_rfl le_rfl
  refine ⟨O.1, hzO, ?_⟩
  rw [← Group.classOf_lineBundleRepresentative T x, Group.pullback_lineBundle_classOf,
    ← LineBundle.classOf_trivial, LineBundle.classOf_eq_iff]
  exact ⟨eO⟩

/-- A class trivial on an open subscheme `Z'` with image `q⁻¹ U'` is trivial on `q⁻¹ U'`. -/
lemma pullback_ι_eq_zero_of_range {Z T : Scheme.{u}} (q : Z ⟶ T) (x : Group Z) (U' : T.Opens)
    {Z' : Scheme.{u}} (jZ : Z' ⟶ Z) [IsOpenImmersion jZ] (hr : Set.range jZ = q ⁻¹' U')
    (h0 : Group.pullback jZ x = 0) : Group.pullback (q ⁻¹ᵁ U').ι x = 0 := by
  have hr' : Set.range jZ = Set.range (q ⁻¹ᵁ U').ι := by
    rw [hr, Scheme.Opens.range_ι]
    rfl
  let iso := IsOpenImmersion.isoOfRangeEq jZ (q ⁻¹ᵁ U').ι hr'
  have hfac : iso.hom ≫ (q ⁻¹ᵁ U').ι = jZ := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have h2 : Group.pullback iso.hom (Group.pullback (q ⁻¹ᵁ U').ι x) = 0 := by
    rw [← pb_comp_apply, hfac, h0]
  rw [← pb_iso_inv_hom iso (Group.pullback _ x), h2, map_zero]

end Classes

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {m : Group Y}

namespace LocalData

variable {ι : Type u} {W : ι → S.Opens} (A : LocalData g m W)
  (hW : TopologicalSpace.IsOpenCover W)

/-- The cover of `Y ×_S G` by the pieces `Y ×_S P_V`. -/
def ycover : (pullback g (A.lG hW)).OpenCover :=
  Scheme.Cover.mkOfCovers (basisCover W hW).I₀ (fun V => pullback g (A.lp V))
    (fun V => mapX g (A.ιV hW V) (A.ιV_lG hW V)) (fun y => by
      let z := (pullback.snd g (A.lG hW)).base y
      obtain ⟨p, hp⟩ := (A.gluingData hW).cover.covers z
      refine ⟨(A.gluingData hW).cover.idx z, ?_⟩
      have : y ∈ Set.range (mapX g (A.ιV hW ((A.gluingData hW).cover.idx z))
          (A.ιV_lG hW _)) := by
        rw [range_mapX]
        exact ⟨p, hp⟩
      exact this) (fun _ => inferInstance)

/-- **Compatibility of the local divisors on overlaps.** -/
lemma compat ⦃V₁ V₂ : (basisCover W hW).I₀⦄ ⦃Z : Scheme.{u}⦄
    (a : Z ⟶ pullback g (A.lp V₁)) (b : Z ⟶ pullback g (A.lp V₂))
    (hab : a ≫ mapX g (A.ιV hW V₁) (A.ιV_lG hW V₁) = b ≫ mapX g (A.ιV hW V₂) (A.ιV_lG hW V₂)) :
    (A.Dp V₁).comap a = (A.Dp V₂).comap b := by
  let V₃ : (basisCover W hW).I₀ := ⟨V₁.1 ⊓ V₂.1, ⟨idx V₁, inf_le_left.trans (le_idx V₁)⟩⟩
  let c := a ≫ mapX g (A.ιV hW V₁) (A.ιV_lG hW V₁)
  have hc₁ : c ≫ pullback.snd g (A.lG hW) ≫ A.lG hW =
      a ≫ pullback.snd g (A.lp V₁) ≫ A.lp V₁ := by
    rw [Category.assoc, mapX_snd_assoc, A.ιV_lG]
  have hc₂ : c ≫ pullback.snd g (A.lG hW) ≫ A.lG hW =
      b ≫ pullback.snd g (A.lp V₂) ≫ A.lp V₂ := by
    change (a ≫ _) ≫ _ = _
    rw [hab, Category.assoc, mapX_snd_assoc, A.ιV_lG]
  have hrange : Set.range ((c ≫ pullback.snd g (A.lG hW)) ≫ A.lG hW) ⊆ (V₃.1 : Set S) := by
    rintro _ ⟨z, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, hc₁]
      exact A.range_lp V₁ ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans
        (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rw [Category.assoc, hc₂]
      exact A.range_lp V₂ ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans
        (Scheme.Hom.comp_apply _ _ _).symm⟩
  have hr : Set.range c ⊆ Set.range (mapX g (A.ιV hW V₃) (A.ιV_lG hW V₃)) := by
    rw [range_mapX]
    rintro _ ⟨z, rfl⟩
    exact A.mem_range_ιV hW _ hrange ⟨z, (Scheme.Hom.comp_apply _ _ _)⟩
  let a₃ := IsOpenImmersion.lift (mapX g (A.ιV hW V₃) (A.ιV_lG hW V₃)) c hr
  have ha₃ : a₃ ≫ mapX g (A.ιV hW V₃) (A.ιV_lG hW V₃) = c := IsOpenImmersion.lift_fac _ _ _
  have h31 : V₃.1 ≤ V₁.1 := inf_le_left
  have h32 : V₃.1 ≤ V₂.1 := inf_le_right
  have key : ∀ (V : (basisCover W hW).I₀) (h : V₃.1 ≤ V.1) (a' : Z ⟶ pullback g (A.lp V)),
      a' ≫ mapX g (A.ιV hW V) (A.ιV_lG hW V) = c →
        (A.Dp V).comap a' = (A.Dp V₃).comap a₃ := by
    intro V h a' ha'
    have e : a' = a₃ ≫ mapX g (A.transition h) (A.transition_lp h) := by
      rw [← cancel_mono (mapX g (A.ιV hW V) (A.ιV_lG hW V)), ha', Category.assoc,
        mapX_comp, ← ha₃]
      exact congrArg _ (mapX_congr g (A.transition_ιV hW (homOfLE h)) _ _).symm
    rw [e, Scheme.IdealSheafData.comap_comp, A.transition_D]
  rw [key V₁ h31 a rfl, key V₂ h32 b hab.symm]

/-- **The glued universal divisor.** -/
theorem exists_glued_divisor : ∃ Wd : (pullback g (A.lG hW)).IdealSheafData,
    ∀ V : (basisCover W hW).I₀,
      Wd.comap (mapX g (A.ιV hW V) (A.ιV_lG hW V)) = A.Dp V :=
  Scheme.IdealSheafData.exists_comap_eq_of_openCover (A.ycover hW) (fun V => A.Dp V)
    (fun _ _ _ a b hab => A.compat hW a b hab)

variable {A hW} {Wd : (pullback g (A.lG hW)).IdealSheafData}
  (hWd : ∀ V : (basisCover W hW).I₀,
    Wd.comap (mapX g (A.ιV hW V) (A.ιV_lG hW V)) = A.Dp V)

lemma range_testCover {T : Scheme.{u}} (t : T ⟶ S) (V : (basisCover W hW).I₀) :
    Set.range (((basisCover W hW).pullback₁ t).f V ≫ t) ⊆ (V.1 : Set S) := by
  have e : ((basisCover W hW).pullback₁ t).f V ≫ t =
      pullback.snd t ((basisCover W hW).f V) ≫ (basisCover W hW).f V := pullback.condition
  rw [e]
  exact range_comp_ι_subset V.1 _

set_option maxHeartbeats 1000000 in
include hWd in
/-- **Existence of classifying points for the glued family.** -/
theorem glued_exists_point (T : Scheme.{u}) [IsLocallyNoetherian T] (t : T ⟶ S)
    (E : (pullback g t).IdealSheafData) (hE : LS g m t E) :
    ∃ (k : T ⟶ A.glued hW) (hk : k ≫ A.lG hW = t), Wd.comap (mapX g k hk) = E := by
  let 𝒯 : T.OpenCover := (basisCover W hW).pullback₁ t
  have hN : ∀ V, IsLocallyNoetherian (𝒯.X V) := fun V => by
    change IsLocallyNoetherian (pullback t ((basisCover W hW).f V))
    infer_instance
  have hloc : ∀ V : (basisCover W hW).I₀, ∃ (k : 𝒯.X V ⟶ A.param V)
      (hk : k ≫ A.lp V = 𝒯.f V ≫ t),
      (A.Dp V).comap (mapX g k hk) = E.comap (mapX g (𝒯.f V) rfl) := fun V =>
    (A.universal_param V).exists_point (𝒯.X V) (𝒯.f V ≫ t) (range_testCover t V) _
      (hE.comap (𝒯.f V) rfl)
  choose kV hkV hkVE using hloc
  have hcompat : ∀ {i j : (basisCover W hW).I₀} (hij : i ⟶ j),
      𝒯.trans hij ≫ (kV j ≫ A.ιV hW j) = kV i ≫ A.ιV hW i := by
    intro i j hij
    have hT : 𝒯.trans hij ≫ 𝒯.f j = 𝒯.f i := 𝒯.trans_map hij
    have w' : 𝒯.trans hij ≫ 𝒯.f j ≫ t = 𝒯.f i ≫ t := by rw [← Category.assoc, hT]
    have h₁ : (𝒯.trans hij ≫ kV j) ≫ A.lp j = 𝒯.f i ≫ t := by
      rw [Category.assoc, hkV, w']
    have h₂ : (kV i ≫ A.transition (leOfHom hij)) ≫ A.lp j = 𝒯.f i ≫ t := by
      rw [Category.assoc, A.transition_lp, hkV]
    have c₁ : mapX g (𝒯.trans hij ≫ kV j) h₁ =
        mapX g (𝒯.trans hij) w' ≫ mapX g (kV j) (hkV j) :=
      (mapX_comp g (kV j) (hkV j) (𝒯.trans hij) w').symm
    have c₂ : mapX g (𝒯.trans hij) w' ≫ mapX g (𝒯.f j) (rfl : 𝒯.f j ≫ t = _) =
        mapX g (𝒯.f i) (rfl : 𝒯.f i ≫ t = _) :=
      (mapX_comp g (𝒯.f j) rfl (𝒯.trans hij) w').trans (mapX_congr g hT _ _)
    have c₃ : mapX g (kV i ≫ A.transition (leOfHom hij)) h₂ =
        mapX g (kV i) (hkV i) ≫ mapX g (A.transition (leOfHom hij)) (A.transition_lp _) :=
      (mapX_comp g _ (A.transition_lp _) (kV i) (hkV i)).symm
    have heq : 𝒯.trans hij ≫ kV j = kV i ≫ A.transition (leOfHom hij) := by
      refine (A.universal_param j).eq_of_comap_eq (𝒯.X i) (𝒯.f i ≫ t) _ _ h₁ h₂ ?_
      rw [c₁, Scheme.IdealSheafData.comap_comp, hkVE, ← Scheme.IdealSheafData.comap_comp, c₂,
        c₃, Scheme.IdealSheafData.comap_comp, A.transition_D, hkVE]
    rw [← Category.assoc, heq, Category.assoc, A.transition_ιV hW hij]
  let k : T ⟶ A.glued hW := 𝒯.glueMorphismsOfLocallyDirected (fun V => kV V ≫ A.ιV hW V)
    hcompat
  have hkι : ∀ V, 𝒯.f V ≫ k = kV V ≫ A.ιV hW V := fun V =>
    𝒯.map_glueMorphismsOfLocallyDirected _ hcompat V
  have hk : k ≫ A.lG hW = t := 𝒯.hom_ext _ _ fun V => by
    rw [← Category.assoc, hkι, Category.assoc, A.ιV_lG, hkV]
  refine ⟨k, hk, ?_⟩
  refine Langlands.AlgebraicGeometry.IdealSheafGluing.eq_of_comap_eq'
    (fun V => mapX g (𝒯.f V) (rfl : 𝒯.f V ≫ t = _)) ?_ fun V => ?_
  · intro y
    obtain ⟨p, hp⟩ := 𝒯.covers ((pullback.snd g t).base y)
    exact ⟨𝒯.idx _, by rw [range_mapX]; exact ⟨p, hp⟩⟩
  · have d₁ : mapX g (𝒯.f V) (rfl : 𝒯.f V ≫ t = _) ≫ mapX g k hk =
        mapX g (kV V) (hkV V) ≫ mapX g (A.ιV hW V) (A.ιV_lG hW V) :=
      (mapX_comp g k hk (𝒯.f V) rfl).trans ((mapX_congr g (hkι V) _ _).trans
        (mapX_comp g _ (A.ιV_lG hW V) (kV V) (hkV V)).symm)
    rw [← Scheme.IdealSheafData.comap_comp, d₁, Scheme.IdealSheafData.comap_comp, hWd, hkVE]

set_option maxHeartbeats 1000000 in
include hWd in
/-- **Uniqueness of classifying points for the glued family.** -/
theorem glued_eq_of_comap_eq (T : Scheme.{u}) [IsLocallyNoetherian T] (t : T ⟶ S)
    (k₁ k₂ : T ⟶ A.glued hW) (hk₁ : k₁ ≫ A.lG hW = t) (hk₂ : k₂ ≫ A.lG hW = t)
    (h : Wd.comap (mapX g k₁ hk₁) = Wd.comap (mapX g k₂ hk₂)) : k₁ = k₂ := by
  let 𝒯 : T.OpenCover := (basisCover W hW).pullback₁ t
  refine 𝒯.hom_ext _ _ fun V => ?_
  have : IsLocallyNoetherian (𝒯.X V) := by
    change IsLocallyNoetherian (pullback t ((basisCover W hW).f V))
    infer_instance
  have hrange : ∀ k : T ⟶ A.glued hW, k ≫ A.lG hW = t →
      Set.range ((𝒯.f V ≫ k) ≫ A.lG hW) ⊆ (V.1 : Set S) := by
    intro k hk
    rw [Category.assoc, hk]
    exact range_testCover t V
  have hD : ∀ (μ : 𝒯.X V ⟶ A.param V) (k : T ⟶ A.glued hW) (hk : k ≫ A.lG hW = t)
      (hμ : μ ≫ A.ιV hW V = 𝒯.f V ≫ k) (e : μ ≫ A.lp V = 𝒯.f V ≫ t),
      (A.Dp V).comap (mapX g μ e) =
        (Wd.comap (mapX g k hk)).comap (mapX g (𝒯.f V) (rfl : 𝒯.f V ≫ t = _)) := by
    intro μ k hk hμ e
    have d : mapX g μ e ≫ mapX g (A.ιV hW V) (A.ιV_lG hW V) =
        mapX g (𝒯.f V) (rfl : 𝒯.f V ≫ t = _) ≫ mapX g k hk :=
      (mapX_comp g _ (A.ιV_lG hW V) μ e).trans ((mapX_congr g hμ _ _).trans
        (mapX_comp g k hk (𝒯.f V) rfl).symm)
    rw [← hWd V, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, d]
  obtain ⟨μ₁, hμ₁⟩ : ∃ μ : 𝒯.X V ⟶ A.param V, μ ≫ A.ιV hW V = 𝒯.f V ≫ k₁ :=
    ⟨IsOpenImmersion.lift _ _ (A.mem_range_ιV hW _ (hrange k₁ hk₁)),
      IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨μ₂, hμ₂⟩ : ∃ μ : 𝒯.X V ⟶ A.param V, μ ≫ A.ιV hW V = 𝒯.f V ≫ k₂ :=
    ⟨IsOpenImmersion.lift _ _ (A.mem_range_ιV hW _ (hrange k₂ hk₂)),
      IsOpenImmersion.lift_fac _ _ _⟩
  have e₁ : μ₁ ≫ A.lp V = 𝒯.f V ≫ t := by
    rw [← A.ιV_lG hW, ← Category.assoc, hμ₁, Category.assoc, hk₁]
  have e₂ : μ₂ ≫ A.lp V = 𝒯.f V ≫ t := by
    rw [← A.ιV_lG hW, ← Category.assoc, hμ₂, Category.assoc, hk₂]
  have hμ : μ₁ = μ₂ := (A.universal_param V).eq_of_comap_eq _ _ μ₁ μ₂ e₁ e₂
    (by rw [hD μ₁ k₁ hk₁ hμ₁ e₁, hD μ₂ k₂ hk₂ hμ₂ e₂, h])
  rw [← hμ₁, ← hμ₂, hμ]

include hWd in
/-- **The glued divisor is relative effective Cartier.** -/
theorem glued_isRelativeEffective :
    IsRelativeEffectiveCartierIdeal (pullback.snd g (A.lG hW)) Wd := by
  refine RelativeEffectiveLocal.isRelativeEffectiveCartierIdeal_of_cover
    (pullback.snd g (A.lG hW)) Wd
    (fun V : (basisCover W hW).I₀ => mapX g (A.ιV hW V) (A.ιV_lG hW V))
    (fun V => pullback.snd g (A.lp V)) (fun V => A.ιV hW V) (fun V => mapX_snd g _ _)
    (fun y => ⟨(A.ycover hW).idx y, (A.ycover hW).covers y⟩) (fun V => ?_) (fun V z => ?_)
  · rw [hWd V]
    exact (A.universal_param V).ls.1
  · rw [hWd V]
    obtain ⟨h, -⟩ := (A.universal_param V).ls
    exact exists_local_regular_generator_of_isEffectiveCartierIdeal _ h.1 z

set_option maxHeartbeats 1000000 in
include hWd in
/-- **The class of the glued divisor is `[m] + [n]` for a class `n` on the glued scheme.** -/
theorem glued_class [IsProper g] [Flat g] [LocallyOfFinitePresentation g]
    [GeometricallyIntegral g]
    (hrel : IsRelativeEffectiveCartierIdeal (pullback.snd g (A.lG hW)) Wd) :
    ∃ n : Group (A.glued hW), dcl Wd hrel.1 =
      Group.pullback (pullback.fst g (A.lG hW)) m +
        Group.pullback (pullback.snd g (A.lG hW)) n := by
  have : GeometricallyConnected (pullback.snd g (A.lG hW)) :=
    Langlands.AbelianScheme.TranslationOfSmoothFamily.geometricallyConnected_of_geometricallyIntegral _
  have hq : ∀ U : (A.glued hW).Opens, Function.Bijective ((pullback.snd g (A.lG hW)).app U) :=
    fun U => bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected
      _ U
  let x := dcl Wd hrel.1 - Group.pullback (pullback.fst g (A.lG hW)) m
  have hx : ∀ z : A.glued hW, ∃ U : (A.glued hW).Opens, z ∈ U ∧
      Group.pullback ((pullback.snd g (A.lG hW)) ⁻¹ᵁ U).ι x = 0 := by
    intro z
    obtain ⟨p, hp⟩ := (A.gluingData hW).cover.covers z
    obtain ⟨hE, n, hn⟩ := (A.universal_param ((A.gluingData hW).cover.idx z)).ls
    obtain ⟨U, hpU, hU⟩ := exists_open_pullback_eq_zero n p
    let V := (A.gluingData hW).cover.idx z
    have hw : (U.ι ≫ A.ιV hW V) ≫ A.lG hW = U.ι ≫ A.lp V := by
      rw [Category.assoc, A.ιV_lG]
    refine ⟨(U.ι ≫ A.ιV hW V).opensRange, ?_, ?_⟩
    · refine ⟨⟨p, hpU⟩, ?_⟩
      rw [Scheme.Hom.comp_apply]
      exact hp
    · refine pullback_ι_eq_zero_of_range _ x _ (mapX g (U.ι ≫ A.ιV hW V) hw) ?_ ?_
      · rw [range_mapX]
        rfl
      · have e : mapX g (U.ι ≫ A.ιV hW V) hw =
            mapX g U.ι (rfl : U.ι ≫ A.lp V = _) ≫ mapX g (A.ιV hW V) (A.ιV_lG hW V) :=
          (mapX_comp g _ (A.ιV_lG hW V) U.ι rfl).symm
        obtain ⟨h1, hd1⟩ := PicardHilbertPiecesReduction.flat_comap
          (mapX g (A.ιV hW V) (A.ιV_lG hW V)) (pullback.snd g (A.lG hW)) Wd hrel
        have hcl : Group.pullback (mapX g (A.ιV hW V) (A.ιV_lG hW V)) x =
            Group.pullback (pullback.snd g (A.lp V)) n := by
          change Group.pullback _ (dcl Wd hrel.1 - _) = _
          rw [map_sub, ← hd1, dcl_congr (hWd V) h1.1 hE.1, hn, pb_mapX_fst,
            add_sub_cancel_left]
        rw [e, pb_comp_apply, hcl, ← pb_comp_apply, mapX_snd, pb_comp_apply, hU, map_zero]
  obtain ⟨N, hN⟩ := PushforwardLineBundle.exists_classOf_pullback (pullback.snd g (A.lG hW)) hq x
    hx
  refine ⟨N.classOf, ?_⟩
  rw [hN, add_sub_cancel]

variable (A hW) in
/-- **Morphism properties local on the target pass to the glued scheme.** -/
theorem glued_prop (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget Q]
    [Q.IsStableUnderBaseChange] (hQ : ∀ i, Q (pullback.snd (A.l i) (W i).ι)) :
    Q (A.lG hW) := by
  refine IsZariskiLocalAtTarget.of_openCover (basisCover W hW) fun V => ?_
  have hpb := ((A.gluingData hW).isPullback_natTrans_ι_toBase V).flip
  have hsnd : pullback.snd (A.lG hW) ((basisCover W hW).f V) =
      hpb.isoPullback.inv ≫ (A.natTrans hW).app V :=
    hpb.isoPullback_inv_snd.symm
  change Q (pullback.snd (A.lG hW) ((basisCover W hW).f V))
  rw [hsnd, Q.cancel_left_of_respectsIso]
  change Q (pullback.snd (A.l (idx V)) V.1.ι)
  -- base change from the member `W (idx V)` of the cover
  let j : (V.1 : Scheme.{u}) ⟶ (W (idx V) : Scheme.{u}) := S.homOfLE (le_idx V)
  have hj : j ≫ (W (idx V)).ι = V.1.ι := S.homOfLE_ι _
  have hbig : IsPullback (pullback.fst (A.l (idx V)) V.1.ι) (pullback.snd (A.l (idx V)) V.1.ι)
      (A.l (idx V)) (j ≫ (W (idx V)).ι) := by
    rw [hj]
    exact IsPullback.of_hasPullback _ _
  have hsq := IsPullback.of_right (h₁₁ := pullback.lift (pullback.fst (A.l (idx V)) V.1.ι)
      (pullback.snd (A.l (idx V)) V.1.ι ≫ j) (by rw [Category.assoc, hj, pullback.condition]))
    (h₁₂ := pullback.fst (A.l (idx V)) (W (idx V)).ι) (by rw [pullback.lift_fst]; exact hbig)
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  exact MorphismProperty.of_isPullback hsq (hQ (idx V))

end LocalData

end Langlands.AlgebraicGeometry.Picard.LinearSystemGluing
