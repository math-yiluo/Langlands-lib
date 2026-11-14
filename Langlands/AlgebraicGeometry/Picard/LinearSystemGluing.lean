import Langlands.AlgebraicGeometry.Picard.LinearSystemUniversality
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyOpenCoverGluing
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover
import Langlands.AlgebraicGeometry.IdealSheafGluing

/-! # Gluing universal families of linear systems over an open cover of the base

Universal families of the linear system of a class `m` on `Y` over the members of an open
cover `W` of `S` restrict to universal families over all smaller opens, are unique up to unique
isomorphism, and hence glue (relative gluing over the cover by all opens contained in some
member of `W`) to a universal family over `S`. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemGluing

open PicardHilbertPiecesReduction (mapX mapX_comp mapX_congr mapX_fst mapX_snd dcl dcl_congr
  pb_comp_apply pb_iso_inv_hom pb_mapX_fst)
open Langlands.AbelianScheme.SmoothFamilyOpenCover (SubOpens isBasis_subOpens basisCover
  basisCover_trans_ι range_comp_ι_subset idx le_idx)

section Maps

variable {S Y : Scheme.{u}} (g : Y ⟶ S)

instance isOpenImmersion_mapX {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T)
    [IsOpenImmersion h] (w : h ≫ s = s') : IsOpenImmersion (mapX g h w) := by
  unfold mapX
  infer_instance

lemma range_mapX {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T) (w : h ≫ s = s') :
    Set.range (mapX g h w) = pullback.snd g s ⁻¹' Set.range h := by
  rw [mapX, Scheme.Pullback.range_map]
  simp

end Maps

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {m : Group Y}

variable (g m) in
/-- **Local universal families** of the linear system over the members of an open cover. -/
structure LocalData {ι : Type u} (W : ι → S.Opens) where
  /-- The local parameter schemes. -/
  P : ι → Scheme.{u}
  /-- Their structure maps. -/
  l : ∀ i, P i ⟶ S
  /-- The local universal divisors. -/
  D : ∀ i, (pullback g (l i)).IdealSheafData
  noetherian : ∀ i, IsLocallyNoetherian (P i)
  universal : ∀ i, IsUniversalOn g m (W i) (l i) (D i)

namespace LocalData

variable {ι : Type u} {W : ι → S.Opens} (A : LocalData g m W)

/-- The preimage of `V` in the chosen local parameter. -/
abbrev param (V : SubOpens W) : Scheme.{u} := pullback (A.l (idx V)) V.1.ι

/-- The structure map of the preimage of `V`. -/
abbrev lp (V : SubOpens W) : A.param V ⟶ S := pullback.snd (A.l (idx V)) V.1.ι ≫ V.1.ι

lemma fst_l (V : SubOpens W) : pullback.fst (A.l (idx V)) V.1.ι ≫ A.l (idx V) = A.lp V :=
  pullback.condition

/-- The restriction of the local universal divisor to the preimage of `V`. -/
abbrev Dp (V : SubOpens W) : (pullback g (A.lp V)).IdealSheafData :=
  (A.D (idx V)).comap (mapX g (pullback.fst (A.l (idx V)) V.1.ι) (A.fst_l V))

instance (V : SubOpens W) : IsLocallyNoetherian (A.param V) := by
  have := A.noetherian (idx V)
  infer_instance

lemma universal_param (V : SubOpens W) : IsUniversalOn g m V.1 (A.lp V) (A.Dp V) :=
  (A.universal (idx V)).of_isPullback (le_idx V) _ _ (IsPullback.of_hasPullback _ _)

lemma range_lp (V : SubOpens W) : Set.range (A.lp V) ⊆ (V.1 : Set S) :=
  (A.universal_param V).range_le

lemma existsUnique_transition {V V' : SubOpens W} (h : V.1 ≤ V'.1) :
    ∃ t : A.param V ⟶ A.param V', ∃ ht : t ≫ A.lp V' = A.lp V,
      (A.Dp V').comap (mapX g t ht) = A.Dp V :=
  (A.universal_param V').exists_point (A.param V) (A.lp V)
    ((A.range_lp V).trans h) (A.Dp V) (A.universal_param V).ls

/-- The transition between the parameters of `V ≤ V'`. -/
def transition {V V' : SubOpens W} (h : V.1 ≤ V'.1) : A.param V ⟶ A.param V' :=
  (A.existsUnique_transition h).choose

lemma transition_lp {V V' : SubOpens W} (h : V.1 ≤ V'.1) :
    A.transition h ≫ A.lp V' = A.lp V :=
  (A.existsUnique_transition h).choose_spec.choose

lemma transition_D {V V' : SubOpens W} (h : V.1 ≤ V'.1) :
    (A.Dp V').comap (mapX g (A.transition h) (A.transition_lp h)) = A.Dp V :=
  (A.existsUnique_transition h).choose_spec.choose_spec

lemma transition_unique {V V' : SubOpens W} (h : V.1 ≤ V'.1) (t : A.param V ⟶ A.param V')
    (ht : t ≫ A.lp V' = A.lp V) (hD : (A.Dp V').comap (mapX g t ht) = A.Dp V) :
    t = A.transition h :=
  (A.universal_param V').eq_of_comap_eq (A.param V) (A.lp V) _ _ ht (A.transition_lp h)
    (hD.trans (A.transition_D h).symm)

lemma transition_id (V : SubOpens W) (h : V.1 ≤ V.1) : A.transition h = 𝟙 _ :=
  (A.transition_unique h _ (Category.id_comp _)
    (by rw [mapX_id, Scheme.IdealSheafData.comap_id])).symm

lemma transition_comp {V V' V'' : SubOpens W} (h : V.1 ≤ V'.1) (h' : V'.1 ≤ V''.1)
    (h'' : V.1 ≤ V''.1) : A.transition h'' = A.transition h ≫ A.transition h' := by
  refine (A.transition_unique h'' _ (by rw [Category.assoc, A.transition_lp, A.transition_lp])
    ?_).symm
  rw [← mapX_comp g _ (A.transition_lp h') _ (A.transition_lp h),
    Scheme.IdealSheafData.comap_comp, A.transition_D, A.transition_D]

variable (hW : TopologicalSpace.IsOpenCover W)

/-- The diagram of local parameters over the basis cover. -/
def functor : (basisCover W hW).I₀ ⥤ Scheme.{u} where
  obj V := A.param V
  map f := A.transition (leOfHom f)
  map_id V := A.transition_id V _
  map_comp f g := A.transition_comp (leOfHom f) (leOfHom g) _

lemma transition_snd {V V' : (basisCover W hW).I₀} (f : V ⟶ V') :
    A.transition (leOfHom f) ≫ pullback.snd (A.l (idx V')) V'.1.ι =
      pullback.snd (A.l (idx V)) V.1.ι ≫ (basisCover W hW).trans f := by
  rw [← cancel_mono V'.1.ι, Category.assoc, Category.assoc, basisCover_trans_ι hW]
  exact A.transition_lp (leOfHom f)

/-- The structure maps of the local parameters to the members of the basis cover. -/
def natTrans : A.functor hW ⟶ (basisCover W hW).functorOfLocallyDirected where
  app V := pullback.snd (A.l (idx V)) V.1.ι
  naturality _ _ f := A.transition_snd hW f

lemma equifibered : (A.natTrans hW).Equifibered := by
  intro V V' f
  let a' := pullback.snd (A.l (idx V')) V'.1.ι
  let τ := (basisCover W hW).trans f
  have hτ : τ ≫ V'.1.ι = V.1.ι := basisCover_trans_ι hW f
  have hpb : IsPullback (pullback.fst a' τ) (pullback.snd a' τ) (A.lp V') V.1.ι := by
    have h : IsPullback (pullback.fst a' τ) (pullback.snd a' τ) (a' ≫ V'.1.ι) (τ ≫ V'.1.ι) :=
      IsPullback.of_isLimit (pullbackIsPullbackOfCompMono a' τ V'.1.ι)
    rw [hτ] at h
    exact h
  have hY := (A.universal_param V').of_isPullback (leOfHom f) _ _ hpb
  have : IsLocallyNoetherian (pullback a' τ) := inferInstance
  have hsq : A.transition (leOfHom f) ≫ a' = pullback.snd (A.l (idx V)) V.1.ι ≫ τ :=
    A.transition_snd hW f
  let ℓ : A.param V ⟶ pullback a' τ := pullback.lift _ _ hsq
  have hℓ1 : ℓ ≫ pullback.fst a' τ = A.transition (leOfHom f) := pullback.lift_fst _ _ _
  have hℓ2 : ℓ ≫ pullback.snd a' τ = pullback.snd (A.l (idx V)) V.1.ι := pullback.lift_snd _ _ _
  have hℓ : ℓ ≫ pullback.snd a' τ ≫ V.1.ι = A.lp V := by rw [← Category.assoc, hℓ2]
  have hiso : IsIso ℓ := by
    refine isIso_of_isUniversalOn (A.universal_param V) hY ℓ hℓ ?_
    rw [← Scheme.IdealSheafData.comap_comp, mapX_comp, ← A.transition_D (leOfHom f)]
    exact congrArg _ (mapX_congr g hℓ1 _ _)
  exact IsPullback.of_iso_pullback ⟨hsq⟩ (asIso ℓ) hℓ1 hℓ2

/-- The relative gluing datum of the local parameters. -/
def gluingData : (basisCover W hW).RelativeGluingData where
  functor := A.functor hW
  natTrans := A.natTrans hW
  equifibered := A.equifibered hW

/-- **The glued parameter scheme.** -/
abbrev glued : Scheme.{u} := (A.gluingData hW).glued

/-- **Its structure map.** -/
abbrev lG : A.glued hW ⟶ S := (A.gluingData hW).toBase

/-- The inclusion of a local parameter. -/
abbrev ιV (V : (basisCover W hW).I₀) : A.param V ⟶ A.glued hW :=
  colimit.ι (A.gluingData hW).functor V

instance (V : (basisCover W hW).I₀) : IsOpenImmersion (A.ιV hW V) :=
  inferInstanceAs (IsOpenImmersion ((A.gluingData hW).cover.f V))

lemma ιV_lG (V : (basisCover W hW).I₀) : A.ιV hW V ≫ A.lG hW = A.lp V :=
  (A.gluingData hW).ι_toBase V

lemma transition_ιV {V V' : (basisCover W hW).I₀} (f : V ⟶ V') :
    A.transition (leOfHom f) ≫ A.ιV hW V' = A.ιV hW V :=
  colimit.w (A.gluingData hW).functor f

lemma range_ιV (V : (basisCover W hW).I₀) :
    Set.range (A.ιV hW V) = A.lG hW ⁻¹' (V.1 : Set S) := by
  have h := (A.gluingData hW).preimage_toBase_eq_range_ι V
  have h' : Set.range ((basisCover W hW).f V) = (V.1 : Set S) := Scheme.Opens.range_ι V.1
  rw [h'] at h
  exact h.symm

lemma mem_range_ιV {V : (basisCover W hW).I₀} {Z : Scheme.{u}} (c : Z ⟶ A.glued hW)
    (hc : Set.range (c ≫ A.lG hW) ⊆ (V.1 : Set S)) : Set.range c ⊆ Set.range (A.ιV hW V) := by
  rw [A.range_ιV]
  rintro _ ⟨z, rfl⟩
  exact hc ⟨z, (Scheme.Hom.comp_apply _ _ _).symm⟩

end LocalData

end Langlands.AlgebraicGeometry.Picard.LinearSystemGluing
