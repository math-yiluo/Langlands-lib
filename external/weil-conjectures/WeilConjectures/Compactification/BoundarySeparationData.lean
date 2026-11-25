/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BoundaryPreparation
public import WeilConjectures.Compactification.IdealSheafPower

/-!
# Separation data for boundary pieces

This file records, as standalone declarations, the auxiliary nodes of the blueprint
subsection "Separating boundary closures" (`lemma-separation-closures--1`) whose content is
used inline in `AlgebraicGeometry.exists_admissibleBlowup_disjoint_closures`.

## Main definitions

- `AlgebraicGeometry.Scheme.IdealSheafData.separationPreparationCenter`: the center of the
  Tag 080P preparation (blueprint: `lemma-separation-closures--1`);
- `AlgebraicGeometry.Scheme.IdealSheafData.separationPreparationBlowupSubscheme`: the
  `U_Z`-admissible blow-up `Bl_C(Z) → Z` of that preparation;
- `AlgebraicGeometry.separationPreparationBlowup`: the blow-up of `X` along the composite
  center `C ↪ Z ↪ X` (blueprint: `lemma-separation-closures--1`, second paragraph);
- `AlgebraicGeometry.Scheme.IdealSheafData.constructibleClosedExtension`: the ideal
  `Ext_{X,U}(J_U(T))` of a constructible closed subset `T ⊆ U`;
- `AlgebraicGeometry.constructibleSeparationBlowup`: the constructible-boundary separation
  blow-up `CSepBl_U(T₁, T₂)` (blueprint: `lemma-separation-closures--1`).

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.exists_pow_eq_bot_of_support_eq_top`: a
  finite-type nil ideal sheaf on a quasi-compact scheme is nilpotent (blueprint:
  `lemma-separation-closures--1`);
- `AlgebraicGeometry.range_strictTransformMap_eq_closure`: the underlying set of the strict
  transform of a closed subscheme is the closure of the inverse image of its part over `U`;
- `AlgebraicGeometry.exists_separationPreparation`: the Tag 080P preparation (blueprint:
  `lemma-separation-closures--1`);
- `AlgebraicGeometry.disjoint_closure_preimage_constructibleSeparationBlowup`: the closures of
  the inverse images of `T₁`, `T₂` in `CSepBl_U(T₁, T₂)` are disjoint (blueprint:
  `lemma-separation-closures--1`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ### Finite-type nil ideals -/

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- **A finite type nil ideal sheaf is uniformly nilpotent** (blueprint:
`lemma-separation-closures--1`): on a quasi-compact scheme, a finite-type
quasi-coherent ideal sheaf with `V(I) = X` has a nonzero power equal to `0`. This is the case
`A = 0` of `Scheme.IdealSheafData.exists_pow_le`, whose proof is the chart-wise argument of the
blueprint (finitely generated ideals inside the nilradical are nilpotent, and a finite affine
cover bounds the exponents). -/
theorem exists_pow_eq_bot_of_support_eq_top [CompactSpace X] {I : X.IdealSheafData}
    (hI : I.ofFiniteType) (h : I.support = ⊤) : ∃ n : ℕ, 0 < n ∧ I ^ n = ⊥ := by
  obtain ⟨n, hn⟩ := exists_pow_le (A := ⊥) hI (by rw [h, support_bot])
  refine ⟨n + 1, n.succ_pos, le_bot_iff.mp (le_trans (le_def.mpr fun U ↦ ?_) hn)⟩
  change I.ideal U ^ (n + 1) ≤ I.ideal U ^ n
  exact Ideal.pow_le_pow_right n.le_succ

/-- A product of ideal sheaves is contained in the first factor. -/
lemma mul_le_self_left (I J : X.IdealSheafData) : I * J ≤ I :=
  le_def.mpr fun V ↦ show I.ideal V * J.ideal V ≤ I.ideal V from Ideal.mul_le_left

/-- A product of ideal sheaves is contained in the second factor. -/
lemma mul_le_self_right (I J : X.IdealSheafData) : I * J ≤ J :=
  le_def.mpr fun V ↦ show I.ideal V * J.ideal V ≤ J.ideal V from Ideal.mul_le_right

/-- The underlying set of the closed subscheme `V(J) ↪ V(I)` attached to `I ≤ J` is the
preimage of the support of `J`. -/
lemma range_inclusion {I J : X.IdealSheafData} (h : I ≤ J) :
    Set.range (inclusion h) = I.subschemeι ⁻¹' (J.support : Set X) := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, inclusion_subschemeι, ← range_subschemeι]
    exact ⟨y, rfl⟩
  · intro hz
    rw [Set.mem_preimage, ← range_subschemeι J] at hz
    obtain ⟨y, hy⟩ := hz
    refine ⟨y, I.subschemeι.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, inclusion_subschemeι, hy]

end Scheme.IdealSheafData

/-! ### The underlying set of a strict transform -/

section StrictTransformRange

variable {X Y X' : Scheme.{u}} (f : Y ⟶ X) (π : X' ⟶ X) (U : X.Opens)

/-- **The underlying set of the strict transform of a closed subscheme**: if `f` is a closed
immersion and the inclusion of the open locus over `U` is quasi-compact, the strict transform
of `f` along `π` is, as a subset of `X'`, the closure of the inverse image of the `U`-part of
the image of `f` (Stacks Project Tag 01R8 applied to the open locus). In particular it only
depends on the image of `f`. -/
theorem range_strictTransformMap_eq_closure [IsClosedImmersion f]
    [QuasiCompact (strictTransformOpen f π U).ι] :
    Set.range (strictTransformMap f π U) = closure (π ⁻¹' ((U : Set X) ∩ Set.range f)) := by
  apply subset_antisymm
  · rintro _ ⟨t, rfl⟩
    have hwcl : strictTransformι f π U t ∈
        closure (strictTransformOpen f π U : Set ↥(pullback f π)) := by
      have hmem : strictTransformι f π U t ∈ Set.range (strictTransformι f π U) := ⟨t, rfl⟩
      have hrange : Set.range (strictTransformι f π U) =
          (((strictTransformOpen f π U).ι.ker.support : Set _)) :=
        Scheme.IdealSheafData.range_subschemeι _
      rw [hrange, Scheme.Hom.support_ker, Scheme.Opens.range_ι] at hmem
      exact hmem
    have himg := image_closure_subset_closure_image (pullback.snd f π).continuous
      ⟨_, hwcl, rfl⟩
    change (strictTransformι f π U ≫ pullback.snd f π) t ∈ _
    rw [Scheme.Hom.comp_apply]
    refine closure_mono ?_ himg
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨hw, pullback.fst f π w, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  · refine closure_minimal ?_ (strictTransformMap f π U).isClosedEmbedding.isClosed_range
    rintro x ⟨hU, hf⟩
    exact mem_range_strictTransformMap_of_mem_of_mem_range f π U hU hf

/-- The inclusion of the open locus of the strict transform of a closed subscheme along the
blow-up of a finite-type ideal on a quasi-separated scheme, over the complement of the
center, is quasi-compact as soon as that complement is quasi-compact. -/
lemma quasiCompact_strictTransformOpen_ι_blowupMap {Z : Scheme.{u}} [QuasiSeparatedSpace Z]
    {K : Z.IdealSheafData} (hK : K.ofFiniteType)
    (hU₀ : IsCompact ((K.support.compl : Z.Opens) : Set Z)) (g : Y ⟶ Z) [IsClosedImmersion g] :
    QuasiCompact (strictTransformOpen g K.blowupMap K.support.compl).ι := by
  have : QuasiCompact K.blowupMap := Scheme.IdealSheafData.quasiCompact_blowupMap hK
  have : IsProper K.blowupMap := K.isProper_blowupMap fun U ↦ hK U le_top
  have : QuasiSeparatedSpace ↥(pullback g K.blowupMap) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd g K.blowupMap ≫ K.blowupMap)
  exact quasiCompact_strictTransformOpen_ι_of_isCompact _ _ _ hU₀

end StrictTransformRange

/-! ### The Tag 080P preparation for separating two closed boundaries -/

section SeparationPreparation

variable {X : Scheme.{u}} {U : X.Opens}

open Scheme.IdealSheafData in
/-- **The boundary of `Z = V(I₁ I₂)` over `U` splits into two pieces** (part of blueprint:
`lemma-separation-closures--1`): if `V(I₁) ∩ V(I₂) ∩ U = ∅`, the open
`U_Z = Z ×_X U` of `Z` is the disjoint union of the traces `Pᵢ = Zᵢ ×_X U` of the closed
subschemes `Zᵢ = V(Iᵢ) ↪ Z`. Both traces are closed in `U_Z`, hence open and closed. -/
theorem disjoint_range_inclusion_inter_preimage_and_subset
    (I₁ I₂ : X.IdealSheafData)
    (hdisj : Disjoint (U : Set X) ((I₁.support : Set X) ∩ (I₂.support : Set X))) :
    Disjoint (Set.range (inclusion (mul_le_self_left I₁ I₂)) ∩ (I₁ * I₂).subschemeι ⁻¹' U)
      (Set.range (inclusion (mul_le_self_right I₁ I₂)) ∩ (I₁ * I₂).subschemeι ⁻¹' U) ∧
    (I₁ * I₂).subschemeι ⁻¹' U ⊆
      Set.range (inclusion (mul_le_self_left I₁ I₂)) ∪
        Set.range (inclusion (mul_le_self_right I₁ I₂)) := by
  rw [range_inclusion, range_inclusion]
  refine ⟨Set.disjoint_left.mpr fun z ⟨h₁, hU⟩ ⟨h₂, _⟩ ↦
    Set.disjoint_left.mp hdisj hU ⟨h₁, h₂⟩, fun z _ ↦ ?_⟩
  have hz : (I₁ * I₂).subschemeι z ∈ (((I₁ * I₂).support : Set X)) := by
    rw [← range_subschemeι]
    exact ⟨z, rfl⟩
  rw [support_mul] at hz
  exact hz

open Scheme.IdealSheafData in
/-- **Preparation data for separating two closed boundaries** (Stacks Project Tag 080P;
blueprint: `lemma-separation-closures--1`).

Let `X` be qcqs and let `Zᵢ = V(Iᵢ)` be closed subschemes cut out by finite-type ideals (i.e.
finite-presentation closed immersions) with `Z₁ ∩ Z₂ ∩ U = ∅`; put `Z = V(I₁ I₂)`, with the
closed immersions `Zᵢ ↪ Z`. Then there is a finite-presentation closed center `C ↪ Z`, disjoint
from `U_Z = Z ×_X U`, such that the strict transforms of `Z₁` and `Z₂` in `Bl_C(Z)` are
disjoint. The center is recorded by a finite-type ideal `K ⊇ I₁ I₂` on `X` with
`V(K) ∩ U = ∅`: `C = V(K 𝒪_Z)` (finite presentation over `Z` by
`Scheme.IdealSheafData.ofFiniteType.comap`), and the composite `C ↪ Z ↪ X` is `V(K)`. The
blow-up of `Z` along `C` is `U_Z`-admissible
(`Scheme.IdealSheafData.separationPreparationBlowupSubscheme`), and the decomposition
`U_Z = P₁ ∐ P₂` is `disjoint_range_inclusion_inter_preimage_and_subset`.

The quasi-compactness of `U` assumed in the blueprint is not needed. Instead of the
nilpotence argument of the blueprint, the proof takes `K = I₁ + I₂` and applies the chart
argument of Stacks Tag 0F3V (`disjoint_range_strictTransformMap_sup`) to the restrictions of
`I₁`, `I₂` to `Z`; this is the route described in `separating-boundary-pieces--remark-1`.
The strict transforms of `Zᵢ ↪ Z` and of `V(Iᵢ 𝒪_Z) ↪ Z` agree since both closed immersions
have the same image (`range_strictTransformMap_eq_closure`). -/
theorem exists_separationPreparation [CompactSpace X] [QuasiSeparatedSpace X]
    (I₁ I₂ : X.IdealSheafData) (h₁ : I₁.ofFiniteType) (h₂ : I₂.ofFiniteType)
    (hdisj : Disjoint (U : Set X) ((I₁.support : Set X) ∩ (I₂.support : Set X))) :
    ∃ K : X.IdealSheafData, I₁ * I₂ ≤ K ∧ K.ofFiniteType ∧
      Disjoint (U : Set X) (K.support : Set X) ∧
      Disjoint
        (Set.range (strictTransformMap (inclusion (mul_le_self_left I₁ I₂))
          (K.comap (I₁ * I₂).subschemeι).blowupMap
          (K.comap (I₁ * I₂).subschemeι).support.compl))
        (Set.range (strictTransformMap (inclusion (mul_le_self_right I₁ I₂))
          (K.comap (I₁ * I₂).subschemeι).blowupMap
          (K.comap (I₁ * I₂).subschemeι).support.compl)) := by
  have : CompactSpace (I₁ * I₂).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (I₁ * I₂).subschemeι
  have : QuasiSeparatedSpace (I₁ * I₂).subscheme :=
    quasiSeparatedSpace_of_quasiSeparated (I₁ * I₂).subschemeι
  refine ⟨I₁ ⊔ I₂, (mul_le_self_left I₁ I₂).trans le_sup_left, h₁.sup h₂,
    hdisj.mono_right (coe_support_sup I₁ I₂).subset, ?_⟩
  rw [comap_sup]
  have h₁' := h₁.comap (I₁ * I₂).subschemeι
  have h₂' := h₂.comap (I₁ * I₂).subschemeι
  have hKft := h₁'.sup h₂'
  have hU₀ := isCompact_coe_compl_support hKft
  have := quasiCompact_strictTransformOpen_ι_blowupMap hKft hU₀
    (inclusion (mul_le_self_left I₁ I₂))
  have := quasiCompact_strictTransformOpen_ι_blowupMap hKft hU₀
    (inclusion (mul_le_self_right I₁ I₂))
  have := quasiCompact_strictTransformOpen_ι_blowupMap hKft hU₀
    (I₁.comap (I₁ * I₂).subschemeι).subschemeι
  have := quasiCompact_strictTransformOpen_ι_blowupMap hKft hU₀
    (I₂.comap (I₁ * I₂).subschemeι).subschemeι
  have key := disjoint_range_strictTransformMap_sup _ _ h₁' h₂'
  rw [range_strictTransformMap_eq_closure (I₁.comap (I₁ * I₂).subschemeι).subschemeι,
    range_strictTransformMap_eq_closure (I₂.comap (I₁ * I₂).subschemeι).subschemeι,
    range_subschemeι, range_subschemeι, coe_support_comap, coe_support_comap] at key
  rw [range_strictTransformMap_eq_closure (inclusion (mul_le_self_left I₁ I₂)),
    range_strictTransformMap_eq_closure (inclusion (mul_le_self_right I₁ I₂)),
    range_inclusion, range_inclusion]
  exact key

/-- The center ideal of the Tag 080P preparation (blueprint:
`lemma-separation-closures--1`), chosen
from `exists_separationPreparation`: a finite-type ideal `K ⊇ I₁ I₂` on `X` with
`V(K) ∩ U = ∅`, so that `C = V(K 𝒪_Z) ↪ Z = V(I₁ I₂)` is the center of the preparation and
`V(K)` is the composite center `C ↪ Z ↪ X`. -/
def Scheme.IdealSheafData.separationPreparationCenter [CompactSpace X] [QuasiSeparatedSpace X]
    (I₁ I₂ : X.IdealSheafData) (h₁ : I₁.ofFiniteType) (h₂ : I₂.ofFiniteType)
    (hdisj : Disjoint (U : Set X) ((I₁.support : Set X) ∩ (I₂.support : Set X))) :
    X.IdealSheafData :=
  (exists_separationPreparation I₁ I₂ h₁ h₂ hdisj).choose

open Scheme.IdealSheafData in
lemma Scheme.IdealSheafData.separationPreparationCenter_spec [CompactSpace X]
    [QuasiSeparatedSpace X]
    (I₁ I₂ : X.IdealSheafData) (h₁ : I₁.ofFiniteType) (h₂ : I₂.ofFiniteType)
    (hdisj : Disjoint (U : Set X) ((I₁.support : Set X) ∩ (I₂.support : Set X))) :
    I₁ * I₂ ≤ separationPreparationCenter I₁ I₂ h₁ h₂ hdisj ∧
      (separationPreparationCenter I₁ I₂ h₁ h₂ hdisj).ofFiniteType ∧
      Disjoint (U : Set X) ((separationPreparationCenter I₁ I₂ h₁ h₂ hdisj).support : Set X) ∧
      Disjoint
        (Set.range (strictTransformMap (inclusion (mul_le_self_left I₁ I₂))
          ((separationPreparationCenter I₁ I₂ h₁ h₂ hdisj).comap
            (I₁ * I₂).subschemeι).blowupMap
          ((separationPreparationCenter I₁ I₂ h₁ h₂ hdisj).comap
            (I₁ * I₂).subschemeι).support.compl))
        (Set.range (strictTransformMap (inclusion (mul_le_self_right I₁ I₂))
          ((separationPreparationCenter I₁ I₂ h₁ h₂ hdisj).comap
            (I₁ * I₂).subschemeι).blowupMap
          ((separationPreparationCenter I₁ I₂ h₁ h₂ hdisj).comap
            (I₁ * I₂).subschemeι).support.compl)) :=
  (exists_separationPreparation I₁ I₂ h₁ h₂ hdisj).choose_spec

/-- The `U_Z`-admissible blow-up `Bl_C(Z) → Z` of the Tag 080P preparation, for
`Z = V(I₁ I₂)` and `U_Z = Z ×_X U` (blueprint: `lemma-separation-closures--1`).
The strict transforms of `Z₁` and `Z₂` in it are disjoint
(`Scheme.IdealSheafData.separationPreparationCenter_spec`). -/
def Scheme.IdealSheafData.separationPreparationBlowupSubscheme [CompactSpace X]
    [QuasiSeparatedSpace X]
    (I₁ I₂ : X.IdealSheafData) (h₁ : I₁.ofFiniteType) (h₂ : I₂.ofFiniteType)
    (hdisj : Disjoint (U : Set X) ((I₁.support : Set X) ∩ (I₂.support : Set X))) :
    IsAdmissible (I₁ * I₂).subscheme ((I₁ * I₂).subschemeι ⁻¹ᵁ U) where
  I := (separationPreparationCenter I₁ I₂ h₁ h₂ hdisj).comap (I₁ * I₂).subschemeι
  finiteType := (separationPreparationCenter_spec I₁ I₂ h₁ h₂ hdisj).2.1.comap _
  disjoint_support := by
    rw [coe_support_comap]
    exact (separationPreparationCenter_spec I₁ I₂ h₁ h₂ hdisj).2.2.1.preimage _

/-- **The Tag 080P separation blow-up** (blueprint: `lemma-separation-closures--1`,
second paragraph): for `X` qcqs and finite-presentation closed subschemes `Zᵢ = V(Iᵢ)` with
`Z₁ ∩ Z₂ ∩ U = ∅`, the `U`-admissible blow-up of `X` along the composite center
`C ↪ Z ↪ X`, where `C ↪ Z = V(I₁ I₂)` is the center of the Tag 080P preparation
(`Scheme.IdealSheafData.separationPreparationCenter`); the composite center is `V(K)` for the
chosen ideal `K ⊇ I₁ I₂`, which is of finite type and disjoint from `U`. -/
def separationPreparationBlowup [CompactSpace X] [QuasiSeparatedSpace X]
    (I₁ I₂ : X.IdealSheafData) (h₁ : I₁.ofFiniteType) (h₂ : I₂.ofFiniteType)
    (hdisj : Disjoint (U : Set X) ((I₁.support : Set X) ∩ (I₂.support : Set X))) :
    IsAdmissible X U where
  I := Scheme.IdealSheafData.separationPreparationCenter I₁ I₂ h₁ h₂ hdisj
  finiteType := (Scheme.IdealSheafData.separationPreparationCenter_spec I₁ I₂ h₁ h₂ hdisj).2.1
  disjoint_support :=
    (Scheme.IdealSheafData.separationPreparationCenter_spec I₁ I₂ h₁ h₂ hdisj).2.2.1

end SeparationPreparation

/-! ### The constructible-boundary separation blow-up as a construction -/

section ConstructibleSeparation

variable {X : Scheme.{u}} {U : X.Opens}

/-- The finite-type ideal `Ext_{X,U}(J_U(T))` on `X` attached to a constructible closed subset
`T` of a quasi-compact open `U` of a qcqs scheme (the ideals `𝓘ᵢ` of blueprint
`lemma-separation-closures--1`): `J_U(T)` is the chosen finite-type ideal on `U`
with vanishing set `T` (`Scheme.exists_finiteType_ideal_coe_support_eq_compl`, Stacks Tag
01PH), and `Ext_{X,U}` is the chosen finite-type extension to `X`
(`Scheme.IdealSheafData.exists_finiteType_comap_eq`, Stacks Tag 01PF). -/
def Scheme.IdealSheafData.constructibleClosedExtension [CompactSpace X] [QuasiSeparatedSpace X]
    (hU : IsCompact (U : Set X)) {T : Set U.toScheme} (hT : IsClosed T) (hc : IsCompact Tᶜ) :
    X.IdealSheafData :=
  haveI : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  haveI : QuasiSeparatedSpace U.toScheme := quasiSeparatedSpace_of_quasiSeparated U.ι
  (exists_finiteType_comap_eq U hU
    (U.toScheme.exists_finiteType_ideal_coe_support_eq_compl ⟨Tᶜ, hT.isOpen_compl⟩ hc).choose
    (U.toScheme.exists_finiteType_ideal_coe_support_eq_compl ⟨Tᶜ, hT.isOpen_compl⟩
      hc).choose_spec.1).choose

/-- The ideal `Ext_{X,U}(J_U(T))` is of finite type and cuts out `T` on `U`. -/
lemma Scheme.IdealSheafData.constructibleClosedExtension_spec [CompactSpace X]
    [QuasiSeparatedSpace X] (hU : IsCompact (U : Set X)) {T : Set U.toScheme}
    (hT : IsClosed T) (hc : IsCompact Tᶜ) :
    (constructibleClosedExtension hU hT hc).ofFiniteType ∧
      U.ι ⁻¹' ((constructibleClosedExtension hU hT hc).support : Set X) = T := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : QuasiSeparatedSpace U.toScheme := quasiSeparatedSpace_of_quasiSeparated U.ι
  have hJ := (U.toScheme.exists_finiteType_ideal_coe_support_eq_compl ⟨Tᶜ, hT.isOpen_compl⟩
    hc).choose_spec
  have hI := (exists_finiteType_comap_eq U hU _ hJ.1).choose_spec
  refine ⟨hI.1, ?_⟩
  rw [← coe_support_comap]
  unfold constructibleClosedExtension
  rw [hI.2, hJ.2]
  exact compl_compl T

/-- The common support of the two extended ideals misses `U`. -/
lemma Scheme.IdealSheafData.disjoint_support_constructibleClosedExtension [CompactSpace X]
    [QuasiSeparatedSpace X] (hU : IsCompact (U : Set X)) {T₁ T₂ : Set U.toScheme}
    (hT₁ : IsClosed T₁) (hT₂ : IsClosed T₂) (hc₁ : IsCompact T₁ᶜ) (hc₂ : IsCompact T₂ᶜ)
    (hdisj : Disjoint T₁ T₂) :
    Disjoint (U : Set X) (((constructibleClosedExtension hU hT₁ hc₁).support : Set X) ∩
      ((constructibleClosedExtension hU hT₂ hc₂).support : Set X)) := by
  have hpre₁ := (constructibleClosedExtension_spec hU hT₁ hc₁).2
  have hpre₂ := (constructibleClosedExtension_spec hU hT₂ hc₂).2
  rw [Set.disjoint_left]
  rintro x hxU ⟨hx1, hx2⟩
  obtain ⟨t, rfl⟩ : x ∈ Set.range U.ι := by
    rwa [Scheme.Opens.range_ι]
  exact Set.disjoint_left.mp hdisj (hpre₁ ▸ Set.mem_preimage.mpr hx1)
    (hpre₂ ▸ Set.mem_preimage.mpr hx2)

/-- **The constructible-boundary separation blow-up** `CSepBl_U(T₁, T₂)` (blueprint:
`lemma-separation-closures--1`): the closed-boundary separation blow-up
`SepBl_U(Z₁, Z₂)` (`separationBlowup`) of the closed subschemes `Zᵢ = V(𝓘ᵢ)` cut out by the
extended ideals `𝓘ᵢ = Ext_{X,U}(J_U(Tᵢ))`
(`Scheme.IdealSheafData.constructibleClosedExtension`). -/
def constructibleSeparationBlowup [CompactSpace X] [QuasiSeparatedSpace X]
    (hU : IsCompact (U : Set X)) {T₁ T₂ : Set U.toScheme} (hT₁ : IsClosed T₁)
    (hT₂ : IsClosed T₂) (hc₁ : IsCompact T₁ᶜ) (hc₂ : IsCompact T₂ᶜ) (hdisj : Disjoint T₁ T₂) :
    IsAdmissible X U :=
  separationBlowup (Scheme.IdealSheafData.constructibleClosedExtension hU hT₁ hc₁)
    (Scheme.IdealSheafData.constructibleClosedExtension hU hT₂ hc₂)
    (Scheme.IdealSheafData.constructibleClosedExtension_spec hU hT₁ hc₁).1
    (Scheme.IdealSheafData.constructibleClosedExtension_spec hU hT₂ hc₂).1
    (Scheme.IdealSheafData.disjoint_support_constructibleClosedExtension hU hT₁ hT₂ hc₁ hc₂
      hdisj)

/-- **Properties of constructible-boundary separation**, for the explicit construction
(blueprint: `lemma-separation-closures--1`): the closures of the inverse
images of `T₁` and `T₂` in `CSepBl_U(T₁, T₂)` are disjoint. The closure of the inverse image
of `Tᵢ` lies in the strict transform of `V(𝓘ᵢ)`, and these strict transforms are disjoint
(`disjoint_range_strictTransformMap_sup`). -/
theorem disjoint_closure_preimage_constructibleSeparationBlowup [CompactSpace X]
    [QuasiSeparatedSpace X] (hU : IsCompact (U : Set X)) {T₁ T₂ : Set U.toScheme}
    (hT₁ : IsClosed T₁) (hT₂ : IsClosed T₂) (hc₁ : IsCompact T₁ᶜ) (hc₂ : IsCompact T₂ᶜ)
    (hdisj : Disjoint T₁ T₂) :
    Disjoint
      (closure ((constructibleSeparationBlowup hU hT₁ hT₂ hc₁ hc₂ hdisj).I.blowupMap ⁻¹'
        (U.ι '' T₁)))
      (closure ((constructibleSeparationBlowup hU hT₁ hT₂ hc₁ hc₂ hdisj).I.blowupMap ⁻¹'
        (U.ι '' T₂))) := by
  have h₁ := Scheme.IdealSheafData.constructibleClosedExtension_spec hU hT₁ hc₁
  have h₂ := Scheme.IdealSheafData.constructibleClosedExtension_spec hU hT₂ hc₂
  exact (disjoint_range_strictTransformMap_sup _ _ h₁.1 h₂.1).mono
    ((constructibleSeparationBlowup hU hT₁ hT₂ hc₁ hc₂
      hdisj).closure_preimage_subset_range_strictTransformMap _ h₁.2.symm.le)
    ((constructibleSeparationBlowup hU hT₁ hT₂ hc₁ hc₂
      hdisj).closure_preimage_subset_range_strictTransformMap _ h₂.2.symm.le)

end ConstructibleSeparation

end AlgebraicGeometry
