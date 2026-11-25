/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorExtension

/-!
# Functoriality of the extension attached to a torsor

Let `t` be a `ℤ/m`-torsor and `t'` a `ℤ/m'`-torsor over the same scheme `Y`, with `m ∣ m'`, and
let `h : P' ⟶ P` be a morphism of the total spaces over `Y` with `h ∘ (1 +ᵥ -) = (c +ᵥ -) ∘ h`.
Pulling back functions along `h` maps the extension `0 ⟶ μ_m ⟶ K₂ ⟶ μ_m ⟶ 0` of `t` to that of
`t'`, by the inclusion `μ_m ⊆ μ_{m'}` on the subobject and by `c` times it on the quotient. Hence
the connecting homomorphisms satisfy `ι_* (δ_t x) = δ_{t'} (c • ι_* x)`
(`AlgebraicGeometry.Scheme.EtaleTorsor.map_cupMu`).

The two cases used are: `m' = m` and `c` arbitrary, for a torsor whose monodromy is `c` times that
of another; and `m' = ℓ m`, `c = 1`, for the reduction of a `ℤ/ℓm`-torsor to a `ℤ/m`-torsor.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleTorsor

variable {Y : Scheme.{u}} {m : ℕ} [NeZero m] (t : EtaleTorsor (ULift.{u + 1} (ZMod m)) Y)

lemma transl_one : t.transl 1 = t.pushforwardGmTranslate 1 := by
  rw [transl, one_nsmul]

section Translate

variable {Z : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (j : Z ⟶ t.pushforwardGm)

/-- A map into the invariants is invariant under all translations. -/
lemma comp_transl_of_comp_gmDiff (hj : j ≫ t.gmDiff = 0) (k : ℕ) : j ≫ t.transl k = j := by
  induction k with
  | zero => rw [transl, zero_nsmul, pushforwardGmTranslate_zero, Category.comp_id]
  | succ k ih =>
    rw [transl_succ, ← Category.assoc, ih]
    rw [gmDiff, Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at hj
    exact hj

/-- On `ker D²`, translation by `k` is `1 + k • D`. -/
lemma comp_transl_sub (hj : j ≫ t.gmDiff ≫ t.gmDiff = 0) (k : ℕ) :
    j ≫ (t.transl k - 𝟙 _) = k • (j ≫ t.gmDiff) := by
  have hD : (j ≫ t.gmDiff) ≫ t.gmDiff = 0 := by rw [Category.assoc, hj]
  induction k with
  | zero => rw [transl, zero_nsmul, pushforwardGmTranslate_zero, sub_self, comp_zero, zero_smul]
  | succ k ih =>
    have e : t.transl (k + 1) - 𝟙 _ = (t.transl k - 𝟙 _) ≫ t.pushforwardGmTranslate 1 +
        t.gmDiff := by
      rw [transl_succ, gmDiff, Preadditive.sub_comp, Category.id_comp]
      abel
    rw [e, Preadditive.comp_add, ← Category.assoc, ih, Preadditive.nsmul_comp, ← transl_one,
      t.comp_transl_of_comp_gmDiff _ hD, succ_nsmul]

end Translate

lemma ιK₁_gmDiff :
    (kernel.ι t.muDiff ≫ kernel.ι (m • 𝟙 t.pushforwardGm)) ≫ t.gmDiff = 0 := by
  calc _ = kernel.ι t.muDiff ≫ t.muDiff ≫ kernel.ι (m • 𝟙 t.pushforwardGm) := by
        simp only [Category.assoc, muDiff_ι]
    _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp]

lemma ιK₂_gmDiff_gmDiff :
    (kernel.ι (t.muDiff ≫ t.muDiff) ≫ kernel.ι (m • 𝟙 t.pushforwardGm)) ≫ t.gmDiff ≫
      t.gmDiff = 0 := by
  calc _ = kernel.ι (t.muDiff ≫ t.muDiff) ≫ (t.muDiff ≫ t.muDiff) ≫
        kernel.ι (m • 𝟙 t.pushforwardGm) := by
        simp only [Category.assoc, muDiff_ι, muDiff_ι_assoc]
    _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp]

variable {m' : ℕ} [NeZero m'] (t' : EtaleTorsor (ULift.{u + 1} (ZMod m')) Y)
  (h : t'.P ⟶ t.P) (hπ : h ≫ t.π = t'.π) (c : ℕ)

/-- Pullback of units along `h : P' ⟶ P`. -/
noncomputable abbrev mapW : t.pushforwardGm ⟶ t'.pushforwardGm :=
  lowerStarGmSheafMap t.π h t'.π hπ

lemma mapW_translate (hc : t'.vadd 1 ≫ h = h ≫ t.vadd (c • 1)) :
    t.mapW t' h hπ ≫ t'.pushforwardGmTranslate 1 = t.transl c ≫ t.mapW t' h hπ := by
  rw [mapW, pushforwardGmTranslate, transl, pushforwardGmTranslate, lowerStarGmSheafMap_comp,
    lowerStarGmSheafMap_comp]
  congr 1

@[reassoc]
lemma mapW_gmDiff (hc : t'.vadd 1 ≫ h = h ≫ t.vadd (c • 1)) :
    t.mapW t' h hπ ≫ t'.gmDiff = (t.transl c - 𝟙 _) ≫ t.mapW t' h hπ := by
  rw [gmDiff, Preadditive.comp_sub, t.mapW_translate t' h hπ c hc, Preadditive.sub_comp,
    Category.comp_id, Category.id_comp]

@[reassoc (attr := simp)]
lemma pushforwardGmUnit_mapW : t.pushforwardGmUnit ≫ t.mapW t' h hπ = t'.pushforwardGmUnit :=
  gmSheafToLowerStarGmSheaf_comp_lowerStarGmSheafMap _ _ _ _

lemma ιK₁_mapW_gmDiff (hc : t'.vadd 1 ≫ h = h ≫ t.vadd (c • 1)) :
    (kernel.ι t.muDiff ≫ kernel.ι (m • 𝟙 t.pushforwardGm)) ≫ t.mapW t' h hπ ≫ t'.gmDiff = 0 := by
  rw [t.mapW_gmDiff t' h hπ c hc, ← Category.assoc, Preadditive.comp_sub, Category.comp_id,
    t.comp_transl_of_comp_gmDiff _ t.ιK₁_gmDiff, sub_self, zero_comp]

lemma ιK₂_mapW_gmDiff_gmDiff (hc : t'.vadd 1 ≫ h = h ≫ t.vadd (c • 1)) :
    (kernel.ι (t.muDiff ≫ t.muDiff) ≫ kernel.ι (m • 𝟙 t.pushforwardGm)) ≫ t.mapW t' h hπ ≫
      t'.gmDiff ≫ t'.gmDiff = 0 := by
  set X := kernel.ι (t.muDiff ≫ t.muDiff) ≫ kernel.ι (m • 𝟙 t.pushforwardGm)
  have hX : (X ≫ t.gmDiff) ≫ t.gmDiff = 0 := by
    rw [Category.assoc]
    exact t.ιK₂_gmDiff_gmDiff
  rw [t.mapW_gmDiff_assoc t' h hπ c hc, t.mapW_gmDiff t' h hπ c hc, ← Category.assoc,
    t.comp_transl_sub _ t.ιK₂_gmDiff_gmDiff, Preadditive.nsmul_comp, ← Category.assoc,
    Preadditive.comp_sub, Category.comp_id, t.comp_transl_of_comp_gmDiff _ hX, sub_self,
    zero_comp, nsmul_zero]

lemma nsmul_kernel_ι_mapW (hm : m ∣ m') :
    m' • (kernel.ι (m • 𝟙 t.pushforwardGm) ≫ t.mapW t' h hπ) = 0 := by
  obtain ⟨e, he⟩ := hm
  calc m' • (kernel.ι (m • 𝟙 t.pushforwardGm) ≫ t.mapW t' h hπ) =
      (m * e) • (kernel.ι (m • 𝟙 t.pushforwardGm) ≫ t.mapW t' h hπ) := congrArg (· • _) he
    _ = 0 := by
      rw [mul_comm, mul_smul, ← Preadditive.nsmul_comp, t.nsmul_kernel_ι_pushforwardMu,
        zero_comp, smul_zero]

/-- Pullback along `h` on `π_* μ`. -/
noncomputable def mapV (hm : m ∣ m') : t.pushforwardMu ⟶ t'.pushforwardMu :=
  kernel.lift _ (kernel.ι _ ≫ t.mapW t' h hπ) (by
    rw [Category.assoc, Preadditive.comp_nsmul, Category.comp_id, Preadditive.comp_nsmul,
      t.nsmul_kernel_ι_mapW t' h hπ hm])

@[reassoc (attr := simp)]
lemma mapV_ι (hm : m ∣ m') : t.mapV t' h hπ hm ≫ kernel.ι _ = kernel.ι _ ≫ t.mapW t' h hπ :=
  kernel.lift_ι _ _ _

/-- The map `K₁ ⟶ K₁'`. -/
noncomputable def mapK₁ (hc : t'.vadd 1 ≫ h = h ≫ t.vadd (c • 1)) (hm : m ∣ m') :
    kernel t.muDiff ⟶ kernel t'.muDiff :=
  kernel.lift _ (kernel.ι _ ≫ t.mapV t' h hπ hm) (by
    rw [← cancel_mono (kernel.ι (m' • 𝟙 t'.pushforwardGm))]
    simp only [Category.assoc, muDiff_ι, mapV_ι_assoc, zero_comp]
    simpa only [Category.assoc] using t.ιK₁_mapW_gmDiff t' h hπ c hc)

@[reassoc (attr := simp)]
lemma mapK₁_ι (hc : t'.vadd 1 ≫ h = h ≫ t.vadd (c • 1)) (hm : m ∣ m') :
    t.mapK₁ t' h hπ c hc hm ≫ kernel.ι _ = kernel.ι _ ≫ t.mapV t' h hπ hm :=
  kernel.lift_ι _ _ _

/-- The map `K₂ ⟶ K₂'`. -/
noncomputable def mapK₂ (hc : t'.vadd 1 ≫ h = h ≫ t.vadd (c • 1)) (hm : m ∣ m') :
    kernel (t.muDiff ≫ t.muDiff) ⟶ kernel (t'.muDiff ≫ t'.muDiff) :=
  kernel.lift _ (kernel.ι _ ≫ t.mapV t' h hπ hm) (by
    rw [← cancel_mono (kernel.ι (m' • 𝟙 t'.pushforwardGm))]
    simp only [Category.assoc, muDiff_ι, muDiff_ι_assoc, mapV_ι_assoc, zero_comp]
    simpa only [Category.assoc] using t.ιK₂_mapW_gmDiff_gmDiff t' h hπ c hc)

@[reassoc (attr := simp)]
lemma mapK₂_ι (hc : t'.vadd 1 ≫ h = h ≫ t.vadd (c • 1)) (hm : m ∣ m') :
    t.mapK₂ t' h hπ c hc hm ≫ kernel.ι _ = kernel.ι _ ≫ t.mapV t' h hπ hm :=
  kernel.lift_ι _ _ _

lemma mapK₂_comm₂₃ (hc : t'.vadd 1 ≫ h = h ≫ t.vadd (c • 1)) (hm : m ∣ m') :
    t.mapK₂ t' h hπ c hc hm ≫ kernelCompToKernel t'.muDiff =
      kernelCompToKernel t.muDiff ≫ (c • t.mapK₁ t' h hπ c hc hm) := by
  rw [← cancel_mono (kernel.ι _), ← cancel_mono (kernel.ι (m' • 𝟙 t'.pushforwardGm))]
  have hX := t.comp_transl_sub
    (kernel.ι (t.muDiff ≫ t.muDiff) ≫ kernel.ι (m • 𝟙 t.pushforwardGm)) t.ιK₂_gmDiff_gmDiff c
  have e₁ : ((kernelCompToKernel t.muDiff ≫ (c • t.mapK₁ t' h hπ c hc hm)) ≫ kernel.ι _) ≫
      kernel.ι (m' • 𝟙 t'.pushforwardGm) = c • (((kernel.ι (t.muDiff ≫ t.muDiff) ≫
        kernel.ι (m • 𝟙 t.pushforwardGm)) ≫ t.gmDiff) ≫ t.mapW t' h hπ) := by
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.assoc, mapK₁_ι_assoc,
      mapV_ι, kernelCompToKernel_ι_assoc, muDiff_ι_assoc]
  have e₂ : ((t.mapK₂ t' h hπ c hc hm ≫ kernelCompToKernel t'.muDiff) ≫ kernel.ι _) ≫
      kernel.ι (m' • 𝟙 t'.pushforwardGm) = ((kernel.ι (t.muDiff ≫ t.muDiff) ≫
        kernel.ι (m • 𝟙 t.pushforwardGm)) ≫ (t.transl c - 𝟙 _)) ≫ t.mapW t' h hπ := by
    simp only [Category.assoc, kernelCompToKernel_ι_assoc, mapK₂_ι_assoc, muDiff_ι, mapV_ι_assoc,
      t.mapW_gmDiff t' h hπ c hc]
  rw [e₁, e₂, hX, Preadditive.nsmul_comp]

/-- Pulling back along `h` is a morphism from the extension of `t` to that of `t'`, by `c` times
the natural map on the quotient. -/
noncomputable def extSeqMap (hc : t'.vadd 1 ≫ h = h ≫ t.vadd (c • 1)) (hm : m ∣ m') :
    t.extSeq ⟶ t'.extSeq where
  τ₁ := t.mapK₁ t' h hπ c hc hm
  τ₂ := t.mapK₂ t' h hπ c hc hm
  τ₃ := c • t.mapK₁ t' h hπ c hc hm
  comm₁₂ := by
    rw [← cancel_mono (kernel.ι _)]
    simp [kernelToKernelComp]
  comm₂₃ := t.mapK₂_comm₂₃ t' h hπ c hc hm

/-- The inclusion `μ_m ⊆ μ_{m'}` for `m ∣ m'`. -/
noncomputable def rootsOfUnityInclusion {X : Scheme.{u}} (m m' : ℕ) (hm : m ∣ m') :
    X.rootsOfUnitySheaf m ⟶ X.rootsOfUnitySheaf m' :=
  kernel.lift _ (kernel.ι (m • 𝟙 X.gmSheaf)) (by
    obtain ⟨e, rfl⟩ := hm
    have := kernel.condition (m • 𝟙 X.gmSheaf)
    rw [Preadditive.comp_nsmul, Category.comp_id] at this
    rw [Preadditive.comp_nsmul, Category.comp_id, mul_comm, mul_smul, this, smul_zero])

@[reassoc (attr := simp)]
lemma rootsOfUnityInclusion_ι {X : Scheme.{u}} (m m' : ℕ) (hm : m ∣ m') :
    rootsOfUnityInclusion (X := X) m m' hm ≫ kernel.ι (m' • 𝟙 X.gmSheaf) =
      kernel.ι (m • 𝟙 X.gmSheaf) :=
  kernel.lift_ι _ _ _

lemma muUnit_mapK₁ (hc : t'.vadd 1 ≫ h = h ≫ t.vadd (c • 1)) (hm : m ∣ m') :
    t.muUnit ≫ t.mapK₁ t' h hπ c hc hm = rootsOfUnityInclusion m m' hm ≫ t'.muUnit := by
  rw [← cancel_mono (kernel.ι _), ← cancel_mono (kernel.ι (m' • 𝟙 t'.pushforwardGm))]
  simp [muUnit, muUnitV, rootsOfUnityInclusion]

/-- Functoriality of the connecting homomorphism: `ι_* (δ_t x) = δ_{t'} (c • ι_* x)` for the
inclusion `ι : μ_m ⟶ μ_{m'}`. -/
lemma map_cupMu (hπ : h ≫ t.π = t'.π) (hc : t'.vadd 1 ≫ h = h ≫ t.vadd (c • 1))
    (hm : m ∣ m')
    (x : Sheaf.H (Y.rootsOfUnitySheaf m) 1) :
    Sheaf.H.map (rootsOfUnityInclusion m m' hm) 2 (t.cupMu x) =
      t'.cupMu (c • Sheaf.H.map (rootsOfUnityInclusion m m' hm) 1 x) := by
  have := t.isIso_muUnit
  have := t'.isIso_muUnit
  have e₁ : inv t.muUnit ≫ rootsOfUnityInclusion m m' hm =
      t.mapK₁ t' h hπ c hc hm ≫ inv t'.muUnit := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, muUnit_mapK₁, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  simp only [cupMu, AddMonoidHom.comp_apply]
  rw [← Sheaf.H.map_comp_apply, e₁, Sheaf.H.map_comp_apply]
  congr 1
  have h₁ := Sheaf.H.map_δSucc t.extSeq_shortExact t'.extSeq_shortExact
    (t.extSeqMap t' h hπ c hc hm) 1 (Sheaf.H.map t.muUnit 1 x)
  refine h₁.trans ?_
  congr 1
  have e := congrArg (fun f ↦ Sheaf.H.map f 1 x) (t.muUnit_mapK₁ t' h hπ c hc hm)
  simp only [Sheaf.H.map_comp_apply] at e
  rw [extSeqMap, Sheaf.H.map_nsmul_apply, map_nsmul]
  exact congrArg (c • ·) e

end AlgebraicGeometry.Scheme.EtaleTorsor
