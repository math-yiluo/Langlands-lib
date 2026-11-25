/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GradedLineFractionChart.GradedLineFractionChart
import all WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Overlap comparison over a fixed affine base

Source: Stacks Project, Constructions, Tags 01NK and 01O9.
(blueprint: lem-trf-graded-line-fraction-same-base).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

attribute [local irreducible] Scheme.GradedAlgebraData.relProj
attribute [local irreducible] Scheme.GradedAlgebraData.relProjι

private theorem fractionBaseFramePower_generator {T : Scheme.{u}} {L : T.Modules}
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    (W : T.Opens) (l : Γ(L, W)) (hl : IsFreeGenerator l) (n : ℕ) :
    IsFreeGenerator (P l n) := by
  induction n with
  | zero => rw [hP0]; exact isFreeGenerator_one W
  | succ n ih => rw [hPs]; exact hl.tmulSection ih

private theorem fractionBaseFramePower_eq {T : Scheme.{u}} {L : T.Modules}
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    (W : T.Opens) (l : Γ(L, W)) (n : ℕ) : P l n = tensorPowLocalSection l n := by
  induction n with
  | zero => exact hP0 W l
  | succ n ih => rw [hPs, ih]; rfl

private theorem fractionBaseFramePower_mul {T : Scheme.{u}} {L : T.Modules}
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    (W : T.Opens) (l : Γ(L, W)) (m n : ℕ) :
    (L.tensorPowAddIso m n).inv.app W (tmulSection (P l m) (P l n)) =
      P l (m + n) := by
  simp only [fractionBaseFramePower_eq P hP0 hPs]
  exact tensorPowLocalSection_mul l m n

section Coefficients

variable {S T : Scheme.{u}} {h : T ⟶ S} {A : S.GradedAlgebraData} {L : T.Modules}
  (ψ : RelativeGradedLineMap h A L)
  (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
  (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
  (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
    P l (n + 1) = tmulSection l (P l n))
  (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
  (l : Γ(L, W.1)) (hl : IsFreeGenerator l)
  (c : (n : ℕ) → A.grading U n → Γ(T, W.1))
  (hc : ∀ (n : ℕ) (a : A.grading U n), c n a • P l n =
    (L.tensorPow n).val.map (homOfLE hWU).op (ψ.component U n a))

include ψ P hP0 hPs U W hWU l hl c hc

private theorem fractionBaseCoefficient_zero (n : ℕ) : c n 0 = 0 := by
  apply (fractionBaseFramePower_generator P hP0 hPs W.1 l hl n).smul_left_injective
  simp only [hc, map_zero, zero_smul]

private theorem fractionBaseCoefficient_add (n : ℕ) (a b : A.grading U n) :
    c n (a + b) = c n a + c n b := by
  apply (fractionBaseFramePower_generator P hP0 hPs W.1 l hl n).smul_left_injective
  simp only [add_smul, hc, map_add]

private noncomputable def fractionBaseCoefficientAddHom (n : ℕ) :
    A.grading U n →+ Γ(T, W.1) where
  toFun := c n
  map_zero' := fractionBaseCoefficient_zero ψ P hP0 hPs U W hWU l hl c hc n
  map_add' := fractionBaseCoefficient_add ψ P hP0 hPs U W hWU l hl c hc n

private theorem fractionBaseCoefficient_one :
    c 0 ⟨1, SetLike.one_mem_graded (A.grading U)⟩ = 1 := by
  apply (fractionBaseFramePower_generator P hP0 hPs W.1 l hl 0).smul_left_injective
  dsimp only
  rw [hc, ψ.one, hP0, one_smul]
  change (𝟙_ T.Modules).presheaf.map (homOfLE hWU).op
    (unitSectionsEquiv (h ⁻¹ᵁ U.1) 1) = unitSectionsEquiv W.1 1
  rw [presheaf_map_unitSectionsEquiv]
  exact congrArg (unitSectionsEquiv W.1)
    (map_one (T.presheaf.map (homOfLE hWU).op).hom)

private theorem fractionBaseCoefficient_mul (m n : ℕ) (a : A.grading U m)
    (b : A.grading U n) :
    c (m + n) ⟨a * b, SetLike.mul_mem_graded a.property b.property⟩ = c m a * c n b := by
  apply (fractionBaseFramePower_generator P hP0 hPs W.1 l hl (m + n)).smul_left_injective
  dsimp only
  rw [hc, ψ.mul]
  erw [← Hom.app_presheaf_map]
  rw [tmulSection_map]
  erw [← hc m a, ← hc n b]
  rw [smul_tmulSection, tmulSection_smul, smul_smul, Hom.app_smul,
    fractionBaseFramePower_mul P hP0 hPs]

private noncomputable def fractionBaseCoefficientRingHom : A.obj U →+* Γ(T, W.1) := by
  let := A.gradedAlgebra U
  exact (DirectSum.toSemiring
    (fun n ↦ fractionBaseCoefficientAddHom ψ P hP0 hPs U W hWU l hl c hc n)
    (fractionBaseCoefficient_one ψ P hP0 hPs U W hWU l hl c hc)
    (fun {m n} a b ↦ fractionBaseCoefficient_mul ψ P hP0 hPs U W hWU l hl c hc m n a b)).comp
      (DirectSum.decomposeRingEquiv (A.grading U)).toRingHom

private theorem fractionBaseCoefficientRingHom_apply (n : ℕ) (a : A.grading U n) :
    fractionBaseCoefficientRingHom ψ P hP0 hPs U W hWU l hl c hc a.val = c n a := by
  let := A.gradedAlgebra U
  unfold fractionBaseCoefficientRingHom
  change (DirectSum.toSemiring _
    (fractionBaseCoefficient_one ψ P hP0 hPs U W hWU l hl c hc)
    (fun {m n} a b ↦ fractionBaseCoefficient_mul ψ P hP0 hPs U W hWU l hl c hc m n a b))
    (DirectSum.decompose (A.grading U) a.val) = _
  rw [DirectSum.decompose_coe, DirectSum.toSemiring_of]
  rfl

end Coefficients

private theorem fractionBase_unit_chart {R : Type u} [CommRing R]
    {σ : Type u} [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}}
    (φ : R →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map φ = ⊤)
    {t : R} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) (hu : IsUnit (φ t)) :
    ∃ r : X ⟶ Spec (.of (HomogeneousLocalization.Away 𝒜 t)),
      r ≫ Proj.awayι 𝒜 t ht hd = Proj.fromOfGlobalSections 𝒜 φ hf ∧
      ∀ (m : ℕ) (b : R) (hb : b ∈ 𝒜 (m • d)),
        ((Scheme.ΓSpecIso _).inv ≫ r.appTop)
          (HomogeneousLocalization.Away.mk 𝒜 ht m b hb) * φ t ^ m = φ b := by
  have hbo : X.basicOpen (φ t) = ⊤ := X.basicOpen_of_isUnit hu
  have hι : IsIso (X.basicOpen (φ t)).ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _
      ((Scheme.Opens.opensRange_ι _).trans hbo)
  have hxle : Submonoid.powers t ≤ (Submonoid.powers (φ t)).comap φ :=
    Submonoid.powers_le.mpr (Submonoid.mem_powers _)
  let F := IsLocalization.map (S := Localization.Away t) (Localization.Away (φ t)) φ hxle
  let Θ := F.comp (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t))
  let r := inv (X.basicOpen (φ t)).ι ≫ X.toSpecAway (φ t) ≫
    Spec.map (CommRingCat.ofHom Θ)
  refine ⟨r, ?_, ?_⟩
  · have key : X.toSpecAway (φ t) ≫ Spec.map (CommRingCat.ofHom Θ) =
        Proj.toBasicOpenOfGlobalSections 𝒜 φ rfl hd ht ≫
          (Proj.basicOpenIsoSpec 𝒜 t ht hd).hom := by
      rw [Proj.toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom 𝒜 φ rfl hd ht hxle,
        Scheme.toSpecAway, Category.assoc]
    have hbi : (Proj.basicOpenIsoSpec 𝒜 t ht hd).hom ≫ Proj.awayι 𝒜 t ht hd =
        (Proj.basicOpen 𝒜 t).ι := by
      rw [← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
    dsimp only [r]
    rw [Category.assoc, key, Category.assoc, hbi,
      ← Proj.ι_comp_fromOfGlobalSections 𝒜 φ hf hd ht, IsIso.inv_hom_id_assoc]
  · intro m b hb
    let K : CommRingCat.of (Localization.Away (φ t)) ⟶ Γ(X, ⊤) :=
      (Scheme.ΓSpecIso _).inv ≫ (X.toSpecAway (φ t)).appTop ≫
        (inv (X.basicOpen (φ t)).ι).appTop
    have hK : CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away (φ t))) ≫ K =
        𝟙 _ := by
      have e := Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away (φ t))))
      have e3 : inv (X.basicOpen (φ t)).ι ≫ X.toSpecAway (φ t) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap Γ(X, ⊤) (Localization.Away (φ t)))) = X.toSpecΓ := by
        rw [Scheme.toSpecAway_SpecMap_algebraMap, IsIso.inv_hom_id_assoc]
      dsimp only [K]
      rw [reassoc_of% e, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
        Category.assoc, e3, Scheme.toSpecΓ_appTop]
      exact (Scheme.ΓSpecIso Γ(X, ⊤)).inv_hom_id
    have hscalar : (Scheme.ΓSpecIso _).inv ≫ r.appTop = CommRingCat.ofHom Θ ≫ K := by
      dsimp only [r, K]
      simp only [Scheme.Hom.comp_appTop, Category.assoc]
      rw [← reassoc_of% (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom Θ))]
    have hmk : Θ (HomogeneousLocalization.Away.mk 𝒜 ht m b hb) *
        algebraMap Γ(X, ⊤) (Localization.Away (φ t)) (φ t) ^ m =
          algebraMap Γ(X, ⊤) (Localization.Away (φ t)) (φ b) := by
      have h := IsLocalization.mk'_spec (S := Localization.Away t) b
        (⟨t ^ m, m, rfl⟩ : Submonoid.powers t)
      have hh := congrArg F h
      simpa only [Θ, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
        HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', map_mul, map_pow,
        F, IsLocalization.map_eq] using hh
    rw [hscalar]
    have hh := congrArg K hmk
    have hKa (c : Γ(X, ⊤)) : K (algebraMap Γ(X, ⊤) (Localization.Away (φ t)) c) = c :=
      congrArg (fun g : Γ(X, ⊤) ⟶ Γ(X, ⊤) ↦ g c) hK
    change K (Θ (HomogeneousLocalization.Away.mk 𝒜 ht m b hb)) * φ t ^ m = φ b
    simpa only [map_mul, map_pow, hKa] using hh

private theorem fractionBase_spec_eq {R Q : Type u} [CommRing R] [CommRing Q]
    {σ : Type u} [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (φ : R →+* Q)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map φ = ⊤)
    {t : R} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) (hu : IsUnit (φ t))
    (q : HomogeneousLocalization.Away 𝒜 t →+* Q)
    (hq : ∀ (m : ℕ) (b : R) (hb : b ∈ 𝒜 (m • d)),
      q (HomogeneousLocalization.Away.mk 𝒜 ht m b hb) * φ t ^ m = φ b) :
    Spec.map (CommRingCat.ofHom q) ≫ Proj.awayι 𝒜 t ht hd =
      Proj.fromOfGlobalSections 𝒜 ((Scheme.ΓSpecIso (.of Q)).inv.hom.comp φ)
        (by rw [← Ideal.map_map, hf, Ideal.map_top]) := by
  let Φ := (Scheme.ΓSpecIso (.of Q)).inv.hom.comp φ
  have hΦ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map Φ = ⊤ := by
    rw [← Ideal.map_map, hf, Ideal.map_top]
  obtain ⟨r, hr, hfrac⟩ := fractionBase_unit_chart 𝒜 Φ hΦ hd ht
    (hu.map (Scheme.ΓSpecIso (.of Q)).inv.hom)
  have heq : Spec.map (CommRingCat.ofHom q) = r := by
    apply ext_to_Spec
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    obtain ⟨m, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 ht z
    apply ((hu.map (Scheme.ΓSpecIso (.of Q)).inv.hom).pow m).mul_right_cancel
    change ((Scheme.ΓSpecIso _).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop)
        (HomogeneousLocalization.Away.mk 𝒜 ht m b hb) * Φ t ^ m =
      ((Scheme.ΓSpecIso _).inv ≫ r.appTop)
        (HomogeneousLocalization.Away.mk 𝒜 ht m b hb) * Φ t ^ m
    calc
      _ = Φ b := by
        rw [← Scheme.ΓSpecIso_inv_naturality]
        change (Scheme.ΓSpecIso (.of Q)).inv
          (q (HomogeneousLocalization.Away.mk 𝒜 ht m b hb)) *
            (Scheme.ΓSpecIso (.of Q)).inv (φ t) ^ m = _
        rw [← map_pow, ← map_mul, hq]
        rfl
      _ = _ := (hfrac m b hb).symm
  rw [heq, hr]

private theorem fractionBase_power_restrict {T : Scheme.{u}} {L : T.Modules}
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    {W B : T.Opens} (hB : B ≤ W) (l : Γ(L, W)) (n : ℕ) :
    (L.tensorPow n).presheaf.map (homOfLE hB).op (P l n) =
      P (L.presheaf.map (homOfLE hB).op l) n := by
  induction n with
  | zero =>
    rw [hP0, hP0]
    change (𝟙_ T.Modules).presheaf.map (homOfLE hB).op
      (unitSectionsEquiv W 1) = unitSectionsEquiv B 1
    rw [presheaf_map_unitSectionsEquiv, map_one]
  | succ n ih =>
    rw [hPs, hPs]
    change (L ⊗ L.tensorPow n).presheaf.map (homOfLE hB).op (tmulSection l (P l n)) =
      tmulSection (L.presheaf.map (homOfLE hB).op l) _
    rw [tmulSection_map, ih]

private theorem fractionBase_power_smul {T : Scheme.{u}} {L : T.Modules}
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    {W : T.Opens} (u : Γ(T, W)) (l : Γ(L, W)) (n : ℕ) :
    P (u • l) n = u ^ n • P l n := by
  induction n with
  | zero => rw [hP0, hP0, pow_zero, one_smul]
  | succ n ih =>
    rw [hPs, hPs, ih, smul_tmulSection, tmulSection_smul, smul_smul,
      pow_succ, mul_comm u]

private theorem fractionBase_restrict_relation
    {S T : Scheme.{u}} {h : T ⟶ S} {A : S.GradedAlgebraData} {L : T.Modules}
    (ψ : RelativeGradedLineMap h A L)
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    (c : GradedLineFractionCoefficients h A L)
    (hc : ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
      (l : Γ(L, W.1)), IsFreeGenerator l → ∀ (n : ℕ) (a : A.grading U n),
      c U W hWU l n a • P l n =
        (L.tensorPow n).val.map (homOfLE hWU).op (ψ.component U n a))
    (i : GradedLineFractionChart h A L) {W : T.Opens} (hWi : W ≤ i.W.1)
    (n : ℕ) (a : A.grading i.U n) :
    T.presheaf.map (homOfLE hWi).op (c i.U i.W i.hWU i.l n a) •
        P (L.presheaf.map (homOfLE hWi).op i.l) n =
      (L.tensorPow n).presheaf.map (homOfLE (hWi.trans i.hWU)).op
        (ψ.component i.U n a) := by
  have hh := congrArg ((L.tensorPow n).presheaf.map (homOfLE hWi).op)
    (hc i.U i.W i.hWU i.l i.hl n a)
  change (L.tensorPow n).presheaf.map (homOfLE hWi).op
      (c i.U i.W i.hWU i.l n a • P i.l n) =
    (L.tensorPow n).presheaf.map (homOfLE hWi).op
      ((L.tensorPow n).presheaf.map (homOfLE i.hWU).op (ψ.component i.U n a)) at hh
  rw [map_smul, fractionBase_power_restrict P hP0 hPs, presheaf_map_map_apply] at hh
  refine hh.trans ?_
  exact congrArg (fun f : W ⟶ h ⁻¹ᵁ i.U.1 ↦
    (L.tensorPow n).presheaf.map f.op (ψ.component i.U n a)) (Subsingleton.elim _ _)

private theorem fractionBase_chart
    {S T : Scheme.{u}} {h : T ⟶ S} {A : S.GradedAlgebraData} {L : T.Modules}
    (ψ : RelativeGradedLineMap h A L)
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    (c : GradedLineFractionCoefficients h A L)
    (hc : ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
      (l : Γ(L, W.1)), IsFreeGenerator l → ∀ (n : ℕ) (a : A.grading U n),
      c U W hWU l n a • P l n =
        (L.tensorPow n).val.map (homOfLE hWU).op (ψ.component U n a))
    (ρ : ∀ i : GradedLineFractionChart h A L,
      HomogeneousLocalization.Away (A.grading i.U) i.e.val →+*
        Localization.Away (i.coefficient c))
    (hρ : GradedLineFractionChart.FractionFormula c ρ)
    (i : GradedLineFractionChart h A L) (W : T.affineOpens) (hWi : W ≤ i.W)
    (hD : W.1 ≤ T.basicOpen (i.coefficient c)) :
    ∃ (α : Spec (.of Γ(T, W.1)) ⟶ i.domain c) (φ : A.obj i.U →+* Γ(T, W.1))
      (hf : (HomogeneousIdeal.irrelevant (A.grading i.U)).toIdeal.map φ = ⊤),
      α ≫ i.source c = W.2.fromSpec ∧
      α ≫ i.target c ρ = Proj.fromOfGlobalSections (A.grading i.U)
        ((Scheme.ΓSpecIso (.of Γ(T, W.1))).inv.hom.comp φ)
        (by rw [← Ideal.map_map, hf, Ideal.map_top]) ≫ A.relProjι i.U ∧
      ∀ (n : ℕ) (a : A.grading i.U n),
        φ a.val = T.presheaf.map (homOfLE (X := T.Opens) hWi).op
          (c i.U i.W i.hWU i.l n a) := by
  let := A.gradedAlgebra i.U
  let res : Γ(T, i.W.1) →+* Γ(T, W.1) :=
    (T.presheaf.map (homOfLE (X := T.Opens) hWi).op).hom
  let φ := res.comp (fractionBaseCoefficientRingHom ψ P hP0 hPs i.U i.W i.hWU
    i.l i.hl (c i.U i.W i.hWU i.l) (hc i.U i.W i.hWU i.l i.hl))
  have hφ (n : ℕ) (a : A.grading i.U n) : φ a.val =
      res (c i.U i.W i.hWU i.l n a) := by
    dsimp only [φ, RingHom.comp_apply]
    rw [fractionBaseCoefficientRingHom_apply]
  have hu : IsUnit (res (i.coefficient c)) := T.isUnit_map_of_le_basicOpen _ hD
  have hunit (y : Submonoid.powers (i.coefficient c)) : IsUnit (res y) := by
    obtain ⟨y, n, rfl⟩ := y
    rw [map_pow]
    exact hu.pow n
  let f : Localization.Away (i.coefficient c) →+* Γ(T, W.1) :=
    IsLocalization.lift hunit
  let α : Spec (.of Γ(T, W.1)) ⟶ i.domain c := Spec.map (CommRingCat.ofHom f)
  have halg : CommRingCat.ofHom
      (algebraMap Γ(T, i.W.1) (Localization.Away (i.coefficient c))) ≫
        CommRingCat.ofHom f = T.presheaf.map (homOfLE (X := T.Opens) hWi).op := by
    ext z
    exact IsLocalization.lift_eq hunit z
  have hsource : α ≫ i.source c = W.2.fromSpec := by
    dsimp only [α, GradedLineFractionChart.source]
    rw [← Category.assoc, ← Spec.map_comp, halg]
    rw [reassoc_of% (specMap_res_isoSpec_inv (X := T) hWi), Scheme.homOfLE_ι]
    rfl
  have hφe : IsUnit (φ i.e.val) := by rw [hφ]; exact hu
  have hf : (HomogeneousIdeal.irrelevant (A.grading i.U)).toIdeal.map φ = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _
      (Ideal.mem_map_of_mem φ (HomogeneousIdeal.mem_irrelevant_of_mem _ i.hd i.e.property)) hφe
  have hq (m : ℕ) (b : A.obj i.U) (hb : b ∈ A.grading i.U (m • i.d)) :
      (f.comp (ρ i)) (HomogeneousLocalization.Away.mk (A.grading i.U) i.e.property m b hb) *
        φ i.e.val ^ m = φ b := by
    rw [hφ i.d i.e, hφ (m • i.d) ⟨b, hb⟩]
    change f (ρ i _) * res (i.coefficient c) ^ m = _
    rw [hρ i m ⟨b, hb⟩]
    have hh := congrArg f (IsLocalization.mk'_spec
      (S := Localization.Away (i.coefficient c))
      (c i.U i.W i.hWU i.l (m • i.d) ⟨b, hb⟩)
      (⟨i.coefficient c ^ m, m, rfl⟩ : Submonoid.powers (i.coefficient c)))
    simpa only [map_mul, map_pow, Localization.mk_eq_mk', f, IsLocalization.lift_eq]
      using hh
  have hfactor : α ≫ Spec.map (CommRingCat.ofHom (ρ i)) ≫
        Proj.awayι (A.grading i.U) i.e.val i.e.property i.hd =
      Proj.fromOfGlobalSections (A.grading i.U)
        ((Scheme.ΓSpecIso (.of Γ(T, W.1))).inv.hom.comp φ)
        (by rw [← Ideal.map_map, hf, Ideal.map_top]) := by
    rw [← Category.assoc]
    change (Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (ρ i))) ≫ _ = _
    rw [← Spec.map_comp]
    exact fractionBase_spec_eq (A.grading i.U) φ hf i.hd i.e.property hφe (f.comp (ρ i)) hq
  refine ⟨α, φ, hf, hsource, ?_, hφ⟩
  simpa only [GradedLineFractionChart.target, ← Category.assoc]
    using congrArg (fun g ↦ g ≫ A.relProjι i.U) hfactor

/-- Fraction charts over one fixed affine base agree on their source pullback.
The source frames, their affine opens, and the positive degrees may differ.

Source: Stacks Project, Constructions, Tag 01NK, proof of
lemma-invertible-map-into-proj (uniqueness and the affine construction).
(blueprint: lem-trf-graded-line-fraction-same-base).

Proof: Refine the intersection of the two framed source opens by affine opens B.
Restrict both frames to B; their ratio is a unit. Induction using hP0 and hPs shows
that P commutes with restriction and takes a unit multiple of a frame to the same
unit to the n-th power times its n-th frame power. These powers are free generators,
so hc identifies the two systems of homogeneous coefficients up to these unit powers.
The unit, addition, and multiplication laws of psi make either system the homogeneous
parts of an explicitly constructed ring map A(U) to O(B). Choose B inside the two
coefficient basic opens, so both selected denominator coefficients are units. On either
chart the prescribed fraction map agrees with the standard chart factorization of
Proj.fromOfGlobalSections: both satisfy the same fraction-times-denominator equation,
and its denominator is a unit. Homogeneous-fraction surjectivity and the affine
adjunction therefore identify the morphisms. The proved unit-power invariance theorem
for fromOfGlobalSections then identifies the two maps into Proj A(U). Compose with the
single common relative-Proj chart embedding. The two source morphisms lift to the
original pullback; this lift is an open immersion and its range contains the point
under consideration. Scheme morphism locality on these ranges proves the result.
Empty opens and nilpotent coefficients give empty localization spectra; no domain
assumption is used. -/
theorem gradedLineFraction_sameBase
    {S T : Scheme.{u}} {h : T ⟶ S} {A : S.GradedAlgebraData} {L : T.Modules}
    (ψ : RelativeGradedLineMap h A L)
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    (c : GradedLineFractionCoefficients h A L)
    (hc : ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
      (l : Γ(L, W.1)), IsFreeGenerator l → ∀ (n : ℕ) (a : A.grading U n),
      c U W hWU l n a • P l n =
        (L.tensorPow n).val.map (homOfLE hWU).op (ψ.component U n a))
    (ρ : ∀ i : GradedLineFractionChart h A L,
      HomogeneousLocalization.Away (A.grading i.U) i.e.val →+*
        Localization.Away (i.coefficient c))
    (hρ : GradedLineFractionChart.FractionFormula c ρ) (i j : GradedLineFractionChart h A L)
    (hU : i.U = j.U) :
    pullback.fst (i.source c) (j.source c) ≫ i.target c ρ =
      pullback.snd (i.source c) (j.source c) ≫ j.target c ρ := by
  classical
  rcases i with ⟨U, Wi, hi, li, hli, di, hdi, ei⟩
  rcases j with ⟨V, Wj, hj, lj, hlj, dj, hdj, ej⟩
  dsimp only at hU
  subst V
  let i : GradedLineFractionChart h A L := ⟨U, Wi, hi, li, hli, di, hdi, ei⟩
  let j : GradedLineFractionChart h A L := ⟨U, Wj, hj, lj, hlj, dj, hdj, ej⟩
  change pullback.fst (i.source c) (j.source c) ≫ i.target c ρ =
    pullback.snd (i.source c) (j.source c) ≫ j.target c ρ
  let := A.gradedAlgebra U
  let p := pullback.fst (i.source c) (j.source c)
  let q := pullback.snd (i.source c) (j.source c)
  let r := p ≫ i.source c
  have hr : r = q ≫ j.source c := pullback.condition
  have hrange (k : GradedLineFractionChart h A L) :
      (k.source c).opensRange = T.basicOpen (k.coefficient c) := by
    change (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(T, k.W.1) (Localization.Away (k.coefficient c)))) ≫
        k.W.2.fromSpec).opensRange = _
    rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_localizationAway,
      k.W.2.fromSpec_image_basicOpen]
  apply Scheme.hom_ext_of_forall
  intro x
  have hxi : r x ∈ T.basicOpen (i.coefficient c) := by
    rw [← hrange i]
    exact ⟨p x, rfl⟩
  have hxj : r x ∈ T.basicOpen (j.coefficient c) := by
    rw [← hrange j, hr]
    exact ⟨q x, rfl⟩
  obtain ⟨W₀, hW₀, hxW, hW⟩ := exists_isAffineOpen_mem_and_subset
    (show r x ∈ T.basicOpen (i.coefficient c) ⊓ T.basicOpen (j.coefficient c)
      from ⟨hxi, hxj⟩)
  let W : T.affineOpens := ⟨W₀, hW₀⟩
  have hDi : W.1 ≤ T.basicOpen (i.coefficient c) := hW.trans inf_le_left
  have hDj : W.1 ≤ T.basicOpen (j.coefficient c) := hW.trans inf_le_right
  have hWi : W ≤ i.W := hDi.trans (T.basicOpen_le _)
  have hWj : W ≤ j.W := hDj.trans (T.basicOpen_le _)
  obtain ⟨αi, φi, hφi, hsi, hti, hci⟩ :=
    fractionBase_chart ψ P hP0 hPs c hc ρ hρ i W hWi hDi
  obtain ⟨αj, φj, hφj, hsj, htj, hcj⟩ :=
    fractionBase_chart ψ P hP0 hPs c hc ρ hρ j W hWj hDj
  let liW := L.presheaf.map (homOfLE (X := T.Opens) hWi).op li
  let ljW := L.presheaf.map (homOfLE (X := T.Opens) hWj).op lj
  have hliW : IsFreeGenerator liW := hli.map hWi
  have hljW : IsFreeGenerator ljW := hlj.map hWj
  obtain ⟨u, hu⟩ := hljW.exists_unit_smul_eq hliW
  have hscale (n : ℕ) (a : A.obj U) (ha : a ∈ A.grading U n) :
      φj a = (u : Γ(T, W.1)) ^ n * φi a := by
    have hei := fractionBase_restrict_relation ψ P hP0 hPs c hc i hWi n ⟨a, ha⟩
    have hej := fractionBase_restrict_relation ψ P hP0 hPs c hc j hWj n ⟨a, ha⟩
    rw [← hci n ⟨a, ha⟩] at hei
    rw [← hcj n ⟨a, ha⟩] at hej
    apply (fractionBaseFramePower_generator P hP0 hPs W.1 ljW hljW n).smul_left_injective
    calc
      φj a • P ljW n = _ := hej
      _ = φi a • P liW n := hei.symm
      _ = _ := by
        rw [hu, fractionBase_power_smul P hP0 hPs, smul_smul, mul_comm (φi a)]
  let v : Γ(Spec (.of Γ(T, W.1)), ⊤)ˣ :=
    Units.map (Scheme.ΓSpecIso (.of Γ(T, W.1))).inv.hom.toMonoidHom u
  have hΦscale (n : ℕ) (a : A.obj U) (ha : a ∈ A.grading U n) :
      ((Scheme.ΓSpecIso (.of Γ(T, W.1))).inv.hom.comp φj) a =
        (v : Γ(Spec (.of Γ(T, W.1)), ⊤)) ^ n *
          ((Scheme.ΓSpecIso (.of Γ(T, W.1))).inv.hom.comp φi) a := by
    change (Scheme.ΓSpecIso (.of Γ(T, W.1))).inv (φj a) =
      (Scheme.ΓSpecIso (.of Γ(T, W.1))).inv (u : Γ(T, W.1)) ^ n *
        (Scheme.ΓSpecIso (.of Γ(T, W.1))).inv (φi a)
    rw [hscale n a ha, map_mul, map_pow]
  have hΦi : (HomogeneousIdeal.irrelevant (A.grading U)).toIdeal.map
      ((Scheme.ΓSpecIso (.of Γ(T, W.1))).inv.hom.comp φi) = ⊤ := by
    rw [← Ideal.map_map, hφi, Ideal.map_top]
  have hΦj : (HomogeneousIdeal.irrelevant (A.grading U)).toIdeal.map
      ((Scheme.ΓSpecIso (.of Γ(T, W.1))).inv.hom.comp φj) = ⊤ := by
    rw [← Ideal.map_map, hφj, Ideal.map_top]
  have hProj := Proj.fromOfGlobalSections_eq_of_unit_pow_mul (A.grading U) v
    ((Scheme.ΓSpecIso (.of Γ(T, W.1))).inv.hom.comp φi)
    ((Scheme.ΓSpecIso (.of Γ(T, W.1))).inv.hom.comp φj) hΦscale hΦi hΦj
  have htarget : αi ≫ i.target c ρ = αj ≫ j.target c ρ := by
    rw [hti, htj, hProj]
  let a := pullback.lift αi αj (hsi.trans hsj.symm)
  have har : a ≫ r = W.2.fromSpec := by
    dsimp only [a, r, p]
    rw [← Category.assoc, pullback.lift_fst, hsi]
  have : IsOpenImmersion (a ≫ r) := by rw [har]; infer_instance
  have : IsOpenImmersion a := IsOpenImmersion.of_comp a r
  have hxO : x ∈ a.opensRange := by
    have hm : r x ∈ W.2.fromSpec.opensRange := by
      rw [W.2.opensRange_fromSpec]
      exact hxW
    obtain ⟨z, hz⟩ := hm
    refine ⟨z, r.isOpenEmbedding.injective ?_⟩
    change (a ≫ r) z = r x
    rw [har]
    exact hz
  have hlocal : a ≫ p ≫ i.target c ρ = a ≫ q ≫ j.target c ρ := by
    dsimp only [a, p, q]
    rw [← Category.assoc, ← Category.assoc, pullback.lift_fst, pullback.lift_snd]
    exact htarget
  refine ⟨a.opensRange, hxO, ?_⟩
  have heq := congrArg (fun g ↦ a.isoOpensRange.inv ≫ g) hlocal
  simpa only [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp] using heq

end AlgebraicGeometry.Scheme.Modules
