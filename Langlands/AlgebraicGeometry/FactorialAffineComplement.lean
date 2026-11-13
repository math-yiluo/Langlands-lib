import Langlands.CommutativeAlgebra.FactorialLocalHartogs
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Stalk

/-! # Complements of affine opens near factorial points -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.FactorialAffineComplement

variable (O : CommRingCat.{u}) [IsDomain O]

instance nonempty_top : Nonempty (⊤ : (Spec O).Opens) :=
  ⟨⟨genericPoint (Spec O), trivial⟩⟩

/-- The germ in the function field of a global function of `Spec O` is its image in the
fraction field. -/
theorem germToFunctionField_top_ΓSpecIso_inv (r : O) :
    (Spec O).germToFunctionField ⊤ ((Scheme.ΓSpecIso O).inv r) =
      algebraMap O (Spec O).functionField r := rfl

variable [UniqueFactorizationMonoid O] [IsLocalRing O]

/-- On the spectrum of a factorial local domain having a nonzero non-maximal prime, the
complement of the closed point is not affine. -/
theorem not_isAffineOpen_punctured {q : Ideal O} (hq : q.IsPrime) (hq0 : q ≠ ⊥)
    (hqm : q ≠ IsLocalRing.maximalIdeal O) (P : (Spec O).Opens)
    (hP : ∀ p : Spec O, p ∈ P ↔ p ≠ IsLocalRing.closedPoint O) : ¬ IsAffineOpen P := by
  intro hPa
  let K := (Spec O).functionField
  have hgP : genericPoint (Spec O) ∈ P := by
    rw [hP, genericPoint_eq_bot_of_affine]
    intro h
    have h' := congrArg PrimeSpectrum.asIdeal h
    change (⊥ : Ideal O) = IsLocalRing.maximalIdeal O at h'
    exact hq0 (le_bot_iff.mp (h' ▸ IsLocalRing.le_maximalIdeal hq.ne_top))
  have : Nonempty P := ⟨⟨_, hgP⟩⟩
  let G := (Spec O).germToFunctionField P
  let ρ : O → Γ(Spec O, P) := fun r ↦
    (Spec O).presheaf.map (homOfLE (le_top : P ≤ ⊤)).op ((Scheme.ΓSpecIso O).inv r)
  have hGρ : ∀ r, G (ρ r) = algebraMap O K r := fun r ↦ by
    change (Spec O).presheaf.germ P _ hgP
      ((Spec O).presheaf.map (homOfLE (le_top : P ≤ ⊤)).op ((Scheme.ΓSpecIso O).inv r)) = _
    rw [TopCat.Presheaf.germ_res_apply]
    exact germToFunctionField_top_ΓSpecIso_inv O r
  have hint : ∀ c : Γ(Spec O, P), G c ∈ (algebraMap O K).range := by
    intro c
    have hH : ∀ f ∈ IsLocalRing.maximalIdeal O, f ≠ 0 →
        ∃ (k : ℕ) (a : O), algebraMap O K f ^ k * G c = algebraMap O K a := by
      intro f hf hf0
      let f' : Γ(Spec O, ⊤) := (Scheme.ΓSpecIso O).inv f
      let D := (Spec O).basicOpen f'
      have hDP : D ≤ P := by
        intro p hp
        rw [hP]
        rintro rfl
        have hp' : IsLocalRing.closedPoint O ∈ PrimeSpectrum.basicOpen f := by
          rw [← basicOpen_eq_of_affine]
          exact hp
        exact hp' hf
      have hgD : genericPoint (Spec O) ∈ D := by
        change genericPoint (Spec O) ∈ (Spec O).basicOpen ((Scheme.ΓSpecIso O).inv f)
        rw [basicOpen_eq_of_affine, genericPoint_eq_bot_of_affine]
        change f ∉ (⊥ : Ideal O)
        simpa using hf0
      have : IsLocalization.Away f' Γ(Spec O, D) :=
        (isAffineOpen_top _).isLocalization_basicOpen f'
      let cD : Γ(Spec O, D) := (Spec O).presheaf.map (homOfLE hDP).op c
      obtain ⟨⟨a', _, ⟨k, rfl⟩⟩, hk⟩ := IsLocalization.surj (Submonoid.powers f') cD
      refine ⟨k, (Scheme.ΓSpecIso O).hom a', ?_⟩
      have h1 := congrArg ((Spec O).presheaf.germ D _ hgD) hk
      simp only [map_mul, map_pow] at h1
      have e1 : (Spec O).presheaf.germ D _ hgD cD = G c :=
        TopCat.Presheaf.germ_res_apply _ _ _ _ _
      have e2 : ∀ g : Γ(Spec O, ⊤), (Spec O).presheaf.germ D _ hgD
          (algebraMap Γ(Spec O, ⊤) Γ(Spec O, D) g) = (Spec O).germToFunctionField ⊤ g :=
        fun g ↦ TopCat.Presheaf.germ_res_apply _ _ _ _ _
      have ha' : a' = (Scheme.ΓSpecIso O).inv ((Scheme.ΓSpecIso O).hom a') :=
        (Iso.hom_inv_id_apply _ _).symm
      rw [e1, e2, e2, germToFunctionField_top_ΓSpecIso_inv] at h1
      rw [ha', germToFunctionField_top_ΓSpecIso_inv] at h1
      rw [mul_comm]
      exact h1
    obtain ⟨a, ha⟩ := Langlands.CommutativeAlgebra.FactorialLocalHartogs.exists_eq_of_forall_pow_mul
      hq hq0 hqm (G c) hH
    exact ⟨a, ha⟩
  let s : Set Γ(Spec O, P) := ρ '' (IsLocalRing.maximalIdeal O : Set O)
  have hcov : P ≤ ⨆ f : s, (Spec O).basicOpen f.1 := by
    intro p hp
    have hpm : p ≠ IsLocalRing.closedPoint O := (hP p).mp hp
    have hlt : p.asIdeal < IsLocalRing.maximalIdeal O :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
        (fun h ↦ hpm (PrimeSpectrum.ext h))
    obtain ⟨f, hfm, hfp⟩ := SetLike.exists_of_lt hlt
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨⟨ρ f, f, hfm, rfl⟩, ?_⟩
    change p ∈ (Spec O).basicOpen ((Spec O).presheaf.map _ _)
    rw [Scheme.basicOpen_res]
    refine ⟨hp, ?_⟩
    change p ∈ (Spec O).basicOpen ((Scheme.ΓSpecIso O).inv f)
    rw [basicOpen_eq_of_affine]
    exact hfp
  have hspan : Ideal.span s = ⊤ := (hPa.self_le_iSup_basicOpen_iff).mp hcov
  let α := algebraMap O K
  have hα : Function.Injective α := IsFractionRing.injective O K
  let e : O ≃+* α.range := RingEquiv.ofBijective α.rangeRestrict
    ⟨fun x y h ↦ hα (congrArg Subtype.val h), α.rangeRestrict_surjective⟩
  let g : Γ(Spec O, P) →+* O := e.symm.toRingHom.comp (G.hom.codRestrict α.range hint)
  have hgρ : ∀ r, g (ρ r) = r := fun r ↦ by
    apply e.injective
    change e (e.symm _) = e r
    rw [RingEquiv.apply_symm_apply]
    apply Subtype.ext
    exact hGρ r
  have hspan' : Ideal.span (g '' s) = ⊤ := by
    rw [← Ideal.map_span, hspan, Ideal.map_top]
  have hgs : g '' s = (IsLocalRing.maximalIdeal O : Set O) := by
    rw [Set.image_image]
    simp only [hgρ, Set.image_id']
  rw [hgs, Ideal.span_eq] at hspan'
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top hspan'

/-- Let `W` be an affine open of a separated scheme and `z` a point outside `W` all of whose
proper generizations lie in `W`. If the stalk at `z` is a factorial domain, then `z` has no
chain `y₀ ⤳ y₁ ⤳ z` of proper generizations: the complement of `W` has codimension at most
one at `z`. -/
theorem false_of_generization_chain {X : Scheme.{u}} [X.IsSeparated] {W : X.Opens}
    (hW : IsAffineOpen W) {z y₀ y₁ : X} (hz : z ∉ W)
    (hgen : ∀ y : X, y ⤳ z → y ≠ z → y ∈ W) (h₀₁ : y₀ ⤳ y₁) (h₁z : y₁ ⤳ z)
    (hne₀₁ : y₀ ≠ y₁) (hne₁z : y₁ ≠ z)
    [IsDomain (X.presheaf.stalk z)] [UniqueFactorizationMonoid (X.presheaf.stalk z)] :
    False := by
  let O := X.presheaf.stalk z
  let φ := X.fromSpecStalk z
  have hemb : IsEmbedding φ := φ.isEmbedding
  have hφc : φ (IsLocalRing.closedPoint O) = z := Scheme.fromSpecStalk_closedPoint
  have hrange : ∀ y : X, y ⤳ z → ∃ p, φ p = y := fun y hy ↦ by
    have : y ∈ Set.range φ := by
      rw [Scheme.range_fromSpecStalk]
      exact hy
    exact this
  let P := φ ⁻¹ᵁ W
  have hP : ∀ p : Spec O, p ∈ P ↔ p ≠ IsLocalRing.closedPoint O := by
    intro p
    constructor
    · rintro hp rfl
      exact hz (hφc ▸ hp)
    · intro hp
      have h1 : φ p ⤳ z :=
        ((IsLocalRing.specializes_closedPoint p).map φ.continuous).trans (specializes_of_eq hφc)
      have h2 : φ p ≠ z := fun h ↦ hp (hemb.injective (h.trans hφc.symm))
      exact hgen _ h1 h2
  have hφa : IsAffineHom φ :=
    MorphismProperty.of_postcomp (W' := @IsSeparated) @IsAffineHom φ (terminal.from X)
      inferInstance (isAffineHom_of_isAffine _)
  have hPa : IsAffineOpen P := hW.preimage φ
  obtain ⟨p₁, rfl⟩ := hrange y₁ h₁z
  obtain ⟨p₀, rfl⟩ := hrange y₀ (h₀₁.trans h₁z)
  have hle : p₀ ⤳ p₁ := hemb.specializes_iff.mp h₀₁
  have hlt : p₀.asIdeal < p₁.asIdeal :=
    lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes _ _).mpr hle)
      (fun h ↦ hne₀₁ (congrArg φ (PrimeSpectrum.ext h)))
  refine not_isAffineOpen_punctured O p₁.isPrime (ne_bot_of_gt hlt) ?_ P hP hPa
  intro h
  apply hne₁z
  have hp₁ : p₁ = IsLocalRing.closedPoint O := PrimeSpectrum.ext h
  exact (congrArg φ hp₁).trans hφc

end Langlands.AlgebraicGeometry.FactorialAffineComplement
