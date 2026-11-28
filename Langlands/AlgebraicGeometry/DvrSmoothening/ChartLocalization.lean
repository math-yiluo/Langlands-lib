import Langlands.AlgebraicGeometry.DvrSmoothening.Charts

/-! # Charts on affine opens, their structure maps, and localizations -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

/-- The localization of an intersection of primes away from `s` is the intersection of the
extended primes not containing `s`. -/
theorem map_sInf_eq {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A'] (s : A)
    [IsLocalization.Away s A'] (S : Set (Ideal A)) (hS : ∀ q ∈ S, q.IsPrime) :
    (sInf S).map (algebraMap A A') =
      sInf (Ideal.map (algebraMap A A') '' {q | q ∈ S ∧ s ∉ q}) := by
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨q, ⟨hq, -⟩, rfl⟩
    exact Ideal.map_mono (sInf_le hq)
  · intro x hx
    obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, hxa⟩ := IsLocalization.surj (Submonoid.powers s) x
    simp only at hxa
    have hsa : s * a ∈ sInf S := by
      rw [Submodule.mem_sInf]
      intro q hq
      have := hS q hq
      by_cases hs : s ∈ q
      · exact Ideal.mul_mem_right _ _ hs
      · apply Ideal.mul_mem_left
        have hmem : algebraMap A A' a ∈ Ideal.map (algebraMap A A') q := by
          rw [← hxa]
          exact Ideal.mul_mem_right _ _ ((Submodule.mem_sInf.mp hx) _ ⟨q, ⟨hq, hs⟩, rfl⟩)
        have hdisj : Disjoint (Submonoid.powers s : Set A) q :=
          (Ideal.disjoint_powers_iff_notMem_of_isPrime s).mpr hs
        rw [← IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers s) A' ‹_› hdisj]
        exact hmem
    have hx' : x * algebraMap A A' (s ^ (k + 1)) = algebraMap A A' (s * a) := by
      rw [pow_succ', map_mul, map_mul, ← hxa]
      ring
    have hu : IsUnit (algebraMap A A' (s ^ (k + 1))) :=
      IsLocalization.map_units A' (⟨_, k + 1, rfl⟩ : Submonoid.powers s)
    have hxe : x = algebraMap A A' (s * a) * ↑hu.unit⁻¹ := by
      rw [← hx', mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [hxe]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hsa)

namespace AffineChart

variable {R : Type u} [CommRing R]

theorem restrict_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (x : Γ(Y, ⊤)) :
    X.presheaf.map (homOfLE le_top).op (f.appTop x) = f.appLE ⊤ U le_top x :=
  rfl

/-- The structure map of the chart of an affine open. -/
theorem base_ofAffineOpen {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.affineOpens) :
    (ofAffineOpen U).base f =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top).hom := by
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (CommRingCat.of R)))
    U.2 le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h1
  have h : Spec.map (CommRingCat.ofHom ((ofAffineOpen U).base f)) =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top) := by
    rw [Spec_base, Spec.map_comp, h1]
    rfl
  exact congrArg CommRingCat.Hom.hom (Spec_map_injective h)

/-- The restriction of the pull-back of a global function of `Spec R` to an affine open. -/
theorem restrict_appTop_eq_base {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.affineOpens) (r : R) :
    X.presheaf.map (homOfLE le_top).op (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
      (ofAffineOpen U).base f r := by
  rw [restrict_appTop, base_ofAffineOpen]
  rfl

/-- The structure maps of charts of affine opens are compatible with `appLE`. -/
theorem base_comp {X X₂ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : X₂ ⟶ X)
    (U : X.affineOpens) (U₂ : X₂.affineOpens) (h : (U₂ : X₂.Opens) ≤ g ⁻¹ᵁ U) :
    (ofAffineOpen U₂).base (g ≫ f) = (g.appLE U U₂ h).hom.comp ((ofAffineOpen U).base f) := by
  rw [base_ofAffineOpen, base_ofAffineOpen, ← Scheme.Hom.appLE_comp_appLE g f ⊤ U U₂ le_top h]
  rfl

/-- Points read in the charts of affine opens are compatible with `appLE`. -/
theorem pointHom_comp {X X₂ : Scheme.{u}} {R' : Type u} [CommRing R'] [IsLocalRing R']
    (g : X₂ ⟶ X) (U : X.affineOpens) (U₂ : X₂.affineOpens) (h : (U₂ : X₂.Opens) ≤ g ⁻¹ᵁ U)
    (a : Spec (CommRingCat.of R') ⟶ X₂) (a₁ : Spec (CommRingCat.of R') ⟶ X) (ha : a ≫ g = a₁)
    (h₂ : a (IsLocalRing.closedPoint R') ∈ (ofAffineOpen U₂).ι.opensRange)
    (h₁ : a₁ (IsLocalRing.closedPoint R') ∈ (ofAffineOpen U).ι.opensRange) :
    (ofAffineOpen U).pointHom a₁ h₁ =
      ((ofAffineOpen U₂).pointHom a h₂).comp (g.appLE U U₂ h).hom := by
  apply pointHom_eq_of_Spec
  have e := Spec.map_comp (g.appLE U U₂ h) (CommRingCat.ofHom ((ofAffineOpen U₂).pointHom a h₂))
  change Spec.map (g.appLE U U₂ h ≫ CommRingCat.ofHom ((ofAffineOpen U₂).pointHom a h₂)) ≫
    U.2.fromSpec = a₁
  rw [e, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec g U.2 U₂.2 h, ← ha]
  erw [Spec_pointHom]
  change (ofAffineOpen U₂).liftPoint a h₂ ≫ (ofAffineOpen U₂).ι ≫ g = _
  rw [liftPoint_ι_assoc]

end AffineChart

/-- A morphism which is an isomorphism over an open induces an isomorphism on its sections. -/
theorem isIso_app_of_isIso_restrict {X X₂ : Scheme.{u}} (g : X₂ ⟶ X) (V : X.Opens)
    [IsIso (g ∣_ V)] : IsIso (g.app V) := by
  have hι : IsOpenImmersion ((g ⁻¹ᵁ V).ι ≫ g) := by
    rw [← morphismRestrict_ι]; infer_instance
  have hrange : V ≤ ((g ⁻¹ᵁ V).ι ≫ g).opensRange := by
    have : ((g ⁻¹ᵁ V).ι ≫ g).opensRange = V := by
      have e : (g ⁻¹ᵁ V).ι ≫ g = g ∣_ V ≫ V.ι := (morphismRestrict_ι g V).symm
      simp only [e, Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
    rw [this]
  have h1 := Scheme.Hom.isIso_app ((g ⁻¹ᵁ V).ι ≫ g) V hrange
  rw [Scheme.Hom.comp_app] at h1
  have : IsIso ((g ⁻¹ᵁ V).ι.app (g ⁻¹ᵁ V)) :=
    Scheme.Hom.isIso_app _ _ (by simp)
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ this h1

/-- If `g` is an isomorphism over a basic open `D(s)` of an affine open `U`, the sections of
`g` over the preimage of `D(s)` are a localization of the sections over `U` away from `s`. -/
theorem isLocalization_appLE {X X₂ : Scheme.{u}} (g : X₂ ⟶ X) (U : X.affineOpens)
    (s : Γ(X, U)) [IsIso (g ∣_ X.basicOpen s)] (h : g ⁻¹ᵁ X.basicOpen s ≤ g ⁻¹ᵁ U) :
    letI := (g.appLE U (g ⁻¹ᵁ X.basicOpen s) h).hom.toAlgebra
    IsLocalization.Away s Γ(X₂, g ⁻¹ᵁ X.basicOpen s) := by
  letI := (g.appLE U (g ⁻¹ᵁ X.basicOpen s) h).hom.toAlgebra
  have hV : IsLocalization.Away s Γ(X, X.basicOpen s) := U.2.isLocalization_basicOpen s
  have := isIso_app_of_isIso_restrict g (X.basicOpen s)
  let e : Γ(X, X.basicOpen s) ≃ₐ[Γ(X, U)] Γ(X₂, g ⁻¹ᵁ X.basicOpen s) :=
    { (asIso (g.app (X.basicOpen s))).commRingCatIsoToRingEquiv with
      commutes' := fun r => by
        change (g.app _) (X.presheaf.map (homOfLE (X.basicOpen_le s)).op r) = g.appLE U _ h r
        rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE] }
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers s) e

end Langlands.AlgebraicGeometry.DvrSmoothening
