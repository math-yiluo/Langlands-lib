import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreGenericLiftMaps
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsLocalization

/-! # Descending `NoLargerLift` from basic opens to localizations

If `ξ ∈ F(Spec (A/I))` lifts to no larger closed subscheme of `Spec A[1/g]` for every
multiple `g` of `g₀`, then by condition (F2) it lifts to no larger closed subscheme of
`Spec M⁻¹A` for every localization with `g₀ ∈ M` (`noLargerLift_of_isLocalization`). -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace GenericLift

open Charts

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}

lemma spec_comp₂₂ {T₁ T₂ T₃ T₄ T₅ : Type u} [CommRing T₁] [CommRing T₂] [CommRing T₃]
    [CommRing T₄] [CommRing T₅] {g : Spec (CommRingCat.of T₄) ⟶ S}
    {ψ : T₂ →+* T₁} {α : T₃ →+* T₂} {β : T₄ →+* T₃} {γ : T₅ →+* T₁} {δ : T₄ →+* T₅}
    (e : ψ.comp (α.comp β) = γ.comp δ) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom α) ≫
      Spec.map (CommRingCat.ofHom β) ≫ g =
        Spec.map (CommRingCat.ofHom γ) ≫ Spec.map (CommRingCat.ofHom δ) ≫ g := by
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, RingHom.comp_assoc, e]

section F2

variable {A : Type u} [CommRing A] (f : Spec (CommRingCat.of A) ⟶ S) (M : Submonoid A)
variable (B : Type u) [CommRing B] [Algebra A B] [IsLocalization M B]

lemma toLoc_comp_algebraMap (a : DivIndex M) :
    (toLoc M B a).comp (algebraMap A (Localization.Away a.val)) = algebraMap A B :=
  RingHom.ext (toLoc_algebraMap M B a)

/-- (F2), surjectivity, with maps written as `rhom`. -/
lemma exists_away (hZ : ZariskiSheaf F) (h2 : FilteredColimits F)
    (ζ : F.obj (op (algebraOver f B))) :
    ∃ (a : DivIndex M) (ζ' : F.obj (op (algebraOver f (Localization.Away a.val)))),
      F.map (rhom (toLoc M B a) (spec_comp₁₁ (toLoc_comp_algebraMap M B a))).op ζ' = ζ :=
  exists_eq_of_isLocalization M B hZ h2 f ζ

/-- (F2), injectivity, with maps written as `rhom`. -/
lemma exists_away_eq (hZ : ZariskiSheaf F) (h2 : FilteredColimits F) (a : DivIndex M)
    (ζ₁ ζ₂ : F.obj (op (algebraOver f (Localization.Away a.val))))
    (heq : F.map (rhom (toLoc M B a) (spec_comp₁₁ (toLoc_comp_algebraMap M B a))).op ζ₁ =
      F.map (rhom (toLoc M B a) (spec_comp₁₁ (toLoc_comp_algebraMap M B a))).op ζ₂) :
    ∃ (b : DivIndex M) (hab : a.val ∣ b.val),
      F.map (rhom (awayMap hab) (spec_comp₁₁ (awayMap_comp_algebraMap hab))).op ζ₁ =
        F.map (rhom (awayMap hab) (spec_comp₁₁ (awayMap_comp_algebraMap hab))).op ζ₂ := by
  obtain ⟨b, hab, h⟩ := exists_eq_of_isLocalization_of_eq M B hZ h2 f a ζ₁ ζ₂ heq
  exact ⟨b, leOfHom hab, h⟩

end F2

section Descent

variable {A : Type u} [CommRing A] (f : Spec (CommRingCat.of A) ⟶ S) {I : Ideal A}
variable (M : Submonoid A) (B : Type u) [CommRing B] [Algebra A B] [IsLocalization M B]

/-- A map out of `(A/K)[1/a]` that sends the image of `x ∈ A` to `ρ x`, for `a` the image of an
element `m` of `A` with `ρ m` a unit. -/
lemma exists_away_lift {K : Ideal A} (a : A ⧸ K) {m : A} (hma : Ideal.Quotient.mk K m = a)
    {T : Type u} [CommRing T] (ρ : A ⧸ K →+* T) (hu : IsUnit (ρ (Ideal.Quotient.mk K m))) :
    ∃ ℓ : Localization.Away a →+* T,
      ∀ y, ℓ (algebraMap (A ⧸ K) (Localization.Away a) y) = ρ y := by
  subst hma
  exact ⟨IsLocalization.Away.lift _ hu, fun y ↦ IsLocalization.Away.lift_eq _ hu y⟩

/-- (F2) descends "no larger lift" from the `A[1/g]`, `g₀ ∣ g`, to a localization `M⁻¹A` with
`g₀ ∈ M`. -/
theorem noLargerLift_of_isLocalization (hZ : ZariskiSheaf F) (h2 : FilteredColimits F)
    (ξ : F.obj (op (algebraOver f (A ⧸ I)))) (g₀ : A) (hg₀ : g₀ ∈ M)
    (H : ∀ g : A, g₀ ∣ g → NoLargerLift (Localization.Away g) ξ) : NoLargerLift B ξ := by
  rw [noLargerLift_iff]
  intro J hJ η heq
  obtain ⟨K, hKI, rfl⟩ : ∃ K : Ideal A, K ≤ I ∧ K.map (algebraMap A B) = J :=
    ⟨J.under A ⊓ I, inf_le_right, by
      rw [IsLocalization.map_inf M B, IsLocalization.map_under M B, inf_eq_left.2 hJ.le]⟩
  -- Step 1: (F2) over `A ⧸ K` gives `ζ` over `(A/K)[1/a]` with image `η`.
  have hcK : (RingHom.id (B ⧸ K.map (algebraMap A B))).comp
      (algebraMap A (B ⧸ K.map (algebraMap A B))) =
        (algebraMap (A ⧸ K) (B ⧸ K.map (algebraMap A B))).comp (algebraMap A (A ⧸ K)) :=
    RingHom.ext fun _ ↦ rfl
  obtain ⟨a, ζ, hζ⟩ := exists_away (baseOver f (A ⧸ K))
    (Algebra.algebraMapSubmonoid (A ⧸ K) M) (B ⧸ K.map (algebraMap A B)) hZ h2
    (F.map (rhom (g₁ := Spec.map (CommRingCat.ofHom
      (algebraMap (A ⧸ K) (B ⧸ K.map (algebraMap A B)))) ≫ baseOver f (A ⧸ K))
      (RingHom.id _) (spec_comp₁₂ hcK)).op η)
  obtain ⟨m, hm, hma⟩ := Submonoid.mem_map.1 a.val_mem
  -- Step 2: (F2) over `A ⧸ I` compares the image of `ζ` with the restriction of `ξ`.
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : DivIndex (Algebra.algebraMapSubmonoid (A ⧸ I) M),
      a₁.val = Ideal.Quotient.factor hKI a.val :=
    ⟨DivIndex.mk _ (Submonoid.mem_map.2 ⟨m, hm, by rw [← hma]; rfl⟩), rfl⟩
  obtain ⟨ψ₁, hψ₁⟩ := exists_away_lift a.val hma
    ((algebraMap (A ⧸ I) (Localization.Away a₁.val)).comp (Ideal.Quotient.factor hKI)) (by
      change IsUnit (algebraMap (A ⧸ I) (Localization.Away a₁.val)
        (Ideal.Quotient.factor hKI (algebraMap A (A ⧸ K) m)))
      rw [hma, ← ha₁]
      exact IsLocalization.Away.algebraMap_isUnit _)
  have eψ : ψ₁.comp ((algebraMap (A ⧸ K) (Localization.Away a.val)).comp (algebraMap A (A ⧸ K))) =
      (algebraMap (A ⧸ I) (Localization.Away a₁.val)).comp (algebraMap A (A ⧸ I)) :=
    RingHom.ext fun x ↦ by simp only [RingHom.comp_apply, hψ₁]; rfl
  set φ := Ideal.Quotient.factor hJ.le
  have eφ : φ.comp ((algebraMap (A ⧸ K) (B ⧸ K.map (algebraMap A B))).comp
      (algebraMap A (A ⧸ K))) =
        (algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B))).comp (algebraMap A (A ⧸ I)) :=
    RingHom.ext fun _ ↦ rfl
  have hφ := spec_comp₂₂ (g := f) eφ
  have hid : (RingHom.id (B ⧸ I.map (algebraMap A B))).comp
      (algebraMap A (B ⧸ I.map (algebraMap A B))) =
        (algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B))).comp (algebraMap A (A ⧸ I)) :=
    RingHom.ext fun _ ↦ rfl
  refine (exists_away_eq (baseOver f (A ⧸ I)) (Algebra.algebraMapSubmonoid (A ⧸ I) M)
    (B ⧸ I.map (algebraMap A B)) hZ h2 a₁ (F.map (rhom ψ₁ (spec_comp₂₂ eψ)).op ζ)
    (F.map (rhom (g₁ := Spec.map (CommRingCat.ofHom
      (algebraMap (A ⧸ I) (Localization.Away a₁.val))) ≫ baseOver f (A ⧸ I))
      (g₂ := baseOver f (A ⧸ I)) (algebraMap (A ⧸ I) (Localization.Away a₁.val)) rfl).op ξ)
    ?_).elim fun b ⟨hab, hb⟩ ↦ ?_
  · have h3 := congrArg (F.map (rhom φ hφ).op) hζ
    rw [map_rhom_map_rhom, map_rhom_map_rhom] at h3
    have h4 := congrArg (F.map (rhom (g₁ := Spec.map (CommRingCat.ofHom
      (algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B)))) ≫ baseOver f (A ⧸ I))
      (RingHom.id _) (spec_comp₁₂ hid)).op) heq
    rw [map_rhom_map_rhom, map_rhom_map_rhom] at h4
    rw [map_rhom_map_rhom, map_rhom_map_rhom]
    have e2 : (toLoc (Algebra.algebraMapSubmonoid (A ⧸ I) M) (B ⧸ I.map (algebraMap A B)) a₁).comp
        ψ₁ = φ.comp (toLoc (Algebra.algebraMapSubmonoid (A ⧸ K) M)
          (B ⧸ K.map (algebraMap A B)) a) :=
      IsLocalization.ringHom_ext (Submonoid.powers a.val) (Ideal.Quotient.ringHom_ext
        (RingHom.ext fun x ↦ by
          simp only [RingHom.comp_apply, hψ₁, toLoc_algebraMap, Ideal.Quotient.factor_mk]
          rfl))
    have e3 : φ.comp (RingHom.id _) = (RingHom.id _).comp φ := by
      rw [RingHom.comp_id, RingHom.id_comp]
    rw [map_rhom_eq' e2, h3, map_rhom_eq' e3, h4]
    refine map_rhom_eq _ _ ?_ ξ
    rw [RingHom.id_comp, toLoc_comp_algebraMap]
    rfl
  -- Step 3: restrict to `A[1/g]` for `g = g₀ m m'`.
  obtain ⟨m', hm', hmb⟩ := Submonoid.mem_map.1 b.val_mem
  rw [map_rhom_map_rhom, map_rhom_map_rhom] at hb
  set g := g₀ * m * m' with hg
  have hgM : g ∈ M := M.mul_mem (M.mul_mem hg₀ hm) hm'
  have Hg := H g ⟨m * m', by rw [hg, mul_assoc]⟩
  rw [noLargerLift_iff] at Hg
  have hJ' : K.map (algebraMap A (Localization.Away g)) <
      I.map (algebraMap A (Localization.Away g)) := by
    refine lt_of_le_of_ne (Ideal.map_mono hKI) fun hEq ↦ hJ.ne ?_
    have := congrArg (Ideal.map (IsLocalization.Away.lift (S := Localization.Away g) g
      (IsLocalization.map_units B ⟨g, hgM⟩))) hEq
    simpa only [Ideal.map_map, IsLocalization.Away.lift_comp] using this
  have hmu : ∀ n : A, n ∣ g → ∀ L : Ideal (Localization.Away g),
      IsUnit (Ideal.Quotient.mk L (algebraMap A (Localization.Away g) n)) := fun n hn L ↦
    (isUnit_of_dvd_unit (map_dvd _ hn) (IsLocalization.Away.algebraMap_isUnit g)).map _
  obtain ⟨lam, hlam⟩ := exists_away_lift a.val hma
    (Ideal.quotientMap (K.map (algebraMap A (Localization.Away g)))
      (algebraMap A (Localization.Away g)) Ideal.le_comap_map)
    (hmu m ⟨g₀ * m', by rw [hg]; ring⟩ _)
  obtain ⟨μ, hμ⟩ := exists_away_lift b.val hmb
    (Ideal.quotientMap (I.map (algebraMap A (Localization.Away g)))
      (algebraMap A (Localization.Away g)) Ideal.le_comap_map)
    (hmu m' ⟨g₀ * m, by rw [hg]; ring⟩ _)
  have elam : lam.comp ((algebraMap (A ⧸ K) (Localization.Away a.val)).comp
      (algebraMap A (A ⧸ K))) =
        algebraMap A (Localization.Away g ⧸ K.map (algebraMap A (Localization.Away g))) :=
    RingHom.ext fun x ↦ by simp only [RingHom.comp_apply, hlam]; rfl
  have eμ : μ.comp ((algebraMap (A ⧸ I) (Localization.Away b.val)).comp
      (algebraMap A (A ⧸ I))) =
        algebraMap A (Localization.Away g ⧸ I.map (algebraMap A (Localization.Away g))) :=
    RingHom.ext fun x ↦ by simp only [RingHom.comp_apply, hμ]; rfl
  apply Hg _ hJ' (F.map (rhom (g₁ := Spec.map (CommRingCat.ofHom (algebraMap A
    (Localization.Away g ⧸ K.map (algebraMap A (Localization.Away g))))) ≫ f)
    lam (spec_comp₂₁ elam)).op ζ)
  have key := congrArg (F.map (rhom (g₁ := Spec.map (CommRingCat.ofHom (algebraMap A
    (Localization.Away g ⧸ I.map (algebraMap A (Localization.Away g))))) ≫ f)
    μ (spec_comp₂₁ eμ)).op) hb
  rw [map_rhom_map_rhom, map_rhom_map_rhom] at key
  have e5 : (Ideal.Quotient.factor hJ'.le).comp lam = μ.comp ((awayMap hab).comp ψ₁) :=
    IsLocalization.ringHom_ext (Submonoid.powers a.val) (Ideal.Quotient.ringHom_ext
      (RingHom.ext fun x ↦ by
        simp only [RingHom.comp_apply, hlam, hψ₁, awayMap_algebraMap, hμ, Ideal.quotientMap_mk,
          Ideal.Quotient.factor_mk]))
  rw [map_rhom_map_rhom, map_rhom_eq' e5, key]
  refine map_rhom_eq _ _ ?_ ξ
  exact Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ by
    simp only [RingHom.comp_apply, awayMap_algebraMap, hμ, Ideal.quotientMap_mk])

/-- The case of a localization at a prime `q` not containing `g₀`. -/
theorem noLargerLift_atPrime (hZ : ZariskiSheaf F) (h2 : FilteredColimits F)
    (ξ : F.obj (op (algebraOver f (A ⧸ I)))) (g₀ : A)
    (H : ∀ g : A, g₀ ∣ g → NoLargerLift (Localization.Away g) ξ) (q : Ideal A) [q.IsPrime]
    (hq : g₀ ∉ q) : NoLargerLift (Localization.AtPrime q) ξ :=
  noLargerLift_of_isLocalization f q.primeCompl _ hZ h2 ξ g₀ hq H

end Descent

end GenericLift

end Langlands.AlgebraicGeometry.UnramifiedFunctor
