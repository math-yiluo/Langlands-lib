import Langlands.AlgebraicGeometry.DvrSmoothening.Charts
import Langlands.AlgebraicGeometry.DvrSmootheningStatement
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Points with values in discrete valuation rings of ramification index one -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- For a local homomorphism of discrete valuation rings of ramification index one the structure
map is injective. -/
theorem algebraMap_injective_of_ram {R' : Type u} [CommRing R'] [IsDomain R']
    [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
    (h : IsRamificationIndexOne R R') : Function.Injective (algebraMap R R') := by
  have hp : (RingHom.ker (algebraMap R R')).IsPrime := RingHom.ker_isPrime _
  by_contra hinj
  have hne : RingHom.ker (algebraMap R R') ≠ ⊥ := fun h0 =>
    hinj ((RingHom.injective_iff_ker_eq_bot _).mpr h0)
  have hmax := Ring.DimensionLEOne.maximalOfPrime hne hp
  have hm : RingHom.ker (algebraMap R R') = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal hmax
  apply IsDiscreteValuationRing.not_a_field R'
  rw [← h.1, eq_bot_iff, Ideal.map_le_iff_le_comap, ← hm]
  intro y hy
  simpa [Ideal.mem_comap] using hy

/-- A point of `X` with values in a discrete valuation ring of ramification index one over `R`. -/
structure TestPoint (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) where
  /-- The discrete valuation ring. -/
  ring : Type u
  [commRing : CommRing ring]
  [isDomain : IsDomain ring]
  [dvr : IsDiscreteValuationRing ring]
  [algebra : Algebra R ring]
  [localHom : IsLocalHom (algebraMap R ring)]
  ram : IsRamificationIndexOne R ring
  /-- The point. -/
  a : Spec (CommRingCat.of ring) ⟶ X
  ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R ring))

attribute [instance] TestPoint.commRing TestPoint.isDomain TestPoint.dvr TestPoint.algebra
  TestPoint.localHom

namespace TestPoint

variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- The image of the closed point. -/
noncomputable abbrev special (P : TestPoint X f) : X := P.a (IsLocalRing.closedPoint P.ring)

/-- The point composed with a morphism `g : X₁ ⟶ X`. -/
@[simps]
noncomputable def map {X₁ : Scheme.{u}} (g : X₁ ⟶ X) (P : TestPoint X₁ (g ≫ f)) : TestPoint X f where
  ring := P.ring
  ram := P.ram
  a := P.a ≫ g
  ha := by rw [Category.assoc, P.ha]

@[simp] theorem special_map {X₁ : Scheme.{u}} (g : X₁ ⟶ X) (P : TestPoint X₁ (g ≫ f)) :
    (P.map g).special = g P.special := rfl

/-- A point lifted along `g`. -/
@[simps]
noncomputable def lift {X₁ : Scheme.{u}} (g : X₁ ⟶ X) (P : TestPoint X f)
    (a₁ : Spec (CommRingCat.of P.ring) ⟶ X₁) (h : a₁ ≫ g = P.a) : TestPoint X₁ (g ≫ f) where
  ring := P.ring
  ram := P.ram
  a := a₁
  ha := by rw [← Category.assoc, h, P.ha]

theorem eq_of_a_eq (P : TestPoint X f) {a : Spec (CommRingCat.of P.ring) ⟶ X} (h : a = P.a)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R P.ring))) :
    (⟨P.ring, P.ram, a, ha⟩ : TestPoint X f) = P := by
  subst h
  rfl

@[simp] theorem map_lift {X₁ : Scheme.{u}} (g : X₁ ⟶ X) (P : TestPoint X f)
    (a₁ : Spec (CommRingCat.of P.ring) ⟶ X₁) (h : a₁ ≫ g = P.a) : (P.lift g a₁ h).map g = P :=
  P.eq_of_a_eq h _

theorem mem_chart (P : TestPoint X f) : ∃ C : AffineChart X, P.special ∈ C.ι.opensRange :=
  AffineChart.exists_mem _

/-- The defect of a point, read in any chart. -/
noncomputable def defect (P : TestPoint X f) : ℕ∞ :=
  (Classical.choose P.mem_chart).defectAt f P.a (Classical.choose_spec P.mem_chart)

theorem defect_eq (P : TestPoint X f) (C : AffineChart X) (h : P.special ∈ C.ι.opensRange) :
    P.defect = C.defectAt f P.a h :=
  AffineChart.defectAt_eq f _ _ _ _ _

/-- The defect is unchanged by a morphism which is an isomorphism over an open containing the
closed point. -/
theorem defect_map {X₁ : Scheme.{u}} (g : X₁ ⟶ X) (W : X.Opens) [IsIso (g ∣_ W)]
    (P : TestPoint X₁ (g ≫ f)) (hP : P.special ∈ g ⁻¹ᵁ W) : (P.map g).defect = P.defect := by
  obtain ⟨C, hC, hCW⟩ := AffineChart.exists_le P.special (g ⁻¹ᵁ W) hP
  rw [P.defect_eq C hC, (P.map g).defect_eq (C.push g W hCW) (C.push_mem g W hCW P.a hC)]
  exact C.push_defectAt f g W hCW P.a hC

end TestPoint

/-- A prime ideal of a discrete valuation ring not containing a uniformizer is zero. -/
theorem prime_eq_bot_of_not_mem {ϖ : R} (hϖ : Irreducible ϖ) (p : Ideal R) [p.IsPrime]
    (h : ϖ ∉ p) : p = ⊥ := by
  by_contra hne
  have hmax := Ring.DimensionLEOne.maximalOfPrime hne ‹_›
  rw [IsLocalRing.eq_maximalIdeal hmax, hϖ.maximalIdeal_eq] at h
  exact h (Ideal.mem_span_singleton_self ϖ)

namespace TestPoint

variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- The closed point of a test point lies over the closed point of `Spec R`. -/
theorem f_special (P : TestPoint X f) :
    f P.special = IsLocalRing.closedPoint R := by
  change (P.a ≫ f) (IsLocalRing.closedPoint P.ring) = _
  rw [P.ha]
  exact IsLocalRing.comap_closedPoint (algebraMap R P.ring)

end TestPoint

/-- Smoothness at a point over an open `W` is unchanged by a morphism which is an isomorphism over
`W`. -/
theorem mem_smoothLocus_comp_iff {X X₁ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation f] (g : X₁ ⟶ X) [LocallyOfFinitePresentation (g ≫ f)]
    (W : X.Opens) [IsIso (g ∣_ W)] (x : X₁) (hx : x ∈ g ⁻¹ᵁ W) :
    x ∈ (g ≫ f).smoothLocus ↔ g x ∈ f.smoothLocus := by
  obtain ⟨C, ⟨y, rfl⟩, hCW⟩ := AffineChart.exists_le x (g ⁻¹ᵁ W) hx
  have := isOpenImmersion_comp_of_isIso_restrict C.ι g W hCW
  have h1 : C.ι ⁻¹ᵁ (g ≫ f).smoothLocus = (C.ι ≫ g ≫ f).smoothLocus :=
    Scheme.Hom.preimage_smoothLocus_eq C.ι (g ≫ f)
  have h2 : (C.ι ≫ g) ⁻¹ᵁ f.smoothLocus = ((C.ι ≫ g) ≫ f).smoothLocus :=
    Scheme.Hom.preimage_smoothLocus_eq (C.ι ≫ g) f
  have e1 : C.ι y ∈ (g ≫ f).smoothLocus ↔ y ∈ (C.ι ≫ g ≫ f).smoothLocus := by
    rw [← h1]; rfl
  have e2 : g (C.ι y) ∈ f.smoothLocus ↔ y ∈ ((C.ι ≫ g) ≫ f).smoothLocus := by
    rw [← h2]; rfl
  rw [e1, e2]
  simp only [Category.assoc]

namespace AffineChart

variable {X : Scheme.{u}} (C : AffineChart X) (f : X ⟶ Spec (CommRingCat.of R))

theorem finitePresentation_base [LocallyOfFinitePresentation f] :
    letI := (C.base f).toAlgebra; Algebra.FinitePresentation R C.ring := by
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (C.base f))) := by
    rw [Spec_base]; infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp this

theorem finiteType_base [LocallyOfFiniteType f] :
    letI := (C.base f).toAlgebra; Algebra.FiniteType R C.ring := by
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (C.base f))) := by
    rw [Spec_base]; infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this

/-- A point of a chart is smooth over `R` exactly when its prime is in the algebraic smooth
locus of the coordinate ring. -/
theorem ι_mem_smoothLocus_iff [LocallyOfFinitePresentation f] (y : Spec C.ring) :
    C.ι y ∈ f.smoothLocus ↔
      (letI := (C.base f).toAlgebra; (show PrimeSpectrum C.ring from y) ∈
        Algebra.smoothLocus R C.ring) := by
  have h : C.ι ⁻¹ᵁ f.smoothLocus = (C.ι ≫ f).smoothLocus :=
    Scheme.Hom.preimage_smoothLocus_eq C.ι f
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (C.base f))) := by
    rw [Spec_base]; infer_instance
  have h' : (C.ι ≫ f).smoothLocus = (Spec.map (CommRingCat.ofHom (C.base f))).smoothLocus := by
    congr 1
    exact (Spec_base C f).symm
  change y ∈ C.ι ⁻¹ᵁ f.smoothLocus ↔ _
  rw [h, h']
  exact mem_smoothLocus_SpecMap_iff (CommRingCat.ofHom (C.base f)) y

/-- If all points over the generic point of `Spec R` are smooth, the generic fibre of every
chart is smooth. -/
theorem smooth_away [LocallyOfFinitePresentation f] {ϖ : R} (hϖ : Irreducible ϖ)
    (hgen : ∀ x : X, (f x).asIdeal = ⊥ → x ∈ f.smoothLocus) :
    letI := (C.base f).toAlgebra
    Algebra.Smooth R (Localization.Away (algebraMap R C.ring ϖ)) := by
  let := (C.base f).toAlgebra
  have := C.finitePresentation_base f
  rw [← Algebra.basicOpen_subset_smoothLocus_iff_smooth]
  intro y hy
  have hy' : C.ι y ∈ f.smoothLocus := by
    apply hgen
    have hfy : f (C.ι y) = PrimeSpectrum.comap (C.base f) y := by
      change (C.ι ≫ f) y = _
      rw [← Spec_base]
      rfl
    rw [hfy]
    apply prime_eq_bot_of_not_mem hϖ
    exact hy
  exact (C.ι_mem_smoothLocus_iff f y).mp hy'

end AffineChart

namespace TestPoint

variable {X X₁ : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- The map from the spectrum of the fraction field. -/
noncomputable abbrev genericMap (P : TestPoint X f) :
    Spec (CommRingCat.of (FractionRing P.ring)) ⟶ Spec (CommRingCat.of P.ring) :=
  Spec.map (CommRingCat.ofHom (algebraMap P.ring (FractionRing P.ring)))

/-- The generic point of a test point lies over the generic point of `Spec R`. -/
theorem f_generic (P : TestPoint X f) (z : Spec (CommRingCat.of (FractionRing P.ring))) :
    (f (P.a (P.genericMap z))).asIdeal = ⊥ := by
  have hz : (show PrimeSpectrum (FractionRing P.ring) from z).asIdeal = ⊥ :=
    (Ideal.eq_bot_or_top _).resolve_right z.2.ne_top
  change ((P.genericMap ≫ P.a ≫ f) z).asIdeal = ⊥
  rw [P.ha, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  change Ideal.comap _ (show PrimeSpectrum (FractionRing P.ring) from z).asIdeal = ⊥
  rw [hz]
  apply Ideal.comap_bot_of_injective
  exact (IsFractionRing.injective P.ring (FractionRing P.ring)).comp
    (algebraMap_injective_of_ram P.ram)

theorem generic_range_subset (P : TestPoint X f) (W : X.Opens)
    (hW : ∀ x : X, (f x).asIdeal = ⊥ → x ∈ W) : Set.range (P.genericMap ≫ P.a) ⊆ W := by
  rintro _ ⟨z, rfl⟩
  exact hW _ (P.f_generic z)

/-- Points lift along a proper morphism which is an isomorphism over an open containing the
generic fibre. -/
theorem exists_lift (g : X₁ ⟶ X) [IsProper g] (W : X.Opens) [IsIso (g ∣_ W)]
    (hW : ∀ x : X, (f x).asIdeal = ⊥ → x ∈ W) (P : TestPoint X f) :
    ∃ a₁ : Spec (CommRingCat.of P.ring) ⟶ X₁, a₁ ≫ g = P.a := by
  have hsub : Set.range (P.genericMap ≫ P.a) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]; exact P.generic_range_subset W hW
  let b := IsOpenImmersion.lift W.ι (P.genericMap ≫ P.a) hsub
  let i₁ : Spec (CommRingCat.of (FractionRing P.ring)) ⟶ X₁ :=
    b ≫ inv (g ∣_ W) ≫ (g ⁻¹ᵁ W).ι
  have hi₁ : i₁ ≫ g = P.genericMap ≫ P.a := by
    simp only [i₁, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, b,
      IsOpenImmersion.lift_fac]
  have hval : ValuativeCriterion.Existence g := by
    have h := ‹IsProper g›
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq g :=
    { R := P.ring, K := FractionRing P.ring, i₁ := i₁, i₂ := P.a, commSq := ⟨hi₁⟩ }
  obtain ⟨⟨l⟩⟩ := hval S
  exact ⟨l.l, l.fac_right⟩

/-- Lifts along a proper morphism which is an isomorphism over an open containing the generic
fibre are unique. -/
theorem lift_unique (g : X₁ ⟶ X) [IsProper g] (W : X.Opens) [IsIso (g ∣_ W)]
    (hW : ∀ x : X, (f x).asIdeal = ⊥ → x ∈ W) (P : TestPoint X f)
    (a₁ a₂ : Spec (CommRingCat.of P.ring) ⟶ X₁) (h₁ : a₁ ≫ g = P.a) (h₂ : a₂ ≫ g = P.a) :
    a₁ = a₂ := by
  have hsub : ∀ a : Spec (CommRingCat.of P.ring) ⟶ X₁, a ≫ g = P.a →
      Set.range (P.genericMap ≫ a) ⊆ Set.range (g ⁻¹ᵁ W).ι := by
    intro a ha
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change g ((P.genericMap ≫ a) z) ∈ W
    rw [← Scheme.Hom.comp_apply, Category.assoc, ha]
    exact P.generic_range_subset W hW ⟨z, rfl⟩
  have hgen : P.genericMap ≫ a₁ = P.genericMap ≫ a₂ := by
    rw [← IsOpenImmersion.lift_fac (g ⁻¹ᵁ W).ι _ (hsub a₁ h₁),
      ← IsOpenImmersion.lift_fac (g ⁻¹ᵁ W).ι _ (hsub a₂ h₂)]
    congr 1
    rw [← cancel_mono (g ∣_ W), ← cancel_mono W.ι, Category.assoc, Category.assoc,
      morphismRestrict_ι, ← Category.assoc, ← Category.assoc, IsOpenImmersion.lift_fac,
      IsOpenImmersion.lift_fac, Category.assoc, Category.assoc, h₁, h₂]
  have huniq : ValuativeCriterion.Uniqueness g := IsSeparated.valuativeCriterion g
  let S : ValuativeCommSq g :=
    { R := P.ring, K := FractionRing P.ring, i₁ := P.genericMap ≫ a₁, i₂ := P.a,
      commSq := ⟨by rw [Category.assoc, h₁]⟩ }
  have := huniq S
  have e := Subsingleton.elim (α := S.commSq.LiftStruct) ⟨a₁, rfl, h₁⟩ ⟨a₂, hgen.symm, h₂⟩
  exact congrArg CommSq.LiftStruct.l e

end TestPoint

end Langlands.AlgebraicGeometry.DvrSmoothening
