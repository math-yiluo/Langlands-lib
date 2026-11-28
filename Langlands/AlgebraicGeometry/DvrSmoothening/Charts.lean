import Langlands.AlgebraicGeometry.DvrSmoothening.DefectTransport
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RingTheory.TotallySplit

/-! # Affine charts, points with values in local rings, and the defect of a point -/

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

/-- The defect of the point `φ : A → R'` for a given `R`-algebra structure on `A`. -/
noncomputable def defectWith {R A R' : Type*} [CommRing R] [CommRing A] [CommRing R']
    (I : Algebra R A) (φ : A →+* R') : ℕ∞ :=
  letI := I
  letI := φ.toAlgebra
  torsionLength R' (R' ⊗[A] Ω[A⁄R])

/-- The defect of the point `φ : A → R'`, where `A` is an `R`-algebra through `ψ`. -/
noncomputable def chartDefect {R A R' : Type*} [CommRing R] [CommRing A] [CommRing R']
    (ψ : R →+* A) (φ : A →+* R') : ℕ∞ :=
  defectWith ψ.toAlgebra φ

theorem pointDefect_eq_defectWith {R A R' : Type*} [CommRing R] [CommRing A] [CommRing R']
    [I : Algebra R A] [Algebra R R'] (φ : A →ₐ[R] R') :
    pointDefect φ = defectWith I φ.toRingHom := rfl

theorem chartDefect_algebraMap {R A R' : Type*} [CommRing R] [CommRing A] [CommRing R']
    [I : Algebra R A] [Algebra R R'] (φ : A →ₐ[R] R') :
    chartDefect (algebraMap R A) φ.toRingHom = pointDefect φ := by
  rw [pointDefect_eq_defectWith, chartDefect]
  exact congrArg (defectWith · φ.toRingHom) (Algebra.algebra_ext _ _ fun _ => rfl)

/-- The defect is unchanged by a formally étale change of chart. -/
theorem chartDefect_comp_of_formallyEtale {R A B R' : Type*} [CommRing R] [CommRing A]
    [CommRing B] [CommRing R'] (ψ : R →+* A) (χ : A →+* B) (φ : B →+* R')
    (hχ : letI := χ.toAlgebra; Algebra.FormallyEtale A B) :
    chartDefect (χ.comp ψ) φ = chartDefect ψ (φ.comp χ) := by
  let : Algebra R A := ψ.toAlgebra
  let : Algebra A B := χ.toAlgebra
  let : Algebra R B := (χ.comp ψ).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra R R' := (φ.comp (χ.comp ψ)).toAlgebra
  let φ' : B →ₐ[R] R' := { φ with commutes' := fun _ => rfl }
  have := pointDefect_comp_formallyEtale (R := R) (A := A) (B := B) φ'
  rw [← chartDefect_algebraMap, ← chartDefect_algebraMap] at this
  exact this.symm

/-- An affine chart of a scheme: an open immersion from an affine scheme. -/
structure AffineChart (X : Scheme.{u}) where
  /-- The coordinate ring. -/
  ring : CommRingCat.{u}
  /-- The open immersion. -/
  ι : Spec ring ⟶ X
  [isOpenImmersion : IsOpenImmersion ι]

attribute [instance] AffineChart.isOpenImmersion

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- Every point of the spectrum of a local ring specializes to the closed point, so a morphism
whose closed point lands in an open lands entirely in it. -/
theorem range_subset_of_closedPoint_mem {R' : Type u} [CommRing R'] [IsLocalRing R']
    (a : Spec (CommRingCat.of R') ⟶ X) (U : X.Opens)
    (h : a (IsLocalRing.closedPoint R') ∈ U) : Set.range a ⊆ U := by
  rintro _ ⟨y, rfl⟩
  have hy : y ⤳ IsLocalRing.closedPoint R' :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal y.2.ne_top)
  exact (hy.map a.continuous).mem_open U.2 h

namespace AffineChart

variable (C : AffineChart X)

/-- The structure map of the coordinate ring of a chart, given `f : X ⟶ Spec R`. -/
noncomputable def base (f : X ⟶ Spec (CommRingCat.of R)) : R →+* C.ring :=
  (Spec.preimage (C.ι ≫ f)).hom

theorem Spec_base (f : X ⟶ Spec (CommRingCat.of R)) :
    Spec.map (CommRingCat.ofHom (C.base f)) = C.ι ≫ f := by
  simp [base]

variable {R' : Type u} [CommRing R'] [IsLocalRing R']

/-- The lift of a point through the chart. -/
noncomputable def liftPoint (a : Spec (CommRingCat.of R') ⟶ X)
    (h : a (IsLocalRing.closedPoint R') ∈ C.ι.opensRange) :
    Spec (CommRingCat.of R') ⟶ Spec C.ring :=
  IsOpenImmersion.lift C.ι a (by
    rw [← Scheme.Hom.coe_opensRange C.ι]
    exact range_subset_of_closedPoint_mem a _ h)

@[reassoc (attr := simp)]
theorem liftPoint_ι (a : Spec (CommRingCat.of R') ⟶ X)
    (h : a (IsLocalRing.closedPoint R') ∈ C.ι.opensRange) : C.liftPoint a h ≫ C.ι = a :=
  IsOpenImmersion.lift_fac C.ι a _

/-- The ring map from the coordinate ring of the chart given by a point. -/
noncomputable def pointHom (a : Spec (CommRingCat.of R') ⟶ X)
    (h : a (IsLocalRing.closedPoint R') ∈ C.ι.opensRange) : C.ring →+* R' :=
  (Spec.preimage (C.liftPoint a h)).hom

theorem Spec_pointHom (a : Spec (CommRingCat.of R') ⟶ X)
    (h : a (IsLocalRing.closedPoint R') ∈ C.ι.opensRange) :
    Spec.map (CommRingCat.ofHom (C.pointHom a h)) = C.liftPoint a h := by
  simp [pointHom]

theorem pointHom_eq_of_Spec {a : Spec (CommRingCat.of R') ⟶ X}
    (h : a (IsLocalRing.closedPoint R') ∈ C.ι.opensRange) (φ : C.ring →+* R')
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ C.ι = a) : C.pointHom a h = φ := by
  have : C.liftPoint a h = Spec.map (CommRingCat.ofHom φ) := by
    rw [← cancel_mono C.ι, liftPoint_ι, hφ]
  rw [pointHom, this, Spec.preimage_map]
  rfl

theorem pointHom_comp_base (f : X ⟶ Spec (CommRingCat.of R)) [Algebra R R']
    (a : Spec (CommRingCat.of R') ⟶ X) (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (h : a (IsLocalRing.closedPoint R') ∈ C.ι.opensRange) :
    (C.pointHom a h).comp (C.base f) = algebraMap R R' := by
  have : Spec.map (CommRingCat.ofHom ((C.pointHom a h).comp (C.base f))) =
      Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Spec_pointHom, Spec_base, liftPoint_ι_assoc, ha]
  have := congrArg (fun g => (Spec.preimage g).hom) this
  simpa using this

/-- The defect of a point read in a chart through which it factors. -/
noncomputable def defectAt (f : X ⟶ Spec (CommRingCat.of R)) (a : Spec (CommRingCat.of R') ⟶ X)
    (h : a (IsLocalRing.closedPoint R') ∈ C.ι.opensRange) : ℕ∞ :=
  chartDefect (C.base f) (C.pointHom a h)

theorem formallyEtale_of_isOpenImmersion {A B : CommRingCat.{u}} (ψ : A ⟶ B)
    [IsOpenImmersion (Spec.map ψ)] : letI := ψ.hom.toAlgebra; Algebra.FormallyEtale A B := by
  have h : RingHom.Etale ψ.hom := (HasRingHomProperty.Spec_iff (P := @Etale)).mp inferInstance
  let := ψ.hom.toAlgebra
  have := h.toAlgebra
  infer_instance

theorem Spec_map_injective {A B : CommRingCat.{u}} {φ₁ φ₂ : A ⟶ B}
    (h : Spec.map φ₁ = Spec.map φ₂) : φ₁ = φ₂ := by
  rw [← Spec.preimage_map φ₁, h, Spec.preimage_map]

/-- If a chart factors through another one, the two charts compute the same defect. -/
theorem defectAt_eq_of_factor (f : X ⟶ Spec (CommRingCat.of R)) (C₂ C₃ : AffineChart X)
    (ψ : C₂.ring ⟶ C₃.ring) (hψ : C₃.ι = Spec.map ψ ≫ C₂.ι)
    (a : Spec (CommRingCat.of R') ⟶ X)
    (h₂ : a (IsLocalRing.closedPoint R') ∈ C₂.ι.opensRange)
    (h₃ : a (IsLocalRing.closedPoint R') ∈ C₃.ι.opensRange) :
    C₃.defectAt f a h₃ = C₂.defectAt f a h₂ := by
  have : IsOpenImmersion (Spec.map ψ) := by
    have : IsOpenImmersion (Spec.map ψ ≫ C₂.ι) := hψ ▸ inferInstance
    exact IsOpenImmersion.of_comp _ C₂.ι
  have hbase : C₃.base f = ψ.hom.comp (C₂.base f) := by
    have : CommRingCat.ofHom (C₃.base f) = CommRingCat.ofHom (C₂.base f) ≫ ψ := by
      apply Spec_map_injective
      rw [Spec_base, Spec.map_comp, Spec_base, hψ, Category.assoc]
    exact congrArg CommRingCat.Hom.hom this
  have hpoint : C₂.pointHom a h₂ = (C₃.pointHom a h₃).comp ψ.hom := by
    apply pointHom_eq_of_Spec
    have : CommRingCat.ofHom ((C₃.pointHom a h₃).comp ψ.hom) =
        ψ ≫ CommRingCat.ofHom (C₃.pointHom a h₃) := rfl
    rw [this, Spec.map_comp, Category.assoc, ← hψ, Spec_pointHom, liftPoint_ι]
  rw [defectAt, defectAt, hbase, hpoint]
  exact chartDefect_comp_of_formallyEtale _ _ _ (formallyEtale_of_isOpenImmersion ψ)

/-- The defect of a point does not depend on the chart. -/
theorem defectAt_eq (f : X ⟶ Spec (CommRingCat.of R)) (C₁ C₂ : AffineChart X)
    (a : Spec (CommRingCat.of R') ⟶ X)
    (h₁ : a (IsLocalRing.closedPoint R') ∈ C₁.ι.opensRange)
    (h₂ : a (IsLocalRing.closedPoint R') ∈ C₂.ι.opensRange) :
    C₁.defectAt f a h₁ = C₂.defectAt f a h₂ := by
  set y := C₁.liftPoint a h₁ (IsLocalRing.closedPoint R') with hy
  have hya : C₁.ι y = a (IsLocalRing.closedPoint R') := by
    rw [hy]
    change (C₁.liftPoint a h₁ ≫ C₁.ι) (IsLocalRing.closedPoint R') = _
    rw [liftPoint_ι]
  have hyW : y ∈ C₁.ι ⁻¹ᵁ C₂.ι.opensRange := by
    change C₁.ι y ∈ C₂.ι.opensRange
    rw [hya]; exact h₂
  obtain ⟨_, ⟨s, rfl⟩, hys, hsW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hyW
      (C₁.ι ⁻¹ᵁ C₂.ι.opensRange).2
  let ψ₁ : C₁.ring ⟶ CommRingCat.of (Localization.Away s) :=
    CommRingCat.ofHom (algebraMap C₁.ring (Localization.Away s))
  let C₃ : AffineChart X := ⟨CommRingCat.of (Localization.Away s), Spec.map ψ₁ ≫ C₁.ι⟩
  have hrange : (Spec.map ψ₁).opensRange = PrimeSpectrum.basicOpen s :=
    Scheme.Hom.opensRange_localizationAway s
  have h₃ : a (IsLocalRing.closedPoint R') ∈ C₃.ι.opensRange := by
    rw [← hya]
    have hy' : y ∈ (Spec.map ψ₁).opensRange := by rw [hrange]; exact hys
    obtain ⟨z, hz⟩ := hy'
    exact ⟨z, by simp only [C₃, Scheme.Hom.comp_apply, hz]⟩
  have hsub : Set.range C₃.ι ⊆ Set.range C₂.ι := by
    rintro _ ⟨z, rfl⟩
    have hz : Spec.map ψ₁ z ∈ (Spec.map ψ₁).opensRange := ⟨z, rfl⟩
    rw [hrange] at hz
    exact hsW hz
  rw [← defectAt_eq_of_factor f C₁ C₃ ψ₁ rfl a h₁ h₃]
  have hfac : C₃.ι = Spec.map (Spec.preimage (IsOpenImmersion.lift C₂.ι C₃.ι hsub)) ≫ C₂.ι := by
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
  exact defectAt_eq_of_factor f C₂ C₃ _ hfac a h₂ h₃

/-- The chart of an affine open. -/
noncomputable def ofAffineOpen (U : X.affineOpens) : AffineChart X where
  ring := Γ(X, U)
  ι := U.2.fromSpec
  isOpenImmersion := U.2.isOpenImmersion_fromSpec

@[simp] theorem ofAffineOpen_opensRange (U : X.affineOpens) :
    (ofAffineOpen U).ι.opensRange = U := by
  have := U.2.isOpenImmersion_fromSpec
  exact U.2.opensRange_fromSpec

/-- Every point of an open lies in a chart contained in that open. -/
theorem exists_le (x : X) (W : X.Opens) (hx : x ∈ W) :
    ∃ C : AffineChart X, x ∈ C.ι.opensRange ∧ C.ι.opensRange ≤ W := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  exact ⟨ofAffineOpen ⟨U, hU⟩, by simpa using hxU, by simpa using hUW⟩

theorem exists_mem (x : X) : ∃ C : AffineChart X, x ∈ C.ι.opensRange := by
  obtain ⟨C, hC, -⟩ := exists_le x ⊤ trivial
  exact ⟨C, hC⟩

/-- The image of the closed point under the lift of a point. -/
theorem liftPoint_closedPoint (a : Spec (CommRingCat.of R') ⟶ X)
    (h : a (IsLocalRing.closedPoint R') ∈ C.ι.opensRange) :
    (C.liftPoint a h (IsLocalRing.closedPoint R')).asIdeal =
      (IsLocalRing.maximalIdeal R').comap (C.pointHom a h) := by
  have e := C.Spec_pointHom a h
  calc (C.liftPoint a h (IsLocalRing.closedPoint R')).asIdeal
      = ((Spec.map (CommRingCat.ofHom (C.pointHom a h)))
          (IsLocalRing.closedPoint R')).asIdeal := by rw [e]
    _ = _ := rfl

theorem ι_liftPoint_closedPoint (a : Spec (CommRingCat.of R') ⟶ X)
    (h : a (IsLocalRing.closedPoint R') ∈ C.ι.opensRange) :
    C.ι (C.liftPoint a h (IsLocalRing.closedPoint R')) = a (IsLocalRing.closedPoint R') := by
  change (C.liftPoint a h ≫ C.ι) (IsLocalRing.closedPoint R') = _
  rw [liftPoint_ι]

end AffineChart

theorem isOpenImmersion_comp_of_isIso_restrict {T X₁ : Scheme.{u}} (j : T ⟶ X₁)
    [IsOpenImmersion j] (g : X₁ ⟶ X) (W : X.Opens) [IsIso (g ∣_ W)]
    (h : j.opensRange ≤ g ⁻¹ᵁ W) : IsOpenImmersion (j ≫ g) := by
  have hsub : Set.range j ⊆ Set.range (g ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
    exact h
  have hj : j = IsOpenImmersion.lift (g ⁻¹ᵁ W).ι j hsub ≫ (g ⁻¹ᵁ W).ι :=
    (IsOpenImmersion.lift_fac _ _ _).symm
  have : IsOpenImmersion (IsOpenImmersion.lift (g ⁻¹ᵁ W).ι j hsub) := by
    have : IsOpenImmersion (IsOpenImmersion.lift (g ⁻¹ᵁ W).ι j hsub ≫ (g ⁻¹ᵁ W).ι) :=
      hj ▸ inferInstance
    exact IsOpenImmersion.of_comp _ (g ⁻¹ᵁ W).ι
  rw [hj, Category.assoc, ← morphismRestrict_ι]
  infer_instance

namespace AffineChart

variable {R' : Type u} [CommRing R'] [IsLocalRing R']

/-- A chart of `X₁` pushed along a morphism that is an isomorphism over an open containing it. -/
noncomputable def push {X₁ : Scheme.{u}} (C : AffineChart X₁) (g : X₁ ⟶ X) (W : X.Opens)
    [IsIso (g ∣_ W)] (h : C.ι.opensRange ≤ g ⁻¹ᵁ W) : AffineChart X where
  ring := C.ring
  ι := C.ι ≫ g
  isOpenImmersion := isOpenImmersion_comp_of_isIso_restrict C.ι g W h

theorem push_mem {X₁ : Scheme.{u}} (C : AffineChart X₁) (g : X₁ ⟶ X) (W : X.Opens)
    [IsIso (g ∣_ W)] (h : C.ι.opensRange ≤ g ⁻¹ᵁ W) (a : Spec (CommRingCat.of R') ⟶ X₁)
    (ha : a (IsLocalRing.closedPoint R') ∈ C.ι.opensRange) :
    (a ≫ g) (IsLocalRing.closedPoint R') ∈ (C.push g W h).ι.opensRange := by
  obtain ⟨z, hz⟩ := ha
  refine ⟨z, ?_⟩
  change (C.ι ≫ g) z = (a ≫ g) _
  rw [Scheme.Hom.comp_apply]
  exact congrArg g hz

theorem push_defectAt {X₁ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (C : AffineChart X₁)
    (g : X₁ ⟶ X) (W : X.Opens) [IsIso (g ∣_ W)] (h : C.ι.opensRange ≤ g ⁻¹ᵁ W)
    (a : Spec (CommRingCat.of R') ⟶ X₁) (ha : a (IsLocalRing.closedPoint R') ∈ C.ι.opensRange) :
    (C.push g W h).defectAt f (a ≫ g) (C.push_mem g W h a ha) = C.defectAt (g ≫ f) a ha := by
  have hb : (C.push g W h).base f = C.base (g ≫ f) := by
    unfold base push
    simp only [Category.assoc]
  have hp : (C.push g W h).pointHom (a ≫ g) (C.push_mem g W h a ha) = C.pointHom a ha := by
    apply pointHom_eq_of_Spec
    exact (by rw [Spec_pointHom, liftPoint_ι] :
      (Spec.map (CommRingCat.ofHom (C.pointHom a ha)) ≫ C.ι) ≫ g = a ≫ g)
  rw [defectAt, defectAt, hb, hp]
  rfl

end AffineChart

/-- A point of `Spec B` lies in the smooth locus of `Spec B → Spec A` (assumed locally of finite
presentation) exactly when its prime lies in the algebraic smooth locus of the `A`-algebra `B`. -/
theorem mem_smoothLocus_SpecMap_iff {A B : CommRingCat.{u}} (φ : A ⟶ B)
    [LocallyOfFinitePresentation (Spec.map φ)] (p : Spec B) :
    p ∈ (Spec.map φ).smoothLocus ↔
      (letI := φ.hom.toAlgebra; (show PrimeSpectrum B from p) ∈ Algebra.smoothLocus A B) := by
  let := φ.hom.toAlgebra
  rw [Scheme.Hom.mem_smoothLocus,
    RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso φ p)]
  let p' : PrimeSpectrum B := p
  let q := (p'.comap φ.hom).asIdeal
  have : p'.asIdeal.LiesOver q := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver q p'.asIdeal
  trans Algebra.FormallySmooth (Localization.AtPrime q) (Localization.AtPrime p'.asIdeal)
  · rw [← RingHom.formallySmooth_algebraMap]
    rfl
  · exact Algebra.FormallySmooth.iff_restrictScalars.symm

end Langlands.AlgebraicGeometry.DvrSmoothening
