import Langlands.CommutativeAlgebra.PointedEtaleLocalSections
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Sections of etale and smooth algebras over a Henselian local ring -/

universe u

open Polynomial

noncomputable section

namespace Langlands.CommutativeAlgebra.HenselianSections

variable {R K : Type u} {S : Type*} [CommRing R] [HenselianLocalRing R] [CommRing S] [Algebra R S]
  [Field K] [Algebra R K]

/-- Over a surjection from a local ring onto a field, an element is a unit
exactly when its image is nonzero. -/
theorem isUnit_of_algebraMap_ne_zero (hK : Function.Surjective (algebraMap R K)) {r : R}
    (hr : algebraMap R K r ≠ 0) : IsUnit r := by
  by_contra h
  apply hr
  rw [← RingHom.mem_ker, IsLocalRing.ker_eq_maximalIdeal _ hK]
  exact (IsLocalRing.mem_maximalIdeal r).mpr h

/-- A point of a standard etale algebra with values in a residue field of a
Henselian local ring lifts to an algebra section. -/
theorem exists_lift_of_isStandardEtale [Algebra.IsStandardEtale R S]
    (hK : Function.Surjective (algebraMap R K)) (φ : S →ₐ[R] K) :
    ∃ σ : S →ₐ[R] R, (Algebra.ofId R K).comp σ = φ := by
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := R) (S := S)
  have hφ : P.HasMap (φ P.x) := P.hasMap.map φ
  have hder : IsUnit (aeval (φ P.x) (derivative P.f)) := hφ.isUnit_derivative_f
  have hiff := (HenselianLocalRing.TFAE R).out 1 3
  obtain ⟨a, ha, hax⟩ := hiff.mp ‹_› (K := K) (algebraMap R K) hK P.f P.monic_f (φ P.x)
    (by simpa [aeval_def] using hφ.1) (by simpa [aeval_def] using hder.ne_zero)
  have hga : IsUnit (aeval a P.g) := by
    refine isUnit_of_algebraMap_ne_zero hK ?_
    have : algebraMap R K (aeval a P.g) = aeval (φ P.x) P.g := by
      rw [← hax, coe_aeval_eq_eval, aeval_def, eval₂_at_apply]
    rw [this]
    exact hφ.2.ne_zero
  have hmap : P.HasMap a := ⟨by simpa [coe_aeval_eq_eval] using ha, hga⟩
  refine ⟨(P.P.lift a hmap).comp P.equivRing.toAlgHom, ?_⟩
  apply P.hom_ext
  simp [hax]

/-- A point of an etale algebra with values in a residue field of a Henselian
local ring lifts to an algebra section. -/
theorem exists_lift_of_etale [Algebra.Etale R S]
    (hK : Function.Surjective (algebraMap R K)) (φ : S →ₐ[R] K) :
    ∃ σ : S →ₐ[R] R, (Algebra.ofId R K).comp σ = φ := by
  let Q : Ideal S := RingHom.ker φ.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime _
  have : Algebra.IsEtaleAt R Q := by
    have : Algebra.FormallyEtale S (Localization.AtPrime Q) :=
      .of_isLocalization Q.primeCompl
    exact Algebra.FormallyEtale.comp R S (Localization.AtPrime Q)
  obtain ⟨f, hfQ, _⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
  let Sf := Localization.Away f
  have hfu : IsUnit (φ f) := isUnit_iff_ne_zero.mpr (by simpa [Q, RingHom.mem_ker] using hfQ)
  let φfRing : Sf →+* K := IsLocalization.Away.lift f hfu
  have hφf : φfRing.comp (algebraMap S Sf) = φ.toRingHom := IsLocalization.lift_comp _
  let φf : Sf →ₐ[R] K :=
    ⟨φfRing, fun r => by
      rw [IsScalarTower.algebraMap_apply R S Sf]
      change (φfRing.comp (algebraMap S Sf)) (algebraMap R S r) = _
      rw [hφf]
      exact φ.commutes r⟩
  obtain ⟨σ, hσ⟩ := exists_lift_of_isStandardEtale hK φf
  refine ⟨σ.comp (IsScalarTower.toAlgHom R S Sf), ?_⟩
  ext x
  have h1 := congrArg (fun h : Sf →ₐ[R] K => h (algebraMap S Sf x)) hσ
  have h2 := congrArg (fun h : S →+* K => h x) hφf
  exact h1.trans h2

/-- A point of a smooth algebra with values in a residue field of a Henselian
local ring lifts to an algebra section. -/
theorem exists_lift_of_smooth {S : Type u} [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (hK : Function.Surjective (algebraMap R K)) (φ : S →ₐ[R] K) :
    ∃ σ : S →ₐ[R] R, (Algebra.ofId R K).comp σ = φ := by
  let 𝔪 := IsLocalRing.maximalIdeal R
  have hL : Function.Surjective (algebraMap R 𝔪.ResidueField) :=
    Ideal.algebraMap_residueField_surjective 𝔪
  have hker : ∀ a ∈ RingHom.ker (Algebra.ofId R K), Algebra.ofId R 𝔪.ResidueField a = 0 := by
    intro a ha
    have ha' : a ∈ IsLocalRing.maximalIdeal R := by
      rw [← IsLocalRing.ker_eq_maximalIdeal _ hK]
      exact ha
    have ha'' : a ∈ RingHom.ker (algebraMap R 𝔪.ResidueField) := by
      rw [IsLocalRing.ker_eq_maximalIdeal _ hL]
      exact ha'
    exact ha''
  let e : K →ₐ[R] 𝔪.ResidueField :=
    (Ideal.Quotient.liftₐ _ (Algebra.ofId R 𝔪.ResidueField) hker).comp
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R K) hK).symm.toAlgHom
  obtain ⟨R', _, _, hR', ψ, ρ, hfac⟩ :=
    PointedEtaleLocalSections.exists_etale_factor_of_smooth 𝔪 (e.comp φ)
  obtain ⟨τ, hτ⟩ := exists_lift_of_etale (S := R') hL ρ
  refine ⟨τ.comp ψ, ?_⟩
  ext x
  apply e.toRingHom.injective
  have h1 := congrArg (fun h : R' →ₐ[R] 𝔪.ResidueField => h (ψ x)) hτ
  have h2 := congrArg (fun h : S →ₐ[R] 𝔪.ResidueField => h x) hfac
  change e (algebraMap R K (τ (ψ x))) = e (φ x)
  rw [e.commutes]
  exact h1.trans h2

section Scheme

open CategoryTheory AlgebraicGeometry

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

/-- A smooth scheme over a Henselian local ring with a point over a field
quotient of the ring has a section through that point. -/
theorem exists_section_of_smooth_of_surjective {K : Type u} [Field K] [Algebra R K]
    (hK : Function.Surjective (algebraMap R K)) {U : Scheme.{u}}
    (p : U ⟶ Spec (CommRingCat.of R)) [Smooth p] (b : Spec (CommRingCat.of K) ⟶ U)
    (hb : b ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ σ : Spec (CommRingCat.of R) ⟶ U, σ ≫ p = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ = b := by
  obtain ⟨V, hV, hyV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := b (IsLocalRing.closedPoint K)) (U := ⊤) trivial
  have hrange : Set.range b ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum K) z (IsLocalRing.closedPoint K)]
    exact hyV
  let bV : Spec (CommRingCat.of K) ⟶ Spec Γ(U, V) := IsOpenImmersion.lift hV.fromSpec b hrange
  have hbV : bV ≫ hV.fromSpec = b := IsOpenImmersion.lift_fac _ _ _
  let g : CommRingCat.of R ⟶ Γ(U, V) := Spec.preimage (hV.fromSpec ≫ p)
  have hg : Spec.map g = hV.fromSpec ≫ p := Spec.map_preimage _
  let φ : Γ(U, V) ⟶ CommRingCat.of K := Spec.preimage bV
  have hφ : Spec.map φ = bV := Spec.map_preimage _
  let : Algebra R Γ(U, V) := g.hom.toAlgebra
  have : Algebra.Smooth R Γ(U, V) := by
    have h : Smooth (Spec.map g) := by
      rw [hg]
      infer_instance
    exact RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp h)
  have hgφ : g ≫ φ = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hg, ← Category.assoc, hbV, hb]
  let φA : Γ(U, V) →ₐ[R] K :=
    { toRingHom := φ.hom
      commutes' := fun r => congrArg (fun h : CommRingCat.of R ⟶ CommRingCat.of K => h.hom r) hgφ }
  obtain ⟨τ, hτ⟩ := exists_lift_of_smooth hK φA
  let τC : Γ(U, V) ⟶ CommRingCat.of R := CommRingCat.ofHom τ.toRingHom
  refine ⟨Spec.map τC ≫ hV.fromSpec, ?_, ?_⟩
  · have hτg : g ≫ τC = 𝟙 _ := by
      ext r
      exact τ.commutes r
    rw [Category.assoc, ← hg, ← Spec.map_comp, hτg, Spec.map_id]
  · have hτφ : τC ≫ CommRingCat.ofHom (algebraMap R K) = φ := by
      ext x
      exact congrArg (fun h : Γ(U, V) →ₐ[R] K => h x) hτ
    rw [← Category.assoc, ← Spec.map_comp, hτφ, hφ, hbV]

/-- A smooth scheme over a Henselian local ring with a point over the residue
field of the closed point has a section through that point. -/
theorem exists_section_of_smooth {U : Scheme.{u}} (p : U ⟶ Spec (CommRingCat.of R)) [Smooth p]
    (b : Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) ⟶ U)
    (hb : b ≫ p = (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R)) :
    ∃ σ : Spec (CommRingCat.of R) ⟶ U, σ ≫ p = 𝟙 _ ∧
      (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R) ≫ σ = b := by
  have : (IsLocalRing.closedPoint R).asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  have hL : Function.Surjective
      (algebraMap R (IsLocalRing.closedPoint R).asIdeal.ResidueField) :=
    Ideal.algebraMap_residueField_surjective _
  have hfac := Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField
    (CommRingCat.of R) (IsLocalRing.closedPoint R)
  obtain ⟨σ, hσ, hσb⟩ := exists_section_of_smooth_of_surjective hL p
    (Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of R) (IsLocalRing.closedPoint R)).hom ≫ b)
    (by
      rw [Category.assoc, hb, ← hfac, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
        Spec.map_id, Category.id_comp])
  refine ⟨σ, hσ, ?_⟩
  rw [← hfac, Category.assoc, hσb, ← Category.assoc, ← Spec.map_comp, Iso.hom_inv_id,
    Spec.map_id, Category.id_comp]

/-- An etale scheme over a Henselian local ring with a point over the residue
field of the closed point has a section through that point. -/
theorem exists_section_of_etale {U : Scheme.{u}} (p : U ⟶ Spec (CommRingCat.of R)) [Etale p]
    (b : Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) ⟶ U)
    (hb : b ≫ p = (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R)) :
    ∃ σ : Spec (CommRingCat.of R) ⟶ U, σ ≫ p = 𝟙 _ ∧
      (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R) ≫ σ = b :=
  exists_section_of_smooth p b hb

/-- Every etale scheme over a Henselian local ring, with a point over the
residue field of the closed point, has a section through that point. -/
def HenselianEtaleSectionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [HenselianLocalRing R] (U : Scheme.{u})
    (p : U ⟶ Spec (CommRingCat.of R)), Etale p →
    ∀ (b : Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) ⟶ U),
      b ≫ p = (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R) →
      ∃ σ : Spec (CommRingCat.of R) ⟶ U, σ ≫ p = 𝟙 _ ∧
        (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R) ≫ σ = b

theorem henselianEtaleSection : HenselianEtaleSectionStatement.{u} :=
  fun _ _ _ _ p _ b hb => exists_section_of_etale p b hb

end Scheme

end Langlands.CommutativeAlgebra.HenselianSections
