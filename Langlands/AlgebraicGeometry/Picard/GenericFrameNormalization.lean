import Langlands.AlgebraicGeometry.AffineGenericScalarUnits
import Langlands.AlgebraicGeometry.Picard.FrameUnitGauge

/-! # Compatible normalization of generic frame transitions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.CocycleGluing

variable {X Y : Scheme.{u}} {ι : Type u}

/-- Restriction on the actual groups of section units. -/
def sectionUnitRestrict {U V : X.Opens} (h : V ≤ U) :
    Γ(X, U)ˣ →* Γ(X, V)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom

@[simp]
theorem sectionUnitRestrict_comp {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V)
    (a : Γ(X, U)ˣ) :
    sectionUnitRestrict h' (sectionUnitRestrict h a) =
      sectionUnitRestrict (h'.trans h) a := by
  apply Units.ext
  change X.presheaf.map (homOfLE h').op (X.presheaf.map (homOfLE h).op (a : Γ(X, U))) =
    X.presheaf.map (homOfLE (h'.trans h)).op (a : Γ(X, U))
  exact res_res h h' _

/-- Pullback on the actual groups of section units. -/
def sectionUnitPullback (q : Y ⟶ X) (U : X.Opens) :
    Γ(X, U)ˣ →* Γ(Y, q ⁻¹ᵁ U)ˣ :=
  Units.map (q.app U).hom.toMonoidHom

@[simp]
theorem sectionUnitRestrict_pullback (q : Y ⟶ X) {U V : X.Opens} (h : V ≤ U)
    (a : Γ(X, U)ˣ) :
    sectionUnitRestrict (q.preimage_mono h) (sectionUnitPullback q U a) =
      sectionUnitPullback q V (sectionUnitRestrict h a) := by
  apply Units.ext
  change Y.presheaf.map (homOfLE (q.preimage_mono h)).op (q.app U (a : Γ(X, U))) =
    q.app V (X.presheaf.map (homOfLE h).op (a : Γ(X, U)))
  simp only [Scheme.Hom.app_eq_appLE, ← ConcreteCategory.comp_apply,
    Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

variable (q : Y ⟶ X) (T : ι → X.Opens)
    (g : ∀ i j, Γ(Y, q ⁻¹ᵁ T i ⊓ q ⁻¹ᵁ T j)ˣ) (i₀ : ι)

/-- A compatible generic scalar on each open and a total-unit expression
for each transition from one reference open. -/
structure GenericScalarNormalization where
  scalar : ∀ i, Γ(Y, q ⁻¹ᵁ T i)ˣ
  totalUnit : ∀ i, Γ(X, T i₀ ⊓ T i)ˣ
  reference_eq : ∀ i,
    g i₀ i =
      sectionUnitRestrict (q.preimage_mono (inf_le_right : T i₀ ⊓ T i ≤ T i)) (scalar i) *
        sectionUnitPullback q (T i₀ ⊓ T i) (totalUnit i)

variable {q T g i₀}

/-- After normalization, a transition on a common subopen of the reference
and two cover opens is the ratio of their total reference units. -/
theorem GenericScalarNormalization.transition_restrict
    (n : GenericScalarNormalization q T g i₀) (hg : IsCocycle g) (i j : ι)
    {W : X.Opens} (hW₀ : W ≤ T i₀) (hWi : W ≤ T i) (hWj : W ≤ T j) :
    sectionUnitRestrict (q.preimage_mono (le_inf hWi hWj))
        (unitGaugeCocycle g n.scalar i j) =
      sectionUnitPullback q W
        ((sectionUnitRestrict (le_inf hW₀ hWi) (n.totalUnit i))⁻¹ *
          sectionUnitRestrict (le_inf hW₀ hWj) (n.totalUnit j)) := by
  let A := sectionUnitRestrict (q.preimage_mono hWi) (n.scalar i)
  let B := sectionUnitRestrict (q.preimage_mono hWj) (n.scalar j)
  let a := sectionUnitPullback q W
    (sectionUnitRestrict (le_inf hW₀ hWi) (n.totalUnit i))
  let b := sectionUnitPullback q W
    (sectionUnitRestrict (le_inf hW₀ hWj) (n.totalUnit j))
  let G := sectionUnitRestrict (q.preimage_mono (le_inf hWi hWj)) (g i j)
  have hi :
      sectionUnitRestrict (q.preimage_mono (le_inf hW₀ hWi)) (g i₀ i) = A * a := by
    rw [n.reference_eq i, map_mul, sectionUnitRestrict_comp, sectionUnitRestrict_pullback]
  have hj :
      sectionUnitRestrict (q.preimage_mono (le_inf hW₀ hWj)) (g i₀ j) = B * b := by
    rw [n.reference_eq j, map_mul, sectionUnitRestrict_comp, sectionUnitRestrict_pullback]
  have hc : (A * a) * G = B * b := by
    rw [← hi, ← hj]
    apply Units.ext
    exact cocycle_res g hg i₀ i j
      (q.preimage_mono (le_inf hW₀ hWi))
      (q.preimage_mono (le_inf hWi hWj))
      (q.preimage_mono (le_inf hW₀ hWj))
  have hgroup : A * G * B⁻¹ = a⁻¹ * b := by
    apply mul_left_cancel (a := a)
    calc
      a * (A * G * B⁻¹) = ((A * a) * G) * B⁻¹ := by ac_rfl
      _ = (B * b) * B⁻¹ := by rw [hc]
      _ = b := by rw [mul_comm B b, mul_assoc, mul_inv_cancel, mul_one]
      _ = a * (a⁻¹ * b) := by simp
  change sectionUnitRestrict (le_inf (q.preimage_mono hWi) (q.preimage_mono hWj))
      (sectionUnitRestrict inf_le_left (n.scalar i) * g i j *
        (sectionUnitRestrict inf_le_right (n.scalar j))⁻¹) = _
  rw [map_mul, map_mul, map_inv, sectionUnitRestrict_comp, sectionUnitRestrict_comp]
  change A * G * B⁻¹ = _
  rw [map_mul, map_inv]
  exact hgroup

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    (p : X ⟶ Spec (CommRingCat.of R))
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (s : Y ⟶ Spec (CommRingCat.of K))
    (H : IsPullback q s p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    [Smooth p] [GeometricallyConnected p]

/-- Construct compatible generic scalar normalization from the actual
affine reference-overlap decompositions. Projectivity is retained explicitly. -/
def affineGenericScalarNormalization
    (hT : ∀ i, IsAffineOpen (T i))
    (hI : ∀ i, IsAffineOpen (T i₀ ⊓ T i))
    (hmeet : ∀ i,
      (p ⁻¹' {IsLocalRing.closedPoint R} ∩ ((T i₀ ⊓ T i) : Set X)).Nonempty)
    (hproj : ∀ i, letI := affineSectionAlgebra p (hI i);
      Module.Projective R Γ(X, T i₀ ⊓ T i)) :
    GenericScalarNormalization q T g i₀ := by
  have hdecomp : ∀ i, ∃ (r d : R) (hr : r ≠ 0) (hd : d ≠ 0)
      (a : Γ(X, T i₀ ⊓ T i)ˣ),
      g i₀ i = affineGenericScalarRatio p K q s H (hI i) r d hr hd *
        sectionUnitPullback q (T i₀ ⊓ T i) a := by
    intro i
    let := affineSectionAlgebra p (hI i)
    let := pullbackSectionAlgebra q (T i₀ ⊓ T i)
    let n := affineGenericUnitDecomposition p K q s H (hI i) (hmeet i)
      (hproj i) (g i₀ i)
    exact ⟨n.denominator, n.numerator, n.denominator_ne_zero, n.numerator_ne_zero,
      n.totalUnit, affineGenericUnitDecomposition_eq p K q s H (hI i) (hmeet i)
        (hproj i) (g i₀ i)⟩
  choose r d hr hd a ha using hdecomp
  refine ⟨fun i => affineGenericScalarRatio p K q s H (hT i)
    (r i) (d i) (hr i) (hd i), a, ?_⟩
  intro i
  rw [ha i]
  congr 1
  exact (affineGenericScalarRatio_restrict p K q s H (hT i) (hI i)
    inf_le_right (r i) (d i) (hr i) (hd i)).symm

end Langlands.AlgebraicGeometry.Picard.CocycleGluing
