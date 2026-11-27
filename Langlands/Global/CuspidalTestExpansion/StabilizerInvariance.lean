import Langlands.Global.AdelicEisensteinBruhatAbsoluteBound
import Langlands.Global.DiscreteLeftCosetMeasureTransport
import Langlands.Automorphic.GroupSchemeParabolicWeilMeasure

/-! # Invariance of unfolded Eisenstein stabilizer integrals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions
  EisensteinConstantTerm

variable {F : Type u} [Field F] [NumberField F]
  {G P Q V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine V.X.left]
  (p : P ⟶ G) (q : Q ⟶ G) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
  [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range (iV ≫ q)))]

local notation "Points" => AdelicGroupPoints F G
local notation "j" => (iV ≫ q)
local notation "Vₐ" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)

/-- The integral over `(V(F) ∩ wP(F)w⁻¹) \ V(𝔸)` of `v ↦ Φ(w⁻¹ v y)`. -/
def stabilizerIntegral (w : Points) (Φ : Points → ℂ) (y : Points) : ℂ :=
  ∫ v, eisensteinStabilizerIntegrand p q iV w Φ y v ∂stabilizerMeasure F p j w

set_option maxHeartbeats 800000 in
/-- The stabilizer integral is left invariant under `V(𝔸)`. -/
theorem stabilizerIntegral_adelicPoints_mul (w : Points) (Φ : Points → ℂ)
    (hΦ : IsLeftInvariantUnder F G (rationalImage F p) Φ) (u : Vₐ) (y : Points) :
    stabilizerIntegral p q iV w Φ ((u : Points) * y) = stabilizerIntegral p q iV w Φ y := by
  have hcl : IsClosed (Vₐ : Set Points) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  have : LocallyCompactSpace Vₐ := hcl.locallyCompactSpace
  have : PolishSpace Vₐ := hcl.polishSpace
  let Γ := stabilizerRationalSubgroup F p j w
  have hΓ := isDiscrete_stabilizerRationalSubgroup F p j w
  have : BorelSpace (LeftCosetSpace Γ) := LeftCosetSpace.discreteQuotientBorelSpace Γ hΓ
  let ν := AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j)
  have : (Measure.haar : Measure Vₐ).IsMulRightInvariant :=
    AdelicSubgroupPoints.haar_isMulRightInvariant_of_compactRationalQuotient F G
      (SubgroupFunctor.range j)
  have : ν.IsMulLeftInvariant := by
    dsimp only [ν, AdelicSubgroupPoints.normalizedHaarMeasure]; infer_instance
  have : ν.IsMulRightInvariant := by
    dsimp only [ν, AdelicSubgroupPoints.normalizedHaarMeasure]; infer_instance
  have hmp := LeftCosetSpace.measurePreserving_rightTranslate_discrete Γ hΓ ν u
  have hcomp : eisensteinStabilizerIntegrand p q iV w Φ ((u : Points) * y) =
      eisensteinStabilizerIntegrand p q iV w Φ y ∘ LeftCosetSpace.rightTranslate Γ u := by
    funext x
    induction x using Quotient.inductionOn with
    | _ v =>
      change eisensteinStabilizerIntegrand p q iV w Φ ((u : Points) * y) (LeftCosetSpace.mk Γ v) =
        eisensteinStabilizerIntegrand p q iV w Φ y
          (LeftCosetSpace.rightTranslate Γ u (LeftCosetSpace.mk Γ v))
      rw [LeftCosetSpace.rightTranslate_mk, eisensteinStabilizerIntegrand_mk p q iV w Φ hΦ,
        eisensteinStabilizerIntegrand_mk p q iV w Φ hΦ]
      congr 1
      simp only [Subgroup.coe_mul, mul_assoc]
  have hemb : MeasurableEmbedding (LeftCosetSpace.rightTranslate Γ u) :=
    (LeftCosetSpace.rightTranslateHomeomorph Γ u).measurableEmbedding
  unfold stabilizerIntegral
  rw [hcomp]
  exact hmp.integral_comp hemb _

set_option maxHeartbeats 1200000 in
/-- The stabilizer integral is left invariant under rational points `δ ∈ Q(F)` with
`w⁻¹ δ w ∈ P(F)`. -/
theorem stabilizerIntegral_rational_mul (hN : (SubgroupFunctor.range iV).IsNormal) (w : Points)
    (Φ : Points → ℂ) (hΦ : IsLeftInvariantUnder F G (rationalImage F p) Φ)
    (x₀ : RationalGroupPoints F Q)
    (hx₀ : w⁻¹ * map F Q G q (rational F Q x₀) * w ∈ rationalImage F p) (y : Points) :
    stabilizerIntegral p q iV w Φ (map F Q G q (rational F Q x₀) * y) =
      stabilizerIntegral p q iV w Φ y := by
  have hcl : IsClosed (Vₐ : Set Points) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  have : LocallyCompactSpace Vₐ := hcl.locallyCompactSpace
  have : PolishSpace Vₐ := hcl.polishSpace
  let Γ := stabilizerRationalSubgroup F p j w
  have hΓ := isDiscrete_stabilizerRationalSubgroup F p j w
  have : BorelSpace (LeftCosetSpace Γ) := LeftCosetSpace.discreteQuotientBorelSpace Γ hΓ
  let ν := AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j)
  have : ν.IsMulLeftInvariant := by
    dsimp only [ν, AdelicSubgroupPoints.normalizedHaarMeasure]; infer_instance
  let δ := map F Q G q (rational F Q x₀)
  let Γr := AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range j)
  have hΓr := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range j)
  have : Countable Γr := countable_rationalSubgroup _
  let α := conjAdelic q iV hN (rational F Q x₀)
  have hαr : ∀ v, α v ∈ Γr ↔ v ∈ Γr := conjAdelic_mem_rationalSubgroup_iff q iV hN x₀
  have hmp : MeasurePreserving α ν ν :=
    measurePreserving_of_preserves Γr (LeftCosetSpace.measurableSet_fundamentalDomain Γr hΓr)
      (LeftCosetSpace.fundamentalDomain_unique Γr hΓr) α hαr Measure.haar
      (haar_fundamentalDomain_ne_zero _) (haar_fundamentalDomain_ne_top _) _
  have hx₀' : w⁻¹ * δ * w ∈ rationalImage F p := hx₀
  have hδP : w⁻¹ * δ⁻¹ * w ∈ rationalImage F p := by
    have h := (rationalImage F p).inv_mem hx₀'
    rwa [show (w⁻¹ * δ * w)⁻¹ = w⁻¹ * δ⁻¹ * w by group] at h
  have hstab : ∀ v, α v ∈ Γ ↔ v ∈ Γ := by
    intro v
    rw [mem_stabilizerRationalSubgroup_iff, mem_stabilizerRationalSubgroup_iff, hαr v]
    change _ ∧ w⁻¹ * (δ * (v : Points) * δ⁻¹) * w ∈ rationalImage F p ↔ _
    have heq : w⁻¹ * (δ * (v : Points) * δ⁻¹) * w =
        (w⁻¹ * δ * w) * (w⁻¹ * (v : Points) * w) * (w⁻¹ * δ⁻¹ * w) := by group
    rw [heq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have h := (rationalImage F p).mul_mem ((rationalImage F p).mul_mem
        ((rationalImage F p).inv_mem hx₀') h2) ((rationalImage F p).inv_mem hδP)
      rwa [show (w⁻¹ * δ * w)⁻¹ * ((w⁻¹ * δ * w) * (w⁻¹ * (v : Points) * w) * (w⁻¹ * δ⁻¹ * w)) *
        (w⁻¹ * δ⁻¹ * w)⁻¹ = w⁻¹ * (v : Points) * w by group] at h
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (rationalImage F p).mul_mem ((rationalImage F p).mul_mem hx₀' h2) hδP⟩
  let E := LeftCosetSpace.measurableEquivOfMulEquiv α Γ Γ hstab
  have hE : MeasurePreserving E (stabilizerMeasure F p j w) (stabilizerMeasure F p j w) :=
    LeftCosetSpace.measurePreserving_discreteQuotientMeasure α Γ Γ hstab hΓ hΓ ν ν hmp
  have hcomp : eisensteinStabilizerIntegrand p q iV w Φ (δ * y) ∘ E =
      eisensteinStabilizerIntegrand p q iV w Φ y := by
    funext x
    induction x using Quotient.inductionOn with
    | _ v =>
      change eisensteinStabilizerIntegrand p q iV w Φ (δ * y) (E (LeftCosetSpace.mk Γ v)) =
        eisensteinStabilizerIntegrand p q iV w Φ y (LeftCosetSpace.mk Γ v)
      have hE' : E (LeftCosetSpace.mk Γ v) = LeftCosetSpace.mk Γ (α v) := rfl
      rw [hE', eisensteinStabilizerIntegrand_mk p q iV w Φ hΦ,
        eisensteinStabilizerIntegrand_mk p q iV w Φ hΦ, conjAdelic_coe]
      have hsplit : w⁻¹ * (δ * (v : Points) * δ⁻¹) * (δ * y) =
          (w⁻¹ * δ * w) * (w⁻¹ * (v : Points) * y) := by group
      change Φ (w⁻¹ * (δ * (v : Points) * δ⁻¹) * (δ * y)) = _
      rw [hsplit, hΦ _ hx₀']
  unfold stabilizerIntegral
  rw [← hcomp]
  exact (hE.integral_comp E.measurableEmbedding _).symm

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- Left invariance under two subgroups gives left invariance under their join. -/
theorem isLeftInvariantUnder_join {H₁ H₂ : Subgroup Points} {f : Points → ℂ}
    (h₁ : IsLeftInvariantUnder F G H₁ f) (h₂ : IsLeftInvariantUnder F G H₂ f) :
    IsLeftInvariantUnder F G (H₁ ⊔ H₂) f := by
  let S : Subgroup Points :=
    { carrier := {x | ∀ g, f (x * g) = f g}
      mul_mem' := fun {a b} ha hb g => by rw [mul_assoc, ha, hb]
      one_mem' := fun g => by rw [one_mul]
      inv_mem' := fun {a} ha g => by
        have := ha (a⁻¹ * g)
        rw [mul_inv_cancel_left] at this
        exact this.symm }
  have hle : H₁ ⊔ H₂ ≤ S := sup_le (fun x hx => h₁ x hx) (fun x hx => h₂ x hx)
  exact fun x hx => hle hx

/-- For `V` normal in `Q` and `Φ` left invariant under `P(F)`, the stabilizer integral is left
invariant under the join of `Q(F) ∩ wP(F)w⁻¹` and `V(F)`, that is, under
`(Q(F) ∩ wP(F)w⁻¹) V(F)`. -/
theorem stabilizerIntegral_isLeftInvariantUnder (hN : (SubgroupFunctor.range iV).IsNormal)
    (w : Points) (Φ : Points → ℂ) (hΦ : IsLeftInvariantUnder F G (rationalImage F p) Φ) :
    IsLeftInvariantUnder F G ((rationalImage F q ⊓
        (rationalImage F p).map (MulAut.conj w).toMonoidHom) ⊔ rationalImage F (iV ≫ q))
      (stabilizerIntegral p q iV w Φ) := by
  refine isLeftInvariantUnder_join ?_ ?_
  · rintro x ⟨⟨x₀, rfl⟩, ⟨z, hz, hzx⟩⟩ y
    refine stabilizerIntegral_rational_mul p q iV hN w Φ hΦ x₀ ?_ y
    have hzx' : (MulAut.conj w).toMonoidHom z = map F Q G q (rational F Q x₀) := hzx
    rw [← hzx']
    have hz' : w⁻¹ * (MulAut.conj w).toMonoidHom z * w = z := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hz']
    exact hz
  · intro x hx y
    obtain ⟨u, hu⟩ : ∃ u : Vₐ, (u : Points) = x :=
      ⟨⟨x, rationalImage_le_adelicPoints (iV ≫ q) hx⟩, rfl⟩
    rw [← hu]
    exact stabilizerIntegral_adelicPoints_mul p q iV w Φ hΦ u y

end Langlands.Global
