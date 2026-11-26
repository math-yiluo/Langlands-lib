import Langlands.Automorphic.GroupSchemeSliceAdelicGrowthReduction
import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.Global.AdelicEisensteinGrowthBound
import Langlands.Global.AdelicFiniteTranslateHeightReduction
import Langlands.Global.FiniteAdelicGroupCompactOpen
import Langlands.Representation.Plancherel.ParabolicCharacterDecayProof
import Langlands.Global.AdelicMaximalCompactFactors

/-! # From arithmetic archimedean finiteness to adelic finiteness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme AdelicGroupPoints InfiniteAdelicGroupPoints
  RepresentationGrowth CompactIwasawa

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

/-- The archimedean arithmetic subgroup at the finite point `b` and finite level `L`. -/
def arithmeticInfiniteLevelGroup (L : Subgroup (FiniteAdelicGroupPoints F G))
    (b : FiniteAdelicGroupPoints F G) : Subgroup (InfiniteAdelicGroupPoints F G) :=
  (L.comap ((MulAut.conj b⁻¹).toMonoidHom.comp
    ((finite F G).toMonoidHom.comp (rational F G)))).map
      ((infinite F G).toMonoidHom.comp (rational F G))

/-- Harish-Chandra finiteness of fixed level, compact type and infinitesimal ideal on the
archimedean arithmetic quotients arising from the finite double cosets. -/
def ArithmeticHarishChandraFinitenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left],
    IsConnectedReductive G →
    ∀ {N d : ℕ} (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth)
      (L : OpenSubgroup (FiniteAdelicGroupPoints F G)),
      IsCompact (L : Set (FiniteAdelicGroupPoints F G)) →
    ∀ (b : FiniteAdelicGroupPoints F G) (H : Subgroup (InfiniteAdelicGroupPoints F G)),
      IsMaximalCompact H →
    ∀ (J : Ideal (AdelicEnvelopingCenter F G hsmooth)),
      Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ J.restrictScalars ℂ) →
    ∀ (E : Submodule ℂ (H → ℂ)), FiniteDimensional ℂ E →
      FiniteDimensional ℂ (Submodule.span ℂ {f : InfiniteAdelicGroupPoints F G → ℂ |
        (∀ eta ∈ arithmeticInfiniteLevelGroup F G L.toSubgroup b, ∀ x, f (eta * x) = f x) ∧
        (∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 ≤ r ∧ ∀ x,
          ‖f x‖ ≤ C * adelicHeightAtLeastOne ρ (ofInfinite F G x) ^ r) ∧
        (∃ hf : f ∈ InfinitePlotSmoothFunctions F G,
          ∀ z ∈ J, plotSmoothCenterAction F G hsmooth hcalc z ⟨f, hf⟩ = 0) ∧
        ∀ x, (fun k : H => f (x * k.val)) ∈ E})

/-- Harish-Chandra finiteness on the full rational quotient for a connected reductive group. -/
def RationalHarishChandraFinitenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left],
    IsConnectedReductive G →
    ∀ {N d : ℕ} (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth)
      (L : OpenSubgroup (FiniteAdelicGroupPoints F G))
      (H : Subgroup (InfiniteAdelicGroupPoints F G)), IsMaximalCompact H →
    ∀ (J : Ideal (AdelicEnvelopingCenter F G hsmooth)),
      Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ J.restrictScalars ℂ) →
    ∀ (E : Submodule ℂ (H → ℂ)), FiniteDimensional ℂ E →
      FiniteDimensional ℂ (Submodule.span ℂ {f : AdelicGroupPoints F G → ℂ |
        IsLeftInvariantUnder F G (rationalSubgroup F G) f ∧ IsAdelicSmoothFunction F G f ∧
        HasModerateGrowthFunction F G ρ f ∧
        (∀ b ∈ L, ∀ g, f (g * ofFinite F G b) = f g) ∧
        (∀ z ∈ J, ∀ b : FiniteAdelicGroupPoints F G,
          ∀ hf : functionInfiniteSlice F G f b ∈ InfinitePlotSmoothFunctions F G,
            plotSmoothCenterAction F G hsmooth hcalc z ⟨functionInfiniteSlice F G f b, hf⟩ = 0) ∧
        ∀ g, (fun k : H => f (g * ofInfinite F G k)) ∈ E})

private theorem infiniteSlice_invariant {L : OpenSubgroup (FiniteAdelicGroupPoints F G)}
    {f : AdelicGroupPoints F G → ℂ} (h : IsLeftInvariantUnder F G (rationalSubgroup F G) f)
    (hL : ∀ l ∈ L, ∀ g, f (g * ofFinite F G l) = f g)
    (b : FiniteAdelicGroupPoints F G) :
    ∀ eta ∈ arithmeticInfiniteLevelGroup F G L.toSubgroup b, ∀ x,
      functionInfiniteSlice F G f b (eta * x) = functionInfiniteSlice F G f b x := by
  rintro _ ⟨δ, hδ, rfl⟩ x
  let q := rational F G δ
  change b⁻¹ * finite F G q * (b⁻¹)⁻¹ ∈ L at hδ
  rw [inv_inv] at hδ
  have he : q * pair F G x b =
      pair F G (infinite F G q * x) b * ofFinite F G (b⁻¹ * finite F G q * b) := by
    calc
      q * pair F G x b = pair F G (infinite F G q * x) (finite F G q * b) := by
        conv_lhs => rw [← pair_projections F G q]
        rw [pair_mul]
      _ = _ := by rw [ofFinite_eq_pair, pair_mul, mul_one, ← mul_assoc, mul_inv_cancel_left]
  change f (pair F G (infinite F G q * x) b) = f (pair F G x b)
  rw [← hL _ hδ (pair F G (infinite F G q * x) b), ← he]
  exact h q ⟨δ, rfl⟩ _

/-- The arithmetic archimedean theorem and the finite adelic coset cover imply finiteness
on the full rational quotient. -/
theorem rationalHarishChandraFiniteness_of_arithmetic
    (hArch : ArithmeticHarishChandraFinitenessStatement.{u}) :
    RationalHarishChandraFinitenessStatement.{u} := by
  classical
  intro F _ _ G _ hG N d ρ hρ hsmooth hcalc L H hH J hJ E hE
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let C := FiniteAdelicGroupPoints.compactOpenSubgroup F G
  let L₀ : OpenSubgroup (FiniteAdelicGroupPoints F G) := L ⊓ C
  have hLc : IsCompact (L₀ : Set (FiniteAdelicGroupPoints F G)) := by
    change IsCompact ((L : Set (FiniteAdelicGroupPoints F G)) ∩ (C : Set _))
    exact (FiniteAdelicGroupPoints.isCompact_compactOpenSubgroup F G).inter_left L.isClosed
  obtain ⟨n, σ, hσ⟩ := Langlands.Plancherel.exists_isClosedSubgroup_fin_succ G
  obtain ⟨Ω, _, _, hΩ, _, hcover⟩ :=
    adelicRationalHeightReduction_of_finiteRightSiegelCover F G σ hG hσ (Nat.succ_pos n)
  obtain ⟨B, hB⟩ := exists_finset_mem_leftCoset L₀ hΩ
  let W (b : FiniteAdelicGroupPoints F G) :=
    Submodule.span ℂ {f : InfiniteAdelicGroupPoints F G → ℂ |
      (∀ eta ∈ arithmeticInfiniteLevelGroup F G L₀.toSubgroup b, ∀ x, f (eta * x) = f x) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 ≤ r ∧ ∀ x,
        ‖f x‖ ≤ C * adelicHeightAtLeastOne ρ (ofInfinite F G x) ^ r) ∧
      (∃ hf : f ∈ InfinitePlotSmoothFunctions F G,
        ∀ z ∈ J, plotSmoothCenterAction F G hsmooth hcalc z ⟨f, hf⟩ = 0) ∧
      ∀ x, (fun k : H => f (x * k.val)) ∈ E}
  let (b : B) : FiniteDimensional ℂ (W b.val) :=
    hArch F G hG ρ hρ hsmooth hcalc L₀ hLc b.val H hH J hJ E hE
  let A : Set (AdelicGroupPoints F G → ℂ) := {f |
    IsLeftInvariantUnder F G (rationalSubgroup F G) f ∧ IsAdelicSmoothFunction F G f ∧
    HasModerateGrowthFunction F G ρ f ∧
    (∀ b ∈ L, ∀ g, f (g * ofFinite F G b) = f g) ∧
    (∀ z ∈ J, ∀ b : FiniteAdelicGroupPoints F G,
      ∀ hf : functionInfiniteSlice F G f b ∈ InfinitePlotSmoothFunctions F G,
        plotSmoothCenterAction F G hsmooth hcalc z ⟨functionInfiniteSlice F G f b, hf⟩ = 0) ∧
    ∀ g, (fun k : H => f (g * ofInfinite F G k)) ∈ E}
  let S := Submodule.span ℂ A
  let R (b : B) : (AdelicGroupPoints F G → ℂ) →ₗ[ℂ] (InfiniteAdelicGroupPoints F G → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun x => pair F G x b.val)
  have hR (b : B) : S ≤ (W b.val).comap (R b) := by
    apply Submodule.span_le.mpr
    rintro f ⟨hInv, hSmooth, hGrowth, hLevel, hAnn, hType⟩
    change R b f ∈ W b.val
    apply Submodule.subset_span
    refine ⟨infiniteSlice_invariant F G (L := L₀) hInv (fun l hl => hLevel l hl.1) b.val, ?_,
      ⟨hSmooth.2.1 b.val, fun z hz => hAnn z hz b.val _⟩, ?_⟩
    · obtain ⟨r, hr, h⟩ := RepresentationGrowth.HasModerateGrowthFunction.exists_compact_mul_le_height
        hGrowth
      obtain ⟨B₀, hB₀, hbound⟩ := h {ofFinite F G b.val} isCompact_singleton
      refine ⟨B₀, hB₀, r, hr, fun x => ?_⟩
      simpa only [R, LinearMap.funLeft_apply, Function.comp_apply, ofInfinite_eq_pair,
        ofFinite_eq_pair, pair_mul, mul_one, one_mul] using
        hbound (ofInfinite F G x) (ofFinite F G b.val) rfl
    · intro x
      simpa only [R, LinearMap.funLeft_apply, Function.comp_apply, ofInfinite_eq_pair,
        pair_mul, mul_one] using hType (pair F G x b.val)
  let T : S →ₗ[ℂ] (∀ b : B, W b.val) := LinearMap.pi fun b =>
    ((R b).comp S.subtype).codRestrict (W b.val) (fun f => hR b f.property)
  change Module.Finite ℂ S
  refine Module.Finite.of_injective T (LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_))
  intro ⟨f, hmem⟩ hf
  have hfInv : IsLeftInvariantUnder F G (rationalSubgroup F G) f ∧
      ∀ l ∈ L₀, ∀ g, f (g * ofFinite F G l) = f g := by
    clear hf
    induction hmem using Submodule.span_induction with
    | mem g hg => exact ⟨hg.1, fun l hl => hg.2.2.2.1 l hl.1⟩
    | zero => exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    | add g h _ _ hg hh =>
      exact ⟨fun x hx y => congrArg₂ (· + ·) (hg.1 x hx y) (hh.1 x hx y),
        fun l hl y => congrArg₂ (· + ·) (hg.2 l hl y) (hh.2 l hl y)⟩
    | smul c g _ hg =>
      exact ⟨fun x hx y => congrArg (c • ·) (hg.1 x hx y),
        fun l hl y => congrArg (c • ·) (hg.2 l hl y)⟩
  apply Subtype.ext
  funext g
  change f g = 0
  obtain ⟨δ, hg, _⟩ := hcover g
  let x := rational F G δ * g
  obtain ⟨b, hb, hx⟩ := hB (finite F G x) hg
  have he : pair F G (infinite F G x) b * ofFinite F G (b⁻¹ * finite F G x) = x := by
    rw [ofFinite_eq_pair, pair_mul, mul_one, mul_inv_cancel_left, pair_projections]
  calc
    f g = f x := (hfInv.1 (rational F G δ) ⟨δ, rfl⟩ g).symm
    _ = f (pair F G (infinite F G x) b) :=
      (congrArg f he).symm.trans (hfInv.2 _ hx (pair F G (infinite F G x) b))
    _ = 0 := congrArg (fun t : ∀ b : B, W b.val => (t ⟨b, hb⟩).val (infinite F G x)) hf

end Langlands.Automorphic.GroupSchemeFunctions
