import Langlands.Global.AdelicPoleTransfer
import Langlands.Analysis.Meromorphic.CoordinateRootClearing
import Langlands.Automorphic.GroupSchemeInvariantFormsSubmodule

/-! # Root clearing of local uniform-growth meromorphic presentations -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry Filter Metric Set
open scoped CategoryTheory.MonObj Manifold Topology

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
  Langlands.Analysis.Meromorphic

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : IsClosedSubgroup rho)
  (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G))
  (𝓕 : StandardParabolicFamily F G) (K : Subgroup (AdelicGroupPoints F G))

local notation "𝔉" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "value" => UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L
local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "Kinf" => Subgroup.comap (ContinuousMonoidHom.toMonoidHom (ofInfinite F G)) K

variable {X κ : Type*} [AddCommGroup X] [Module ℂ X] {n : ℕ}

/-- On a local uniform-growth presentation the same prescribed product of linear
forms gives holomorphic extensions of every norm-one cuspidal test pairing. -/
def HasLocalCuspidalRootClearing
    (roots : Set κ) (rootForm : κ → X →ₗ[ℂ] ℂ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X) (s₀ : Fin n → ℂ)
    {W : TopologicalSpace.Opens (Fin n → ℂ)} (f : W → 𝔉) (D : Set W) : Prop :=
  ∃ (S : Finset κ) (m : ℕ) (T : Set (Fin n → ℂ)), (S : Set κ) ⊆ roots ∧ IsOpen T ∧ s₀ ∈ T ∧
    ∀ (J : Idx) ψ, 𝓕.IsLeviCuspForm Kinf rho J ψ → ∀ g : AdelicGroupPoints F G,
      ∃ b : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ b T ∧ ∀ t ∈ D, (t : Fin n → ℂ) ∈ T →
        b t = (∏ β ∈ S, rootForm β (e t - e s₀)) ^ m *
          𝓕.leviPairing J (𝓕.constantTerm J (value (f t))) g ψ

/-- Clearing the cuspidal tests of a meromorphic local presentation gives the
same clearing product for all its scalar adelic evaluations. -/
theorem hasLocalRootClearing_of_cuspidal_pairings
    (hinj : LeadingCuspidalInjectivityStatement.{u})
    (hK : IsMaximalCompactSubgroup F G K)
    (hKmin : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K)
    (hKlevi : ∀ J : Idx, IsMaximalCompactSubgroup F (𝓕.M J)
      (K.comap (AdelicGroupPoints.map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).toMonoidHom))
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G)))
    (hweight : ∀ (J : Idx) ψ, 𝓕.IsLeviCuspForm Kinf rho J ψ → ∀ g,
      𝓕.HasLeviPairingMajorant J ψ g rho R)
    (roots : Set κ) (rootForm : κ → X →ₗ[ℂ] ℂ) (EP : X → AdelicGroupPoints F G → ℂ)
    (e : (Fin n → ℂ) ≃ₗ[ℂ] X) (s₀ : Fin n → ℂ)
    {W : TopologicalSpace.Opens (Fin n → ℂ)} (hs₀ : s₀ ∈ W)
    {f : W → 𝔉} {D : Set W} (hf : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f D)
    (hregular : ∀ t ∈ D, value (f t) = EP (e t) ∧
      IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho (value (f t)))
    (hclear : HasLocalCuspidalRootClearing F G rho hsmooth hcalc hN hrho R L 𝓕 K
      roots rootForm e s₀ f D) : HasLocalRootClearing roots rootForm EP e s₀ := by
  classical
  obtain ⟨S, m, T, hS, hTo, hsT, htests⟩ := hclear
  let p (s : Fin n → ℂ) := (∏ β ∈ S, rootForm β (e s - e s₀)) ^ m
  have hp : Differentiable ℂ p := differentiable_centeredLinearProduct rootForm e s₀ S m
  obtain ⟨U', hU'o, hU'c, hsU', den, num, hden, hdenne, hnum, heq⟩ := hf.2.2.2 ⟨s₀, hs₀⟩
  let U := Subtype.val '' U'
  let D₀ := Subtype.val '' D
  have hUo : IsOpen U := W.isOpen.isOpenMap_subtype_val _ hU'o
  have hUc : IsPreconnected U := hU'c.isPreconnected.image _ continuous_subtype_val.continuousOn
  have hsU : s₀ ∈ U := ⟨⟨s₀, hs₀⟩, hsU', rfl⟩
  have hD₀ : IsOpen D₀ := W.isOpen.isOpenMap_subtype_val _ hf.1
  have hWD₀ : (W : Set (Fin n → ℂ)) ⊆ closure D₀ := fun t ht =>
    image_closure_subset_closure_image continuous_subtype_val ⟨⟨t, ht⟩, hf.2.1 _, rfl⟩
  obtain ⟨r, hr, hrUT⟩ := Metric.isOpen_iff.mp (hUo.inter hTo) s₀ ⟨hsU, hsT⟩
  let B := ball s₀ r
  have hBU : B ⊆ U := fun _ ht => (hrUT ht).1
  have hBT : B ⊆ T := fun _ ht => (hrUT ht).2
  have hsB : s₀ ∈ B := mem_ball_self hr
  let d₀ := extendOpens den
  let f₀ (s : Fin n → ℂ) := p s • extendOpens f s
  let a₀ (s : Fin n → ℂ) := p s • extendOpens num s
  have hd₀ : DifferentiableOn ℂ d₀ U := differentiableOn_extendOpens hU'o hden
  have hd₀ne : ∃ s ∈ B, d₀ s ≠ 0 := by
    apply exists_ne_zero_of_differentiableOn hUo hUc hd₀ ?_ isOpen_ball hBU ⟨s₀, hsB⟩
    obtain ⟨t, ht, hdt⟩ := hdenne
    exact ⟨t, ⟨t, ht, rfl⟩, by simpa only [d₀, extendOpens_coe] using hdt⟩
  have hscalar (v : W → 𝔉) (test : 𝔉 →L[ℂ] ℂ) (s : Fin n → ℂ) :
      test (p s • extendOpens v s) = p s * extendOpens (fun t => test (v t)) s := by
    rw [map_smul, smul_eq_mul]
    by_cases hs : s ∈ W <;> simp [extendOpens, hs]
  have han : ∀ test : 𝔉 →L[ℂ] ℂ, DifferentiableOn ℂ (fun s => test (a₀ s)) B := by
    intro test
    refine (hp.differentiableOn.mul ((differentiableOn_extendOpens hU'o (hnum test)).mono hBU)).congr
      (fun s _ => hscalar num test s)
  have hiff : ∀ s ∈ B ∩ D₀, d₀ s • f₀ s = a₀ s := by
    rintro s ⟨hsB', t, ht, rfl⟩
    obtain ⟨t', ht', htt'⟩ := hBU hsB'
    have htU' : t ∈ U' := Subtype.ext htt' ▸ ht'
    simp only [d₀, f₀, a₀, extendOpens_coe]
    rw [smul_comm, heq t ⟨ht, htU'⟩]
  have hreg₀ (s : Fin n → ℂ) (hs : s ∈ B ∩ D₀) :
      IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho (value (a₀ s)) := by
    rw [← hiff s hs]
    obtain ⟨t, ht, rfl⟩ := hs.2
    change IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho
      (d₀ t • (p t • value (extendOpens f t)))
    rw [extendOpens_coe]
    let A := automorphicFunctionsOn (rationalSubgroup F G) Kinf rho hsmooth hcalc
    exact A.smul_mem _ (A.smul_mem _ (hregular t ht).2)
  have hfd : ∀ test : 𝔉 →L[ℂ] ℂ, DifferentiableOn ℂ (fun s => test (f₀ s)) (B ∩ D₀) := by
    intro test
    refine ((hp.differentiableOn.mono inter_subset_left).mul
      ((differentiableOn_extendOpens hf.1 (hf.2.2.1 test)).mono inter_subset_right)).congr
      (fun s _ => hscalar f test s)
  have hpair : ∀ (J : Idx) ψ, 𝓕.IsLeviCuspForm Kinf rho J ψ → ∀ g,
      ∃ b : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ b B ∧
        EqOn b (fun s => 𝓕.leviPairing J (𝓕.constantTerm J (value (f₀ s))) g ψ) (B ∩ D₀) := by
    intro J ψ hψ g
    obtain ⟨b, hb, hbeq⟩ := htests J ψ hψ g
    refine ⟨b, hb.mono hBT, ?_⟩
    rintro s ⟨hsB', t, htD, rfl⟩
    have hval := hbeq t htD (hBT hsB')
    let test := 𝓕.constantTermLeviPairingCLM J ψ hψ.1.1 g rho hN hrho hsmooth hcalc R L
      hψ.1.2.1.1 (hweight J ψ hψ g)
    have hmap := map_smul test (p t) (f t)
    simp only [test, StandardParabolicFamily.constantTermLeviPairingCLM_apply, smul_eq_mul] at hmap
    change b t = 𝓕.leviPairing J (𝓕.constantTerm J (value (p t • extendOpens f t))) g ψ
    rw [extendOpens_coe, hmap]
    exact hval
  obtain ⟨V, hVB, hVo, hsV, hg⟩ :=
    exists_uniform_holomorphic_evaluations_of_cuspidal_pairings F G rho hsmooth hcalc hN hrho R L
      𝓕 K hinj hK hKmin hKlevi hL isOpen_ball (convex_ball s₀ r).isPreconnected hD₀ hsB
      (show HasHolomorphicNumerator F G rho hsmooth hcalc hN hrho R L B D₀ f₀ a₀ d₀ from
        ⟨hd₀.mono hBU, hd₀ne, han, hiff⟩) hfd hreg₀ hweight hpair
  refine ⟨D₀, V, hVo, hsV, ?_, S, m, hS, fun g => ?_⟩
  · intro s hs
    obtain ⟨t, -, rfl⟩ := hBU (hVB hs)
    exact hWD₀ t.property
  · obtain ⟨b, hb, hbeq⟩ := hg g
    refine ⟨b, hb, ?_⟩
    rintro s ⟨hsV', t, ht, rfl⟩
    have hval := hbeq ⟨hsV', ⟨t, ht, rfl⟩⟩
    change b t = p t * EP (e t) g
    change b t = p t * value (extendOpens f t) g at hval
    simpa only [extendOpens_coe, (hregular t ht).1] using hval

end Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace
