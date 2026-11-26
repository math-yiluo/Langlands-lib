import Langlands.Global.ArthurTruncationRelativeFiniteness
import Langlands.Global.ArthurTruncationConstantTerm
import Langlands.Global.ArthurTruncationCuspidal

/-! # Cancellation of Arthur's partial truncation operators -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Finset
open scoped CategoryTheory.MonObj Classical

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open AdelicGroupPoints ArthurParabolicSpaces

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅)) (Tp : V T)

local notation "Roots" => characterLattice T
local notation "Δ" => simpleRelativeRoots i ν
local notation "Points" => AdelicGroupPoints F G
local notation "Rat" => rationalSubgroup F G
local notation "Pᵣ[" S "]" => parabolicRationalSubgroup F (Standard.parabolicHom i ν (S : Set Roots))
local notation "C[" Q "," P "]" => NestedCosets (Pᵣ[Q]) (Pᵣ[P])
local notation "H₀" => height hi hK hρ
local notation "CT[" S "]" => constantTerm F i ν (S : Set Roots)
local notation "τ[" Q "," P "]" => ArthurRelative.tau hG hi ν D (Q : Set Roots) (P : Set Roots)
local notation "τ̂[" Q "," P "]" => ArthurRelative.tauHat hG hi ν D (Q : Set Roots) (P : Set Roots)
local notation "Λ[" R "]" => relativeTruncation hG hi D hK hρ R Tp

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
include hG hi in
private theorem roots_subset {S : Finset Roots} (hS : S ⊆ simpleFinset ν hG hi) :
    (S : Set Roots) ⊆ Δ := fun _ h => (mem_simpleFinset hG hi).mp (hS h)

private def hattedSummand (Q R : Finset Roots) (φ : Points → ℂ) (x : Points) (a : Rat) : ℂ :=
  CT[Q] φ ((a : Points) * x) * (τ̂[Q,R] (H₀ ((a : Points) * x) - Tp) : ℂ)

omit [Mono i.hom.hom.left] in
include hG hi hν in
private theorem constantTerm_mul_parabolicRational {J : Set Roots} (hJ : J ⊆ Δ)
    {φ : Points → ℂ} (hφ : ∀ a ∈ Pᵣ[J], ∀ x, φ ((a : Points) * x) = φ x)
    (a : Rat) (ha : a ∈ Pᵣ[J]) (x : Points) :
    CT[J] φ ((a : Points) * x) = CT[J] φ x := by
  let p := Standard.parabolicHom i ν J
  have hφ' (b : Points) (hb : b ∈ rationalImage F p) (z : Points) : φ (b * z) = φ z := by
    let c : Rat := ⟨b, rationalImage_le_rationalSubgroup p hb⟩
    exact hφ c ((mem_parabolicRationalSubgroup_iff c).mpr hb) z
  exact constantTerm_rationalParabolic_mul hG hi hν hJ hφ' a
    ((mem_parabolicRationalSubgroup_iff a).mp ha) x

include hν in
private theorem hattedSummand_invariant {Q R : Finset Roots} (hQR : Q ⊆ R) (hR : (R : Set Roots) ⊆ Δ)
    {φ : Points → ℂ} (hφ : ∀ a ∈ Pᵣ[Q], ∀ x, φ ((a : Points) * x) = φ x) (x : Points) :
    ∀ a ∈ Pᵣ[Q], ∀ b : Rat,
      hattedSummand hG hi D hK hρ Tp Q R φ x (a * b) = hattedSummand hG hi D hK hρ Tp Q R φ x b := by
  intro a ha b
  have hQR' : (Q : Set Roots) ⊆ R := fun _ h => hQR h
  simp only [hattedSummand, Subgroup.coe_mul, mul_assoc,
    constantTerm_mul_parabolicRational hG hi hν (hQR'.trans hR) hφ a ha,
    tauHat_rationalParabolic_mul hG hi hν D hK hρ hQR' hR Tp a ha]

include hν in
/-- Partial truncation preserves left invariance under the rational upper parabolic. -/
theorem relativeTruncation_rationalParabolic_mul {R : Finset Roots}
    (hR : (R : Set Roots) ⊆ Δ) {φ : Points → ℂ}
    (hφ : ∀ a ∈ Pᵣ[R], ∀ x, φ ((a : Points) * x) = φ x)
    (a : Pᵣ[R]) (x : Points) : Λ[R] φ ((a : Points) * x) = Λ[R] φ x := by
  unfold relativeTruncation
  refine sum_congr rfl fun Q hQ => ?_
  have hQR := mem_powerset.mp hQ
  have hQR' : (Q : Set Roots) ⊆ R := fun _ h => hQR h
  have hmono := parabolicRationalSubgroup_mono hG hi hν hQR' hR
  have hφ' : ∀ b ∈ Pᵣ[Q], ∀ z, φ ((b : Points) * z) = φ z :=
    fun b hb => hφ b (hmono hb)
  have h := tsum_nestedCosets_mul_right (Pᵣ[Q]) (Pᵣ[R]) a
    (hattedSummand hG hi D hK hρ Tp Q R φ x)
    (hattedSummand_invariant hG hi hν D hK hρ Tp hQR hR hφ' x)
  congr 1
  simpa only [hattedSummand, Subgroup.coe_mul, mul_assoc] using h

private theorem tsum_sum_mul_right_of_finiteSupport {I B : Type*} (s : Finset I)
    (a : I → B → ℂ) (b : B → ℂ) (hb : b.support.Finite) :
    (∑' j, (∑ i ∈ s, a i j) * b j) = ∑ i ∈ s, ∑' j, a i j * b j := by
  have hs (i : I) : Summable (fun j => a i j * b j) :=
    summable_of_hasFiniteSupport (hb.subset fun _ h => right_ne_zero_of_mul h)
  calc
    _ = ∑' j, ∑ i ∈ s, a i j * b j := tsum_congr fun j => sum_mul s (fun i => a i j) (b j)
    _ = _ := Summable.tsum_finsetSum (fun i _ => hs i)

set_option maxHeartbeats 1100000 in
include hν in
private theorem relativeCancellation {P : Finset Roots} (hP : P ⊆ simpleFinset ν hG hi)
    {φ : Points → ℂ} (hφ : ∀ a ∈ Pᵣ[P], ∀ x, φ ((a : Points) * x) = φ x) (x : Points) :
    (∀ R ∈ P.powerset, (Function.support fun c : C[R,P] =>
      Λ[R] φ ((c.out : Points) * x) * (τ[R,P] (H₀ ((c.out : Points) * x) - Tp) : ℂ)).Finite) ∧
    (∑ R ∈ P.powerset, ∑' c : C[R,P],
      Λ[R] φ ((c.out : Points) * x) * (τ[R,P] (H₀ ((c.out : Points) * x) - Tp) : ℂ)) = CT[P] φ x := by
  let f (Q R : Finset Roots) := hattedSummand hG hi D hK hρ Tp Q R φ x
  let g (R : Finset Roots) (a : Rat) : ℂ := (τ[R,P] (H₀ ((a : Points) * x) - Tp) : ℂ)
  have hPs : (P : Set Roots) ⊆ Δ := roots_subset hG hi hP
  have hmono {Q R : Finset Roots} (hQR : Q ⊆ R) (hRP : R ⊆ P) : Pᵣ[Q] ≤ Pᵣ[R] :=
    parabolicRationalSubgroup_mono hG hi hν (fun _ h => hQR h) (fun _ h => hPs (hRP h))
  have hcut {R : Finset Roots} (hRP : R ⊆ P) :
      (Function.support fun c : C[R,P] => g R c.out).Finite := by
    apply (relative_tau_finite hG hi hν D hK hρ hRP hP Tp x).subset
    intro c hc hzero
    change τ[R,P] (H₀ ((c.out : Points) * x) - Tp) = 0 at hzero
    change g R c.out ≠ 0 at hc
    apply hc
    simp only [g, hzero, Int.cast_zero]
  refine ⟨fun R hR => (hcut (mem_powerset.mp hR)).subset fun c hc => right_ne_zero_of_mul hc, ?_⟩
  have hregroup {Q R : Finset Roots} (hQR : Q ⊆ R) (hRP : R ⊆ P) :
      (Function.support fun c : C[Q,P] => f Q R c.out * g R c.out).Finite ∧
      (∑' c : C[R,P], (∑' d : C[Q,R], f Q R ((d.out : Rat) * (c.out : Rat))) * g R c.out) =
        ∑' c : C[Q,P], f Q R c.out * g R c.out := by
    have hf : ∀ a ∈ Pᵣ[Q], ∀ z, φ ((a : Points) * z) = φ z :=
      fun a ha => hφ a (hmono (hQR.trans hRP) le_rfl ha)
    have hf' := hattedSummand_invariant hG hi hν D hK hρ Tp hQR (fun _ h => hPs (hRP h)) hf x
    have hg' : ∀ a ∈ Pᵣ[R], ∀ b : Rat, g R (a * b) = g R b := by
      intro a ha b
      simp only [g, Subgroup.coe_mul, mul_assoc,
        tau_rationalParabolic_mul hG hi hν D hK hρ (fun _ h => hPs (hRP h)) hPs Tp a ha]
    apply tsum_nestedCosets (Pᵣ[Q]) (Pᵣ[R]) (Pᵣ[P]) (hmono hQR hRP) (hmono hRP le_rfl)
      (f Q R) (g R) hf' hg' (hcut hRP)
    intro c
    apply (relative_tauHat_finite hG hi hν D hK hρ hQR (hRP.trans hP) Tp ((c.out : Points) * x)).subset
    intro d hd hzero
    apply hd
    simp only [f, hattedSummand, Subgroup.coe_mul, mul_assoc, hzero, Int.cast_zero, mul_zero]
  let term (Q R : Finset Roots) : ℂ :=
    (-1 : ℂ) ^ (R.card - Q.card) * ∑' c : C[Q,P], f Q R c.out * g R c.out
  have hexpand (R : Finset Roots) (hR : R ∈ P.powerset) :
      (∑' c : C[R,P], Λ[R] φ ((c.out : Points) * x) * g R c.out) = ∑ Q ∈ R.powerset, term Q R := by
    have hRP := mem_powerset.mp hR
    let a (Q : Finset Roots) (c : C[R,P]) :=
      (-1 : ℂ) ^ (R.card - Q.card) * ∑' d : C[Q,R], f Q R ((d.out : Rat) * (c.out : Rat))
    calc
      _ = ∑' c : C[R,P], (∑ Q ∈ R.powerset, a Q c) * g R c.out := by
        simp only [relativeTruncation, a, f, hattedSummand, Subgroup.coe_mul, mul_assoc]
      _ = ∑ Q ∈ R.powerset, ∑' c : C[R,P], a Q c * g R c.out :=
        tsum_sum_mul_right_of_finiteSupport R.powerset a _ (hcut hRP)
      _ = _ := by
        refine sum_congr rfl fun Q hQ => ?_
        simp only [a, mul_assoc, tsum_mul_left, term, (hregroup (mem_powerset.mp hQ) hRP).2]
  have hswap : (∑ R ∈ P.powerset, ∑ Q ∈ R.powerset, term Q R) =
      ∑ Q ∈ P.powerset, ∑ R ∈ P.powerset.filter (Q ⊆ ·), term Q R := by
    apply sum_comm' (f := fun R Q => term Q R)
    intro R Q
    simp only [mem_filter, mem_powerset]
    exact ⟨fun ⟨hRP, hQR⟩ => ⟨⟨hRP, hQR⟩, hQR.trans hRP⟩, fun ⟨h, _⟩ => h⟩
  have hcancel (Q : Finset Roots) (hQ : Q ∈ P.powerset) :
      (∑ R ∈ P.powerset.filter (Q ⊆ ·), term Q R) =
        ∑' c : C[Q,P], CT[Q] φ ((c.out : Points) * x) * (if Q = P then 1 else 0) := by
    let w (R : Finset Roots) (c : C[Q,P]) := (-1 : ℂ) ^ (R.card - Q.card) * (f Q R c.out * g R c.out)
    have hs (R : Finset Roots) (hR : R ∈ P.powerset.filter (Q ⊆ ·)) : Summable (w R) := by
      obtain ⟨hRP, hQR⟩ := mem_filter.mp hR
      exact (summable_of_hasFiniteSupport (hregroup hQR (mem_powerset.mp hRP)).1).mul_left _
    calc
      _ = ∑ R ∈ P.powerset.filter (Q ⊆ ·), ∑' c, w R c := by
        exact sum_congr rfl fun _ _ => tsum_mul_left.symm
      _ = ∑' c, ∑ R ∈ P.powerset.filter (Q ⊆ ·), w R c :=
        (Summable.tsum_finsetSum hs).symm
      _ = _ := by
        refine tsum_congr fun c => ?_
        let y := H₀ ((c.out : Points) * x) - Tp
        have he := ArthurRelative.sum_tauHat_mul_tau hG hi hν D (mem_powerset.mp hQ) hPs y
        rw [← he, mul_sum]
        refine sum_congr rfl fun R _ => ?_
        change (-1 : ℂ) ^ (R.card - Q.card) *
          ((CT[Q] φ ((c.out : Points) * x) * (τ̂[Q,R] y : ℂ)) * (τ[R,P] y : ℂ)) = _
        ring
  change (∑ R ∈ P.powerset, ∑' c : C[R,P], Λ[R] φ ((c.out : Points) * x) * g R c.out) = _
  rw [sum_congr rfl hexpand, hswap, sum_eq_single P]
  · rw [hcancel P (mem_powerset_self P)]
    simp only [ite_true, mul_one]
    let c₀ : C[P,P] := LeftCosetSpace.mk _ 1
    rw [tsum_eq_single c₀]
    · exact constantTerm_mul_parabolicRational hG hi hν hPs hφ _ c₀.out.2 x
    · intro c hne
      exfalso
      apply hne
      refine (Quotient.out_eq c).symm.trans ?_
      apply (LeftCosetSpace.mk_eq_mk_iff (Pᵣ[P].subgroupOf Pᵣ[P]) c.out 1).mpr
      exact (1 * c.out⁻¹ : Pᵣ[P]).2
  · intro Q hQ hne
    rw [hcancel Q hQ]
    simp [hne]
  · simp

set_option maxHeartbeats 1200000 in
include hν in
private theorem fullCancellation (φ : Points → ℂ) (hφ : IsLocallyBoundedInvariant Rat φ) (x : Points) :
    (∀ R ∈ (simpleFinset ν hG hi).powerset,
      (Function.support fun c : LeftCosetSpace (Pᵣ[R]) =>
        Λ[R] φ ((c.out : Points) * x) * (τ[R,Δ] (H₀ ((c.out : Points) * x) - Tp) : ℂ)).Finite) ∧
    (∑ R ∈ (simpleFinset ν hG hi).powerset, ∑' c : LeftCosetSpace (Pᵣ[R]),
      Λ[R] φ ((c.out : Points) * x) * (τ[R,Δ] (H₀ ((c.out : Points) * x) - Tp) : ℂ)) = φ x := by
  let P := simpleFinset ν hG hi
  have hΔ : (P : Set Roots) = Δ := Set.ext fun _ => mem_simpleFinset hG hi
  have htop : Pᵣ[P] = ⊤ := by
    rw [hΔ]
    exact parabolicRationalSubgroup_full_eq_top hG hi hν
  have hφP : ∀ a ∈ Pᵣ[P], ∀ x, φ ((a : Points) * x) = φ x :=
    fun a _ => hφ.2.2 a a.2
  have hrel := relativeCancellation hG hi hν D hK hρ Tp (P := P) le_rfl hφP x
  rw [← hΔ]
  let f (R : Finset Roots) (a : Rat) :=
    Λ[R] φ ((a : Points) * x) * (τ[R,P] (H₀ ((a : Points) * x) - Tp) : ℂ)
  have hcompare (R : Finset Roots) (hR : R ∈ P.powerset) :
      (Function.support fun c : LeftCosetSpace (Pᵣ[R]) => f R c.out).Finite ∧
      (∑' c : LeftCosetSpace (Pᵣ[R]), f R c.out) = ∑' c : C[R,P], f R c.out := by
    have hRs := roots_subset hG hi (mem_powerset.mp hR)
    have hPs := roots_subset hG hi (S := P) le_rfl
    have hφR : ∀ a ∈ Pᵣ[R], ∀ z, φ ((a : Points) * z) = φ z :=
      fun a _ => hφ.2.2 a a.2
    have hfinv : ∀ a ∈ Pᵣ[R], ∀ b : Rat, f R (a * b) = f R b := by
      intro a ha b
      simp only [f, Subgroup.coe_mul, mul_assoc,
        relativeTruncation_rationalParabolic_mul hG hi hν D hK hρ Tp hRs hφR ⟨a, ha⟩,
        tau_rationalParabolic_mul hG hi hν D hK hρ hRs hPs Tp a ha]
    let E := nestedCosetsEquivOfTop (Pᵣ[R]) (Pᵣ[P]) htop
    have he (c : C[R,P]) : f R (E c).out = f R c.out :=
      nestedCosetsEmbedding_out (Pᵣ[R]) (Pᵣ[P]) hfinv c
    refine ⟨?_, (E.tsum_eq (fun c => f R c.out)).symm.trans (tsum_congr he)⟩
    apply ((hrel.1 R hR).image E).subset
    intro c hc
    refine ⟨E.symm c, ?_, E.apply_symm_apply c⟩
    change f R ((E.symm c).out : Rat) ≠ 0
    rw [← he, E.apply_symm_apply]
    exact hc
  change (∀ R ∈ P.powerset, (Function.support fun c : LeftCosetSpace (Pᵣ[R]) => f R c.out).Finite) ∧
    (∑ R ∈ P.powerset, ∑' c : LeftCosetSpace (Pᵣ[R]), f R c.out) = φ x
  refine ⟨fun R hR => (hcompare R hR).1, ?_⟩
  rw [sum_congr rfl fun R hR => (hcompare R hR).2]
  exact hrel.2.trans (by rw [hΔ, constantTerm_full_eq])

/-- Arthur 2005, Proposition 13.3 and (13.10), at every truncation parameter. -/
theorem truncationCancellation : TruncationCancellationStatement.{u} := by
  intro F _ _ G _ _ T i _ ν hG hi hν D K hK hρ Tp
  refine ⟨fullCancellation hG hi hν D hK hρ Tp, ?_⟩
  intro P hP φ hφ x
  have hPs := roots_subset hG hi (mem_powerset.mp hP)
  have hφP : ∀ a ∈ parabolicRationalSubgroup F (Standard.parabolicHom i ν (P : Set (characterLattice T))),
      ∀ z, φ ((a : AdelicGroupPoints F G) * z) = φ z := by
    intro a ha z
    exact hφ.2.2 _ ⟨a, ha, rfl⟩ z
  exact ⟨hasConstantTerm_of_locallyBoundedInvariant hG hi hν hPs hφ x,
    relativeCancellation hG hi hν D hK hρ Tp (mem_powerset.mp hP) hφP x⟩

end Langlands.Global.ArthurTruncation
