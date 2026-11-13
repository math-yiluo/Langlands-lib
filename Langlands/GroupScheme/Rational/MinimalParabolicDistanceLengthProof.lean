import Langlands.GroupScheme.Rational.MinimalParabolicDistanceLengthStatement
import Langlands.GroupScheme.Rational.StandardParabolicClassificationProof
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Rational.RelativeTitsSystemProof
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.DominantChamberMove
import Langlands.Group.TitsSystemBruhat

/-! # Proof: the distance of two minimal semi-standard parabolics is a Weyl length

Renard VII.3.5, opening paragraph, for a minimal Levi subgroup, in corrected form.
`minimalParabolicDistanceLength` proves `MinimalParabolicDistanceLengthStatement`.

* Existence (`exists_map_conj_eq`): the published dominant chamber move gives a normalizing
  point `n` with `n P(ν)(k) n⁻¹ = P(ξ)(k)` that carries the root signs of `ν` to those of `ξ`.
* Uniqueness (`mk_eq_of_map_conj_eq`): `P(ξ)(k)` contains the Borel subgroup of the relative
  Tits system of `ξ`, so it is self-normalizing, and it meets `N(k)` in `Z(k)`.
* Hence every point moving `P(ν)(k)` to `P(ξ)(k)` carries the signs (`pos_iff_of_map_conj_eq`),
  and the distance is the size of an inversion set
  (`ncard_eq_relativeInversionSet_of_map_conj_eq`), which the Coxeter realization identifies
  with a length.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily

namespace MinimalParabolicDistanceLength

/-- Membership in the image of a subgroup under conjugation by `g`. -/
theorem mem_map_conj {X : Type*} [Group X] {H : Subgroup X} {g x : X} :
    x ∈ H.map (MulAut.conj g : X →* X) ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

/-- Two nonzero integers with the same positivity have the same negativity. -/
theorem neg_iff_of_pos_iff {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (h : 0 < x ↔ 0 < y) :
    x < 0 ↔ y < 0 := by
  constructor
  · intro hx0
    rcases lt_or_gt_of_ne hy with h2 | h2
    · exact h2
    · exact absurd (h.mpr h2) (not_lt.mpr hx0.le)
  · intro hy0
    rcases lt_or_gt_of_ne hx with h1 | h1
    · exact h1
    · exact absurd (h.mp h1) (not_lt.mpr hy0.le)

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

section Basic

variable (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- The rational points `P(ξ)(k)` of the dynamic parabolic of a cocharacter of the torus. -/
abbrev parabolicPoints (ξ : cocharacterLattice T) :
    Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :=
  (Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i)).carrier (Over.mk (𝟙 _))

/-- Conjugating `P(ξ)(k)` by a normalizing point `n` gives `P(n · ξ)(k)`. -/
theorem parabolicPoints_map_conj (n : normalizerPoints i) (ξ : cocharacterLattice T) :
    (parabolicPoints i ξ).map
        (MulAut.conj (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
          (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) →*
            (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) =
      parabolicPoints i (cocharacterAut (normalizingAut i n) ξ) := by
  have h := congrArg SubgroupFunctor.rationalPoints
    (dynamicParabolic_comap_normalizerPoint i n⁻¹ ξ)
  rw [SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map] at h
  simp only [Subgroup.coe_inv, inv_inv] at h
  exact h

/-- Inverse normalizing points act inversely on characters. -/
theorem weylAction_inv_apply (c : normalizerPoints i) (x : characterLattice T) :
    weylAction i c⁻¹ (weylAction i c x) = x := by
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

variable [IsAffineHom G.X.hom]

/-- The Weyl action of a normalizing point preserves indivisibility of roots. -/
theorem weylAction_mem_indivisibleRoots_iff (c : normalizerPoints i)
    (α : characterLattice T) :
    weylAction i c α ∈ RelativeRoot.indivisibleRoots i ↔
      α ∈ RelativeRoot.indivisibleRoots i := by
  constructor
  · rintro ⟨hr, hd⟩
    refine ⟨(weylAction_mem_roots_iff c α).1 hr, fun β hβ m hm hmβ => ?_⟩
    exact hd (weylAction i c β) (weylAction_mapsTo_relativeRoots i c hβ) m hm
      (by rw [← map_nsmul, hmβ])
  · rintro ⟨hr, hd⟩
    refine ⟨weylAction_mapsTo_relativeRoots i c hr, fun β hβ m hm hmβ => ?_⟩
    exact hd (weylAction i c⁻¹ β) (weylAction_mapsTo_relativeRoots i c⁻¹ hβ) m hm
      (by rw [← map_nsmul, hmβ, weylAction_inv_apply])

omit [Mono i.hom.hom.left] in
/-- A reduced positive root is an indivisible root pairing positively with `ν`. -/
theorem mem_reducedPositiveRelativeRoots_iff (ν : cocharacterLattice T)
    (x : characterLattice T) :
    x ∈ reducedPositiveRelativeRoots i ν ↔
      x ∈ RelativeRoot.indivisibleRoots i ∧ 0 < latticePairing T x ν := by
  constructor
  · rintro ⟨⟨hr, hp⟩, hd⟩
    exact ⟨⟨hr, fun b hb m hm => hd m hm b hb⟩, hp⟩
  · rintro ⟨⟨hr, hd⟩, hp⟩
    exact ⟨⟨hr, hp⟩, fun m hm b hb => hd b hb m hm⟩

omit [Mono i.hom.hom.left] in
/-- With root negation, `-x` is positive for `ν` exactly when the root `x` is negative. -/
theorem neg_mem_positiveRelativeRoots_iff
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i) (ν : cocharacterLattice T)
    {x : characterLattice T} (hx : x ∈ relativeRoots i) :
    -x ∈ positiveRelativeRoots i ν ↔ latticePairing T x ν < 0 := by
  simp only [positiveRelativeRoots, Set.mem_ofPred_eq, map_neg, LinearMap.neg_apply,
    Left.neg_pos_iff]
  exact ⟨fun h => h.2, fun h => ⟨hneg x hx, h⟩⟩

/-- **Counting by an inversion set.** For normalizing points `a`, `b`, the indivisible roots
`α` with `⟨a⁻¹ α, ν⟩ > 0 > ⟨b⁻¹ α, ν⟩` are the image under `a` of the inversion set of
`b⁻¹ a` for `ν`; in particular they have the same number. -/
theorem ncard_eq_relativeInversionSet
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i) (ν : cocharacterLattice T)
    (a b : normalizerPoints i) :
    {α | α ∈ RelativeRoot.indivisibleRoots i ∧
        0 < latticePairing T (weylAction i a⁻¹ α) ν ∧
          latticePairing T (weylAction i b⁻¹ α) ν < 0}.ncard =
      (relativeInversionSet i ν (QuotientGroup.mk (b⁻¹ * a))).ncard := by
  have hcomp : ∀ α, weylAction i (b⁻¹ * a) (weylAction i a⁻¹ α) = weylAction i b⁻¹ α := by
    intro α
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel, mul_one]
  have hpre : {α | α ∈ RelativeRoot.indivisibleRoots i ∧
        0 < latticePairing T (weylAction i a⁻¹ α) ν ∧
          latticePairing T (weylAction i b⁻¹ α) ν < 0} =
      (weylAction i a⁻¹) ⁻¹' relativeInversionSet i ν (QuotientGroup.mk (b⁻¹ * a)) := by
    ext α
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, relativeInversionSet,
      schemeWeylCharacterAction_mk, hcomp, mem_reducedPositiveRelativeRoots_iff,
      weylAction_mem_indivisibleRoots_iff]
    constructor
    · rintro ⟨hα, hpos, hneg'⟩
      refine ⟨⟨hα, hpos⟩, ?_⟩
      exact (neg_mem_positiveRelativeRoots_iff i hneg ν
        (weylAction_mapsTo_relativeRoots i b⁻¹ hα.1)).2 hneg'
    · rintro ⟨⟨hα, hpos⟩, hneg'⟩
      exact ⟨hα, hpos, (neg_mem_positiveRelativeRoots_iff i hneg ν
        (weylAction_mapsTo_relativeRoots i b⁻¹ hα.1)).1 hneg'⟩
  rw [hpre, Set.ncard_preimage_of_injective_subset_range (weylAction i a⁻¹).injective
    (fun x _ => (weylAction i a⁻¹).surjective x)]

/-- **Uniqueness.** Two normalizing points moving `P(ξ)(k)` to the same subgroup have the same
Weyl class: `n₂⁻¹ n₁` normalizes `P(ξ)(k)`, which contains the Borel subgroup of the relative
Tits system of `ξ` and is therefore self-normalizing, and `P(ξ)(k) ∩ N(k) = Z(k)`. -/
theorem mk_eq_of_map_conj_eq (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {ξ : cocharacterLattice T} (hξ : IsGenericCocharacter i ξ) {n₁ n₂ : normalizerPoints i}
    (h : (parabolicPoints i ξ).map
        (MulAut.conj (n₁ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
          (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) →*
            (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) =
      (parabolicPoints i ξ).map
        (MulAut.conj (n₂ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
          (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) →*
            (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))) :
    (QuotientGroup.mk n₁ : relativeWeylGroup i) = QuotientGroup.mk n₂ := by
  have hT : HasRelativeTitsSystem i ξ := relativeTitsSystem k G hG T i hi ξ hξ
  have hB : standardParabolicPoints i ξ ∅ = parabolicPoints i ξ := by
    have he := (standardParabolicEndpoints k G hG T i hi ξ hξ).1
    simp only [standardParabolicPoints, parabolicPoints]
    rw [he]
  have hmN : ((n₂⁻¹ * n₁ : normalizerPoints i) : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈
      Subgroup.normalizer (parabolicPoints i ξ : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hx := SetLike.ext_iff.mp h ((n₁ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) * x *
      (n₁ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹)
    rw [mem_map_conj, mem_map_conj] at hx
    have e1 : (n₁ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹ *
        ((n₁ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) * x *
          (n₁ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹) *
        (n₁ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) = x := by group
    rw [e1] at hx
    rw [hx]
    push_cast
    group
  have hmP : ((n₂⁻¹ * n₁ : normalizerPoints i) : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈
      parabolicPoints i ξ := by
    rw [← hT.isTitsSystem.normalizer_eq_of_le hB.le]
    exact hmN
  have hmZ : ((n₂⁻¹ * n₁ : normalizerPoints i) : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈
      centralizerPoints i := by
    rw [← hT.inf_eq]
    exact ⟨hB ▸ hmP, (n₂⁻¹ * n₁).2⟩
  exact (QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr hmZ)).symm

/-- **Existence by a chamber move.** For generic `ν`, `ξ` some normalizing point `n` moves
`P(ν)(k)` to `P(ξ)(k)`, and `n` transports the root signs: `⟨n⁻¹ α, ν⟩ > 0 ↔ ⟨α, ξ⟩ > 0`. -/
theorem exists_map_conj_eq (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {ν ξ : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (hξ : IsGenericCocharacter i ξ) :
    ∃ n : normalizerPoints i,
      (parabolicPoints i ν).map
          (MulAut.conj (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
            (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) →*
              (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) =
        parabolicPoints i ξ ∧
      ∀ α ∈ relativeRoots i,
        (0 < latticePairing T (weylAction i n⁻¹ α) ν ↔ 0 < latticePairing T α ξ) := by
  have hroot : HasRelativeRootSystem i := relativeRootSystem k G hG T i hi
  have hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i := relativeRootNegation k G hG T i hi
  obtain ⟨m, hm⟩ := hroot.exists_normalizerPoint_dominant i hi.isSplitSubtorus.1 ν ξ
  have hne : ∀ α ∈ relativeRoots i,
      latticePairing T α (cocharacterAut (normalizingAut i m) ξ) ≠ 0 := by
    intro α hα
    rw [latticePairing_cocharacterAut_normalizingAut]
    exact hξ _ (weylAction_mapsTo_relativeRoots i m⁻¹ hα)
  have hsign : ∀ α ∈ relativeRoots i, (0 < latticePairing T α ν ↔
      0 < latticePairing T α (cocharacterAut (normalizingAut i m) ξ)) := by
    intro α hα
    constructor
    · intro h
      exact lt_of_le_of_ne (hm α ⟨hα, h⟩) (hne α hα).symm
    · intro h
      by_contra h'
      have hlt : latticePairing T α ν < 0 := lt_of_le_of_ne (not_lt.mp h') (hν α hα)
      have h2 := hm (-α) ⟨hneg α hα, by simpa using hlt⟩
      simp only [map_neg, LinearMap.neg_apply, Left.nonneg_neg_iff] at h2
      omega
  have hP : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) =
      Dynamic.parabolic
        (CommGroupScheme.groupHom (cocharacterAut (normalizingAut i m) ξ) ≫ i) := by
    apply le_antisymm
    · rw [(relativeRootSignInclusions k G hG T i hi _ _).1]
      intro α hα h0
      exact ((hsign α hα).1 (lt_of_le_of_ne h0 (hν α hα).symm)).le
    · rw [(relativeRootSignInclusions k G hG T i hi _ _).1]
      intro α hα h0
      exact ((hsign α hα).2 (lt_of_le_of_ne h0 (hne α hα).symm)).le
  have hmap : (parabolicPoints i ξ).map
      (MulAut.conj (m : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
        (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) →*
          (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) = parabolicPoints i ν := by
    rw [parabolicPoints_map_conj]
    simp only [parabolicPoints, hP]
  refine ⟨m⁻¹, ?_, ?_⟩
  · rw [← hmap]
    ext x
    rw [mem_map_conj, mem_map_conj]
    push_cast
    constructor
    · intro hx
      convert hx using 1
      group
    · intro hx
      convert hx using 1
      group
  · intro α hα
    rw [inv_inv, hsign (weylAction i m α) (weylAction_mapsTo_relativeRoots i m hα),
      latticePairing_cocharacterAut_normalizingAut, weylAction_inv_apply]

/-- **Sign transfer.** Every normalizing point moving `P(ν)(k)` to `P(ξ)(k)` transports the root
signs of `ν` to those of `ξ`: it has the Weyl class of the chamber move. -/
theorem pos_iff_of_map_conj_eq (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {ν ξ : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (hξ : IsGenericCocharacter i ξ) {n : normalizerPoints i}
    (h : (parabolicPoints i ν).map
          (MulAut.conj (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
            (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) →*
              (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) =
        parabolicPoints i ξ) :
    ∀ α ∈ relativeRoots i,
      (0 < latticePairing T (weylAction i n⁻¹ α) ν ↔ 0 < latticePairing T α ξ) := by
  obtain ⟨n₀, h₀, hs⟩ := exists_map_conj_eq i hG hi hν hξ
  have hmk : (QuotientGroup.mk n : relativeWeylGroup i) = QuotientGroup.mk n₀ :=
    mk_eq_of_map_conj_eq i hG hi hν (h.trans h₀.symm)
  have hinv : weylAction i n⁻¹ = weylAction i n₀⁻¹ := by
    rw [← schemeWeylCharacterAction_mk, ← schemeWeylCharacterAction_mk, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hmk]
  intro α hα
  rw [hinv]
  exact hs α hα

/-- **The distance as an inversion count.** If `a` moves `P(ν)(k)` to `P(ξ)(k)` and `b` moves
`P(ν)(k)` to `P(ξ')(k)`, the reduced roots in both `U(ξ)` and `U(-ξ')` are as many as the
inversion set of `b⁻¹ a` for `ν`. -/
theorem ncard_eq_relativeInversionSet_of_map_conj_eq (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) {ν ξ ξ' : cocharacterLattice T}
    (hν : IsGenericCocharacter i ν) (hξ : IsGenericCocharacter i ξ)
    (hξ' : IsGenericCocharacter i ξ') {a b : normalizerPoints i}
    (ha : (parabolicPoints i ν).map
          (MulAut.conj (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
            (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) →*
              (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) =
        parabolicPoints i ξ)
    (hb : (parabolicPoints i ν).map
          (MulAut.conj (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
            (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) →*
              (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) =
        parabolicPoints i ξ') :
    (RelativeRoot.intertwiningRelativeRoots i
          (Dynamic.unipotent (CommGroupScheme.groupHom ξ ≫ i))
          (Dynamic.unipotent (CommGroupScheme.groupHom (-ξ') ≫ i)) ∩
        RelativeRoot.indivisibleRoots i).ncard =
      (relativeInversionSet i ν (QuotientGroup.mk (b⁻¹ * a))).ncard := by
  have : Smooth G.X.hom := hG.smooth
  have hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i := relativeRootNegation k G hG T i hi
  have hsa := pos_iff_of_map_conj_eq i hG hi hν hξ ha
  have hsb := pos_iff_of_map_conj_eq i hG hi hν hξ' hb
  rw [← ncard_eq_relativeInversionSet i hneg ν a b,
    RelativeRoot.intertwiningRelativeRoots_dynamic i hi.isSplitSubtorus.1 ξ ξ']
  congr 1
  ext α
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hr, h1, h2⟩, hind⟩
    exact ⟨hind, (hsa α hr).2 h1, (neg_iff_of_pos_iff
      (hν _ (weylAction_mapsTo_relativeRoots i b⁻¹ hr)) (hξ' α hr) (hsb α hr)).2 h2⟩
  · rintro ⟨hind, h1, h2⟩
    have hr := hind.1
    exact ⟨⟨hr, (hsa α hr).1 h1, (neg_iff_of_pos_iff
      (hν _ (weylAction_mapsTo_relativeRoots i b⁻¹ hr)) (hξ' α hr) (hsb α hr)).1 h2⟩, hind⟩

end Basic

end MinimalParabolicDistanceLength

open MinimalParabolicDistanceLength in
/-- **Renard VII.3.5, opening paragraph, minimal Levi, corrected form.** For generic `ξ`, `ξ'`
exactly one Weyl element moves `P_ξ` to `P_ξ'`; `d(P_ξ, P_ξ')` is its length for the simple
roots of `ξ`; and `d(P_ξ, P_ξ') = ℓ(u⁻¹ v)` when `u`, `v` move a standard `P_ν` to `P_ξ`,
`P_ξ'`. -/
theorem minimalParabolicDistanceLength : MinimalParabolicDistanceLengthStatement.{u} := by
  intro k _ G hG T i hi pp d Moves ξ ξ' hξ hξ'
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  have key : ∀ ν : cocharacterLattice T, IsGenericCocharacter i ν →
      ∀ u v : relativeWeylGroup i, Moves u ν ξ → Moves v ν ξ' →
      ∀ (C : CoxeterMatrix (SimpleRoot i ν)) (cs : CoxeterSystem C (relativeWeylGroup i)),
        IsRelativeWeylCoxeterRealization i ν cs → d ξ ξ' = cs.length (u⁻¹ * v) := by
    rintro ν hν u v ⟨a, rfl, ha⟩ ⟨b, rfl, hb⟩ C cs hcs
    have hw : (QuotientGroup.mk (b⁻¹ * a) : relativeWeylGroup i) =
        ((QuotientGroup.mk a : relativeWeylGroup i)⁻¹ * QuotientGroup.mk b)⁻¹ := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_rev, inv_inv]
    change (RelativeRoot.intertwiningRelativeRoots i
          (Dynamic.unipotent (CommGroupScheme.groupHom ξ ≫ i))
          (Dynamic.unipotent (CommGroupScheme.groupHom (-ξ') ≫ i)) ∩
        RelativeRoot.indivisibleRoots i).ncard = _
    rw [ncard_eq_relativeInversionSet_of_map_conj_eq i hG hi hν hξ hξ' ha hb,
      ← hcs.2.2.2.1, hw, cs.length_inv]
  refine ⟨?_, ?_, key⟩
  · obtain ⟨n, hn, -⟩ := exists_map_conj_eq i hG hi hξ hξ'
    refine ⟨QuotientGroup.mk n, ⟨n, rfl, hn⟩, ?_⟩
    rintro w ⟨m, rfl, hm⟩
    exact mk_eq_of_map_conj_eq i hG hi hξ (hm.trans hn.symm)
  · intro w hw C cs hcs
    have h1 : Moves 1 ξ ξ := by
      refine ⟨1, QuotientGroup.mk_one _, ?_⟩
      ext x
      rw [mem_map_conj]
      simp
    have h := key ξ hξ 1 w h1 hw C cs hcs
    rwa [inv_one, one_mul] at h

end Langlands.GroupScheme
