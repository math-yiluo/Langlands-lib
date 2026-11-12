import Langlands.Geometry.Building.QuasiSplitMultipliablePieces

/-! # Opposite factorization inside a piece over a multipliable relative root -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

/-- A *piece* over the character `a` of `S`: two distinct roots `lp`, `lq` of `P` restricting
to `a` along `f`, and a root `lm` that is their sum. -/
def IsMultipliablePiece {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    (f : S ⟶ T) {J : Type*} (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (a : characterLattice S) (lp lq lm : J) : Prop :=
  f ≫ P.root lp = a ∧ f ≫ P.root lq = a ∧ lp ≠ lq ∧ P.root lm = P.root lp + P.root lq

/-- The roots of a piece in the other order also form a piece. -/
theorem IsMultipliablePiece.swap {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))} {f : S ⟶ T} {J : Type*}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} {a : characterLattice S}
    {lp lq lm : J} (h : IsMultipliablePiece f P a lp lq lm) :
    IsMultipliablePiece f P a lq lp lm :=
  ⟨h.2.1, h.1, Ne.symm h.2.2.1, by rw [h.2.2.2, add_comm]⟩

section Gauss

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (j : T.toGrp ⟶ G) [Mono j.hom.hom.left]

omit [IsAffineHom G.X.hom] in
/-- Conjugation by the inverse of a normalizer point carries `U_{wχ}` back to `U_χ`. -/
theorem inv_conj_mem_rootGroupPoints (n : normalizerPoints j) {χ : characterLattice T}
    {x : rationalPoints G} (hx : x ∈ rootGroupPoints j (weylAction j n χ)) :
    (n : rationalPoints G)⁻¹ * x * (n : rationalPoints G) ∈ rootGroupPoints j χ := by
  have h := conj_mem_rootGroupPoints n⁻¹ hx
  have hinv : weylAction j n⁻¹ (weylAction j n χ) = χ := by
    rw [map_inv]
    exact (weylAction j n).symm_apply_apply χ
  rw [hinv, Subgroup.coe_inv, inv_inv] at h
  exact h

/-- **Rank-one Gauss decomposition.** For `f ∈ U_{-α}` and `X ∈ U_α`, either
`f X = X' τ f'` with `X' ∈ U_α`, `τ` normalizing `j` and `f' ∈ U_{-α}`, or `f X = B ν`
with `B ∈ U_α` and `ν` normalizing `j` with `ν α = -α`. -/
theorem gauss_decomposition (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) {α : characterLattice T}
    (hnα : -α ∈ relativeRoots j)
    {f X : rationalPoints G} (hf : f ∈ rootGroupPoints j (-α)) (hX : X ∈ rootGroupPoints j α) :
    (∃ X' ∈ rootGroupPoints j α, ∃ τ : normalizerPoints j, ∃ f' ∈ rootGroupPoints j (-α),
        f * X = X' * τ * f') ∨
      (∃ B ∈ rootGroupPoints j α, ∃ ν : normalizerPoints j,
        f * X = B * ν ∧ weylAction j ν α = -α) := by
  by_cases hf1 : f = 1
  · left
    exact ⟨X, hX, 1, 1, Subgroup.one_mem _, by simp [hf1]⟩
  obtain ⟨pr, hpr⟩ := hE (-α) hnα f hf hf1
  have hpr1 : pr.1 ∈ rootGroupPoints j α := by
    have h := hpr.1; rw [neg_neg] at h; exact h
  have hpr2 : pr.2 ∈ rootGroupPoints j α := by
    have h := hpr.2.1; rw [neg_neg] at h; exact h
  set μf : normalizerPoints j := ⟨pr.1 * f * pr.2, hpr.2.2⟩ with hμf
  have hflip : weylAction j μf (-α) = - -α := hpr.weylAction_eq_neg j hT hnα.1 hf hf1
  have hflip' : weylAction j μf α = -α := by
    have h : -(weylAction j μf α) = - -α := by rw [← map_neg]; exact hflip
    exact neg_injective h
  set Z := pr.2⁻¹ * X with hZ
  have hZmem : Z ∈ rootGroupPoints j α :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hpr2) hX
  have hfX : f * X = pr.1⁻¹ * (μf : rationalPoints G) * Z := by
    rw [hZ, hμf]; group
  by_cases hZ1 : Z = 1
  · right
    refine ⟨pr.1⁻¹, Subgroup.inv_mem _ hpr1, μf, ?_, hflip'⟩
    rw [hfX, hZ1, mul_one]
  left
  have hW : (μf : rationalPoints G) * Z * (μf : rationalPoints G)⁻¹ ∈ rootGroupPoints j (-α) := by
    have h := conj_mem_rootGroupPoints μf hZmem
    rwa [hflip'] at h
  have hW1 : (μf : rationalPoints G) * Z * (μf : rationalPoints G)⁻¹ ≠ 1 := by
    intro h
    apply hZ1
    have := congrArg (fun y => (μf : rationalPoints G)⁻¹ * y * (μf : rationalPoints G)) h
    simpa [mul_assoc] using this
  obtain ⟨qr, hqr⟩ := hE (-α) hnα _ hW hW1
  have hqr1 : qr.1 ∈ rootGroupPoints j α := by
    have h := hqr.1; rw [neg_neg] at h; exact h
  have hqr2 : qr.2 ∈ rootGroupPoints j α := by
    have h := hqr.2.1; rw [neg_neg] at h; exact h
  set μ' : normalizerPoints j :=
    ⟨qr.1 * ((μf : rationalPoints G) * Z * (μf : rationalPoints G)⁻¹) * qr.2, hqr.2.2⟩ with hμ'
  have hf' : (μf : rationalPoints G)⁻¹ * qr.2⁻¹ * (μf : rationalPoints G) ∈
      rootGroupPoints j (-α) := by
    apply inv_conj_mem_rootGroupPoints j μf
    rw [map_neg, hflip', neg_neg]
    exact Subgroup.inv_mem _ hqr2
  refine ⟨pr.1⁻¹ * qr.1⁻¹, Subgroup.mul_mem _ (Subgroup.inv_mem _ hpr1)
    (Subgroup.inv_mem _ hqr1), μ' * μf, _, hf', ?_⟩
  rw [hfX, Subgroup.coe_mul, hμ']
  group

end Gauss

section Piece

variable {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  (j : T.toGrp ⟶ G) [Mono j.hom.hom.left]
  {J : Type*} [Finite J] {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  (hT : IsSplitTorus T.toGrp) (hjc : IsClosedSubgroup j) (hP : IsRootDatumOf j P)
  (hE : RelativeRoot.HasOppositeFactorPairs j)
  {f : S ⟶ T} {a : characterLattice S}
  (hline : RestrictsToMultipliableLine f P a) {lp lq lm : J}
  (hp : f ≫ P.root lp = a) (hq : f ≫ P.root lq = a) (hpq : lp ≠ lq)
  (hm : P.root lm = P.root lp + P.root lq)

omit [Smooth G.X.hom] in
include hT hjc hP hline hp hq hpq hm in
/-- The opposite-pair product of a nontrivial point of `U_m` acts by the reflection in `m`:
it sends `p` to `-q` and `q` to `-p`. -/
theorem piece_weylAction_m {Xm : rationalPoints G} (hXm : Xm ∈ rootGroupPoints j (P.root lm))
    (hXm1 : Xm ≠ 1) {pr : rationalPoints G × rationalPoints G}
    (hpr : RelativeRoot.IsOppositeFactorPair j (P.root lm) Xm pr) :
    weylAction j (⟨pr.1 * Xm * pr.2, hpr.2.2⟩ : normalizerPoints j) (P.root lp) = -P.root lq ∧
      weylAction j (⟨pr.1 * Xm * pr.2, hpr.2.2⟩ : normalizerPoints j) (P.root lq) =
        -P.root lp := by
  obtain ⟨h11, h22, h21, h12, hm1, hm2, h1m, h2m, hmm⟩ := piece_pairings hline hp hq hpq hm
  constructor
  · rw [weylAction_oppositeFactorPair_eq j hT hjc hP lm hXm hXm1 hpr, h1m, one_smul, hm]
    abel
  · rw [weylAction_oppositeFactorPair_eq j hT hjc hP lm hXm hXm1 hpr, h2m, one_smul, hm]
    abel

include hT hjc hP hE hline hp hq hpq hm in
/-- **Opposite factorization of a piece element.** Let `h = X_q X_m X_p` with `X_m ≠ 1`, let
`(Y, Y')` be the opposite pair of `X_m` with product `μ`, and `d = [Y, X_q] ∈ U_{-p}`. Then
either `h = (Y⁻¹ d e) (μ τ) (f' c Y'⁻¹)` with `e ∈ U_{-q}`, `τ` normalizing `j`,
`f' ∈ U_{-p}` and `c ∈ U_{-q}`; or `h = (Y⁻¹ d e) ν (c Y'⁻¹)` with `e ∈ U_{-q}`,
`c ∈ U_{-q}` and `ν` normalizing `j` with `ν p = q`. -/
theorem piece_factorization {Xq Xm Xp : rationalPoints G}
    (hXq : Xq ∈ rootGroupPoints j (P.root lq)) (hXm : Xm ∈ rootGroupPoints j (P.root lm))
    (hXm1 : Xm ≠ 1) (hXp : Xp ∈ rootGroupPoints j (P.root lp))
    {pr : rationalPoints G × rationalPoints G}
    (hpr : RelativeRoot.IsOppositeFactorPair j (P.root lm) Xm pr) :
    (∃ e ∈ rootGroupPoints j (-P.root lq), ∃ τ : normalizerPoints j,
        ∃ f' ∈ rootGroupPoints j (-P.root lp), ∃ c ∈ rootGroupPoints j (-P.root lq),
        Xq * Xm * Xp = (pr.1⁻¹ * (pr.1 * Xq * pr.1⁻¹ * Xq⁻¹) * e) *
          ((pr.1 * Xm * pr.2) * (τ : rationalPoints G)) * (f' * c * pr.2⁻¹)) ∨
      (∃ e ∈ rootGroupPoints j (-P.root lq), ∃ ν : normalizerPoints j,
        ∃ c ∈ rootGroupPoints j (-P.root lq),
        Xq * Xm * Xp = (pr.1⁻¹ * (pr.1 * Xq * pr.1⁻¹ * Xq⁻¹) * e) * (ν : rationalPoints G) *
          (c * pr.2⁻¹) ∧ weylAction j ν (P.root lp) = P.root lq) := by
  obtain ⟨hwp, hwq⟩ := piece_weylAction_m j hT hjc hP hline hp hq hpq hm hXm hXm1 hpr
  set mu : normalizerPoints j := ⟨pr.1 * Xm * pr.2, hpr.2.2⟩ with hμ
  have hmuv : (mu : rationalPoints G) = pr.1 * Xm * pr.2 := rfl
  have hY' : pr.2⁻¹ ∈ rootGroupPoints j (-P.root lm) := Subgroup.inv_mem _ hpr.2.1
  -- the commutator `c ∈ U_{-q}`
  have hm' : P.root lm = P.root lq + P.root lp := by rw [hm, add_comm]
  set c := Xp⁻¹ * pr.2⁻¹ * Xp * pr.2 with hc
  have hcmem : c ∈ rootGroupPoints j (-P.root lq) := by
    have h := piece_commutator_mem_neg_m_q j hT hE hP hline hq hp (Ne.symm hpq) hm' hY'
      (Subgroup.inv_mem _ hXp)
    have heq : c = (pr.2⁻¹ * Xp⁻¹ * pr.2⁻¹⁻¹ * Xp⁻¹⁻¹)⁻¹ := by rw [hc]; group
    rw [heq]
    exact Subgroup.inv_mem _ h
  -- `f = μ⁻¹ X_q μ ∈ U_{-p}`
  set fq := (mu : rationalPoints G)⁻¹ * Xq * (mu : rationalPoints G) with hfq
  have hfqmem : fq ∈ rootGroupPoints j (-P.root lp) := by
    apply inv_conj_mem_rootGroupPoints j mu
    rw [map_neg, hwp, neg_neg]
    exact hXq
  have hkey : Xq * Xm * Xp = pr.1⁻¹ * (pr.1 * Xq * pr.1⁻¹ * Xq⁻¹) * (mu : rationalPoints G) *
      (fq * Xp) * c * pr.2⁻¹ := by
    rw [hfq, hc, hmuv]; group
  have hnp : -P.root lp ∈ relativeRoots j :=
    neg_mem_relativeRoots_of_isRootDatumOf j hP (root_mem_relativeRoots j hP lp)
  rcases gauss_decomposition j hT hE hnp hfqmem hXp with
    ⟨X', hX', τ, f', hf', hgauss⟩ | ⟨B, hB, ν, hgauss, hν⟩
  · left
    have he : (mu : rationalPoints G) * X' * (mu : rationalPoints G)⁻¹ ∈
        rootGroupPoints j (-P.root lq) := by
      have h := conj_mem_rootGroupPoints mu hX'
      rwa [hwp] at h
    refine ⟨_, he, τ, f', hf', c, hcmem, ?_⟩
    rw [hkey, hgauss, ← hmuv]
    group
  · right
    have he : (mu : rationalPoints G) * B * (mu : rationalPoints G)⁻¹ ∈
        rootGroupPoints j (-P.root lq) := by
      have h := conj_mem_rootGroupPoints mu hB
      rwa [hwp] at h
    refine ⟨_, he, mu * ν, c, hcmem, ?_, ?_⟩
    · rw [hkey, hgauss, Subgroup.coe_mul]
      group
    · rw [map_mul, LinearEquiv.mul_apply, hν, map_neg, hwp, neg_neg]

include hT hjc hP hE hline hp hq hpq hm in
/-- **Exact value of `[Y, X_q] ∈ U_{-p}`.** For `Y ∈ U_{-m}` nontrivial and `Z ∈ U_q`, at any
point of a normalizer-stable apartment class, `x_{-p}([Y, Z]) = x_q(Z) + x_{-m}(Y)`. -/
theorem piece_val_commutator_neg_m {ω : kˣ → ℝ} (D : KPApartmentData j ω)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus j) (x : D.Apartment)
    {Y : rationalPoints G} (hY : Y ∈ rootGroupPoints j (-P.root lm)) (hY1 : Y ≠ 1)
    {Z : rationalPoints G} (hZ : Z ∈ rootGroupPoints j (P.root lq)) :
    x.val (-P.root lp) (Y * Z * Y⁻¹ * Z⁻¹) = x.val (P.root lq) Z + x.val (-P.root lm) Y := by
  obtain ⟨h11, h22, h21, h12, hm1, hm2, h1m, h2m, hmm⟩ := piece_pairings hline hp hq hpq hm
  have hnm : -P.root lm ∈ relativeRoots j :=
    neg_mem_relativeRoots_of_isRootDatumOf j hP (root_mem_relativeRoots j hP lm)
  obtain ⟨pr, hpr⟩ := hE (-P.root lm) hnm Y hY hY1
  obtain ⟨t, ht⟩ : ∃ t : ℝ, x.val (-P.root lm) Y = t := by
    have hne : x.val (-P.root lm) Y ≠ ⊤ := fun htop =>
      hY1 ((x.isValuation.eq_top_iff _ hnm Y hY).mp htop)
    obtain ⟨t, htt⟩ := WithTop.ne_top_iff_exists.mp hne
    exact ⟨t, htt.symm⟩
  have hRC := piece_conj_eq_commutator_neg_m j hT hjc hP hE hline hp hq hpq hm hY hY1 hpr hZ
  have hRF := D.val_eq_val_conj_oppositeFactorPair hG hi
    (α := ⟨-P.root lm, hnm⟩) hY hY1 hpr x ht (P.root lq) Z
  set ln := P.reflectionPerm lm lm with hln
  have hroot : P.root ln = -P.root lm := by
    rw [hln, P.root_reflectionPerm, P.reflection_apply_self]
  have hcoroot : P.coroot ln = -P.coroot lm := by
    rw [hln, P.coroot_reflectionPerm, P.coreflection_apply_self]
  have hY' : Y ∈ rootGroupPoints j (P.root ln) := by rw [hroot]; exact hY
  have hpr' : RelativeRoot.IsOppositeFactorPair j (P.root ln) Y pr := by rw [hroot]; exact hpr
  have hcor := IsOppositeFactorPair.coroot_eq_rootDatum j hT hjc hP ln hY' hY1 hpr'
  have hw : weylAction j (⟨pr.1 * Y * pr.2, hpr.2.2⟩ : normalizerPoints j) (P.root lq) =
      -P.root lp := by
    rw [weylAction_oppositeFactorPair_eq j hT hjc hP ln hY' hY1 hpr', hcoroot, map_neg, h2m,
      hroot, hm]
    simp only [neg_smul, one_smul, neg_neg, smul_neg]
    abel
  change x.val (P.root lq) Z = x.val (weylAction j _ (P.root lq)) _ +
    ((t * latticePairing T (P.root lq) (hpr.coroot j _ _ hY hY1) : ℝ) : WithTop ℝ) at hRF
  have hcor' : hpr.coroot j hi.isSplitSubtorus.1 hnm.1 hY hY1 = -P.coroot lm := by
    rw [← hcoroot]
    convert hcor using 2
    exact hroot.symm
  rw [hw, hRC, hcor', ← hP.1, map_neg, h2m] at hRF
  rw [hRF, ht, add_assoc, ← WithTop.coe_add]
  norm_num

end Piece

section Uniqueness

variable {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (j : T.toGrp ⟶ G) [Mono j.hom.hom.left]
  {J : Type*} [Finite J] {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  (hT : IsSplitTorus T.toGrp) (hP : IsRootDatumOf j P)
  {f : S ⟶ T} {a : characterLattice S}
  (hline : RestrictsToMultipliableLine f P a) {lp lq lm : J}
  (hp : f ≫ P.root lp = a) (hq : f ≫ P.root lq = a) (hpq : lp ≠ lq)
  (hm : P.root lm = P.root lp + P.root lq)

omit [Smooth G.X.hom] [Mono j.hom.hom.left] [Finite J] in
/-- A root point lying in the dynamic unipotent subgroup of a cocharacter pairing negatively
with its root is trivial. -/
theorem eq_one_of_mem_rootGroupPoints_of_mem_unipotent {δ : characterLattice T}
    (ν : cocharacterLattice T) (hpos : 0 < latticePairing T δ ν)
    {w : rationalPoints G} (hw : w ∈ rootGroupPoints j δ)
    (hw' : w ∈ (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ j)).carrier
      (Over.mk (𝟙 _))) : w = 1 :=
  RelativeRoot.eq_one_of_mem_subgroup_of_mem_negative_parabolic j ν hpos hw
    (Dynamic.unipotent_le_parabolic _ _ hw')

omit [Smooth G.X.hom] [Mono j.hom.hom.left] in
include hP hline hp hq hpq hm in
/-- **Uniqueness of piece coordinates.** In the order `q, m, p`, a product `x z y` with
`x ∈ U_q`, `z ∈ U_m`, `y ∈ U_p` determines its factors. -/
theorem piece_eq_of_mul_eq {x x' z z' y y' : rationalPoints G}
    (hx : x ∈ rootGroupPoints j (P.root lq)) (hx' : x' ∈ rootGroupPoints j (P.root lq))
    (hz : z ∈ rootGroupPoints j (P.root lm)) (hz' : z' ∈ rootGroupPoints j (P.root lm))
    (hy : y ∈ rootGroupPoints j (P.root lp)) (hy' : y' ∈ rootGroupPoints j (P.root lp))
    (h : x * z * y = x' * z' * y') : x = x' ∧ z = z' ∧ y = y' := by
  obtain ⟨h11, h22, h21, h12, hm1, hm2, h1m, h2m, hmm⟩ := piece_pairings hline hp hq hpq hm
  -- separate `q` from `m` and `p` with the cocharacter `-p^∨`
  have hU : ∀ {w : rationalPoints G} {χ : characterLattice T},
      0 < latticePairing T χ (P.coroot lp) → w ∈ rootGroupPoints j χ →
      w ∈ (Dynamic.unipotent (CommGroupScheme.groupHom (-(-P.coroot lp)) ≫ j)).carrier
        (Over.mk (𝟙 _)) := by
    intro w χ hχ hw
    rw [neg_neg]
    exact RelativeRoot.subgroup_le_dynamicUnipotent j _ hχ _ hw
  have hmpos : 0 < latticePairing T (P.root lm) (P.coroot lp) := by rw [← hP.1, hm1]; norm_num
  have hppos : 0 < latticePairing T (P.root lp) (P.coroot lp) := by rw [← hP.1, h11]; norm_num
  have hxx : x'⁻¹ * x = z' * (y' * y⁻¹) * z⁻¹ := by
    have : x = x' * z' * y' * y⁻¹ * z⁻¹ := by rw [← h]; group
    rw [this]; group
  have h1 : x'⁻¹ * x = 1 := by
    apply eq_one_of_mem_rootGroupPoints_of_mem_unipotent j (-P.coroot lp)
      (by rw [← hP.1, map_neg, h21]; norm_num)
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx') hx)
    rw [hxx]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (hU hmpos hz') (Subgroup.mul_mem _
      (hU hppos hy') (Subgroup.inv_mem _ (hU hppos hy)))) (Subgroup.inv_mem _ (hU hmpos hz))
  have hxeq : x = x' := (inv_mul_eq_one.mp h1).symm
  subst hxeq
  have h' : z * y = z' * y' := by
    have := h
    simp only [mul_assoc] at this
    exact mul_left_cancel this
  have hzz : z'⁻¹ * z = y' * y⁻¹ := by
    have : z = z' * y' * y⁻¹ := by rw [← h']; group
    rw [this]; group
  have h2 : z'⁻¹ * z = 1 := by
    apply eq_one_of_mem_rootGroupPoints_of_pairing j (P.coroot lq)
      (by rw [← hP.1, hm2]; norm_num) (by rw [← hP.1, h12]; norm_num)
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hz') hz)
    rw [hzz]
    exact Subgroup.mul_mem _ hy' (Subgroup.inv_mem _ hy)
  have hzeq : z = z' := (inv_mul_eq_one.mp h2).symm
  subst hzeq
  exact ⟨rfl, rfl, mul_left_cancel h'⟩

include hT hP hline hp hq hpq hm in
/-- **Reordering a piece.** `x z y = y (z [x, y]) x` for `x ∈ U_q`, `z ∈ U_m`, `y ∈ U_p`, and
`z [x, y] ∈ U_m`. -/
theorem piece_reorder (hE : RelativeRoot.HasOppositeFactorPairs j) {x z y : rationalPoints G}
    (hx : x ∈ rootGroupPoints j (P.root lq)) (hz : z ∈ rootGroupPoints j (P.root lm))
    (hy : y ∈ rootGroupPoints j (P.root lp)) :
    z * (x * y * x⁻¹ * y⁻¹) ∈ rootGroupPoints j (P.root lm) ∧
      x * z * y = y * (z * (x * y * x⁻¹ * y⁻¹)) * x := by
  have hm' : P.root lm = P.root lq + P.root lp := by rw [hm, add_comm]
  have hc : x * y * x⁻¹ * y⁻¹ ∈ rootGroupPoints j (P.root lm) :=
    piece_commutator_mem_pq j hT hE hP hline hq hp (Ne.symm hpq) hm' hx hy
  refine ⟨Subgroup.mul_mem _ hz hc, ?_⟩
  have hzx : z * x = x * z := (piece_commute_m_q j hT hP hline hp hq hpq hm hz hx).eq
  have hWy : (z * (x * y * x⁻¹ * y⁻¹)) * y = y * (z * (x * y * x⁻¹ * y⁻¹)) :=
    (piece_commute_m_q j hT hP hline hq hp (Ne.symm hpq) hm' (Subgroup.mul_mem _ hz hc) hy).eq
  calc x * z * y = z * x * y := by rw [hzx]
    _ = (z * (x * y * x⁻¹ * y⁻¹)) * y * x := by group
    _ = y * (z * (x * y * x⁻¹ * y⁻¹)) * x := by rw [hWy]

include hT hP hline hp hq hpq hm in
/-- **A symmetry swapping `p` and `q`.** Let `s` be an endomorphism of the rational points
carrying each `U_χ` into `U_{σχ}` and preserving `φ`, where `σ` swaps `p` and `q` and fixes
`m`. If `s` fixes `x z y` (`x ∈ U_q`, `z ∈ U_m`, `y ∈ U_p`), then `s x = y`, `s y = x`,
`s z = z [x, y]`, and hence `φ_p(y) = φ_q(x)` and `φ_m(z [x, y]) = φ_m(z)`. -/
theorem piece_swap (hE : RelativeRoot.HasOppositeFactorPairs j) {φ : RootFunctionFamily T G}
    (s : rationalPoints G →* rationalPoints G) (σ : characterLattice T → characterLattice T)
    (hσp : σ (P.root lp) = P.root lq) (hσq : σ (P.root lq) = P.root lp)
    (hσm : σ (P.root lm) = P.root lm)
    (hsU : ∀ (χ : characterLattice T) (w : rationalPoints G),
      w ∈ rootGroupPoints j χ → s w ∈ rootGroupPoints j (σ χ))
    (hsφ : ∀ (χ : characterLattice T) (w : rationalPoints G), φ (σ χ) (s w) = φ χ w)
    {x z y : rationalPoints G}
    (hx : x ∈ rootGroupPoints j (P.root lq)) (hz : z ∈ rootGroupPoints j (P.root lm))
    (hy : y ∈ rootGroupPoints j (P.root lp)) (hfix : s (x * z * y) = x * z * y) :
    s x = y ∧ s y = x ∧ s z = z * (x * y * x⁻¹ * y⁻¹) ∧
      φ (P.root lp) y = φ (P.root lq) x ∧
      φ (P.root lm) (z * (x * y * x⁻¹ * y⁻¹)) = φ (P.root lm) z := by
  obtain ⟨hW, hre⟩ := piece_reorder j hT hP hline hp hq hpq hm hE hx hz hy
  have hm' : P.root lm = P.root lq + P.root lp := by rw [hm, add_comm]
  have hsx : s x ∈ rootGroupPoints j (P.root lp) := by rw [← hσq]; exact hsU _ _ hx
  have hsz : s z ∈ rootGroupPoints j (P.root lm) := by rw [← hσm]; exact hsU _ _ hz
  have hsy : s y ∈ rootGroupPoints j (P.root lq) := by rw [← hσp]; exact hsU _ _ hy
  have heq : s x * s z * s y = y * (z * (x * y * x⁻¹ * y⁻¹)) * x := by
    rw [← map_mul, ← map_mul, hfix, hre]
  obtain ⟨h1, h2, h3⟩ := piece_eq_of_mul_eq j hP hline hq hp (Ne.symm hpq) hm' hsx hy hsz hW
    hsy hx heq
  refine ⟨h1, h3, h2, ?_, ?_⟩
  · rw [← h1]
    have := hsφ (P.root lq) x
    rwa [hσq] at this
  · rw [← h2]
    have := hsφ (P.root lm) z
    rwa [hσm] at this

end Uniqueness

end Langlands.Geometry.Building
