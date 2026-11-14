import Langlands.GroupScheme.Rational.A2OrbitGeneration
import Langlands.FieldTheory.QuadraticFixedFieldCoordinates

/-! # Good units of an `A₂` orbit from stabilizer-fixed base triples -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme.GaloisPointComparison Langlands.Geometry.Building

private theorem ite_neg' {α : Sort*} {P : Prop} [Decidable P] {x y : α} (h : ¬ P) :
    (if P then x else y) = y := by simp [h]

private theorem ite_pos' {α : Sort*} {P : Prop} [Decidable P] {x y : α} (h : P) :
    (if P then x else y) = x := by simp [h]

namespace Langlands.GroupScheme

namespace GaloisCompatiblePinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : GaloisCompatiblePinningData k K G)

local instance a2OrbitUnitsAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

attribute [local instance] rootIndexMulAction

theorem transportElement_basePair (m₀ : D.pinning.rootIndex) :
    D.transportElement (D.basePair m₀) = 1 :=
  mul_inv_cancel _

variable {S : CommGroupScheme (Spec (CommRingCat.of k))} (t : S ⟶ D.torus)
  {p₀ q₀ : D.pinning.base.support} {m₀ : D.pinning.rootIndex}
  (hm₀ : D.pinning.rootDatum.root m₀ =
    D.pinning.rootDatum.root (p₀ : D.pinning.rootIndex) +
      D.pinning.rootDatum.root (q₀ : D.pinning.rootIndex))
  (hS : IsSplitTorus S.toGrp) {a : characterLattice S}
  (hp₀ : D.restrictMap t ≫ D.pinning.rootDatum.root (p₀ : D.pinning.rootIndex) =
    characterLattice.baseChange (algebraBaseMap k K) S a)
  (hq₀ : D.restrictMap t ≫ D.pinning.rootDatum.root (q₀ : D.pinning.rootIndex) =
    characterLattice.baseChange (algebraBaseMap k K) S a)
  (hpq : p₀ ≠ q₀)
  (hline : RestrictsToMultipliableLine (D.restrictMap t) D.pinning.rootDatum
    (characterLattice.baseChange (algebraBaseMap k K) S a))

/-- The roots of every piece lie in the Galois orbit of the base root `A`. -/
theorem pair_mem_orbit {σ₀ : K ≃ₐ[k] K} (hσ₀ : D.action σ₀ p₀ = q₀) (c : D.PairOrbit m₀) :
    (∃ g : K ≃ₐ[k] K, D.action g (D.pairA p₀ (D.basePair m₀)) = D.pairA p₀ c) ∧
      ∃ g : K ≃ₐ[k] K, D.action g (D.pairA p₀ (D.basePair m₀)) = D.pairB q₀ c := by
  refine ⟨⟨_, D.action_transportElement_pairA c⟩,
    ⟨D.transportElement c * D.swapElement σ₀ m₀, ?_⟩⟩
  rw [map_mul, Equiv.Perm.mul_apply, D.action_swapElement hσ₀,
    D.action_transportElement_pairB]

section Units

variable (M : D.PairOrbit m₀ → D.pinning.SteinbergModifiedData)
  (hM : ∀ c, (M c).a = D.pairA p₀ c ∧ (M c).b = D.pairB q₀ c)
  (hMx : ∀ (σ : K ≃ₐ[k] K) (c : D.PairOrbit m₀) (s : K),
    rationalConjugate k K G σ ((M c).xAlpha.rationalPoint s) =
      (M (σ • c)).xAlpha.rationalPoint (σ s))
  [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffineHom D.torus.toGrp.X.hom]
  [LocallyOfFiniteType D.torus.toGrp.X.hom] [FiniteDimensional k K] [IsGalois k K]
  (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj D.torus).toGrp)
  (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom t ≫ D.inclusion))
  (hjc : IsClosedSubgroup D.inclusion)
  (hcent : (torusCentralizer (CommGroupScheme.groupHom t ≫ D.inclusion)).IsRepresentedBy
      D.inclusion)
  (hic : IsClosedSubgroup (CommGroupScheme.groupHom t ≫ D.inclusion))
  (hspan : D.pinning.rootDatum.corootSpan ℤ = ⊤)
  (hE : RelativeRoot.HasOppositeFactorPairs (CommGroupScheme.groupHom t ≫ D.inclusion))
  (ha : a ∈ relativeRoots (CommGroupScheme.groupHom t ≫ D.inclusion))
  (hna : -a ∈ relativeRoots (CommGroupScheme.groupHom t ≫ D.inclusion))

include hm₀ hS hp₀ hq₀ hpq hline hM hMx hT hf hjc hcent hic hspan hE ha hna in
/-- **Good units from stabilizer-fixed base triples.** If the base triple
`x_B(u) x_m(w) x_A(u)` is fixed by the stabilizer of the base piece and `w ≠ 0`, then `w` is a
good unit at the base root `A`. -/
theorem mem_orbitGoodUnits_of_fixed {σ₀ : K ≃ₐ[k] K} (hσ₀ : D.action σ₀ p₀ = q₀) (u w : K)
    (hw : w ≠ 0)
    (hfix : ∀ g : K ≃ₐ[k] K, g • D.basePair m₀ = D.basePair m₀ →
      rationalConjugate k K G g (D.pieceTriple p₀ q₀ M (D.basePair m₀) u w u) =
        D.pieceTriple p₀ q₀ M (D.basePair m₀) u w u) :
    Units.mk0 w hw ∈ D.orbitGoodUnits t (D.pairA p₀ (D.basePair m₀)) := by
  classical
  have ha0 : a ≠ 0 := ha.1
  have : Smooth ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
    D.pinning.isConnectedReductive.smooth
  have hSK : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj S).toGrp :=
    hS.baseChange (algebraBaseMap k K)
  have ha0K : characterLattice.baseChange (algebraBaseMap k K) S a ≠ 0 := by
    intro h
    apply ha0
    apply (characterLattice.baseChangeEquiv (algebraBaseMap k K) S hS).map_eq_zero_iff.mp
    rw [characterLattice.baseChangeEquiv_apply, h]
  have hfac := D.groupHom_restrictMap_comp_inclusion t
  set F := D.a2PieceFamily t hm₀ hS hp₀ hq₀ hpq hline M hM hT hf hjc hcent with hF
  set e := D.pieceEquiv m₀ with he
  -- the two rational points
  obtain ⟨X, hX, hXK⟩ := D.exists_rootGroupPoint_pieceTriple M hMx t hm₀ hS hp₀ hq₀ hpq hline hM
    hT hf hjc hcent ha0 u w u hfix
  obtain ⟨X₀, hX₀, hX₀K⟩ := D.exists_rootGroupPoint_pieceTriple M hMx t hm₀ hS hp₀ hq₀ hpq hline
    hM hT hf hjc hcent ha0 0 1 0
    (D.pieceTriple_zero_fixed M hMx (IntermediateField.fixedField _).one_mem)
  simp only [map_zero, map_one, simplePoint_zero] at hX₀K
  have hτw : ∀ l, D.transportElement (e l) w ≠ 0 := fun l => by
    rw [map_ne_zero_iff _ (D.transportElement (e l)).injective]; exact hw
  let w' : Fin F.r → Kˣ := fun l => Units.mk0 _ (hτw l)
  have hXK' : rationalExtend k K G X = F.tripleProd
      (fun l => D.simplePoint (D.pairB q₀ (e l)) (D.transportElement (e l) u))
      (fun l => (M (e l)).xAlpha.rationalPoint (w' l))
      (fun l => D.simplePoint (D.pairA p₀ (e l)) (D.transportElement (e l) u)) := hXK
  have hXq : ∀ l, D.simplePoint (D.pairB q₀ (e l)) (D.transportElement (e l) u) ∈
      rootGroupPoints D.pinning.inclusion (D.pinning.rootDatum.root (F.lq l)) := fun l =>
    (D.rootMaps _).toRootParametrization.rationalPoint_mem _
  have hYp : ∀ l, D.simplePoint (D.pairA p₀ (e l)) (D.transportElement (e l) u) ∈
      rootGroupPoints D.pinning.inclusion (D.pinning.rootDatum.root (F.lp l)) := fun l =>
    (D.rootMaps _).toRootParametrization.rationalPoint_mem _
  -- nontriviality
  have hl0 : e (e.symm (D.basePair m₀)) = D.basePair m₀ := Equiv.apply_symm_apply _ _
  have hnt : ∀ {Y : rationalPoints G}, Y ∈ rootGroupPoints
      (CommGroupScheme.groupHom t ≫ D.inclusion) a →
      ∀ {x z y : Fin F.r → rationalPoints (baseChanged k K G)},
      (∀ l, x l ∈ rootGroupPoints D.pinning.inclusion (D.pinning.rootDatum.root (F.lq l))) →
      (∀ l, z l ∈ rootGroupPoints D.pinning.inclusion (D.pinning.rootDatum.root (F.lm l))) →
      (∀ l, y l ∈ rootGroupPoints D.pinning.inclusion (D.pinning.rootDatum.root (F.lp l))) →
      rationalExtend k K G Y = F.tripleProd x z y → (∃ l, z l ≠ 1) → Y ≠ 1 := by
    intro Y hY x z y hx hz hy hYK ⟨l, hzl⟩ hY1
    have hg : F.tripleProd x z y ∈ rootGroupPoints
        (CommGroupScheme.groupHom (D.restrictMap t) ≫ D.pinning.inclusion)
        (characterLattice.baseChange (algebraBaseMap k K) S a) := by
      rw [← hYK, hfac]
      exact rationalExtend_mem_rootGroupPoints (K := K) _ a hY
    exact SplitPinning.tripleProd_ne_one D.pinning hSK hline F ha0K hx hz hy hg hzl
      (by rw [← hYK, hY1, map_one])
  have hX1 : X ≠ 1 := hnt hX hXq (fun l => (M (e l)).xAlpha.rationalPoint_mem _) hYp hXK'
    ⟨e.symm (D.basePair m₀), (M _).xAlpha.rationalPoint_ne_one (w' _).ne_zero⟩
  have hX₀1 : X₀ ≠ 1 := hnt hX₀ (fun _ => Subgroup.one_mem _)
    (fun l => (M (e l)).xAlpha.rationalPoint_mem _) (fun _ => Subgroup.one_mem _) hX₀K
    ⟨e.symm (D.basePair m₀), (M _).xAlpha.rationalPoint_ne_one one_ne_zero⟩
  -- opposite pairs and the torus part
  obtain ⟨⟨A₁, B₁⟩, hAB⟩ := hE a ha X hX hX1
  obtain ⟨⟨A₀, B₀⟩, hAB₀⟩ := hE a ha X₀ hX₀ hX₀1
  obtain ⟨x, hx, hxω⟩ := D.exists_rationalTorusPart t hic hjc hS ha0 hline hcent F
    (fun l => (M (e l)).xAlpha) w' hXq hYp hXK' hX₀K hX hX1 hX₀ hX₀1 hAB hAB₀
  have ht : A₁ * X * B₁ * (A₀ * X₀ * B₀)⁻¹ ∈
      relativeRootGeneratedSubgroup (CommGroupScheme.groupHom t ≫ D.inclusion) := by
    have hpos := relativeRoot_subgroup_le_generated (CommGroupScheme.groupHom t ≫ D.inclusion) ha
    have hneg := relativeRoot_subgroup_le_generated (CommGroupScheme.groupHom t ≫ D.inclusion) hna
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hneg hAB.1) (hpos hX))
      (hneg hAB.2.1)) (Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (hneg hAB₀.1) (hpos hX₀)) (hneg hAB₀.2.1)))
  -- character values
  have hpair : ∀ (b : D.pinning.base.support) (l : Fin F.r),
      D.pinning.rootDatum.toLinearMap
        (Langlands.RootDatum.fundamentalWeightBasis D.pinning.rootDatum D.pinning.base hspan b)
        (D.pinning.rootDatum.coroot (F.lp l)) = (if D.pairA p₀ (e l) = b then 1 else 0) ∧
      D.pinning.rootDatum.toLinearMap
        (Langlands.RootDatum.fundamentalWeightBasis D.pinning.rootDatum D.pinning.base hspan b)
        (D.pinning.rootDatum.coroot (F.lq l)) = (if D.pairB q₀ (e l) = b then 1 else 0) := by
    intro b l
    exact ⟨Langlands.RootDatum.fundamentalWeightBasis_pairing _ _ hspan b _,
      Langlands.RootDatum.fundamentalWeightBasis_pairing _ _ hspan b _⟩
  have hB : ∀ l, D.pairB q₀ (e l) ≠ D.pairA p₀ (D.basePair m₀) := by
    intro l h
    have hc := D.pair_eq_of_mem t hm₀ hS hp₀ hq₀ hpq hline
      (x := (D.pairA p₀ (D.basePair m₀) : D.pinning.rootIndex))
      (Or.inr (congrArg Subtype.val h.symm))
      (Or.inl rfl)
    rw [hc] at h
    exact D.baseA_ne_baseB hpq h.symm
  have hval : ∀ b : D.pinning.base.support,
      (∀ l, D.pairB q₀ (e l) ≠ b) →
      D.pinning.fundamentalWeightEval hspan b x =
        ∏ l, (w' l) ^ (if D.pairA p₀ (e l) = b then (1 : ℤ) else 0) := by
    intro b hb
    have h := hxω (Langlands.RootDatum.fundamentalWeightBasis D.pinning.rootDatum D.pinning.base
      hspan b) (fun l => by rw [(hpair b l).2, ite_neg' (hb l)])
    rw [show D.pinning.fundamentalWeightEval hspan b x = D.pinning.charEval
      (Langlands.RootDatum.fundamentalWeightBasis D.pinning.rootDatum D.pinning.base hspan b) x
      from rfl, h]
    exact Finset.prod_congr rfl fun l _ => by rw [(hpair b l).1]
  -- the good-unit witness
  refine ⟨fun b => D.pinning.fundamentalWeightEval hspan b x, ⟨fun σ b => ?_, fun b hb => ?_⟩,
    ?_, ?_⟩
  · show ((D.pinning.fundamentalWeightEval hspan (D.action σ b) x : Kˣ) : K) =
      σ (D.pinning.fundamentalWeightEval hspan b x)
    rw [D.fundamentalWeightEval_action hspan hjc hx σ b]
    rfl
  · have hob := D.pair_mem_orbit (m₀ := m₀) hσ₀
    show D.pinning.fundamentalWeightEval hspan b x = 1
    rw [hval b (fun l h => by
      obtain ⟨g, hg⟩ := (hob (e l)).2
      exact hb g (hg.trans h))]
    apply Finset.prod_eq_one
    intro l _
    rw [ite_neg' (fun h => by
      obtain ⟨g, hg⟩ := (hob (e l)).1
      exact hb g (hg.trans h)), zpow_zero]
  · rw [D.pinning.simpleCorootProduct_fundamentalWeightEval hspan x, ← hx]
    exact ⟨_, ht, rfl⟩
  · show D.pinning.fundamentalWeightEval hspan (D.pairA p₀ (D.basePair m₀)) x = Units.mk0 w hw
    rw [hval _ hB]
    refine (Finset.prod_eq_single (s := Finset.univ)
      ((D.pieceEquiv m₀).symm (D.basePair m₀) : Fin F.r) ?_ ?_).trans ?_
    · intro l _ hl
      rw [ite_neg' (fun h => hl ?_), zpow_zero]
      have hc := D.pair_eq_of_mem t hm₀ hS hp₀ hq₀ hpq hline
        (x := (D.pairA p₀ (D.basePair m₀) : D.pinning.rootIndex))
        (Or.inl (congrArg Subtype.val h.symm)) (Or.inl rfl)
      change l = (D.pieceEquiv m₀).symm (D.basePair m₀)
      rw [← hc]
      exact ((D.pieceEquiv m₀).symm_apply_apply l).symm
    · intro h
      exact absurd (Finset.mem_univ _) h
    · have h1 : e ((D.pieceEquiv m₀).symm (D.basePair m₀)) = D.basePair m₀ :=
        Equiv.apply_symm_apply _ _
      rw [ite_pos' (congrArg (D.pairA p₀) h1), zpow_one]
      apply Units.ext
      rw [Units.val_mk0, Units.val_mk0]
      rw [h1, D.transportElement_basePair]
      rfl

include hm₀ hS hp₀ hq₀ hpq hline hM hMx hT hf hjc hcent hic hspan hE ha hna in
/-- **The `A₂`-orbit case.** Let the base simple-root points `x_A(1)` and `x_B(1)` not commute.
Then for every Galois-equivariant unit family `c` supported on the Galois orbit of the base root
`A`, the coroot product `∏ b^∨(c b)` lies in the image of `G(k)^+`. -/
theorem simpleCorootProduct_mem_of_a2 {σ₀ : K ≃ₐ[k] K} (hσ₀ : D.action σ₀ p₀ = q₀)
    (hnc : ¬ Commute (D.simplePoint (D.pairA p₀ (D.basePair m₀)) 1)
      (D.simplePoint (D.pairB q₀ (D.basePair m₀)) 1))
    {c : D.pinning.base.support → Kˣ} (hc : D.IsOrbitFamily (D.pairA p₀ (D.basePair m₀)) c) :
    rationalPoints.map D.pinning.inclusion (D.pinning.simpleCorootProduct c) ∈
      relativeRootGeneratedExtension k K (CommGroupScheme.groupHom t ≫ D.inclusion) := by
  classical
  have : Smooth ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
    D.pinning.isConnectedReductive.smooth
  set A := D.pairA p₀ (D.basePair m₀) with hA
  set H := D.rootStabilizer A with hH
  set H' := D.pairStabilizer m₀ with hH'
  set σ := D.swapElement σ₀ m₀ with hσdef
  have hHH' : H ≤ H' := D.rootStabilizer_le_pairStabilizer t hm₀ hS hp₀ hq₀ hpq hline
  have hindex : H.relIndex H' = 2 := D.relIndex_rootStabilizer t hm₀ hS hp₀ hq₀ hpq hline hσ₀
  have hσ : σ ∈ H' := D.swapElement_mem t hm₀ hS hp₀ hq₀ hpq hline hσ₀
  have hσnot : σ ∉ H := D.swapElement_not_mem hpq hσ₀
  have hσA := D.action_swapElement (m₀ := m₀) hσ₀
  -- the commutator scalar
  obtain ⟨r, hr⟩ := D.exists_commutatorScalar t hm₀ hS hp₀ hq₀ hpq hline M hM
  have hrE : r ∈ IntermediateField.fixedField H := (IntermediateField.mem_fixedField_iff _ _).mpr
    fun g hg => D.commutatorScalar_fixed t hm₀ hS hp₀ hq₀ hpq hline M hMx hr hg
  have hrσ : σ r = -r := D.commutatorScalar_swap t hm₀ hS hp₀ hq₀ hpq hline M hMx hr hσ hσA
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hnc
    have h0 : (M (D.basePair m₀)).xAlpha.rationalPoint 0 = 1 := by
      have h := SplitPinning.RootParametrization.rationalPoint_add (M (D.basePair m₀)).xAlpha 0 0
      rw [add_zero] at h
      exact left_eq_mul.mp h
    rw [h0, mul_one] at hr
    exact hr
  obtain ⟨w₁, hw₁E, hw₁r⟩ :=
    Langlands.FieldTheory.QuadraticFixedField.exists_sub_conjugate_eq hHH' hindex hσ hσnot hrE hrσ
  have hw₁L : w₁ ∉ IntermediateField.fixedField H' := fun h => by
    apply hr0
    rw [← hw₁r, (IntermediateField.mem_fixedField_iff _ _).mp h σ hσ, sub_self]
  -- good units
  have hG1 : ∀ lam : Kˣ, (lam : K) ∈ IntermediateField.fixedField H' →
      lam ∈ D.orbitGoodUnits t A := by
    intro lam hlam
    have h := D.mem_orbitGoodUnits_of_fixed t hm₀ hS hp₀ hq₀ hpq hline M hM hMx hT hf hjc hcent
      hic hspan hE ha hna hσ₀ 0 lam lam.ne_zero (D.pieceTriple_zero_fixed M hMx hlam)
    rwa [Units.mk0_val] at h
  have hG2 : ∀ b ∈ IntermediateField.fixedField H', ∀ hb : w₁ + b ≠ 0,
      Units.mk0 (w₁ + b) hb ∈ D.orbitGoodUnits t A := by
    intro b hbL hb
    have hbE : b ∈ IntermediateField.fixedField H := IntermediateField.fixedField_le hHH' hbL
    have hwE : w₁ + b ∈ IntermediateField.fixedField H := add_mem hw₁E hbE
    have hwr : w₁ + b - σ (w₁ + b) = r := by
      rw [map_add, (IntermediateField.mem_fixedField_iff _ _).mp hbL σ hσ, ← hw₁r]
      ring
    exact D.mem_orbitGoodUnits_of_fixed t hm₀ hS hp₀ hq₀ hpq hline M hM hMx hT hf hjc hcent
      hic hspan hE ha hna hσ₀ 1 (w₁ + b) hb
      (D.pieceTriple_one_fixed t hm₀ hS hp₀ hq₀ hpq hline M hM hMx hr hwE hσA hwr)
  -- the value at `A`
  have hcA : (c A : K) ∈ IntermediateField.fixedField H := by
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    rw [← hc.1 g A, D.mem_rootStabilizer.mp hg]
  obtain ⟨a', ha'L, ha'⟩ :=
    Langlands.FieldTheory.QuadraticFixedField.unit_decomposition hHH' hindex hσ hσnot hw₁E hw₁L
      (c A) hcA
  have hmem : c A ∈ D.orbitGoodUnits t A := by
    rcases ha' with h | ⟨b, hbL, h⟩
    · rw [show c A = a' from Units.ext h]
      exact hG1 a' ha'L
    · have hb : w₁ + b ≠ 0 := fun h0 => hw₁L (by
        rw [show w₁ = -b by linear_combination h0]
        exact neg_mem hbL)
      rw [show c A = a' * Units.mk0 (w₁ + b) hb from Units.ext (by rw [h]; rfl)]
      exact Subgroup.mul_mem _ (hG1 a' ha'L) (hG2 b hbL hb)
  exact D.mem_of_mem_orbitGoodUnits t hc hmem

end Units

end GaloisCompatiblePinningData

end Langlands.GroupScheme
