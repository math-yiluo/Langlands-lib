import Langlands.GroupScheme.Rational.MaximalLeviConeComplementStatement
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.Rational.ParabolicRootConeEvaluation
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityProof
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.GroupScheme.Rational.SubtorusIntertwiningRoots
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Missed directions on a central-annihilator line

If the annihilator in `Vstar A` of the central cocharacters of a split component is the
line spanned by `x`, then two parabolics with that Levi whose positive cones miss `x` have
the same image and the same unipotent-radical image (`range_eq_of_line`). No maximality of
a parabolic is used there. Consequently `MaximalLeviConeComplementStatement` follows from
the line property `MaximalLeviCentralLineStatement` for maximal proper parabolics, which
this module retains as a premise and does not prove.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RealTorusSpace

namespace MaximalLeviConeComplementLine

variable {k : Type u} [Field k]
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The real pairing of two integral vectors is their lattice pairing. -/
theorem pair_one_tmul_one_tmul (χ : characterLattice A) (ν : cocharacterLattice A) :
    pair A ((1 : ℝ) ⊗ₜ[ℤ] χ) ((1 : ℝ) ⊗ₜ[ℤ] ν) = (latticePairing A χ ν : ℝ) := by
  rw [pair_tmul_tmul, one_mul, one_mul]

/-- Restricting a relative root along a factorization of `m` kills every cocharacter
whose composite with `m` is central. -/
theorem latticePairing_restrict_eq_zero_of_isCentral [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (i : T.toGrp ⟶ G) (f : A ⟶ T) {m : A.toGrp ⟶ G}
    (hf : CommGroupScheme.groupHom f ≫ i = m) {β : characterLattice T}
    (hβ : β ∈ relativeRoots i) {ν : cocharacterLattice A}
    (hν : IsCentral (CommGroupScheme.groupHom ν ≫ m)) :
    latticePairing A (f ≫ β) ν = 0 := by
  rw [RelativeRoot.latticePairing_restrict_cocharacterMapInt]
  have hc : IsCentral (CommGroupScheme.groupHom (cocharacterMapInt f ν) ≫ i) := by
    change IsCentral ((CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom f) ≫ i)
    rwa [Category.assoc, hf]
  have hzero := root_restrict_eq_zero_of_isCentral i (cocharacterMapInt f ν)
    isSplitTorus_gm hc hβ
  rw [latticePairing_apply, hzero, map_zero]

/-- Under the line hypothesis, every restricted relative root is a real multiple of `x`. -/
theorem exists_smul_eq_of_line [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {m : A.toGrp ⟶ G} {x : Vstar A}
    (hline : ∀ y : Vstar A, (∀ ν : cocharacterLattice A,
      IsCentral (CommGroupScheme.groupHom ν ≫ m) → pair A y ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0) →
        y ∈ Submodule.span ℝ {x})
    (i : T.toGrp ⟶ G) (f : A ⟶ T) (hf : CommGroupScheme.groupHom f ≫ i = m)
    {β : characterLattice T} (hβ : β ∈ relativeRoots i) :
    ∃ c : ℝ, c • x = (1 : ℝ) ⊗ₜ[ℤ] (f ≫ β) := by
  apply Submodule.mem_span_singleton.mp
  apply hline
  intro ν hν
  rw [pair_one_tmul_one_tmul, latticePairing_restrict_eq_zero_of_isCentral i f hf hβ hν,
    Int.cast_zero]

/-- A closed subgroup that is not an isomorphism has a Levi image different from `⊤`. -/
theorem range_comp_ne_top_of_not_isIso {P M : GroupScheme (Spec (CommRingCat.of k))}
    {p : P ⟶ G} (hp : IsClosedSubgroup p) (hprop : ¬ IsIso p) (l : M ⟶ P) :
    SubgroupFunctor.range (l ≫ p) ≠ ⊤ := by
  intro htop
  apply hprop
  have hfull : SubgroupFunctor.range p = ⊤ :=
    le_antisymm (SubgroupFunctor.le_def.mpr fun _ => le_top)
      (htop.ge.trans (SubgroupFunctor.range_comp_le l p))
  have := hp.mono
  have hfrep : (⊤ : SubgroupFunctor G).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, hfull⟩
  have hidrep : (⊤ : SubgroupFunctor G).IsRepresentedBy (𝟙 G) :=
    ⟨inferInstance, SubgroupFunctor.range_id G⟩
  have he : (hfrep.isoOfIsRepresentedBy hidrep).hom = p := by
    simpa only [Category.comp_id] using hfrep.isoOfIsRepresentedBy_hom_comp hidrep
  rw [← he]
  infer_instance

end MaximalLeviConeComplementLine

namespace ParabolicRootPresentation

open MaximalLeviConeComplementLine

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Q M : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  {q : Q ⟶ G} {lQ : M ⟶ Q} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation q lQ a)

omit [Smooth G.X.hom] in
theorem splitComponentEvaluation_apply (y : Vstar A) :
    r.splitComponentEvaluation y = pair A y ((1 : ℝ) ⊗ₜ[ℤ] r.splitComponentCocharacter) :=
  rfl

omit [Smooth G.X.hom] in
/-- The image of a split-component cocharacter in the presentation torus has the
same ambient composite. -/
theorem groupHom_cocharacterMapInt_comp (ν : cocharacterLattice A) :
    CommGroupScheme.groupHom (cocharacterMapInt r.data.f ν) ≫ r.data.i =
      CommGroupScheme.groupHom ν ≫ a ≫ lQ ≫ q := by
  change (CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom r.data.f) ≫ r.data.i = _
  rw [Category.assoc, r.isCompatible.factor_comp]

/-- A presentation of a parabolic whose Levi image is not the whole group has a
restricted simple root. -/
theorem restrictedRoots_nonempty (hG : IsConnectedReductive G)
    (hM : SubgroupFunctor.range (lQ ≫ q) ≠ ⊤) : r.restrictedRoots.Nonempty := by
  have := hG.connectedSpace
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  apply hM
  have hsub := r.restrictedRoots_eq_empty_iff.mp hempty
  have hstd := r.isStandard_splitComponentCocharacter
  have hneg := relativeRootNegation k G hG r.data.T r.data.i r.isCompatible.maximalSplit
  have hcl := relativeRoots_subset_addSubgroupClosure_simpleRelativeRoots r.data.i r.data.ν
    r.isCompatible.generic hneg
  have hzero : ∀ α ∈ relativeRoots r.data.i, latticePairing r.data.T α
      (cocharacterMapInt r.data.f r.splitComponentCocharacter) = 0 := by
    intro α hα
    have hle : AddSubgroup.closure (simpleRelativeRoots r.data.i r.data.ν) ≤
        (LinearMap.ker ((latticePairing r.data.T).flip
          (cocharacterMapInt r.data.f r.splitComponentCocharacter))).toAddSubgroup := by
      rw [AddSubgroup.closure_le]
      intro β hβ
      exact LinearMap.mem_ker.mpr (hstd.2.1 β (hsub hβ))
    exact LinearMap.mem_ker.mp (hle (hcl hα))
  have hc := rootAnnihilatorCentrality k G r.data.T
    r.isCompatible.maximalSplit.isSplitSubtorus.1 r.data.i _ hzero
  rw [r.groupHom_cocharacterMapInt_comp] at hc
  rw [r.levi_eq_splitComponentCocharacter]
  exact (isCentral_iff_dynamicCentralizer_eq_top _).mp hc

/-- If the central-annihilator line is spanned by `x` and `x` misses the positive cone,
then `x` is negative on the defining split-component cocharacter. -/
theorem splitComponentEvaluation_neg_of_line (hG : IsConnectedReductive G)
    (hM : SubgroupFunctor.range (lQ ≫ q) ≠ ⊤) {x : Vstar A}
    (hline : ∀ y : Vstar A, (∀ ν : cocharacterLattice A,
      IsCentral (CommGroupScheme.groupHom ν ≫ a ≫ lQ ≫ q) →
        pair A y ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0) → y ∈ Submodule.span ℝ {x})
    (hx : x ∉ r.positiveCone) : r.splitComponentEvaluation x < 0 := by
  have hmul : ∀ β ∈ r.restrictedRoots, ∃ c : ℝ, c • x = β := by
    intro β hβ
    obtain ⟨α, hα, -, rfl⟩ := r.mem_restrictedRoots.mp hβ
    exact exists_smul_eq_of_line hline r.data.i r.data.f r.isCompatible.factor_comp
      (positiveRelativeRoots_subset_relativeRoots _ _
        (simpleRelativeRoots_subset_positive _ _ hα))
  obtain ⟨β₀, hβ₀⟩ := r.restrictedRoots_nonempty hG hM
  obtain ⟨c₀, hc₀⟩ := hmul β₀ hβ₀
  have hpos₀ := r.splitComponentEvaluation_pos_of_mem_restrictedRoots hβ₀
  rw [← hc₀, map_smul, smul_eq_mul] at hpos₀
  by_contra hnot
  have hxpos : 0 < r.splitComponentEvaluation x := by
    rcases lt_or_eq_of_le (not_lt.mp hnot) with h | h
    · exact h
    · rw [← h, mul_zero] at hpos₀
      exact absurd hpos₀ (lt_irrefl 0)
  apply hx
  have hycone : (∑ᶠ β ∈ r.restrictedRoots, (1 : ℝ) • β) ∈ r.positiveCone :=
    r.mem_positiveCone.mpr ⟨fun _ => 1, fun _ _ => one_pos, rfl⟩
  have hyspan : (∑ᶠ β ∈ r.restrictedRoots, (1 : ℝ) • β) ∈ Submodule.span ℝ {x} := by
    apply finsum_mem_induction (fun z => z ∈ Submodule.span ℝ {x})
    · exact Submodule.zero_mem _
    · intro z w hz hw
      exact Submodule.add_mem _ hz hw
    · intro β hβ
      obtain ⟨c, hc⟩ := hmul β hβ
      rw [one_smul, ← hc]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self x)
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hyspan
  have hypos := r.splitComponentEvaluation_pos_of_mem_positiveCone ⟨β₀, hβ₀⟩ hycone
  rw [← ht, map_smul, smul_eq_mul] at hypos
  have htpos : 0 < t := by
    by_contra htn
    have htn' := not_lt.mp htn
    nlinarith
  have hxeq : x = t⁻¹ • (∑ᶠ β ∈ r.restrictedRoots, (1 : ℝ) • β) := by
    rw [← ht, smul_smul, inv_mul_cancel₀ htpos.ne', one_smul]
  rw [hxeq]
  exact r.smul_mem_positiveCone (inv_pos.mpr htpos) hycone

end ParabolicRootPresentation

namespace MaximalLeviConeComplementLine

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G P M : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- Two parabolics with the specified Levi whose positive cones miss a vector `x`
spanning the central-annihilator line have the same image and the same radical image. -/
theorem range_eq_of_line (hG : IsConnectedReductive G)
    {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    (hM : SubgroupFunctor.range (l ≫ p) ≠ ⊤) {x : Vstar A}
    (hline : ∀ y : Vstar A, (∀ ν : cocharacterLattice A,
      IsCentral (CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p) →
        pair A y ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0) → y ∈ Submodule.span ℝ {x})
    {Q₁ U₁ Q₂ U₂ : GroupScheme (Spec (CommRingCat.of k))}
    {q₁ : Q₁ ⟶ G} {lQ₁ : M ⟶ Q₁} {rQ₁ : U₁ ⟶ Q₁}
    {q₂ : Q₂ ⟶ G} {lQ₂ : M ⟶ Q₂} {rQ₂ : U₂ ⟶ Q₂}
    (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical rQ₁)
    (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical rQ₂)
    (hc₁ : lQ₁ ≫ q₁ = l ≫ p) (hc₂ : lQ₂ ≫ q₂ = l ≫ p)
    (pres₁ : ParabolicRootPresentation q₁ lQ₁ a)
    (pres₂ : ParabolicRootPresentation q₂ lQ₂ a)
    (hx₁ : x ∉ pres₁.positiveCone) (hx₂ : x ∉ pres₂.positiveCone) :
    SubgroupFunctor.range q₁ = SubgroupFunctor.range q₂ ∧
      SubgroupFunctor.range (rQ₁ ≫ q₁) = SubgroupFunctor.range (rQ₂ ≫ q₂) := by
  have hline₁ : ∀ y : Vstar A, (∀ ν : cocharacterLattice A,
      IsCentral (CommGroupScheme.groupHom ν ≫ a ≫ lQ₁ ≫ q₁) →
        pair A y ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0) → y ∈ Submodule.span ℝ {x} := by
    rw [hc₁]
    exact hline
  have hline₂ : ∀ y : Vstar A, (∀ ν : cocharacterLattice A,
      IsCentral (CommGroupScheme.groupHom ν ≫ a ≫ lQ₂ ≫ q₂) →
        pair A y ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0) → y ∈ Submodule.span ℝ {x} := by
    rw [hc₂]
    exact hline
  have he₁ := pres₁.splitComponentEvaluation_neg_of_line hG (by rw [hc₁]; exact hM)
    hline₁ hx₁
  have he₂ := pres₂.splitComponentEvaluation_neg_of_line hG (by rw [hc₂]; exact hM)
    hline₂ hx₂
  have hζ₁ : CommGroupScheme.groupHom
        (cocharacterMapInt pres₁.data.f pres₁.splitComponentCocharacter) ≫ pres₁.data.i =
      CommGroupScheme.groupHom pres₁.splitComponentCocharacter ≫ a ≫ lQ₁ ≫ q₁ :=
    pres₁.groupHom_cocharacterMapInt_comp _
  have hζ₂ : CommGroupScheme.groupHom
        (cocharacterMapInt pres₁.data.f pres₂.splitComponentCocharacter) ≫ pres₁.data.i =
      CommGroupScheme.groupHom pres₂.splitComponentCocharacter ≫ a ≫ lQ₂ ≫ q₂ := by
    rw [pres₁.groupHom_cocharacterMapInt_comp, hc₁, hc₂]
  have hpair : ∀ α ∈ relativeRoots pres₁.data.i, ∃ c : ℝ,
      (latticePairing pres₁.data.T α
          (cocharacterMapInt pres₁.data.f pres₁.splitComponentCocharacter) : ℝ) =
        c * pres₁.splitComponentEvaluation x ∧
      (latticePairing pres₁.data.T α
          (cocharacterMapInt pres₁.data.f pres₂.splitComponentCocharacter) : ℝ) =
        c * pres₂.splitComponentEvaluation x := by
    intro α hα
    obtain ⟨c, hc⟩ := exists_smul_eq_of_line hline₁ pres₁.data.i pres₁.data.f
      pres₁.isCompatible.factor_comp hα
    refine ⟨c, ?_, ?_⟩
    · rw [← RelativeRoot.latticePairing_restrict_cocharacterMapInt,
        ← pair_one_tmul_one_tmul, ← hc, map_smul, LinearMap.smul_apply, smul_eq_mul,
        ParabolicRootPresentation.splitComponentEvaluation_apply]
    · rw [← RelativeRoot.latticePairing_restrict_cocharacterMapInt,
        ← pair_one_tmul_one_tmul, ← hc, map_smul, LinearMap.smul_apply, smul_eq_mul,
        ParabolicRootPresentation.splitComponentEvaluation_apply]
  have hsign := relativeRootSignInclusions k G hG pres₁.data.T pres₁.data.i
    pres₁.isCompatible.maximalSplit
  have hnonneg : ∀ (z w : cocharacterLattice A) (ez ew : ℝ), ez < 0 → ew < 0 →
      (∀ α ∈ relativeRoots pres₁.data.i, ∃ c : ℝ,
        (latticePairing pres₁.data.T α (cocharacterMapInt pres₁.data.f z) : ℝ) = c * ez ∧
        (latticePairing pres₁.data.T α (cocharacterMapInt pres₁.data.f w) : ℝ) = c * ew) →
      (∀ α ∈ relativeRoots pres₁.data.i,
        0 ≤ latticePairing pres₁.data.T α (cocharacterMapInt pres₁.data.f z) →
          0 ≤ latticePairing pres₁.data.T α (cocharacterMapInt pres₁.data.f w)) ∧
      (∀ α ∈ relativeRoots pres₁.data.i,
        0 < latticePairing pres₁.data.T α (cocharacterMapInt pres₁.data.f z) →
          0 < latticePairing pres₁.data.T α (cocharacterMapInt pres₁.data.f w)) := by
    intro z w ez ew hz hw h
    constructor
    · intro α hα h0
      obtain ⟨c, h₁, h₂⟩ := h α hα
      have h0' : (0 : ℝ) ≤ (latticePairing pres₁.data.T α
          (cocharacterMapInt pres₁.data.f z) : ℝ) := by exact_mod_cast h0
      rw [h₁] at h0'
      have hc : c ≤ 0 := by nlinarith
      have : (0 : ℝ) ≤ (latticePairing pres₁.data.T α
          (cocharacterMapInt pres₁.data.f w) : ℝ) := by rw [h₂]; nlinarith
      exact_mod_cast this
    · intro α hα h0
      obtain ⟨c, h₁, h₂⟩ := h α hα
      have h0' : (0 : ℝ) < (latticePairing pres₁.data.T α
          (cocharacterMapInt pres₁.data.f z) : ℝ) := by exact_mod_cast h0
      rw [h₁] at h0'
      have hc : c < 0 := by nlinarith
      have : (0 : ℝ) < (latticePairing pres₁.data.T α
          (cocharacterMapInt pres₁.data.f w) : ℝ) := by rw [h₂]; nlinarith
      exact_mod_cast this
  have h₁₂ := hnonneg pres₁.splitComponentCocharacter pres₂.splitComponentCocharacter
    _ _ he₁ he₂ hpair
  have h₂₁ := hnonneg pres₂.splitComponentCocharacter pres₁.splitComponentCocharacter
    _ _ he₂ he₁ (fun α hα => (hpair α hα).imp fun _ h => h.symm)
  have hs₁₂ := hsign (cocharacterMapInt pres₁.data.f pres₁.splitComponentCocharacter)
    (cocharacterMapInt pres₁.data.f pres₂.splitComponentCocharacter)
  have hs₂₁ := hsign (cocharacterMapInt pres₁.data.f pres₂.splitComponentCocharacter)
    (cocharacterMapInt pres₁.data.f pres₁.splitComponentCocharacter)
  rw [hζ₁, hζ₂] at hs₁₂
  rw [hζ₁, hζ₂] at hs₂₁
  constructor
  · rw [pres₁.parabolic_eq_splitComponentCocharacter,
      pres₂.parabolic_eq_splitComponentCocharacter]
    exact le_antisymm (hs₁₂.1.mpr h₁₂.1) (hs₂₁.1.mpr h₂₁.1)
  · rw [pres₁.range_comp_radical_eq hr₁, pres₂.range_comp_radical_eq hr₂]
    exact le_antisymm (hs₁₂.2 h₁₂.2) (hs₂₁.2 h₂₁.2)

end MaximalLeviConeComplementLine

/-- For every actual maximal proper rational parabolic `P` of a connected reductive group,
with rational Levi `M` and split component `a : A ⟶ M`, every nonzero real character `x` of
`A` vanishing on the central cocharacters spans the whole annihilator of those
cocharacters in `Vstar A`. -/
def MaximalLeviCentralLineStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI := hG.smooth
    ∀ (P M : GroupScheme (Spec (CommRingCat.of k)))
      (A : CommGroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M),
      IsParabolicSubgroup p → IsRationalLeviSubgroup l → ¬ IsIso p →
      (∀ (Q' : GroupScheme (Spec (CommRingCat.of k))) (q' : Q' ⟶ G) (j : P ⟶ Q'),
        IsParabolicSubgroup q' → j ≫ q' = p → IsIso j ∨ IsIso q') →
      IsSplitComponent a →
      ∀ x : Vstar A, x ≠ 0 →
        (∀ ν : cocharacterLattice A, IsCentral (CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p) →
          pair A x ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0) →
        ∀ y : Vstar A, (∀ ν : cocharacterLattice A,
          IsCentral (CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p) →
            pair A y ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0) → y ∈ Submodule.span ℝ {x}

/-- The implication from the central-annihilator line property to the exact
`MaximalLeviConeComplementStatement`. -/
def MaximalLeviConeComplementFromLine : Prop :=
  MaximalLeviCentralLineStatement.{u} → MaximalLeviConeComplementStatement.{u}

namespace MaximalLeviConeComplementLine

/-- The line property implies the target statement; maximality, `x ≠ 0` and the vanishing
of `x` on central cocharacters are used only through the line property. -/
theorem maximalLeviConeComplement_of_line : MaximalLeviConeComplementFromLine.{u} := by
  intro hline k _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  intro P M A p l a hp hl hpp hmax ha x hx0 hx Q₁ U₁ Q₂ U₂ q₁ lQ₁ rQ₁ q₂ lQ₂ rQ₂ hr₁ hr₂
    hc₁ hc₂ pres₁ pres₂ hx₁ hx₂
  exact range_eq_of_line hG (range_comp_ne_top_of_not_isIso hp.isClosedSubgroup hpp l)
    (hline k G hG P M A p l a hp hl hpp hmax ha x hx0 hx) hr₁ hr₂ hc₁ hc₂ pres₁ pres₂ hx₁ hx₂

end MaximalLeviConeComplementLine

end Langlands.GroupScheme
