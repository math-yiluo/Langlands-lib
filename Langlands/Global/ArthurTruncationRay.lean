import Langlands.Global.ArthurTruncationStatement
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof
import Langlands.LinearAlgebra.ArthurCombinatoricsSigma

/-! # Pointwise exhaustion by Arthur truncation on a regular ray

Finiteness of the cutoff support at parameter zero suffices for eventual pointwise equality.
This is a pointwise substitute for the exhausting Siegel-region identity in Lapid 2011, Lemma 9.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Filter TensorProduct
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces

section Weights

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)

include hν in
/-- Strict positivity of the simple roots implies strict positivity of the corresponding full
fundamental weights. -/
theorem fullWeight_pos_of_simple_pos {v : V T}
    (hv : ∀ β ∈ simpleRelativeRoots i ν, 0 < eval T β v)
    {β : characterLattice T} (hβ : β ∈ simpleRelativeRoots i ν) :
    0 < ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) β v := by
  classical
  let Δ := simpleRelativeRoots i ν
  let I := ArthurRelative.standardIndex hG hi ν Δ
  let P := ArthurRelative.rootPairing hG hi D
  let Y := ArthurRelative.toCorootSpan hG hi D v
  let b := ArthurRelative.base hG hi hν D
  let : Finite (RelativeRoot.indivisibleRoots i) := ArthurRelative.finite_indivisibleRoots hG hi
  have heval (α : RelativeRoot.indivisibleRoots i) : P.root' α Y = eval T α v := by
    have he := ArthurRelative.eval_sub_toCorootSpan hG hi D α.2.1 v
    rw [map_sub, sub_eq_zero] at he
    change pair T ((P.root α : relativeRootSpanReal i) : Vstar T) (Y : V T) = _
    rw [ArthurRelative.rootPairing_root, ← eval_eq_pair, ← he]
  let β' : RelativeRoot.indivisibleRoots i :=
    ⟨β, ArthurRelative.simpleRelativeRoots_subset_indivisibleRoots hG hi ν hβ⟩
  have hβ' : β' ∈ I := (ArthurRelative.mem_standardIndex hG hi ν).2 ⟨hβ, hβ⟩
  have hpos (α : RelativeRoot.indivisibleRoots i) (hα : α ∈ I) : 0 < P.root' α Y := by
    rw [heval]
    exact hv α ((ArthurRelative.mem_standardIndex hG hi ν).1 hα).1
  change 0 < ArthurRelative.weight hG hi ν D Δ (β' : characterLattice T) v
  rw [ArthurRelative.weight_coe]
  exact ArthurCombinatorics.weightCoordinate_pos b
    (ArthurRelative.standardIndex_subset_support hG hi D hν Δ) hβ'
    (fun α hα => (hpos α hα).le) (hpos β' hβ')

omit [Mono i.hom.hom.left] in
/-- The real image of the chosen positive cocharacter is a regular direction for the simple
roots. When the simple-root set is empty, the condition is vacuous. -/
theorem cocharacter_simple_pos {β : characterLattice T} (hβ : β ∈ simpleRelativeRoots i ν) :
    0 < eval T β ((1 : ℝ) ⊗ₜ[ℤ] ν) := by
  rw [eval_tmul, one_mul, Int.cast_pos]
  exact (simpleRelativeRoots_subset_positive i ν hβ).2

private theorem tauHat_ne_zero_iff (J : Set (characterLattice T)) (H : V T) :
    ArthurRelative.tauHat hG hi ν D J (simpleRelativeRoots i ν) H ≠ 0 ↔
      ∀ β ∈ simpleRelativeRoots i ν \ J,
        0 < ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) β H := by
  classical
  rw [ArthurRelative.tauHat_eq hG hi D (ν := ν) J Set.Subset.rfl]
  split <;> simp_all

/-- A proper parabolic cutoff with finite support at zero is identically zero, on these same
height arguments, eventually along the ray. The height arguments need not be distinct. -/
private theorem eventually_tauHat_eq_zero_of_finite {C : Type*} (H : C → V T)
    {J : Set (characterLattice T)} {β : characterLattice T} (hβ : β ∈ simpleRelativeRoots i ν \ J)
    {v : V T} (hv : ∀ α ∈ simpleRelativeRoots i ν,
      0 < ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) α v)
    (hf : {c | ArthurRelative.tauHat hG hi ν D J (simpleRelativeRoots i ν) (H c) ≠ 0}.Finite) :
    ∀ᶠ n : ℕ in atTop, ∀ c,
      ArthurRelative.tauHat hG hi ν D J (simpleRelativeRoots i ν) (H c - (n : ℝ) • v) = 0 := by
  let w := ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν)
  have hpos := hv β hβ.1
  have hvan : ∀ᶠ n : ℕ in atTop,
      ∀ c ∈ {c | ArthurRelative.tauHat hG hi ν D J (simpleRelativeRoots i ν) (H c) ≠ 0},
        w β (H c - (n : ℝ) • v) ≤ 0 := by
    refine (eventually_all_finite hf).2 fun c _ => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (w β (H c) / w β v)
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [map_sub, map_smul, smul_eq_mul]
    exact sub_nonpos.mpr ((div_lt_iff₀ hpos).mp (hN.trans_le (Nat.cast_le.mpr hn))).le
  filter_upwards [hvan] with n hn c
  by_contra hc
  have h := (tauHat_ne_zero_iff hG hi D J _).1 hc
  have hc₀ : c ∈ {c | ArthurRelative.tauHat hG hi ν D J (simpleRelativeRoots i ν) (H c) ≠ 0} := by
    refine (tauHat_ne_zero_iff hG hi D J _).2 ?_
    intro α hα
    have h' := h α hα
    rw [map_sub, map_smul, smul_eq_mul] at h'
    exact h'.trans_le (sub_le_self _ (mul_nonneg (Nat.cast_nonneg n) (hv α hα.1).le))
  exact (not_lt_of_ge (hn c hc₀)) (h β hβ)

end Weights

section Endpoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine P.X.left]

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left] in
private theorem parabolicRationalSubgroup_eq_top_of_range_eq_top (p : P ⟶ G)
    [IsClosedImmersion p.hom.hom.left] (hp : SubgroupFunctor.range p = ⊤) :
    parabolicRationalSubgroup F p = ⊤ := by
  apply top_unique
  rintro ⟨g, ⟨q, rfl⟩⟩ _
  have hq : q ∈ (SubgroupFunctor.range p).carrier _ := by rw [hp]; exact Subgroup.mem_top q
  rcases SubgroupFunctor.mem_range.mp hq with ⟨a, ha⟩
  change rational F G q ∈ (rationalSubgroup F P).map (map F P G p).toMonoidHom
  refine ⟨rational F P a, ⟨a, rfl⟩, ?_⟩
  have h := DFunLike.congr_fun (rational_naturality F P p) a
  change rational F G (a ≫ p.hom.hom) = map F P G p (rational F P a) at h
  exact h.symm.trans (congrArg (rational F G) ha)

private theorem subgroupConstantTerm_eq_of_range_eq_bot (j : P ⟶ G)
    [IsClosedImmersion j.hom.hom.left] (hj : SubgroupFunctor.range j = ⊥)
    (φ : AdelicGroupPoints F G → ℂ) (x : AdelicGroupPoints F G) :
    subgroupConstantTerm F j φ x = φ x := by
  let U := SubgroupFunctor.range j
  let A := AdelicSubgroupPoints.adelicPoints F G U
  let Q := AdelicSubgroupPoints.RationalQuotient F G U
  let : IsClosed (A : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  have hbot : A = ⊥ := by
    change AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) = ⊥
    rw [hj]
    rfl
  have hone (y : A) : (y : AdelicGroupPoints F G) = 1 :=
    Subgroup.mem_bot.mp ((congrArg (fun B : Subgroup (AdelicGroupPoints F G) =>
      (y : AdelicGroupPoints F G) ∈ B) hbot).mp y.property)
  let : Subsingleton A := ⟨fun y z => Subtype.ext ((hone y).trans (hone z).symm)⟩
  let : Subsingleton Q := ⟨fun a b => Quotient.inductionOn₂ a b fun y z =>
    congrArg (fun p => (Quotient.mk'' p : Q)) (Subsingleton.elim y z)⟩
  let : CompactSpace Q := inferInstance
  let μU := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U
  let : IsProbabilityMeasure μU :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
  change (∫ q : Q, φ (((q.out : A) : AdelicGroupPoints F G) * x) ∂μU) = φ x
  simp only [hone, one_mul]
  rw [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

include hν in
private theorem full_truncation_summand (Tp : V T) (φ : AdelicGroupPoints F G → ℂ)
    (hφ : ∀ g ∈ rationalSubgroup F G, ∀ x, φ (g * x) = φ x) (x : AdelicGroupPoints F G) :
    (∑' c : ParabolicRationalCosets F (Standard.parabolicHom i ν (simpleRelativeRoots i ν)),
      constantTerm F i ν (simpleRelativeRoots i ν) φ
          (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * x) *
        (ArthurRelative.tauHat hG hi ν D (simpleRelativeRoots i ν) (simpleRelativeRoots i ν)
          (height hi hK hρ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * x) - Tp) : ℂ))
      = φ x := by
  classical
  let Δ := simpleRelativeRoots i ν
  let p := Standard.parabolicHom i ν Δ
  have htop : SubgroupFunctor.range p = ⊤ :=
    (Standard.isRepresentedBy_parabolicHom i ν Δ).2.trans
      (standardParabolicEndpoints F G hG T i hi ν hν).2.2.1
  have hbot : SubgroupFunctor.range (Standard.unipotentHom i ν Δ) = ⊥ :=
    (Standard.isRepresentedBy_unipotentHom i ν Δ).2.trans (standardUnipotent_simple_eq_bot i ν)
  have hr : parabolicRationalSubgroup F p = ⊤ :=
    parabolicRationalSubgroup_eq_top_of_range_eq_top p htop
  have hone (H : V T) : ArthurRelative.tauHat hG hi ν D Δ Δ H = 1 := by
    rw [ArthurRelative.tauHat_eq hG hi D (ν := ν) Δ Set.Subset.rfl H]
    simp [Δ]
  let c₀ : ParabolicRationalCosets F p := Quotient.mk'' (1 : rationalSubgroup F G)
  change (∑' c : ParabolicRationalCosets F p, _) = _
  rw [tsum_eq_single c₀]
  · rw [hone, Int.cast_one, mul_one]
    change subgroupConstantTerm F (Standard.unipotentHom i ν Δ) φ _ = _
    rw [subgroupConstantTerm_eq_of_range_eq_bot _ hbot]
    exact hφ _ (Quotient.out c₀).property x
  · intro c hc
    exfalso
    apply hc
    rw [← Quotient.out_eq c]
    apply Quotient.sound
    change QuotientGroup.rightRel (parabolicRationalSubgroup F p) c.out 1
    rw [QuotientGroup.rightRel_apply]
    generalize (1 * c.out⁻¹ : rationalSubgroup F G) = g
    rw [hr]
    exact Subgroup.mem_top g

end Endpoints

/-- Pointwise consequence of cutoff finiteness: along the natural-number ray in any direction
strictly positive on the simple roots, Arthur truncation eventually fixes each value of a
left-rational-invariant function. The pointwise threshold can depend on `x`. -/
def TruncationRayStatement : Prop :=
  TruncationFinitenessStatement.{u} →
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν → ∀ (D : RelativeRootReflectionData i)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅))
    (v : V T), (∀ β ∈ simpleRelativeRoots i ν, 0 < eval T β v) →
    ∀ (φ : AdelicGroupPoints F G → ℂ),
      (∀ g ∈ rationalSubgroup F G, ∀ x, φ (g * x) = φ x) →
      ∀ x, ∀ᶠ n : ℕ in atTop, truncation hG hi D hK hρ ((n : ℝ) • v) φ x = φ x

theorem truncationRay : TruncationRayStatement.{u} := by
  intro hfin F _ _ G _ _ T i _ ν hG hi hν D K hK hρ v hv φ hφ x
  classical
  let Δ := simpleFinset ν hG hi
  have hΔ : (Δ : Set (characterLattice T)) = simpleRelativeRoots i ν := by
    ext β
    exact mem_simpleFinset (ν := ν) hG hi
  let H (S : Finset (characterLattice T))
      (c : ParabolicRationalCosets F (Standard.parabolicHom i ν (S : Set (characterLattice T)))) :=
    height hi hK hρ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * x)
  have hw (β : characterLattice T) (hβ : β ∈ simpleRelativeRoots i ν) :
      0 < ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) β v :=
    fullWeight_pos_of_simple_pos hG hi hν D hv hβ
  have hex : ∀ᶠ n : ℕ in atTop, ∀ S ∈ Δ.powerset.erase Δ, ∀ c,
      ArthurRelative.tauHat hG hi ν D (S : Set (characterLattice T)) (simpleRelativeRoots i ν)
        (H S c - (n : ℝ) • v) = 0 := by
    refine (eventually_all_finset _).2 fun S hS => ?_
    obtain ⟨hne, hS⟩ := Finset.mem_erase.mp hS
    have hsub := Finset.mem_powerset.mp hS
    obtain ⟨β, hβ, hnβ⟩ := Finset.not_subset.mp (fun h => hne (Finset.Subset.antisymm hsub h))
    exact eventually_tauHat_eq_zero_of_finite hG hi D (H S)
      (β := β) ⟨hΔ ▸ hβ, hnβ⟩ hw (by
        simpa only [H, sub_zero] using hfin F G T i ν hG hi hν D K hK hρ S hS 0 x)
  filter_upwards [hex] with n hn
  let term (S : Finset (characterLattice T)) : ℂ :=
    (-1 : ℂ) ^ (Δ.card - S.card) *
      ∑' c : ParabolicRationalCosets F (Standard.parabolicHom i ν (S : Set (characterLattice T))),
        constantTerm F i ν (S : Set (characterLattice T)) φ
          (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * x) *
        (ArthurRelative.tauHat hG hi ν D (S : Set (characterLattice T))
          (simpleRelativeRoots i ν) (H S c - (n : ℝ) • v) : ℂ)
  change (∑ S ∈ Δ.powerset, term S) = φ x
  rw [Finset.sum_eq_single_of_mem Δ (Finset.mem_powerset.mpr subset_rfl)]
  · simp only [term, Nat.sub_self, pow_zero, one_mul]
    change (∑' c : ParabolicRationalCosets F (Standard.parabolicHom i ν (Δ : Set _)),
      constantTerm F i ν (Δ : Set _) φ
          (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * x) *
        (ArthurRelative.tauHat hG hi ν D (Δ : Set _) (simpleRelativeRoots i ν)
          (height hi hK hρ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * x) -
            (n : ℝ) • v) : ℂ)) = φ x
    rw [hΔ]
    exact full_truncation_summand hG hi hν D hK hρ _ φ hφ x
  · intro S hS hne
    have hzero := hn S (Finset.mem_erase.mpr ⟨hne, hS⟩)
    simp only [term, hzero, Int.cast_zero, mul_zero, tsum_zero]

end Langlands.Global.ArthurTruncation
