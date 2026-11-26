import Langlands.Global.ArthurRightCosetTower
import Langlands.Global.ArthurRelativeSigmaExpansion
import Langlands.Global.ArthurAlternatingConstantTerm
import Langlands.Global.ArthurSiegelPartitionProof
import Langlands.Global.ArthurParabolicSpacesProof
import Langlands.Global.ArthurTruncationFinitenessProof
import Langlands.Global.AdelicCompactConstantTermCovariance
import Langlands.Global.AdelicNormalizerConjugation
import Langlands.Representation.LanglandsClassification.StandardParabolicDatum

/-! # Arthur's regrouping of truncation using the relative partition -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj Classical

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces AdelicSiegelFactors Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {K : Subgroup (AdelicGroupPoints F G)}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (D : RelativeRootReflectionData i) (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

local notation "Δ" => simpleFinset ν hG hi
local notation "J" => Finset (characterLattice T)
local notation "Γ" => rationalSubgroup F G
local notation "A" => AdelicGroupPoints F G
local notation "PΓ" S => parabolicRationalSubgroup F (Standard.parabolicHom i ν (S : Set (characterLattice T)))
local notation "PImage" S => parabolicRationalImage (Standard.parabolicHom i ν (S : Set (characterLattice T)))
local notation "PQuot" S => ParabolicRationalCosets F (Standard.parabolicHom i ν (S : Set (characterLattice T)))
local notation "τ" => ArthurRelative.tau hG hi ν D
local notation "τ̂" => ArthurRelative.tauHat hG hi ν D
local notation "σ₀" => ArthurRelative.sigma hG hi ν D
local notation "H₀" => height hi hK hρ

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
private theorem subset_simpleRoots {S : J} (hS : S ⊆ Δ) :
    (S : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν :=
  fun _ h => (mem_simpleFinset hG hi).mp (hS h)

include hν in
/-- The hatted cutoff attached to a parabolic is invariant under its rational points. -/
theorem tauHat_height_mul_left {R : J} (hR : R ⊆ Δ) {r : A} (hr : r ∈ PImage R)
    (Tp : V T) (x : A) :
    τ̂ (R : Set (characterLattice T)) (simpleRelativeRoots i ν) (H₀ (r * x) - Tp) =
      τ̂ (R : Set (characterLattice T)) (simpleRelativeRoots i ν) (H₀ x - Tp) := by
  rw [ArthurRelative.tauHat_eq hG hi D _ (Set.Subset.rfl (s := simpleRelativeRoots i ν)),
    ArthurRelative.tauHat_eq hG hi D _ (Set.Subset.rfl (s := simpleRelativeRoots i ν))]
  have hdiff := height_sub_mem_span parabolicSpacesComparison hG hi hν D hK hρ
    (subset_simpleRoots hG hi hR) hr x
  have hweight (α : characterLattice T) (hα : α ∈ simpleRelativeRoots i ν \ (R : Set (characterLattice T))) :
      ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) α (H₀ (r * x) - H₀ x) = 0 := by
    have hle : Submodule.span ℝ (D.realCorootsOf (R : Set (characterLattice T))) ≤
        (ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) α).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨β, hβ, rfl⟩
      change D.realCoroot β ∈ (ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) α).ker
      have hne : α ≠ (β : characterLattice T) := fun he => hα.2 (he.symm ▸ hβ)
      rw [LinearMap.mem_ker, ArthurRelative.weight_coroot hG hi D hν Set.Subset.rfl hα.1 β
        (subset_simpleRoots hG hi hR hβ), ite_eq_right hne]
    exact LinearMap.mem_ker.mp (hle hdiff)
  congr 1
  apply propext
  have heq (α : characterLattice T) (hα : α ∈ simpleRelativeRoots i ν \ (R : Set (characterLattice T))) :
      ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) α (H₀ (r * x) - Tp) =
        ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) α (H₀ x - Tp) := by
    have hz := hweight α hα
    simp only [map_sub] at hz ⊢
    linarith
  exact ⟨fun h α hα => heq α hα ▸ h α hα, fun h α hα => (heq α hα).symm ▸ h α hα⟩

include hν in
/-- The constant term attached to a standard parabolic is invariant under its rational points. -/
theorem constantTerm_rationalImage_mul {S : J} (hS : S ⊆ Δ)
    (f : ContinuousRationalFunctions F G) {r : A} (hr : r ∈ PImage S) (x : A) :
    constantTerm F i ν (S : Set (characterLattice T)) (evaluate F G f) (r * x) =
      constantTerm F i ν (S : Set (characterLattice T)) (evaluate F G f) x := by
  let p := Standard.parabolicHom i ν (S : Set (characterLattice T))
  let j := Standard.unipotentToParabolic i ν (S : Set (characterLattice T))
  let U := Standard.unipotentScheme i ν (S : Set (characterLattice T))
  let Q := Standard.parabolicScheme i ν (S : Set (characterLattice T))
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  have hj : j ≫ p = Standard.unipotentHom i ν (S : Set (characterLattice T)) :=
    Standard.unipotentToParabolic_comp i ν _
  let : IsClosedImmersion (j ≫ p).hom.hom.left := hj.symm ▸
    Standard.isClosedSubgroup_unipotentHom i ν (S : Set (characterLattice T))
  have hU := (Standard.parabolicStructure i ν hG hi hν _ (subset_simpleRoots hG hi hS)).2.2.1
  have hr' : r ∈ (rationalSubgroup F Q).map (map F Q G p).toMonoidHom := by
    rw [← rationalImage_eq_map]
    exact (mem_parabolicRationalImage_iff _ _).mp hr
  obtain ⟨_, ⟨q, rfl⟩, rfl⟩ := hr'
  let z := (basePointEquiv (F := F) (G := Q)).symm q
  have heq : map F Q G p (rational F Q q) = innerAdelicPoint F G (z ≫ p.hom.hom) := by
    have hbase : rational F G (basePointEquiv (z ≫ p.hom.hom)) =
        innerAdelicPoint F G (z ≫ p.hom.hom) := rational_basePointEquiv _
    rw [← hbase, basePointEquiv_comp, ← map_rational, MulEquiv.apply_symm_apply]
  change subgroupConstantTerm F (Standard.unipotentHom i ν (S : Set (characterLattice T)))
    (evaluate F G f) (map F Q G p (rational F Q q) * x) = _
  have hrange := congrArg SubgroupFunctor.range hj.symm
  rw [heq, subgroupConstantTerm_eq_of_range_eq _ _ hrange,
    show constantTerm F i ν (S : Set (characterLattice T)) (evaluate F G f) x =
      subgroupConstantTerm F (j ≫ p) (evaluate F G f) x from
        subgroupConstantTerm_eq_of_range_eq _ _ hrange _ _]
  exact subgroupConstantTerm_rational_parabolic_mul p j hU f z x

private theorem cast_tsum_int_of_finite_support {I : Type*} {a : I → ℤ}
    (ha : (Function.support a).Finite) : (∑' j, (a j : ℂ)) = ((∑' j, a j : ℤ) : ℂ) := by
  classical
  have hz (j : I) (hj : j ∉ ha.toFinset) : a j = 0 := by simpa using hj
  rw [tsum_eq_sum (s := ha.toFinset) (fun j hj => by simp [hz j hj]),
    tsum_eq_sum (s := ha.toFinset) hz, Int.cast_sum]

variable (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
  (T₁ Tp : V T)

/-- The product of the truncated Siegel indicator and the relative chamber indicator. -/
def relativePartitionCoefficient (R S : J) (y : A) : ℤ :=
  siegelIndicator hG hi D hK hρ C R T₁ Tp y * τ (R : Set (characterLattice T)) S (H₀ y - Tp)

/-- The truncation summand with its sign, before inserting a relative partition. -/
def signedTruncationTerm (f : A → ℂ) (S : J) (y : A) : ℂ :=
  (-1 : ℂ) ^ ((Δ).card - S.card) * constantTerm F i ν (S : Set (characterLattice T)) f y *
    (τ̂ (S : Set (characterLattice T)) (simpleRelativeRoots i ν) (H₀ y - Tp) : ℂ)

include hν in
/-- Inserting the relative partition and regrouping give a sum on the smaller rational cosets. -/
theorem truncation_eq_relativePartitionSum (f : ContinuousRationalFunctions F G) (x : A)
    (hpart : ∀ S ∈ (Δ).powerset, ∀ g : A,
      (∀ R ∈ S.powerset, (Function.support (fun d : RelativeCosets (F := F) (i := i) (ν := ν)
        (R : Set (characterLattice T)) (S : Set (characterLattice T)) =>
          relativePartitionCoefficient hG hi D hK hρ C T₁ Tp R S
            ((((Quotient.out d : PΓ S) : Γ) : A) * g))).Finite) ∧
      ∑ R ∈ S.powerset, ∑' d : RelativeCosets (F := F) (i := i) (ν := ν)
        (R : Set (characterLattice T)) (S : Set (characterLattice T)),
          relativePartitionCoefficient hG hi D hK hρ C T₁ Tp R S
            ((((Quotient.out d : PΓ S) : Γ) : A) * g) = 1) :
    let a := signedTruncationTerm hG hi D hK hρ Tp (evaluate F G f)
    let b := relativePartitionCoefficient hG hi D hK hρ C T₁ Tp
    (∀ S ⊆ Δ, ∀ R ⊆ S, (Function.support (fun d : PQuot R =>
      τ̂ (S : Set (characterLattice T)) (simpleRelativeRoots i ν)
        (H₀ (((Quotient.out d : Γ) : A) * x) - Tp) * b R S (((Quotient.out d : Γ) : A) * x))).Finite) ∧
    (∀ S ⊆ Δ, ∀ R ⊆ S, (Function.support (fun d : PQuot R =>
      a S (((Quotient.out d : Γ) : A) * x) * (b R S (((Quotient.out d : Γ) : A) * x) : ℂ))).Finite) ∧
    truncation hG hi D hK hρ Tp (evaluate F G f) x =
      ∑ R ∈ (Δ).powerset, ∑ S ∈ (Δ).powerset.filter (R ⊆ ·), ∑' d : PQuot R,
        a S (((Quotient.out d : Γ) : A) * x) * (b R S (((Quotient.out d : Γ) : A) * x) : ℂ) := by
  intro a b
  let a' (S : J) (q : Γ) := a S ((q : A) * x)
  let b' (R S : J) (q : Γ) := (b R S ((q : A) * x) : ℂ)
  have hle (R S : J) (hRS : R ⊆ S) (hS : S ⊆ Δ) : (PΓ R) ≤ (PΓ S) := by
    intro q hq
    rw [mem_parabolicRationalSubgroup_iff_mem_parabolicRationalImage] at hq ⊢
    exact parabolicRationalImage_mono hG hi hν (show (R : Set (characterLattice T)) ⊆ S from hRS)
      (subset_simpleRoots hG hi hS) hq
  have ha (S : J) (hS : S ⊆ Δ) (p : Γ) (hp : p ∈ PΓ S) (g : Γ) : a' S (p * g) = a' S g := by
    have hp' := (mem_parabolicRationalSubgroup_iff_mem_parabolicRationalImage _).mp hp
    dsimp only [a', a, signedTruncationTerm]
    rw [Subgroup.coe_mul, mul_assoc (p : A) (g : A) x, constantTerm_rationalImage_mul hG hi hν hS f hp',
      tauHat_height_mul_left hG hi hν D hK hρ hS hp']
  have hb (S : J) (hS : S ⊆ Δ) (R : J) (hR : R ⊆ S) (p : Γ) (hp : p ∈ PΓ R) (g : Γ) :
      b' R S (p * g) = b' R S g := by
    have hp' := (mem_parabolicRationalSubgroup_iff_mem_parabolicRationalImage _).mp hp
    dsimp only [b', b, relativePartitionCoefficient]
    rw [Subgroup.coe_mul, mul_assoc (p : A) (g : A) x, siegelIndicator_mul_left hG hi D hK hρ C T₁ Tp R hp',
      tau_height_mul_left parabolicSpacesComparison hG hi hν D hK hρ Tp _
        (subset_simpleRoots hG hi (hR.trans hS)) hp']
  have hfin (S : J) (hS : S ⊆ Δ) : (Function.support (fun q : PQuot S => a' S (Quotient.out q))).Finite := by
    have h := truncationFiniteness F G T i ν hG hi hν D K hK hρ S (Finset.mem_powerset.mpr hS) Tp x
    refine h.subset (fun q hq hz => hq ?_)
    change τ̂ (S : Set (characterLattice T)) (simpleRelativeRoots i ν)
      (H₀ (((Quotient.out q : Γ) : A) * x) - Tp) = 0 at hz
    simp [a', a, signedTruncationTerm, hz]
  have hrel (S : J) (hS : S ⊆ Δ) (q : PQuot S) :
      (∀ R ⊆ S, (Function.support (fun d : RelativeCosets (F := F) (i := i) (ν := ν) R S =>
        b' R S ((Quotient.out d : PΓ S).val * Quotient.out q))).Finite) ∧
      ∑ R ∈ S.powerset, ∑' d : RelativeCosets (F := F) (i := i) (ν := ν) R S,
        b' R S ((Quotient.out d : PΓ S).val * Quotient.out q) = 1 := by
    obtain ⟨hf, he⟩ := hpart S (Finset.mem_powerset.mpr hS) (((Quotient.out q : Γ) : A) * x)
    refine ⟨fun R hR => (hf R (Finset.mem_powerset.mpr hR)).subset (fun d hd hz => hd ?_), ?_⟩
    · change b R S ((((Quotient.out d : PΓ S) : Γ) : A) * (((Quotient.out q : Γ) : A) * x)) = 0 at hz
      simp [b', Subgroup.coe_mul, mul_assoc, hz]
    have hcast := congrArg (fun k : ℤ => (k : ℂ)) he
    rw [Int.cast_sum, Int.cast_one] at hcast
    refine (Finset.sum_congr rfl (fun R hR => ?_)).trans hcast
    simpa only [b', Subgroup.coe_mul, mul_assoc] using cast_tsum_int_of_finite_support (hf R hR)
  let w (S : J) (q : Γ) : ℂ :=
    τ̂ (S : Set (characterLattice T)) (simpleRelativeRoots i ν) (H₀ ((q : A) * x) - Tp)
  have hwinv (S : J) (hS : S ⊆ Δ) (p : Γ) (hp : p ∈ PΓ S) (g : Γ) :
      w S (p * g) = w S g := by
    have hp' := (mem_parabolicRationalSubgroup_iff_mem_parabolicRationalImage _).mp hp
    dsimp only [w]
    rw [Subgroup.coe_mul, mul_assoc (p : A) (g : A) x,
      tauHat_height_mul_left hG hi hν D hK hρ hS hp']
  have hwfin (S : J) (hS : S ⊆ Δ) : (Function.support (fun q : PQuot S => w S (Quotient.out q))).Finite :=
    (truncationFiniteness F G T i ν hG hi hν D K hK hρ S (Finset.mem_powerset.mpr hS) Tp x).subset
      (fun q hq hz => hq (by simp only [w, hz, Int.cast_zero]))
  have hweight :=
    (rightCosetPartitionRegrouping _ Γ Δ (fun S => PΓ S) w b' hle hwinv hb hwfin hrel).1
  refine ⟨fun S hS R hR => (hweight S hS R hR).subset ?_, ?_⟩
  · intro d hd hzero
    apply hd
    simpa only [w, b', ← Int.cast_mul, Int.cast_eq_zero] using hzero
  obtain ⟨hsupport, heq⟩ := rightCosetPartitionRegrouping _ Γ Δ (fun S => PΓ S) a' b'
    hle ha hb hfin hrel
  refine ⟨hsupport, ?_⟩
  refine Eq.trans ?_ heq
  unfold truncation
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← tsum_mul_left]
  exact tsum_congr fun d => (mul_assoc _ _ _).symm

/-- The product of the truncated Siegel indicator and sigma. -/
def siegelSigmaCoefficient (R S : J) (y : A) : ℤ :=
  siegelIndicator hG hi D hK hρ C R T₁ Tp y * σ₀ (R : Set (characterLattice T)) S (H₀ y - Tp)

include hν in
/-- The expansion (13.7) with the two cutoffs, as finite-support sums on rational cosets. -/
theorem truncation_eq_siegelSigmaSum (f : ContinuousRationalFunctions F G) (x : A)
    (hpart : ∀ S ∈ (Δ).powerset, ∀ g : A,
      (∀ R ∈ S.powerset, (Function.support (fun d : RelativeCosets (F := F) (i := i) (ν := ν)
        (R : Set (characterLattice T)) (S : Set (characterLattice T)) =>
          relativePartitionCoefficient hG hi D hK hρ C T₁ Tp R S
            ((((Quotient.out d : PΓ S) : Γ) : A) * g))).Finite) ∧
      ∑ R ∈ S.powerset, ∑' d : RelativeCosets (F := F) (i := i) (ν := ν)
        (R : Set (characterLattice T)) (S : Set (characterLattice T)),
          relativePartitionCoefficient hG hi D hK hρ C T₁ Tp R S
            ((((Quotient.out d : PΓ S) : Γ) : A) * g) = 1) :
    let W := siegelSigmaCoefficient hG hi D hK hρ C T₁ Tp
    (∀ S ⊆ Δ, ∀ R ⊆ S, (Function.support (fun d : PQuot R =>
      W R S (((Quotient.out d : Γ) : A) * x))).Finite) ∧
    truncation hG hi D hK hρ Tp (evaluate F G f) x =
      ∑ R ∈ (Δ).powerset, ∑ S ∈ (Δ).powerset.filter (R ⊆ ·), ∑' d : PQuot R,
        (W R S (((Quotient.out d : Γ) : A) * x) : ℂ) *
          alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f) (((Quotient.out d : Γ) : A) * x) := by
  intro W
  obtain ⟨hweight, hterm, heq⟩ :=
    truncation_eq_relativePartitionSum hG hi hν D hK hρ C T₁ Tp f x hpart
  let b := relativePartitionCoefficient hG hi D hK hρ C T₁ Tp
  let y (R : J) (d : PQuot R) := ((Quotient.out d : Γ) : A) * x
  let kept (R : J) := (Δ).powerset.filter (R ⊆ ·)
  let a (R S : J) (d : PQuot R) := τ̂ (S : Set (characterLattice T)) (simpleRelativeRoots i ν)
    (H₀ (y R d) - Tp) * b R S (y R d)
  have ha (S : J) (hS : S ⊆ Δ) (R : J) (hR : R ⊆ S) :
      (Function.support (a R S)).Finite := hweight S hS R hR
  have hW (S : J) (hS : S ⊆ Δ) (R : J) (hR : R ⊆ S) :
      (Function.support (fun d : PQuot R => W R S (y R d))).Finite := by
    have hU : (⋃ P ∈ (kept R : Set J), Function.support (a R P)).Finite := by
      refine (kept R).finite_toSet.biUnion (fun P hP => ?_)
      obtain ⟨hPΔ, hRP⟩ := Finset.mem_filter.mp hP
      exact ha P (Finset.mem_powerset.mp hPΔ) R hRP
    refine hU.subset fun d hd => ?_
    by_contra hnot
    apply hd
    change W R S (y R d) = 0
    dsimp only [W, siegelSigmaCoefficient]
    rw [arthurRelative_sigma_eq_sum hG hi hν D R S hS, Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro P hP
    obtain ⟨hPΔ, hSP⟩ := Finset.mem_filter.mp hP
    have hPR : P ∈ kept R := Finset.mem_filter.mpr ⟨hPΔ, hR.trans hSP⟩
    have hzero : a R P d = 0 := not_not.mp (fun hn =>
      hnot (Set.mem_iUnion₂.mpr ⟨P, hPR, hn⟩))
    calc
      _ = (-1 : ℤ) ^ (P \ S).card * a R P d := by dsimp only [a, b, relativePartitionCoefficient]; ring
      _ = _ := by rw [hzero, mul_zero]
  refine ⟨hW, Eq.trans heq ?_⟩
  refine Finset.sum_congr rfl fun R _ => ?_
  let c (P : J) (z : A) :=
    (-1 : ℂ) ^ ((Δ).card - P.card) * constantTerm F i ν (P : Set (characterLattice T)) (evaluate F G f) z
  let L (P : J) (d : PQuot R) := signedTruncationTerm hG hi D hK hρ Tp (evaluate F G f) P (y R d) *
    (b R P (y R d) : ℂ)
  let U (P : J) (d : PQuot R) :=
    (W R P (y R d) : ℂ) * alternatingConstantTerm (ν := ν) hG hi R P (evaluate F G f) (y R d)
  have hlsum (P : J) (hP : P ∈ kept R) : Summable (L P) := by
    obtain ⟨hPΔ, hRP⟩ := Finset.mem_filter.mp hP
    exact summable_of_hasFiniteSupport
      (hterm P (Finset.mem_powerset.mp hPΔ) R hRP)
  have husum (P : J) (hP : P ∈ kept R) : Summable (U P) := by
    obtain ⟨hPΔ, hRP⟩ := Finset.mem_filter.mp hP
    apply summable_of_hasFiniteSupport
    refine (hW P (Finset.mem_powerset.mp hPΔ) R hRP).subset fun d hd hz => hd ?_
    change W R P (y R d) = 0 at hz
    simp only [U, hz, Int.cast_zero, zero_mul]
  change (∑ P ∈ kept R, ∑' d, L P d) = ∑ P ∈ kept R, ∑' d, U P d
  rw [← Summable.tsum_finsetSum hlsum, ← Summable.tsum_finsetSum husum]
  apply tsum_congr
  intro d
  let z := y R d
  let F₁ := (siegelIndicator hG hi D hK hρ C R T₁ Tp z : ℂ)
  let σc (P : J) := (σ₀ (R : Set (characterLattice T)) P (H₀ z - Tp) : ℂ)
  calc
    _ = ∑ P ∈ kept R, ∑ Q ∈ (Δ).powerset.filter (P ⊆ ·), (F₁ * σc Q) * c P z := by
      refine Finset.sum_congr rfl fun P hP => ?_
      obtain ⟨hPΔ, hRP⟩ := Finset.mem_filter.mp hP
      have he := congrArg (fun n : ℤ => (n : ℂ))
        (arthurRelative_tau_mul_tauHat_eq_sum_sigma hG hi hν D R P hRP
          (Finset.mem_powerset.mp hPΔ) (H₀ z - Tp))
      rw [Int.cast_mul, Int.cast_sum] at he
      simp only [← Finset.sum_mul, ← Finset.mul_sum, σc, ← he, L, signedTruncationTerm,
        b, relativePartitionCoefficient, Int.cast_mul, c, F₁, z]
      ring
    _ = ∑ Q ∈ kept R, ∑ P ∈ Q.powerset.filter (R ⊆ ·), (F₁ * σc Q) * c P z := by
      refine Finset.sum_comm' fun P Q => ?_
      simp only [kept, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨⟨hPΔ, hRP⟩, hQΔ, hPQ⟩
        exact ⟨⟨hPQ, hRP⟩, hQΔ, hRP.trans hPQ⟩
      · rintro ⟨⟨hPQ, hRP⟩, hQΔ, hRQ⟩
        exact ⟨⟨hPQ.trans hQΔ, hRP⟩, hQΔ, hPQ⟩
    _ = _ := by
      refine Finset.sum_congr rfl fun P _ => ?_
      simp only [← Finset.mul_sum, U, W, siegelSigmaCoefficient, Int.cast_mul, F₁, σc, z, c,
        alternatingConstantTerm]

/-- Under the covering and reduction conditions, the finite-support
sigma expansion holds once the truncation parameter is sufficiently regular. -/
def ArthurTruncationSigmaExpansionStatement : Prop :=
  C.compactSubgroup = K → IsSiegelCovering hG hi hK hρ C T₁ →
  IsSiegelReductionLemma hG hi hK hρ →
  ∃ c : ℝ, ∀ T' : V T, (∀ α ∈ simpleRelativeRoots i ν, c < eval T α T') →
    ∀ (f : ContinuousRationalFunctions F G) (x : A),
      let W := siegelSigmaCoefficient hG hi D hK hρ C T₁ T'
      (∀ S ⊆ Δ, ∀ R ⊆ S, (Function.support (fun d : PQuot R =>
        W R S (((Quotient.out d : Γ) : A) * x))).Finite) ∧
      truncation hG hi D hK hρ T' (evaluate F G f) x =
        ∑ R ∈ (Δ).powerset, ∑ S ∈ (Δ).powerset.filter (R ⊆ ·), ∑' d : PQuot R,
          (W R S (((Quotient.out d : Γ) : A) * x) : ℂ) *
            alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f) (((Quotient.out d : Γ) : A) * x)

include hν in
theorem arthurTruncationSigmaExpansion : ArthurTruncationSigmaExpansionStatement hG hi D hK hρ C T₁ := by
  intro hC hcover hred
  obtain ⟨c, hRel⟩ := isRelativeSiegelPartition_of_reduction parabolicSpacesComparison hG hi hν D hK hρ
    hred C T₁ hC hcover
  exact ⟨c, fun T' hT' f x => truncation_eq_siegelSigmaSum hG hi hν D hK hρ C T₁ T' f x
    (fun S hS y => by simpa only [relativePartitionCoefficient] using hRel T' hT' S hS y)⟩

end Langlands.Global.ArthurTruncation
