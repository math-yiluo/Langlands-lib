import Langlands.GroupScheme.Rational.StandardLeviWeylStatements
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof
import Langlands.GroupScheme.Rational.StandardParabolicClassificationProof
import Langlands.GroupScheme.Rational.StandardParabolicPointsProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.GroupScheme.Rational.StandardAssociatedConjugation
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.Group.RelativeWeylSolomonProof
import Langlands.Representation.Aubert.General.RationalRankOneNormalizingWeyl

/-! # Proof of Renard V.4.8: maximal standard Levi subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

namespace StandardMaximalLeviWeyl

/-! ### Conjugation of subgroups -/

/-- Conjugating by a product is conjugating by the second factor, then by the first. -/
theorem map_conj_mul {M : Type*} [Group M] (H : Subgroup M) (x y : M) :
    H.map (MulAut.conj (x * y) : M →* M) =
      (H.map (MulAut.conj y : M →* M)).map (MulAut.conj x : M →* M) := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  change x * y * z * (x * y)⁻¹ = x * (y * z * y⁻¹) * x⁻¹
  group

/-- Conjugation by a member of a subgroup maps the subgroup onto itself. -/
theorem map_conj_eq_self_of_mem {M : Type*} [Group M] {H : Subgroup M} {x : M}
    (hx : x ∈ H) : H.map (MulAut.conj x : M →* M) = H := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change x * z * x⁻¹ ∈ H
    exact H.mul_mem (H.mul_mem hx hz) (H.inv_mem hx)
  · intro hy
    refine ⟨x⁻¹ * y * x, H.mul_mem (H.mul_mem (H.inv_mem hx) hy) hx, ?_⟩
    change x * (x⁻¹ * y * x) * x⁻¹ = y
    group

/-- If conjugation by `x` maps `H` onto `K`, conjugation by `x⁻¹` maps `K` onto `H`. -/
theorem map_conj_inv_of_map_conj_eq {M : Type*} [Group M] {H K : Subgroup M} {x : M}
    (h : H.map (MulAut.conj x : M →* M) = K) : K.map (MulAut.conj x⁻¹ : M →* M) = H := by
  rw [← h, ← map_conj_mul, inv_mul_cancel, map_conj_eq_self_of_mem H.one_mem]

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-! ### Conjugating cocharacters by normalizer points -/

/-- The cocharacter of `T` obtained from `ζ` by conjugation with a normalizer point. -/
abbrev conjCochar (n : normalizerPoints i) (ζ : cocharacterLattice T) : cocharacterLattice T :=
  cocharacterAut (normalizingAut i n) ζ

omit [IsAffineHom G.X.hom] in
theorem latticePairing_conjCochar (n : normalizerPoints i) (ζ : cocharacterLattice T)
    (α : characterLattice T) :
    latticePairing T α (conjCochar i n ζ) =
      latticePairing T ((weylAction i n).symm α) ζ := by
  have h := latticePairing_characterAut_cocharacterAut (normalizingAut i n)
    ((weylAction i n).symm α) ζ
  have h2 : characterAut (normalizingAut i n) ((weylAction i n).symm α) = α :=
    (weylAction i n).apply_symm_apply α
  rw [h2] at h
  exact h

omit [IsAffineHom G.X.hom] [Mono i.hom.hom.left] in
theorem parabolic_conjCochar_points (n : normalizerPoints i) (ζ : cocharacterLattice T) :
    ((Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)).carrier (Over.mk (𝟙 _))).map
        (MulAut.conj (n : RationalPoint k G.X) : RationalPoint k G.X →* RationalPoint k G.X) =
      (Dynamic.parabolic (CommGroupScheme.groupHom (conjCochar i n ζ) ≫ i)).carrier
        (Over.mk (𝟙 _)) := by
  rw [groupHom_cocharacterAut_comp]
  exact (Dynamic.rationalPoints_parabolic_conjugate _ _).symm

omit [IsAffineHom G.X.hom] [Mono i.hom.hom.left] in
theorem parabolic_eq_comap_conjCochar (n : normalizerPoints i) (ζ : cocharacterLattice T) :
    Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) =
      (Dynamic.parabolic (CommGroupScheme.groupHom (conjCochar i n ζ) ≫ i)).comap
        (G.innerIso (n : RationalPoint k G.X)).hom := by
  rw [groupHom_cocharacterAut_comp]
  exact Dynamic.parabolic_eq_comap_of_iso _ _

variable {i} {ν : cocharacterLattice T}

/-! ### The standard Weyl subgroups and standard cocharacters -/

/-- Elements of `W_J` preserve the pairing with every cocharacter vanishing on `J`. -/
theorem pairing_action_eq_of_mem_standard {M : CoxeterMatrix (SimpleRoot i ν)}
    {cs : CoxeterSystem M (relativeWeylGroup i)} (h : IsRelativeWeylCoxeterRealization i ν cs)
    {J : Finset (SimpleRoot i ν)} {lam : cocharacterLattice T}
    (hlam : ∀ b ∈ J, latticePairing T b.1 lam = 0)
    {u : relativeWeylGroup i} (hu : u ∈ standardRelativeWeylGroup i ν (rootSet i ν J))
    (χ : characterLattice T) :
    latticePairing T (schemeWeylCharacterAction i u χ) lam = latticePairing T χ lam := by
  rw [← h.2.2.2.2 J] at hu
  induction hu using Subgroup.closure_induction generalizing χ with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨f, -, hf⟩ := h.1 b
    rw [hf, map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, hlam b hb,
      smul_zero, sub_zero]
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul, LinearEquiv.mul_apply, hx, hy]
  | inv x _ hx =>
    have h1 := hx (schemeWeylCharacterAction i x⁻¹ χ)
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h1
    exact h1.symm

/-- If `w s_a w⁻¹ ∈ W_J`, every cocharacter vanishing on `J` vanishes on `w a`. -/
theorem pairing_action_simple_eq_zero {M : CoxeterMatrix (SimpleRoot i ν)}
    {cs : CoxeterSystem M (relativeWeylGroup i)} (h : IsRelativeWeylCoxeterRealization i ν cs)
    {J : Finset (SimpleRoot i ν)} {lam : cocharacterLattice T}
    (hlam : ∀ b ∈ J, latticePairing T b.1 lam = 0)
    (w : relativeWeylGroup i) (a : SimpleRoot i ν)
    (hw : w * cs.simple a * w⁻¹ ∈ standardRelativeWeylGroup i ν (rootSet i ν J)) :
    latticePairing T (schemeWeylCharacterAction i w a.1) lam = 0 := by
  have h1 := pairing_action_eq_of_mem_standard h hlam hw (schemeWeylCharacterAction i w a.1)
  obtain ⟨f, hfa, hf⟩ := h.1 a
  have hs : schemeWeylCharacterAction i (w * cs.simple a * w⁻¹)
      (schemeWeylCharacterAction i w a.1) = -(schemeWeylCharacterAction i w a.1) := by
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      ← LinearEquiv.mul_apply (schemeWeylCharacterAction i w⁻¹), ← map_mul, inv_mul_cancel,
      map_one]
    change schemeWeylCharacterAction i w (schemeWeylCharacterAction i (cs.simple a) a.1) = _
    rw [hf, hfa]
    rw [show a.1 - (2 : ℤ) • a.1 = -a.1 by rw [two_smul]; abel, map_neg]
  rw [hs, map_neg, LinearMap.neg_apply] at h1
  omega

/-- A simple reflection in `W_K` is indexed by `K`. -/
theorem mem_of_simple_mem_standard [Fintype (SimpleRoot i ν)] {M : CoxeterMatrix (SimpleRoot i ν)}
    {cs : CoxeterSystem M (relativeWeylGroup i)} (h : IsRelativeWeylCoxeterRealization i ν cs)
    {K : Finset (SimpleRoot i ν)} {x : SimpleRoot i ν}
    (hx : cs.simple x ∈ standardRelativeWeylGroup i ν (rootSet i ν K)) : x ∈ K := by
  rw [← h.2.2.2.2 K] at hx
  exact mem_of_simple_mem_standardSubgroup cs hx

omit [Mono i.hom.hom.left] in
/-- Conjugation of standard Levis gives conjugation of standard Weyl subgroups. -/
theorem conj_mem_standardRelativeWeylGroup {I J : Finset (SimpleRoot i ν)}
    (n : normalizerPoints i)
    (hIJ : (levi i ν I).map (MulAut.conj (n : RationalPoint k G.X) :
      RationalPoint k G.X →* RationalPoint k G.X) ≤ levi i ν J)
    {u : relativeWeylGroup i} (hu : u ∈ standardRelativeWeylGroup i ν (rootSet i ν I)) :
    QuotientGroup.mk n * u * (QuotientGroup.mk n)⁻¹ ∈
      standardRelativeWeylGroup i ν (rootSet i ν J) := by
  obtain ⟨x, hx, rfl⟩ := (mem_standardRelativeWeylGroup_iff i ν).1 hu
  refine (mem_standardRelativeWeylGroup_iff i ν).2 ⟨n * x * n⁻¹, ?_, ?_⟩
  · apply hIJ
    exact ⟨x, hx, rfl⟩
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

/-! ### The key identity for a maximal standard Levi -/

/-- If `n L_I n⁻¹ ⊆ L_J` with `I = Δ ∖ {a}`, then for every relative root `α`,
`⟨α, n·ζ_I⟩ ⟨w a, ζ_J⟩ = ⟨α, ζ_J⟩ ⟨a, ζ_I⟩`. -/
theorem key_identity (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {M : CoxeterMatrix (SimpleRoot i ν)}
    {cs : CoxeterSystem M (relativeWeylGroup i)} (h : IsRelativeWeylCoxeterRealization i ν cs)
    {I J : Finset (SimpleRoot i ν)} {a : SimpleRoot i ν} (hIa : ∀ b, b ∈ I ↔ b ≠ a)
    {ζI ζJ : cocharacterLattice T} (hζI : IsStandardCocharacter i ν (rootSet i ν I) ζI)
    (hζJ : IsStandardCocharacter i ν (rootSet i ν J) ζJ)
    (n : normalizerPoints i)
    (hIJ : (levi i ν I).map (MulAut.conj (n : RationalPoint k G.X) :
      RationalPoint k G.X →* RationalPoint k G.X) ≤ levi i ν J)
    {α : characterLattice T} (hα : α ∈ relativeRoots i) :
    latticePairing T α (conjCochar i n ζI) * latticePairing T (weylAction i n a.1) ζJ =
      latticePairing T α ζJ * latticePairing T a.1 ζI := by
  set p := latticePairing T a.1 ζI
  set q := latticePairing T (weylAction i n a.1) ζJ
  have hzero : ∀ x ∈ simpleRelativeRoots i ν,
      latticePairing T x ζI * q = latticePairing T (weylAction i n x) ζJ * p := by
    intro x hx
    by_cases hxa : x = a.1
    · rw [hxa]
      ring
    · have hxI : (⟨x, hx⟩ : SimpleRoot i ν) ∈ I :=
        (hIa _).2 (fun he => hxa (congrArg Subtype.val he))
      have h1 : latticePairing T x ζI = 0 :=
        hζI.2.1 x ((val_mem_rootSet i ν I ⟨x, hx⟩).2 hxI)
      have hs : cs.simple ⟨x, hx⟩ ∈ standardRelativeWeylGroup i ν (rootSet i ν I) := by
        rw [← h.2.2.2.2 I]
        exact simple_mem_standardSubgroup cs hxI
      have h2 := pairing_action_simple_eq_zero h (J := J) (lam := ζJ)
        (fun b hb => hζJ.2.1 _ ((val_mem_rootSet i ν J b).2 hb)) (QuotientGroup.mk n) ⟨x, hx⟩
        (conj_mem_standardRelativeWeylGroup n hIJ hs)
      rw [schemeWeylCharacterAction_mk] at h2
      rw [h1, h2]
      ring
  let φ : characterLattice T →+ ℤ :=
    { toFun := fun β => latticePairing T β ζI * q - latticePairing T (weylAction i n β) ζJ * p
      map_zero' := by simp
      map_add' := by
        intro β β'
        simp only [map_add, LinearMap.add_apply]
        ring }
  have hcl : AddSubgroup.closure (simpleRelativeRoots i ν) ≤ φ.ker := by
    rw [AddSubgroup.closure_le]
    intro x hx
    change latticePairing T x ζI * q - latticePairing T (weylAction i n x) ζJ * p = 0
    rw [hzero x hx, sub_self]
  have hβ : (weylAction i n).symm α ∈ relativeRoots i := by
    rw [← weylAction_image_relativeRoots i n] at hα
    obtain ⟨y, hy, rfl⟩ := hα
    rw [LinearEquiv.symm_apply_apply]
    exact hy
  have hker := hcl (relativeRoots_subset_addSubgroupClosure_simpleRelativeRoots i ν hν hneg hβ)
  change latticePairing T ((weylAction i n).symm α) ζI * q -
    latticePairing T (weylAction i n ((weylAction i n).symm α)) ζJ * p = 0 at hker
  rw [LinearEquiv.apply_symm_apply] at hker
  rw [latticePairing_conjCochar]
  linarith

/-! ### Dynamic and standard parabolics -/

section Structure

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
include hG hi

omit [Mono i.hom.hom.left] in
/-- Cocharacters with the same nonnegative relative roots have the same dynamic parabolic. -/
theorem parabolic_eq_of_nonneg_iff {lam mu : cocharacterLattice T}
    (h : ∀ α ∈ relativeRoots i, (0 ≤ latticePairing T α lam ↔ 0 ≤ latticePairing T α mu)) :
    Dynamic.parabolic (CommGroupScheme.groupHom lam ≫ i) =
      Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ i) :=
  le_antisymm ((relativeRootSignInclusions k G hG T i hi lam mu).1.2 fun α hα => (h α hα).1)
    ((relativeRootSignInclusions k G hG T i hi mu lam).1.2 fun α hα => (h α hα).2)

variable (hν : IsGenericCocharacter i ν)
include hν

omit [Mono i.hom.hom.left] in
/-- A standard parabolic that is the conjugate of a standard parabolic by a normalizer point
`n` has the same index set, and the class of `n` lies in its standard Weyl subgroup. -/
theorem eq_and_mk_mem_of_standardParabolic_eq_comap {K K' : Finset (SimpleRoot i ν)}
    (n : normalizerPoints i)
    (h : standardParabolic i ν (rootSet i ν K) =
      (standardParabolic i ν (rootSet i ν K')).comap
        (G.innerIso (n : RationalPoint k G.X)).hom) :
    K = K' ∧ (QuotientGroup.mk n : relativeWeylGroup i) ∈
      standardRelativeWeylGroup i ν (rootSet i ν K) := by
  obtain ⟨⟨ζ, hζ⟩, hcmp⟩ := standardCocharacter k G hG T i hi ν hν (rootSet i ν K)
    (rootSet_subset i ν K)
  have hP : Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) =
      standardParabolic i ν (rootSet i ν K) := ((hcmp ζ hζ).1).symm
  have huniq := (standardParabolicClassification k G hG T i hi ν hν).2
    (CommGroupScheme.groupHom ζ ≫ i)
  have h1 : ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) =
        (standardParabolic i ν (⟨rootSet i ν K, rootSet_subset i ν K⟩ :
          {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν}).1).comap
          (G.innerIso g).hom :=
    ⟨1, by rw [innerIso_one_hom, SubgroupFunctor.comap_id]; exact hP⟩
  have h2 : ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) =
        (standardParabolic i ν (⟨rootSet i ν K', rootSet_subset i ν K'⟩ :
          {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν}).1).comap
          (G.innerIso g).hom :=
    ⟨n, by rw [hP]; exact h⟩
  have hKK' : K = K' := by
    have := huniq.unique h1 h2
    exact rootSet_injective i ν (congrArg Subtype.val this)
  subst hKK'
  refine ⟨rfl, ?_⟩
  have hnorm : (n : RationalPoint k G.X) ∈ Subgroup.normalizer
      (↑(standardParabolicPoints i ν (rootSet i ν K)) : Set (RationalPoint k G.X)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hx := SubgroupFunctor.mem_rationalPoints_comap_innerIso_hom
      (standardParabolic i ν (rootSet i ν K)) (n : RationalPoint k G.X) x
    rw [← h] at hx
    exact hx
  rw [(standardParabolicPointsStatement_proof k G hG T i hi ν hν).2.2.1 _
    (rootSet_subset i ν K)] at hnorm
  exact ((normalizerStandardParabolicStatement_of_statements
    standardParabolicPointsStatement_proof rationalBruhat) k G hG T i hi ν hν _
      (rootSet_subset i ν K) n).1 hnorm

variable [Fintype (SimpleRoot i ν)] {M : CoxeterMatrix (SimpleRoot i ν)}
  {cs : CoxeterSystem M (relativeWeylGroup i)} (h : IsRelativeWeylCoxeterRealization i ν cs)
include h

/-- The standard parabolics `P_I(k)` are ordered by inclusion of index sets. -/
theorem parabolic_le_iff {I J : Finset (SimpleRoot i ν)} :
    parabolic i ν I ≤ parabolic i ν J ↔ I ⊆ J := by
  constructor
  · intro hle x hx
    have hs : cs.simple x ∈ standardRelativeWeylGroup i ν (rootSet i ν I) := by
      rw [← h.2.2.2.2 I]
      exact simple_mem_standardSubgroup cs hx
    obtain ⟨m, hm, hmx⟩ := (mem_standardRelativeWeylGroup_iff i ν).1 hs
    have hmJ : (m : RationalPoint k G.X) ∈ parabolic i ν J :=
      hle (levi_le_parabolic i ν I hm)
    have hW := ((normalizerStandardParabolicStatement_of_statements
      standardParabolicPointsStatement_proof rationalBruhat) k G hG T i hi ν hν _
        (rootSet_subset i ν J) m).1 hmJ
    rw [hmx] at hW
    exact mem_of_simple_mem_standard h hW
  · intro hIJ
    have hle := ((standardParabolicOrder k G hG T i hi ν hν).1 (rootSet i ν I) (rootSet i ν J)
      (rootSet_subset i ν I) (rootSet_subset i ν J)).1.1 ((rootSet_subset_iff i ν I J).2 hIJ)
    exact hle (Over.mk (𝟙 _))

omit h [Mono i.hom.hom.left] in
/-- The standard parabolic of all simple roots is `G(k)`. -/
theorem parabolic_univ : parabolic i ν (Finset.univ : Finset (SimpleRoot i ν)) = ⊤ := by
  change (standardParabolic i ν (rootSet i ν Finset.univ)).carrier (Over.mk (𝟙 _)) = ⊤
  rw [rootSet_univ, (standardParabolicEndpoints k G hG T i hi ν hν).2.2.1]
  rfl

theorem parabolic_eq_top_iff {J : Finset (SimpleRoot i ν)} :
    parabolic i ν J = ⊤ ↔ J = Finset.univ := by
  constructor
  · intro hJ
    apply Finset.eq_univ_of_forall
    intro b
    have hle : parabolic i ν Finset.univ ≤ parabolic i ν J := by
      rw [hJ]
      exact le_top
    exact (parabolic_le_iff hG hi hν h).1 hle (Finset.mem_univ b)
  · rintro rfl
    exact parabolic_univ hG hi hν

/-- **Clause 1.** `P_I` is maximal exactly when `I = Δ ∖ {a}`. -/
theorem isMaximal_iff (I : Finset (SimpleRoot i ν)) :
    (parabolic i ν I ≠ ⊤ ∧
        ∀ J : Finset (SimpleRoot i ν), parabolic i ν I < parabolic i ν J → parabolic i ν J = ⊤) ↔
      ∃ a : SimpleRoot i ν, ∀ b : SimpleRoot i ν, b ∈ I ↔ b ≠ a := by
  classical
  have hlt : ∀ J, parabolic i ν I < parabolic i ν J ↔ I ⊂ J := by
    intro J
    rw [lt_iff_le_not_ge, parabolic_le_iff hG hi hν h, parabolic_le_iff hG hi hν h,
      Finset.ssubset_iff_subset_ne]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun he => h2 (he ▸ subset_refl _)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h3 => h2 (Finset.Subset.antisymm h1 h3)⟩
  simp only [hlt, ne_eq, parabolic_eq_top_iff hG hi hν h]
  constructor
  · rintro ⟨hne, hmax⟩
    obtain ⟨a, ha⟩ : ∃ a, a ∉ I := by
      by_contra hc
      push Not at hc
      exact hne (Finset.eq_univ_of_forall hc)
    refine ⟨a, fun b => ⟨fun hb hba => ha (hba ▸ hb), fun hba => ?_⟩⟩
    by_contra hbI
    have hss : I ⊂ insert b I := Finset.ssubset_insert hbI
    have hall := hmax _ hss
    have haI : a ∈ insert b I := hall ▸ Finset.mem_univ a
    rcases Finset.mem_insert.1 haI with hab | haI'
    · exact hba hab.symm
    · exact ha haI'
  · rintro ⟨a, ha⟩
    refine ⟨fun hI => (ha a).1 (hI ▸ Finset.mem_univ a) rfl, fun J hIJ => ?_⟩
    obtain ⟨c, hcJ, hcI⟩ := Finset.exists_of_ssubset hIJ
    have hca : c = a := by
      by_contra hca
      exact hcI ((ha c).2 hca)
    apply Finset.eq_univ_of_forall
    intro b
    by_cases hba : b = a
    · rw [hba, ← hca]
      exact hcJ
    · exact hIJ.1 ((ha b).2 hba)

/-- **Dichotomy.** For a maximal `I = Δ ∖ {a}` and `n L_I n⁻¹ = L_J`, either the class of `n`
lies in `W_I`, or `n` conjugates `P(ζ_I)` to the opposite `P(-ζ_J)` of `P_J`. -/
theorem mk_mem_or_parabolic_eq_neg {I J : Finset (SimpleRoot i ν)} {a : SimpleRoot i ν}
    (hIa : ∀ b, b ∈ I ↔ b ≠ a)
    {ζI ζJ : cocharacterLattice T} (hζI : IsStandardCocharacter i ν (rootSet i ν I) ζI)
    (hζJ : IsStandardCocharacter i ν (rootSet i ν J) ζJ)
    (n : normalizerPoints i)
    (hIJ : (levi i ν I).map (MulAut.conj (n : RationalPoint k G.X) :
      RationalPoint k G.X →* RationalPoint k G.X) = levi i ν J) :
    (QuotientGroup.mk n : relativeWeylGroup i) ∈ standardRelativeWeylGroup i ν (rootSet i ν I) ∨
      Dynamic.parabolic (CommGroupScheme.groupHom (conjCochar i n ζI) ≫ i) =
        Dynamic.parabolic (CommGroupScheme.groupHom (-ζJ) ≫ i) := by
  have hneg := relativeRootNegation k G hG T i hi
  have haI : a.1 ∉ rootSet i ν I := fun hmem =>
    ((hIa a).1 ((val_mem_rootSet i ν I a).1 hmem)) rfl
  have hp : 0 < latticePairing T a.1 ζI := hζI.2.2 a.1 a.2 haI
  have key := fun α (hα : α ∈ relativeRoots i) =>
    key_identity hν hneg h hIa hζI hζJ n hIJ.le hα
  set p := latticePairing T a.1 ζI
  set q := latticePairing T (weylAction i n a.1) ζJ
  rcases lt_trichotomy q 0 with hq | hq | hq
  · right
    apply parabolic_eq_of_nonneg_iff hG hi
    intro α hα
    have hk := key α hα
    rw [map_neg]
    constructor
    · intro h0
      have : latticePairing T α ζJ * p ≤ 0 := by rw [← hk]; nlinarith
      have : latticePairing T α ζJ ≤ 0 := by nlinarith
      linarith
    · intro h0
      have : latticePairing T α (conjCochar i n ζI) * q ≤ 0 := by rw [hk]; nlinarith
      nlinarith
  · exfalso
    -- every simple root lies in `J`, so `L_J = G(k)`, hence `L_I = P_I = G(k)`
    have hJ : J = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro b
      by_contra hb
      have hbJ : b.1 ∉ rootSet i ν J := fun hmem => hb ((val_mem_rootSet i ν J b).1 hmem)
      have hpos : 0 < latticePairing T b.1 ζJ := hζJ.2.2 b.1 b.2 hbJ
      have hk := key b.1 b.2.1.1
      rw [hq, mul_zero] at hk
      have : latticePairing T b.1 ζJ * p > 0 := mul_pos hpos hp
      linarith
    have hLJ : levi i ν J = ⊤ := by
      subst hJ
      change (standardLevi i ν (rootSet i ν Finset.univ)).carrier (Over.mk (𝟙 _)) = ⊤
      rw [rootSet_univ, (standardParabolicEndpoints k G hG T i hi ν hν).2.2.2.1]
      rfl
    have hLI : levi i ν I = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : (n : RationalPoint k G.X) * x * (n : RationalPoint k G.X)⁻¹ ∈
          (levi i ν I).map (MulAut.conj (n : RationalPoint k G.X) :
            RationalPoint k G.X →* RationalPoint k G.X) := by
        rw [hIJ, hLJ]
        exact Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := hx
      change (n : RationalPoint k G.X) * y * (n : RationalPoint k G.X)⁻¹ = _ at hyx
      have : y = x := by
        have := congrArg (fun z => (n : RationalPoint k G.X)⁻¹ * z * (n : RationalPoint k G.X))
          hyx
        simpa [mul_assoc] using this
      exact this ▸ hy
    have hPI : parabolic i ν I = ⊤ := by
      rw [eq_top_iff, ← hLI]
      exact levi_le_parabolic i ν I
    have hne := (isMaximal_iff hG hi hν h I).2 ⟨a, hIa⟩
    exact hne.1 hPI
  · left
    have hPJ : Dynamic.parabolic (CommGroupScheme.groupHom (conjCochar i n ζI) ≫ i) =
        Dynamic.parabolic (CommGroupScheme.groupHom ζJ ≫ i) := by
      apply parabolic_eq_of_nonneg_iff hG hi
      intro α hα
      have hk := key α hα
      constructor
      · intro h0
        have : 0 ≤ latticePairing T α ζJ * p := by rw [← hk]; positivity
        nlinarith
      · intro h0
        have : 0 ≤ latticePairing T α (conjCochar i n ζI) * q := by rw [hk]; positivity
        nlinarith
    obtain ⟨-, hcmpI⟩ := standardCocharacter k G hG T i hi ν hν (rootSet i ν I)
      (rootSet_subset i ν I)
    obtain ⟨-, hcmpJ⟩ := standardCocharacter k G hG T i hi ν hν (rootSet i ν J)
      (rootSet_subset i ν J)
    have heq : standardParabolic i ν (rootSet i ν I) =
        (standardParabolic i ν (rootSet i ν J)).comap
          (G.innerIso (n : RationalPoint k G.X)).hom := by
      rw [(hcmpI ζI hζI).1, (hcmpJ ζJ hζJ).1, ← hPJ]
      exact parabolic_eq_comap_conjCochar i n ζI
    exact (eq_and_mk_mem_of_standardParabolic_eq_comap hG hi hν n heq).2

/-- **Clause 3.** If `P_I` is maximal, `n` has class outside `W_I` and `n L_I n⁻¹ = L_J`, then
`n P_I n⁻¹ = P(-ζ)(k)` for every standard cocharacter `ζ` of `J`. -/
theorem parabolic_map_conj_eq {I J : Finset (SimpleRoot i ν)} {a : SimpleRoot i ν}
    (hIa : ∀ b, b ∈ I ↔ b ≠ a) (n : normalizerPoints i)
    (hn : (QuotientGroup.mk n : relativeWeylGroup i) ∉
      standardRelativeWeylGroup i ν (rootSet i ν I))
    (hIJ : (levi i ν I).map (MulAut.conj (n : RationalPoint k G.X) :
      RationalPoint k G.X →* RationalPoint k G.X) = levi i ν J)
    {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν J) ζ) :
    (parabolic i ν I).map (MulAut.conj (n : RationalPoint k G.X) :
        RationalPoint k G.X →* RationalPoint k G.X) =
      (Dynamic.parabolic (CommGroupScheme.groupHom (-ζ) ≫ i)).carrier (Over.mk (𝟙 _)) := by
  obtain ⟨⟨ζI, hζI⟩, hcmpI⟩ := standardCocharacter k G hG T i hi ν hν (rootSet i ν I)
    (rootSet_subset i ν I)
  rcases mk_mem_or_parabolic_eq_neg hG hi hν h hIa hζI hζ n hIJ with hmem | hP
  · exact absurd hmem hn
  · change ((standardParabolic i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _))).map _ = _
    rw [(hcmpI ζI hζI).1, parabolic_conjCochar_points, hP]

end Structure

/-! ### Helpers for the count `l(L_I)` -/

section Helpers

/-- `W(L_I, *)`: the classes with a representative conjugating `L_I(k)` onto some `L_J(k)`. -/
def WLstar (I : Finset (SimpleRoot i ν)) : Set (relativeWeylGroup i) :=
  {w | ∃ n : normalizerPoints i, (QuotientGroup.mk n : relativeWeylGroup i) = w ∧
    ∃ J : Finset (SimpleRoot i ν), (levi i ν I).map (MulAut.conj (n : RationalPoint k G.X) :
      RationalPoint k G.X →* RationalPoint k G.X) = levi i ν J}

/-- The left cosets `w W_I` of the elements of `W(L_I, *)`. -/
def cosets (I : Finset (SimpleRoot i ν)) :
    Set (relativeWeylGroup i ⧸ standardRelativeWeylGroup i ν (rootSet i ν I)) :=
  (QuotientGroup.mk : relativeWeylGroup i →
    relativeWeylGroup i ⧸ standardRelativeWeylGroup i ν (rootSet i ν I)) '' WLstar I

omit [Mono i.hom.hom.left] in
theorem one_mem_WLstar (I : Finset (SimpleRoot i ν)) : (1 : relativeWeylGroup i) ∈ WLstar I :=
  ⟨1, QuotientGroup.mk_one _, I, by exact map_conj_eq_self_of_mem (levi i ν I).one_mem⟩

omit [Mono i.hom.hom.left] in
/-- A normalizer point has class in `W_I` exactly when it lies in `L_I(k)`. -/
theorem mk_mem_iff_mem_levi (I : Finset (SimpleRoot i ν)) (n : normalizerPoints i) :
    (QuotientGroup.mk n : relativeWeylGroup i) ∈
        standardRelativeWeylGroup i ν (rootSet i ν I) ↔
      (n : RationalPoint k G.X) ∈ levi i ν I := by
  constructor
  · intro hn
    obtain ⟨m, hm, hmn⟩ := (mem_standardRelativeWeylGroup_iff i ν).1 hn
    have hq : m⁻¹ * n ∈ (centralizerPoints i).subgroupOf (normalizerPoints i) :=
      QuotientGroup.eq.1 hmn
    rw [Subgroup.mem_subgroupOf] at hq
    have hz : ((m : RationalPoint k G.X))⁻¹ * (n : RationalPoint k G.X) ∈ levi i ν I := by
      simpa using centralizerPoints_le_levi i ν I hq
    have h2 := (levi i ν I).mul_mem hm hz
    simpa using h2
  · intro hn
    exact (mem_standardRelativeWeylGroup_iff i ν).2 ⟨n, hn, rfl⟩

omit [IsAffineHom G.X.hom] in
theorem weylAction_symm_apply (n : normalizerPoints i) (α : characterLattice T) :
    (weylAction i n).symm α = weylAction i n⁻¹ α := by
  apply (weylAction i n).injective
  rw [LinearEquiv.apply_symm_apply, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

variable [Fintype (SimpleRoot i ν)] {M : CoxeterMatrix (SimpleRoot i ν)}
  {cs : CoxeterSystem M (relativeWeylGroup i)}

/-- Equal standard Levis `L_K(k) = L_{K'}(k)` have equal index sets. -/
theorem eq_of_levi_eq (h : IsRelativeWeylCoxeterRealization i ν cs)
    {K K' : Finset (SimpleRoot i ν)} (hKK' : levi i ν K = levi i ν K') : K = K' := by
  have hW : standardRelativeWeylGroup i ν (rootSet i ν K) =
      standardRelativeWeylGroup i ν (rootSet i ν K') := by
    simp only [standardRelativeWeylGroup]
    rw [show standardLeviPoints i ν (rootSet i ν K) = standardLeviPoints i ν (rootSet i ν K')
      from hKK']
  apply Finset.Subset.antisymm
  · intro x hx
    apply mem_of_simple_mem_standard h
    rw [← hW, ← h.2.2.2.2 K]
    exact simple_mem_standardSubgroup cs hx
  · intro x hx
    apply mem_of_simple_mem_standard h
    rw [hW, ← h.2.2.2.2 K']
    exact simple_mem_standardSubgroup cs hx

/-- A normalizer point carrying the roots of `K` onto those of `K'` conjugates `L_K(k)` onto
`L_{K'}(k)`. -/
theorem levi_map_conj_of_image (h : IsRelativeWeylCoxeterRealization i ν cs)
    {K K' : Finset (SimpleRoot i ν)} (n : normalizerPoints i)
    (himg : weylAction i n '' rootSet i ν K = rootSet i ν K') :
    (levi i ν K).map (MulAut.conj (n : RationalPoint k G.X) :
      RationalPoint k G.X →* RationalPoint k G.X) = levi i ν K' := by
  have hfin : (simpleRelativeRoots i ν).Finite := by
    rw [← rootSet_univ i ν]
    exact rootSet_finite i ν _
  obtain ⟨hL, -⟩ := restrictedStandardSubgroups_eq_comap_of_character_images i ν hfin
    (subset_refl _) (subset_refl _) (h.exists_standardCocharacter_finset K)
    (h.exists_standardCocharacter_finset K') n himg himg
  have hinf : ∀ J : Set (characterLattice T),
      standardLevi i ν J ⊓ standardParabolic i ν J = standardLevi i ν J := by
    intro J
    apply SubgroupFunctor.ext
    intro Q
    apply Subgroup.ext
    intro x
    rw [SubgroupFunctor.inf_carrier, Subgroup.mem_inf]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, standardLevi_le_standardParabolic i ν J Q hx⟩⟩
  rw [hinf, hinf] at hL
  have hp := congrArg (fun F : SubgroupFunctor G => F.rationalPoints) hL
  simp only [SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map] at hp
  change levi i ν K = (levi i ν K').map (MulAut.conj ((n : RationalPoint k G.X)⁻¹) :
    RationalPoint k G.X →* RationalPoint k G.X) at hp
  rw [hp, ← map_conj_mul, mul_inv_cancel, map_conj_eq_self_of_mem (levi i ν K').one_mem]

end Helpers

/-! ### The count `l(L_I)` -/

section Clause2

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  [Fintype (SimpleRoot i ν)] [Fintype (relativeWeylGroup i)] {M : CoxeterMatrix (SimpleRoot i ν)}
  {cs : CoxeterSystem M (relativeWeylGroup i)} (h : IsRelativeWeylCoxeterRealization i ν cs)
include hG hi hν h

omit [Fintype (relativeWeylGroup i)] h in
/-- For `n L_I n⁻¹ = L_K` with class outside `W_I`, some simple root `x` has
`⟨n x, ζ_K⟩ < 0`. Otherwise the transported cocharacter would be dominant, so `n⁻¹ P_K n` would
be standard and the class of `n` would lie in `W_I`. -/
theorem exists_simple_neg {I K : Finset (SimpleRoot i ν)} (n : normalizerPoints i)
    (hIK : (levi i ν I).map (MulAut.conj (n : RationalPoint k G.X) :
      RationalPoint k G.X →* RationalPoint k G.X) = levi i ν K)
    {ζK : cocharacterLattice T} (hζK : IsStandardCocharacter i ν (rootSet i ν K) ζK)
    (hn : (QuotientGroup.mk n : relativeWeylGroup i) ∉
      standardRelativeWeylGroup i ν (rootSet i ν I)) :
    ∃ x : SimpleRoot i ν, latticePairing T (weylAction i n x.1) ζK < 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set lam := conjCochar i n⁻¹ ζK with hlamdef
  have hlam : ∀ α, latticePairing T α lam = latticePairing T (weylAction i n α) ζK := by
    intro α
    rw [hlamdef, latticePairing_conjCochar, weylAction_symm_apply, inv_inv]
  let F : Finset (SimpleRoot i ν) :=
    Finset.univ.filter (fun x => latticePairing T x.1 lam = 0)
  have hF : IsStandardCocharacter i ν (rootSet i ν F) lam := by
    refine ⟨rootSet_subset i ν F, ?_, ?_⟩
    · rintro α ⟨x, hx, rfl⟩
      exact (Finset.mem_filter.1 hx).2
    · intro α hα hαF
      have hx : (⟨α, hα⟩ : SimpleRoot i ν) ∉ F :=
        fun hx => hαF ((val_mem_rootSet i ν F _).2 hx)
      have hne : latticePairing T α lam ≠ 0 :=
        fun h0 => hx (Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩)
      have hge : 0 ≤ latticePairing T α lam := by
        rw [hlam]
        exact hcon ⟨α, hα⟩
      exact lt_of_le_of_ne hge (Ne.symm hne)
  obtain ⟨-, hcmpF⟩ := standardCocharacter k G hG T i hi ν hν (rootSet i ν F)
    (rootSet_subset i ν F)
  obtain ⟨-, hcmpK⟩ := standardCocharacter k G hG T i hi ν hν (rootSet i ν K)
    (rootSet_subset i ν K)
  have hPK : Dynamic.parabolic (CommGroupScheme.groupHom (conjCochar i n lam) ≫ i) =
      Dynamic.parabolic (CommGroupScheme.groupHom ζK ≫ i) := by
    apply parabolic_eq_of_nonneg_iff hG hi
    intro α _
    rw [latticePairing_conjCochar, hlam, LinearEquiv.apply_symm_apply]
  have heq : standardParabolic i ν (rootSet i ν F) =
      (standardParabolic i ν (rootSet i ν K)).comap
        (G.innerIso (n : RationalPoint k G.X)).hom := by
    rw [(hcmpF lam hF).1, (hcmpK ζK hζK).1, ← hPK]
    exact parabolic_eq_comap_conjCochar i n lam
  obtain ⟨hFK, hmem⟩ := eq_and_mk_mem_of_standardParabolic_eq_comap hG hi hν n heq
  rw [hFK] at hmem
  have hKI := map_conj_inv_of_map_conj_eq hIK
  have hc := conj_mem_standardRelativeWeylGroup n⁻¹ (by exact hKI.le) hmem
  apply hn
  simpa [QuotientGroup.mk_inv] using hc

omit hG hi hν in
/-- For maximal `I`, some element of `W(L_I, *)` lies outside `W_I`: the inverse of the
longest representative `w_I`. -/
theorem exists_mem_WLstar_not_mem {I : Finset (SimpleRoot i ν)} {a : SimpleRoot i ν}
    (hIa : ∀ b, b ∈ I ↔ b ≠ a) :
    ∃ w ∈ WLstar I, w ∉ standardRelativeWeylGroup i ν (rootSet i ν I) := by
  classical
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (longestRep cs I)
  have himg := (weylAction_image_associatedStandardFamily i ν cs h I m hm ∅).2
  have hL := levi_map_conj_of_image h m himg
  refine ⟨QuotientGroup.mk m⁻¹, ⟨m⁻¹, rfl, associatedSubset cs I, ?_⟩, ?_⟩
  · exact map_conj_inv_of_map_conj_eq hL
  · intro hmem
    have hI : I = Finset.univ.erase a := by
      ext b
      simp [hIa b]
    apply longestRep_not_mem_standardSubgroup cs hI
    rw [h.2.2.2.2 I, ← hm]
    have := (standardRelativeWeylGroup i ν (rootSet i ν I)).inv_mem hmem
    simpa [QuotientGroup.mk_inv] using this

omit [Fintype (relativeWeylGroup i)] in
/-- For maximal `I`, any two elements of `W(L_I, *)` outside `W_I` have the same coset. -/
theorem coset_eq_of_not_mem {I : Finset (SimpleRoot i ν)} {a : SimpleRoot i ν}
    (hIa : ∀ b, b ∈ I ↔ b ≠ a) {n1 n2 : normalizerPoints i} {J1 J2 : Finset (SimpleRoot i ν)}
    (h1 : (levi i ν I).map (MulAut.conj (n1 : RationalPoint k G.X) :
      RationalPoint k G.X →* RationalPoint k G.X) = levi i ν J1)
    (h2 : (levi i ν I).map (MulAut.conj (n2 : RationalPoint k G.X) :
      RationalPoint k G.X →* RationalPoint k G.X) = levi i ν J2)
    (hn1 : (QuotientGroup.mk n1 : relativeWeylGroup i) ∉
      standardRelativeWeylGroup i ν (rootSet i ν I))
    (hn2 : (QuotientGroup.mk n2 : relativeWeylGroup i) ∉
      standardRelativeWeylGroup i ν (rootSet i ν I)) :
    (QuotientGroup.mk (QuotientGroup.mk n1 : relativeWeylGroup i) :
        relativeWeylGroup i ⧸ standardRelativeWeylGroup i ν (rootSet i ν I)) =
      QuotientGroup.mk (QuotientGroup.mk n2 : relativeWeylGroup i) := by
  obtain ⟨⟨ζI, hζI⟩, -⟩ := standardCocharacter k G hG T i hi ν hν (rootSet i ν I)
    (rootSet_subset i ν I)
  obtain ⟨⟨ζ1, hζ1⟩, hcmp1⟩ := standardCocharacter k G hG T i hi ν hν (rootSet i ν J1)
    (rootSet_subset i ν J1)
  obtain ⟨⟨ζ2, hζ2⟩, hcmp2⟩ := standardCocharacter k G hG T i hi ν hν (rootSet i ν J2)
    (rootSet_subset i ν J2)
  have hneg := relativeRootNegation k G hG T i hi
  have hP1 := (mk_mem_or_parabolic_eq_neg hG hi hν h hIa hζI hζ1 n1 h1).resolve_left hn1
  have hP2 := (mk_mem_or_parabolic_eq_neg hG hi hν h hIa hζI hζ2 n2 h2).resolve_left hn2
  have hs : ∀ (n : normalizerPoints i) (ζ : cocharacterLattice T),
      Dynamic.parabolic (CommGroupScheme.groupHom (conjCochar i n ζI) ≫ i) =
        Dynamic.parabolic (CommGroupScheme.groupHom (-ζ) ≫ i) →
      ∀ α ∈ relativeRoots i,
        (0 ≤ latticePairing T ((weylAction i n).symm α) ζI ↔ latticePairing T α ζ ≤ 0) := by
    intro n ζ hP α hα
    have e1 := (relativeRootSignInclusions k G hG T i hi _ _).1.1 hP.le α hα
    have e2 := (relativeRootSignInclusions k G hG T i hi _ _).1.1 hP.ge α hα
    rw [latticePairing_conjCochar, map_neg] at e1 e2
    constructor
    · intro h0
      have := e1 h0
      linarith
    · intro h0
      exact e2 (by linarith)
  set y := n2 * n1⁻¹ with hydef
  have hPy : Dynamic.parabolic (CommGroupScheme.groupHom (conjCochar i y ζ1) ≫ i) =
      Dynamic.parabolic (CommGroupScheme.groupHom ζ2 ≫ i) := by
    apply parabolic_eq_of_nonneg_iff hG hi
    intro α hα
    rw [latticePairing_conjCochar]
    have hy : (weylAction i y).symm α = weylAction i n1 ((weylAction i n2).symm α) := by
      rw [weylAction_symm_apply, weylAction_symm_apply, hydef, mul_inv_rev, inv_inv, map_mul,
        LinearEquiv.mul_apply]
    rw [hy]
    set β := (weylAction i n2).symm α with hβdef
    have hβ : β ∈ relativeRoots i := by
      rw [← weylAction_image_relativeRoots i n2] at hα
      obtain ⟨z, hz, rfl⟩ := hα
      rw [hβdef, LinearEquiv.symm_apply_apply]
      exact hz
    have hwβ : weylAction i n1 β ∈ relativeRoots i := weylAction_mapsTo_relativeRoots i n1 hβ
    have e1 := hs n1 ζ1 hP1 (-(weylAction i n1 β)) (hneg _ hwβ)
    simp only [map_neg, LinearEquiv.symm_apply_apply, LinearMap.neg_apply] at e1
    have e2 := hs n2 ζ2 hP2 (-α) (hneg _ hα)
    simp only [map_neg, LinearMap.neg_apply, ← hβdef] at e2
    constructor
    · intro h0
      have := e2.1 (e1.2 (by linarith))
      linarith
    · intro h0
      have := e1.1 (e2.2 (by linarith))
      linarith
  have heq : standardParabolic i ν (rootSet i ν J1) =
      (standardParabolic i ν (rootSet i ν J2)).comap
        (G.innerIso (y : RationalPoint k G.X)).hom := by
    rw [(hcmp1 ζ1 hζ1).1, (hcmp2 ζ2 hζ2).1, ← hPy]
    exact parabolic_eq_comap_conjCochar i y ζ1
  obtain ⟨-, hymem⟩ := eq_and_mk_mem_of_standardParabolic_eq_comap hG hi hν y heq
  have hJ1I := map_conj_inv_of_map_conj_eq h1
  have hc := conj_mem_standardRelativeWeylGroup n1⁻¹ (by exact hJ1I.le) hymem
  rw [QuotientGroup.eq]
  convert hc using 1
  simp only [hydef, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  group

/-- For maximal `I`, there are exactly two cosets. -/
theorem card_cosets_eq_two {I : Finset (SimpleRoot i ν)} {a : SimpleRoot i ν}
    (hIa : ∀ b, b ∈ I ↔ b ≠ a) : Nat.card (cosets I) = 2 := by
  obtain ⟨w0, hw0, hw0n⟩ := exists_mem_WLstar_not_mem h hIa
  have hS : cosets I = {QuotientGroup.mk 1, QuotientGroup.mk w0} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      by_cases hwI : w ∈ standardRelativeWeylGroup i ν (rootSet i ν I)
      · left
        rw [QuotientGroup.eq]
        simpa using hwI
      · right
        obtain ⟨n, rfl, J, hJ⟩ := hw
        obtain ⟨n0, rfl, J0, hJ0⟩ := hw0
        exact coset_eq_of_not_mem hG hi hν h hIa hJ hJ0 hwI hw0n
    · rintro (rfl | rfl)
      · exact ⟨1, one_mem_WLstar I, rfl⟩
      · exact ⟨w0, hw0, rfl⟩
  have hne : (QuotientGroup.mk 1 :
      relativeWeylGroup i ⧸ standardRelativeWeylGroup i ν (rootSet i ν I)) ≠
        QuotientGroup.mk w0 := by
    intro he
    rw [QuotientGroup.eq] at he
    apply hw0n
    simpa using he
  rw [hS, Nat.card_coe_set_eq, Set.ncard_pair hne]

omit hG hi hν in
/-- For `I = Δ`, there is at most one coset. -/
theorem card_cosets_le_one_of_univ {I : Finset (SimpleRoot i ν)} (hI : I = Finset.univ) :
    Nat.card (cosets I) ≤ 1 := by
  have htop : standardRelativeWeylGroup i ν (rootSet i ν I) = ⊤ := by
    rw [← h.2.2.2.2 I, hI, standardSubgroup_univ]
  have : Subsingleton
      (relativeWeylGroup i ⧸ standardRelativeWeylGroup i ν (rootSet i ν I)) := by
    constructor
    intro x y
    induction x using QuotientGroup.induction_on with | H x => ?_
    induction y using QuotientGroup.induction_on with | H y => ?_
    rw [QuotientGroup.eq, htop]
    exact Subgroup.mem_top _
  have : Subsingleton (cosets I) := ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  exact Finite.card_le_one_iff_subsingleton.2 inferInstance

omit hG hi hν in
/-- For `c ∉ I`, a lift `n` of `w_{Δ∖{c}}⁻¹` conjugates `L_I(k)` onto a standard Levi `L_K(k)`,
and `⟨n x, ζ_K⟩ > 0` for every simple root `x` outside `I ∪ {c}`. -/
theorem exists_longest_lift [DecidableEq (SimpleRoot i ν)] {I : Finset (SimpleRoot i ν)}
    {c : SimpleRoot i ν} (hc : c ∉ I) :
    ∃ (n : normalizerPoints i) (K : Finset (SimpleRoot i ν)),
      (levi i ν I).map (MulAut.conj (n : RationalPoint k G.X) :
        RationalPoint k G.X →* RationalPoint k G.X) = levi i ν K ∧
      (QuotientGroup.mk n : relativeWeylGroup i) = (longestRep cs (Finset.univ.erase c))⁻¹ ∧
      ∀ x : SimpleRoot i ν, x ∉ I → x ≠ c → ∀ ζK : cocharacterLattice T,
        IsStandardCocharacter i ν (rootSet i ν K) ζK →
          0 < latticePairing T (weylAction i n x.1) ζK := by
  set J := Finset.univ.erase c with hJdef
  have hIJ : I ⊆ J := fun x hx =>
    Finset.mem_erase.2 ⟨fun hxc => hc (hxc ▸ hx), Finset.mem_univ x⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (longestRep cs J)
  let I' : Finset (associatedSubset cs J) :=
    (associatedFinsetEquiv cs J).symm (I.subtype (· ∈ J))
  set K := I'.map (Function.Embedding.subtype (· ∈ associatedSubset cs J)) with hKdef
  have himg := (weylAction_image_associatedStandardFamily i ν cs h J m hm I').1
  have hback : (associatedFinsetEquiv cs J I').map (Function.Embedding.subtype (· ∈ J)) = I := by
    simp only [I', Equiv.apply_symm_apply, Finset.subtype_map]
    exact Finset.filter_true_of_mem hIJ
  rw [hback] at himg
  have hL := levi_map_conj_of_image h m himg
  refine ⟨m⁻¹, K, map_conj_inv_of_map_conj_eq hL, by rw [QuotientGroup.mk_inv, hm], ?_⟩
  intro x hxI hxc ζK hζK
  have hxJ : x ∈ J := Finset.mem_erase.2 ⟨hxc, Finset.mem_univ x⟩
  set y := (associatedSimpleEquiv cs J).symm ⟨x, hxJ⟩ with hydef
  have hy : weylAction i m (y : SimpleRoot i ν).1 = x.1 := by
    have := schemeWeylCharacterAction_associatedSimpleEquiv i ν cs h J y
    rw [← hm, schemeWeylCharacterAction_mk] at this
    rw [this, hydef, Equiv.apply_symm_apply]
  have hw : weylAction i m⁻¹ x.1 = (y : SimpleRoot i ν).1 := by
    rw [← weylAction_symm_apply, ← hy, LinearEquiv.symm_apply_apply]
  rw [hw]
  apply hζK.2.2 _ (y : SimpleRoot i ν).2
  intro hmem
  rw [val_mem_rootSet] at hmem
  rw [show (y : SimpleRoot i ν) = Function.Embedding.subtype (· ∈ associatedSubset cs J) y
    from rfl, hKdef, Finset.mem_map'] at hmem
  simp only [I', associatedFinsetEquiv, Equiv.finsetCongr_symm, Equiv.finsetCongr_apply,
    Finset.mem_map_equiv, Equiv.symm_symm, hydef, Equiv.apply_symm_apply,
    Finset.mem_subtype] at hmem
  exact hxI hmem

/-- If two simple roots `a ≠ b` lie outside `I`, there are at least three cosets. -/
theorem three_le_card_cosets {I : Finset (SimpleRoot i ν)} {a b : SimpleRoot i ν}
    (hab : a ≠ b) (ha : a ∉ I) (hb : b ∉ I) : 3 ≤ Nat.card (cosets I) := by
  classical
  obtain ⟨na, Ka, hKa, hna, hposa⟩ := exists_longest_lift h ha
  obtain ⟨nb, Kb, hKb, hnb, hposb⟩ := exists_longest_lift h hb
  have hout : ∀ c : SimpleRoot i ν, c ∉ I → ∀ n : normalizerPoints i,
      (QuotientGroup.mk n : relativeWeylGroup i) = (longestRep cs (Finset.univ.erase c))⁻¹ →
        (QuotientGroup.mk n : relativeWeylGroup i) ∉
          standardRelativeWeylGroup i ν (rootSet i ν I) := by
    intro c hc n hn hmem
    have hIJ : I ⊆ Finset.univ.erase c := fun x hx =>
      Finset.mem_erase.2 ⟨fun hxc => hc (hxc ▸ hx), Finset.mem_univ x⟩
    apply longestRep_not_mem_standardSubgroup cs (J := Finset.univ.erase c) (α := c) rfl
    have h1 : longestRep cs (Finset.univ.erase c) ∈ standardSubgroup cs I := by
      rw [h.2.2.2.2 I]
      have := (standardRelativeWeylGroup i ν (rootSet i ν I)).inv_mem hmem
      rwa [hn, inv_inv] at this
    exact standardSubgroup_mono cs hIJ h1
  have hna_out := hout a ha na hna
  have hnb_out := hout b hb nb hnb
  have hzero : ∀ (n : normalizerPoints i) (K : Finset (SimpleRoot i ν)),
      (levi i ν I).map (MulAut.conj (n : RationalPoint k G.X) :
        RationalPoint k G.X →* RationalPoint k G.X) = levi i ν K →
      ∀ ζ : cocharacterLattice T, IsStandardCocharacter i ν (rootSet i ν K) ζ →
        ∀ x ∈ I, latticePairing T (weylAction i n x.1) ζ = 0 := by
    intro n K hK ζ hζ x hx
    have hz := pairing_action_simple_eq_zero h (J := K) (lam := ζ)
      (fun y hy => hζ.2.1 _ ((val_mem_rootSet i ν K y).2 hy)) (QuotientGroup.mk n) x
      (conj_mem_standardRelativeWeylGroup n hK.le (by
        rw [← h.2.2.2.2 I]
        exact simple_mem_standardSubgroup cs hx))
    rwa [schemeWeylCharacterAction_mk] at hz
  have hnegc : ∀ (c : SimpleRoot i ν) (n : normalizerPoints i) (K : Finset (SimpleRoot i ν)),
      (levi i ν I).map (MulAut.conj (n : RationalPoint k G.X) :
        RationalPoint k G.X →* RationalPoint k G.X) = levi i ν K →
      (QuotientGroup.mk n : relativeWeylGroup i) ∉
        standardRelativeWeylGroup i ν (rootSet i ν I) →
      (∀ x : SimpleRoot i ν, x ∉ I → x ≠ c → ∀ ζK : cocharacterLattice T,
        IsStandardCocharacter i ν (rootSet i ν K) ζK →
          0 < latticePairing T (weylAction i n x.1) ζK) →
      ∀ ζ : cocharacterLattice T, IsStandardCocharacter i ν (rootSet i ν K) ζ →
        latticePairing T (weylAction i n c.1) ζ < 0 := by
    intro c n K hK hout' hpos ζ hζ
    obtain ⟨x, hx⟩ := exists_simple_neg hG hi hν n hK hζ hout'
    by_cases hxI : x ∈ I
    · have := hzero n K hK ζ hζ x hxI
      linarith
    · by_cases hxc : x = c
      · rw [← hxc]
        exact hx
      · have := hpos x hxI hxc ζ hζ
        linarith
  have hFin : Finite (relativeWeylGroup i ⧸ standardRelativeWeylGroup i ν (rootSet i ν I)) :=
    Finite.of_surjective _ QuotientGroup.mk_surjective
  let q : relativeWeylGroup i →
      relativeWeylGroup i ⧸ standardRelativeWeylGroup i ν (rootSet i ν I) := QuotientGroup.mk
  have h0 : q 1 ∈ cosets I := ⟨1, one_mem_WLstar I, rfl⟩
  have hA : q (QuotientGroup.mk na) ∈ cosets I := ⟨_, ⟨na, rfl, Ka, hKa⟩, rfl⟩
  have hB : q (QuotientGroup.mk nb) ∈ cosets I := ⟨_, ⟨nb, rfl, Kb, hKb⟩, rfl⟩
  have hne0a : q 1 ≠ q (QuotientGroup.mk na) := by
    intro he
    rw [QuotientGroup.eq] at he
    apply hna_out
    simpa using he
  have hne0b : q 1 ≠ q (QuotientGroup.mk nb) := by
    intro he
    rw [QuotientGroup.eq] at he
    apply hnb_out
    simpa using he
  have hneab : q (QuotientGroup.mk na) ≠ q (QuotientGroup.mk nb) := by
    intro he
    rw [QuotientGroup.eq, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      mk_mem_iff_mem_levi] at he
    have he' : ((na : RationalPoint k G.X))⁻¹ * (nb : RationalPoint k G.X) ∈ levi i ν I := he
    have hKK : levi i ν Ka = levi i ν Kb := by
      rw [← hKa, ← hKb]
      have hnb' : (nb : RationalPoint k G.X) =
          (na : RationalPoint k G.X) * (((na : RationalPoint k G.X))⁻¹ *
            (nb : RationalPoint k G.X)) := by group
      rw [hnb', map_conj_mul, map_conj_eq_self_of_mem he']
    have hKeq := eq_of_levi_eq h hKK
    obtain ⟨ζ, hζ⟩ := h.exists_standardCocharacter_finset Ka
    have hζb : IsStandardCocharacter i ν (rootSet i ν Kb) ζ := hKeq ▸ hζ
    set lam := conjCochar i na⁻¹ ζ with hlamdef
    have hlam : ∀ α, latticePairing T α lam = latticePairing T (weylAction i na α) ζ := by
      intro α
      rw [hlamdef, latticePairing_conjCochar, weylAction_symm_apply, inv_inv]
    have hlamI : ∀ y ∈ I, latticePairing T y.1 lam = 0 := by
      intro y hy
      rw [hlam]
      exact hzero na Ka hKa ζ hζ y hy
    have hfix := pairing_action_eq_of_mem_standard h hlamI
      (u := QuotientGroup.mk (na⁻¹ * nb)) ((mk_mem_iff_mem_levi I _).2 he) a.1
    rw [schemeWeylCharacterAction_mk, hlam, hlam, ← LinearEquiv.mul_apply, ← map_mul,
      mul_inv_cancel_left] at hfix
    have h1 := hposb a ha hab ζ hζb
    have h2 := hnegc a na Ka hKa hna_out hposa ζ hζ
    linarith
  have hsub : ({q 1, q (QuotientGroup.mk na), q (QuotientGroup.mk nb)} :
      Set (relativeWeylGroup i ⧸ standardRelativeWeylGroup i ν (rootSet i ν I))) ⊆ cosets I := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact h0
    · exact hA
    · exact hB
  have h3 : ({q 1, q (QuotientGroup.mk na), q (QuotientGroup.mk nb)} :
      Set (relativeWeylGroup i ⧸ standardRelativeWeylGroup i ν (rootSet i ν I))).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨_, _, _, hne0a, hne0b, hneab, rfl⟩
  rw [Nat.card_coe_set_eq, ← h3]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

/-- **Clause 2.** `P_I` is maximal exactly when there are two cosets, `l(L_I) = 2`. -/
theorem isMaximal_iff_card (I : Finset (SimpleRoot i ν)) :
    (parabolic i ν I ≠ ⊤ ∧
        ∀ J : Finset (SimpleRoot i ν), parabolic i ν I < parabolic i ν J → parabolic i ν J = ⊤) ↔
      Nat.card (cosets I) = 2 := by
  classical
  rw [isMaximal_iff hG hi hν h I]
  constructor
  · rintro ⟨a, hIa⟩
    exact card_cosets_eq_two hG hi hν h hIa
  · intro h2
    by_contra hno
    by_cases hall : I = Finset.univ
    · have := card_cosets_le_one_of_univ h hall
      omega
    · obtain ⟨a, ha⟩ : ∃ a, a ∉ I := by
        by_contra hc
        push Not at hc
        exact hall (Finset.eq_univ_of_forall hc)
      obtain ⟨b, hb, hba⟩ : ∃ b, b ∉ I ∧ b ≠ a := by
        by_contra hc
        push Not at hc
        exact hno ⟨a, fun x => ⟨fun hx hxa => ha (hxa ▸ hx),
          fun hxa => by_contra fun hxI => hxa (hc x hxI)⟩⟩
      have := three_le_card_cosets hG hi hν h (Ne.symm hba) ha hb
      omega

end Clause2

end StandardMaximalLeviWeyl

open StandardMaximalLeviWeyl in
/-- **Renard V.4.8.** For the standard parabolics `P_I` of a connected reductive group over a
nonarchimedean local field: `P_I` is maximal exactly when `I = Δ ∖ {α}`, exactly when
`l(L_I) = 2`; and then a normalizer point outside `W_I` with `n L_I n⁻¹ = L_J` conjugates `P_I`
onto the opposite `P(-ζ)(k)` of `P_J`, for every standard cocharacter `ζ` of `J`. -/
theorem standardMaximalLeviWeyl : StandardMaximalLeviWeylStatement.{u} := by
  intro k _ _ _ _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν
  obtain ⟨hWfin, hSfin, M, cs, h⟩ := relativeWeylCoxeter k G hG T i hi ν hν
  let := Fintype.ofFinite (relativeWeylGroup i)
  let := Fintype.ofFinite (SimpleRoot i ν)
  intro conj WS WLstar' ell IsMaximal I
  refine ⟨isMaximal_iff hG hi hν h I, isMaximal_iff_card hG hi hν h I, ?_⟩
  rintro hmax n J hn hJ ζ hζ
  obtain ⟨a, hIa⟩ := (isMaximal_iff hG hi hν h I).1 hmax
  exact parabolic_map_conj_eq hG hi hν h hIa n hn hJ hζ

end Langlands.GroupScheme
