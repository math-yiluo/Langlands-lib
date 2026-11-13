import Langlands.GroupScheme.Rational.StandardWeylMinimalRepresentativesStatement
import Langlands.GroupScheme.Dynamic.CommonTorusIntersections
import Langlands.GroupScheme.Dynamic.NestedDecomposition
import Langlands.GroupScheme.Rational.StandardSourceTwistedIntersectionProof
import Langlands.GroupScheme.Rational.StandardLeviTwistedIntersectionProof
import Langlands.GroupScheme.Rational.StandardLeviCentralizerRealization
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Langlands.GroupScheme.Rational.RelativeTitsSystemProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.Group.RelativeWeylMinimalUniqueProof
import Langlands.Group.RelativeWeylMinimalityProof
import Langlands.Group.TitsParabolicRigidity

/-! # Proof of Renard V.4.6 (Lemma) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

namespace Dynamic

section Affine

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
    [IsSeparated G.X.hom] {A : CommGroupScheme (Spec R)} (i : A.toGrp ⟶ G)
    (α β : (Gm (Spec R)).toGrp ⟶ A.toGrp)

/-- The parabolic ordered intersection product for two cocharacters of a common
commutative acting group, over every test scheme. -/
theorem parabolic_inf_parabolic_eq_mul (T : Over (Spec R)) :
    (↑((parabolic (α ≫ i) ⊓ parabolic (β ≫ i)).carrier T) : Set (T ⟶ G.X)) =
      (↑((parabolic (α ≫ i) ⊓ centralizer (β ≫ i)).carrier T) : Set (T ⟶ G.X)) *
        (↑((parabolic (α ≫ i) ⊓ unipotent (β ≫ i)).carrier T) : Set (T ⟶ G.X)) := by
  have hF := (parabolic_isStable_conjugation i α).restrict β
  rw [AutomorphicAction.restrict_conjugation] at hF
  exact inf_parabolic_eq_mul_of_isStable (β ≫ i)
    (Affine.isRepresentedBy_parabolicHom (α ≫ i))
    (Affine.isClosedSubgroup_parabolicHom (α ≫ i)) hF T

end Affine

end Dynamic

namespace StandardWeylMinimal

open Langlands.Aubert.General.RationalPointFamily
open Langlands.Group.RelativeWeylIndexing

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)

omit [IsAffineHom G.X.hom] [Mono i.hom.hom.left] in
/-- Conjugation by a normalizer point on rational points is the preimage under the
inner automorphism of its inverse. -/
theorem map_conj_eq_rationalPoints_comap (F : SubgroupFunctor G) (n : normalizerPoints i) :
    F.rationalPoints.map (MulAut.conj (n : rationalPoints G)).toMonoidHom =
      (F.comap (G.innerIso ((n⁻¹ : normalizerPoints i) : rationalPoints G)).hom).rationalPoints := by
  rw [Subgroup.coe_inv, G.innerIso_inv_hom, SubgroupFunctor.rationalPoints_comap_innerIso_inv]

omit [Mono i.hom.hom.left] in
/-- The conjugated standard parabolic, Levi and unipotent subgroups are the rational points of
the dynamic subgroups of one transported torus cocharacter. -/
theorem exists_map_conj_eq_dynamic (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν)) (n : normalizerPoints i) :
    ∃ eta : cocharacterLattice T,
      (parabolic i ν I).map (MulAut.conj (n : rationalPoints G)).toMonoidHom =
        (Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i)).rationalPoints ∧
      (levi i ν I).map (MulAut.conj (n : rationalPoints G)).toMonoidHom =
        (Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)).rationalPoints ∧
      (unipotent i ν I).map (MulAut.conj (n : rationalPoints G)).toMonoidHom =
        (Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)).rationalPoints := by
  obtain ⟨⟨zeta, hzeta⟩, hc⟩ :=
    standardCocharacter k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨hP, hL, hU⟩ := hc zeta hzeta
  refine ⟨(cocharacterAut (normalizingAut i n⁻¹)).symm zeta, ?_, ?_, ?_⟩
  · change (standardParabolic i ν (rootSet i ν I)).rationalPoints.map _ = _
    rw [map_conj_eq_rationalPoints_comap, hP, dynamicParabolic_comap_innerIso]
  · change (standardLevi i ν (rootSet i ν I)).rationalPoints.map _ = _
    rw [map_conj_eq_rationalPoints_comap, hL, dynamicCentralizer_comap_innerIso_hom]
  · change (standardUnipotent i ν (rootSet i ν I)).rationalPoints.map _ = _
    rw [map_conj_eq_rationalPoints_comap, hU, dynamicUnipotent_comap_innerIso]

omit [Mono i.hom.hom.left] in
/-- The standard parabolic, Levi and unipotent subgroups are the rational points of the
dynamic subgroups of one standard cocharacter. -/
theorem exists_eq_dynamic (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (J : Finset (SimpleRoot i ν)) :
    ∃ mu : cocharacterLattice T,
      parabolic i ν J = (Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ i)).rationalPoints ∧
      levi i ν J = (Dynamic.centralizer (CommGroupScheme.groupHom mu ≫ i)).rationalPoints ∧
      unipotent i ν J = (Dynamic.unipotent (CommGroupScheme.groupHom mu ≫ i)).rationalPoints := by
  obtain ⟨⟨mu, hmu⟩, hc⟩ :=
    standardCocharacter k G hG T i hi ν hν (rootSet i ν J) (rootSet_subset i ν J)
  obtain ⟨hP, hL, hU⟩ := hc mu hmu
  exact ⟨mu, congrArg SubgroupFunctor.rationalPoints hP,
    congrArg SubgroupFunctor.rationalPoints hL, congrArg SubgroupFunctor.rationalPoints hU⟩

omit [Mono i.hom.hom.left] in
/-- `P_J ∩ n P_I n⁻¹ = (P_J ∩ n L_I n⁻¹)(P_J ∩ n U_I n⁻¹)` for every normalizer point. -/
theorem parabolic_inf_map_parabolic_eq_mul (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (I J : Finset (SimpleRoot i ν)) (n : normalizerPoints i) :
    ((parabolic i ν J ⊓ (parabolic i ν I).map (MulAut.conj (n : rationalPoints G)).toMonoidHom :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) =
      ((parabolic i ν J ⊓ (levi i ν I).map (MulAut.conj (n : rationalPoints G)).toMonoidHom :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
      ((parabolic i ν J ⊓ (unipotent i ν I).map (MulAut.conj (n : rationalPoints G)).toMonoidHom :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.isSeparated
  obtain ⟨eta, hP, hL, hU⟩ := exists_map_conj_eq_dynamic i ν hG hi hν I n
  obtain ⟨mu, hPJ, -, -⟩ := exists_eq_dynamic i ν hG hi hν J
  rw [hP, hL, hU, hPJ]
  exact Dynamic.parabolic_inf_parabolic_eq_mul i (CommGroupScheme.groupHom mu)
    (CommGroupScheme.groupHom eta) (Over.mk (𝟙 _))

omit [Mono i.hom.hom.left] in
/-- `U_J ∩ n P_I n⁻¹ = (U_J ∩ n L_I n⁻¹)(U_J ∩ n U_I n⁻¹)` for every normalizer point. -/
theorem unipotent_inf_map_parabolic_eq_mul (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (I J : Finset (SimpleRoot i ν)) (n : normalizerPoints i) :
    ((unipotent i ν J ⊓ (parabolic i ν I).map (MulAut.conj (n : rationalPoints G)).toMonoidHom :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) =
      ((unipotent i ν J ⊓ (levi i ν I).map (MulAut.conj (n : rationalPoints G)).toMonoidHom :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
      ((unipotent i ν J ⊓ (unipotent i ν I).map (MulAut.conj (n : rationalPoints G)).toMonoidHom :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.isSeparated
  obtain ⟨eta, hP, hL, hU⟩ := exists_map_conj_eq_dynamic i ν hG hi hν I n
  obtain ⟨mu, -, -, hUJ⟩ := exists_eq_dynamic i ν hG hi hν J
  rw [hP, hL, hU, hUJ]
  exact Dynamic.unipotent_inf_parabolic_eq_mul i (CommGroupScheme.groupHom mu)
    (CommGroupScheme.groupHom eta) (Over.mk (𝟙 _))

section Coxeter

variable {CM : CoxeterMatrix (SimpleRoot i ν)} (cs : CoxeterSystem CM (relativeWeylGroup i))

omit [Mono i.hom.hom.left] in
/-- With `I = ∅` the source-side intersection subset is empty. -/
theorem intersectionSubset_empty (J : Finset (SimpleRoot i ν)) (w : relativeWeylGroup i) :
    intersectionSubset cs ∅ J w = ∅ := by
  classical
  unfold intersectionSubset
  rw [Finset.filter_eq_empty_iff]
  intro j _ hj
  rw [standardSubgroup_empty, Subgroup.mem_bot] at hj
  have h1 : cs.simple j = 1 := by
    have h := congrArg (fun x => w⁻¹ * x * w) hj
    simpa [mul_assoc] using h
  have h2 := cs.length_simple j
  rw [h1, cs.length_one] at h2
  exact zero_ne_one h2

omit [Mono i.hom.hom.left] in
/-- Double-coset minimality is inherited by smaller index sets. -/
theorem isMinimal_mono {I I' J J' : Finset (SimpleRoot i ν)} {w : relativeWeylGroup i}
    (h : IsMinimal cs I J w) (hI : I' ⊆ I) (hJ : J' ⊆ J) : IsMinimal cs I' J' w :=
  fun a ha b hb => h a (standardSubgroup_mono cs hI ha) b (standardSubgroup_mono cs hJ hb)

/-- For an element minimal in `w W_J`, conjugation by any lift preserves membership in
`P_∅` on `L_J`. -/
theorem conj_mem_parabolic_empty_iff (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hcs : IsRelativeWeylCoxeterRealization i ν cs)
    (J : Finset (SimpleRoot i ν)) {x : relativeWeylGroup i} (hx : IsMinimal cs ∅ J x)
    (m : normalizerPoints i) (hm : QuotientGroup.mk m = x) {y : rationalPoints G}
    (hy : y ∈ levi i ν J) :
    (m : rationalPoints G) * y * (m : rationalPoints G)⁻¹ ∈ parabolic i ν ∅ ↔
      y ∈ parabolic i ν ∅ := by
  obtain ⟨hP, hU⟩ :=
    standardSourceTwistedIntersection k G hG T i hi ν hν CM cs hcs ∅ J x hx m hm
  obtain ⟨hp, -⟩ := standardSourcePoints_twistedIntersection_of_functor_eq i ν ∅ J _ _ hP hU
  rw [intersectionSubset_empty] at hp
  have h := SetLike.ext_iff.mp hp y
  simp only [Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv] at h
  exact ⟨fun hmy => (h.mp ⟨hy, hmy⟩).2, fun hy0 => (h.mpr ⟨hy, hy0⟩).2⟩

omit [Mono i.hom.hom.left] in
theorem parabolic_empty_eq : parabolic i ν ∅ = standardParabolicPoints i ν ∅ := by
  show standardParabolicPoints i ν (rootSet i ν ∅) = _
  rw [rootSet_empty]

/-- **Right minimality from the Tits system.** If `n (L_J ∩ P_∅) n⁻¹ ⊆ P_∅`, the class of `n`
is minimal in its coset `w W_J`. -/
theorem isMinimal_empty_of_conj_le (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hcs : IsRelativeWeylCoxeterRealization i ν cs)
    (hT : HasRelativeTitsSystem i ν) (J : Finset (SimpleRoot i ν)) (n : normalizerPoints i)
    (hn : ∀ y ∈ levi i ν J, y ∈ parabolic i ν ∅ →
      (n : rationalPoints G) * y * (n : rationalPoints G)⁻¹ ∈ parabolic i ν ∅) :
    IsMinimal cs ∅ J (QuotientGroup.mk n) := by
  have := hG.isSeparated
  obtain ⟨x, ⟨a, ha, b, hb, hxe⟩, hxmin⟩ :=
    exists_minimal_in_doubleCoset_unrestricted cs ∅ J (QuotientGroup.mk n)
  rw [standardSubgroup_empty, Subgroup.mem_bot] at ha
  subst ha
  rw [hcs.2.2.2.2 J] at hb
  obtain ⟨nb, hnbL, rfl⟩ := (mem_standardRelativeWeylGroup_iff i ν).mp hb
  have hx : QuotientGroup.mk (n * nb) = x := by rw [hxe, one_mul]; rfl
  have h1 : ∀ y ∈ levi i ν J, y ∈ parabolic i ν ∅ →
      (nb : rationalPoints G)⁻¹ * y * nb ∈ parabolic i ν ∅ := by
    intro y hyL hyP
    have hyL' : (nb : rationalPoints G)⁻¹ * y * nb ∈ levi i ν J :=
      mul_mem (mul_mem (inv_mem hnbL) hyL) hnbL
    refine (conj_mem_parabolic_empty_iff i ν cs hG hi hν hcs J hxmin (n * nb) hx hyL').mp ?_
    have he : ((n * nb : normalizerPoints i) : rationalPoints G) *
        ((nb : rationalPoints G)⁻¹ * y * nb) * ((n * nb : normalizerPoints i) : rationalPoints G)⁻¹ =
        (n : rationalPoints G) * y * (n : rationalPoints G)⁻¹ := by
      simp only [Subgroup.coe_mul]
      group
    rw [he]
    exact hn y hyL hyP
  obtain ⟨mu, hPJ, hLJ, hUJ⟩ := exists_eq_dynamic i ν hG hi hν J
  obtain ⟨hord, -⟩ := standardParabolicOrder k G hG T i hi ν hν
  have hsub : rootSet i ν ∅ ⊆ rootSet i ν J := by simp
  have hP0PJ : parabolic i ν ∅ ≤ parabolic i ν J :=
    ((hord _ _ (rootSet_subset i ν ∅) (rootSet_subset i ν J)).1.mp hsub) (Over.mk (𝟙 _))
  have hUJU0 : unipotent i ν J ≤ unipotent i ν ∅ :=
    ((hord _ _ (rootSet_subset i ν ∅) (rootSet_subset i ν J)).2 hsub).2 (Over.mk (𝟙 _))
  have hU0P0 : unipotent i ν ∅ ≤ parabolic i ν ∅ := unipotent_le_parabolic i ν ∅
  have h2 : ∀ b0 ∈ standardParabolicPoints i ν ∅,
      (nb : rationalPoints G)⁻¹ * b0 * nb ∈ standardParabolicPoints i ν ∅ := by
    intro b0 hb0
    rw [← parabolic_empty_eq] at hb0 ⊢
    have hb0J : b0 ∈ parabolic i ν J := hP0PJ hb0
    rw [hPJ] at hb0J
    obtain ⟨l, hl, u, hu, hlu⟩ := Dynamic.exists_centralizer_mul_unipotent _ hb0J
    have hu' : u ∈ unipotent i ν J := by rw [hUJ]; exact hu
    have hl' : l ∈ levi i ν J := by rw [hLJ]; exact hl
    have huP0 : u ∈ parabolic i ν ∅ := hU0P0 (hUJU0 hu')
    have hlP0 : l ∈ parabolic i ν ∅ := by
      have hle : l = b0 * u⁻¹ := by rw [← hlu, mul_inv_cancel_right]
      rw [hle]
      exact mul_mem hb0 (inv_mem huP0)
    have hconjU : (nb : rationalPoints G)⁻¹ * u * nb ∈ unipotent i ν J := by
      have hnbP : (nb : rationalPoints G)⁻¹ ∈
          (Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ i)).rationalPoints := by
        rw [← hPJ]
        exact levi_le_parabolic i ν J (inv_mem hnbL)
      rw [hUJ]
      simpa only [inv_inv] using Dynamic.conj_mem_unipotent _ hnbP hu
    have he : (nb : rationalPoints G)⁻¹ * b0 * nb =
        ((nb : rationalPoints G)⁻¹ * l * nb) * ((nb : rationalPoints G)⁻¹ * u * nb) := by
      rw [← hlu]
      group
    rw [he]
    exact mul_mem (h1 l hl' hlP0) (hU0P0 (hUJU0 hconjU))
  have hnbB : (nb : rationalPoints G) ∈ standardParabolicPoints i ν ∅ :=
    hT.isTitsSystem.mem_of_conjugate_le le_rfl (nb : rationalPoints G) h2
  have hnbZ : (nb : rationalPoints G) ∈ centralizerPoints i := by
    rw [← hT.inf_eq]
    exact ⟨hnbB, nb.2⟩
  have hb1 : (QuotientGroup.mk nb : relativeWeylGroup i) = 1 :=
    (QuotientGroup.eq_one_iff nb).mpr hnbZ
  rw [hxe, hb1, one_mul, mul_one] at hxmin
  exact hxmin

/-- **Key equivalence.** For any lift `n`, the two `P_∅`-conditions defining `W^{L,M}` hold
iff the class of `n` is minimal in its double coset `W_M w W_L`. -/
theorem conj_le_iff_isMinimal (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hcs : IsRelativeWeylCoxeterRealization i ν cs)
    (hT : HasRelativeTitsSystem i ν) (IL IM : Finset (SimpleRoot i ν))
    (n : normalizerPoints i) :
    ((levi i ν IL ⊓ parabolic i ν ∅).map (MulAut.conj (n : rationalPoints G)).toMonoidHom ≤
        parabolic i ν ∅ ∧
      (levi i ν IM ⊓ parabolic i ν ∅).map
          (MulAut.conj ((n⁻¹ : normalizerPoints i) : rationalPoints G)).toMonoidHom ≤
        parabolic i ν ∅) ↔
      IsMinimal cs IM IL (QuotientGroup.mk n) := by
  have hinv : (QuotientGroup.mk n⁻¹ : relativeWeylGroup i) = (QuotientGroup.mk n)⁻¹ := rfl
  constructor
  · rintro ⟨h1, h2⟩
    have hR := isMinimal_empty_of_conj_le i ν cs hG hi hν hcs hT IL n
      (fun y hyL hyP => h1 ⟨y, ⟨hyL, hyP⟩, rfl⟩)
    have hL := isMinimal_inv cs (isMinimal_empty_of_conj_le i ν cs hG hi hν hcs hT IM n⁻¹
      (fun y hyL hyP => h2 ⟨y, ⟨hyL, hyP⟩, rfl⟩))
    rw [hinv, inv_inv] at hL
    have c := minimalityLengthCriterion_proof cs
    exact (c IM IL _).mpr ⟨((c IM ∅ _).mp hL).1, ((c ∅ IL _).mp hR).2⟩
  · intro hmin
    constructor
    · rw [Subgroup.map_le_iff_le_comap]
      rintro y ⟨hyL, hyP⟩
      exact (conj_mem_parabolic_empty_iff i ν cs hG hi hν hcs IL
        (isMinimal_mono i ν cs hmin (Finset.empty_subset _) subset_rfl) n rfl hyL).mpr hyP
    · rw [Subgroup.map_le_iff_le_comap]
      rintro y ⟨hyL, hyP⟩
      exact (conj_mem_parabolic_empty_iff i ν cs hG hi hν hcs IM
        (isMinimal_mono i ν cs (isMinimal_inv cs hmin) (Finset.empty_subset _) subset_rfl)
        n⁻¹ hinv hyL).mpr hyP

/-- Membership in `W^{L,M}` (some lift satisfies both `P_∅`-conditions) is minimality in the
double coset `W_M v W_L`, for every Coxeter system realizing the relative root action. -/
theorem exists_conj_le_iff_isMinimal (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hcs : IsRelativeWeylCoxeterRealization i ν cs)
    (hT : HasRelativeTitsSystem i ν) (IL IM : Finset (SimpleRoot i ν))
    (v : relativeWeylGroup i) :
    (∃ n : normalizerPoints i, (QuotientGroup.mk n : relativeWeylGroup i) = v ∧
      (levi i ν IL ⊓ parabolic i ν ∅).map (MulAut.conj (n : rationalPoints G)).toMonoidHom ≤
          parabolic i ν ∅ ∧
        (levi i ν IM ⊓ parabolic i ν ∅).map
            (MulAut.conj ((n⁻¹ : normalizerPoints i) : rationalPoints G)).toMonoidHom ≤
          parabolic i ν ∅) ↔
      IsMinimal cs IM IL v := by
  constructor
  · rintro ⟨n, rfl, h⟩
    exact (conj_le_iff_isMinimal i ν cs hG hi hν hcs hT IL IM n).mp h
  · intro h
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective v
    exact ⟨n, rfl, (conj_le_iff_isMinimal i ν cs hG hi hν hcs hT IL IM n).mpr h⟩

/-- Part (ii), Levi `M` side: for a lift `n` of a minimal double-coset representative,
`M ∩ nQn⁻¹`, `M ∩ nLn⁻¹` and `M ∩ nUn⁻¹` are given by the standard subset
`K = intersectionSubset cs IL IM w⁻¹ ⊆ IM`. -/
theorem exists_levi_inf_map_conj_eq (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hcs : IsRelativeWeylCoxeterRealization i ν cs)
    (IL IM : Finset (SimpleRoot i ν)) (n : normalizerPoints i)
    (hmin : IsMinimal cs IM IL (QuotientGroup.mk n)) :
    ∃ K : Finset (SimpleRoot i ν), K ⊆ IM ∧
      levi i ν IM ⊓ (parabolic i ν IL).map (MulAut.conj (n : rationalPoints G)).toMonoidHom =
        levi i ν IM ⊓ parabolic i ν K ∧
      levi i ν IM ⊓ (levi i ν IL).map (MulAut.conj (n : rationalPoints G)).toMonoidHom =
        levi i ν K ∧
      levi i ν IM ⊓ (unipotent i ν IL).map (MulAut.conj (n : rationalPoints G)).toMonoidHom =
        levi i ν IM ⊓ unipotent i ν K := by
  have hinv : (QuotientGroup.mk n⁻¹ : relativeWeylGroup i) = (QuotientGroup.mk n)⁻¹ := rfl
  have hmin' := isMinimal_inv cs hmin
  obtain ⟨hP, hU⟩ :=
    standardSourceTwistedIntersection k G hG T i hi ν hν CM cs hcs IL IM _ hmin' n⁻¹ hinv
  obtain ⟨hp, hu⟩ := standardSourcePoints_twistedIntersection_of_functor_eq i ν IL IM _ _ hP hU
  have hL := standardLeviTwistedIntersection k G hG T i hi ν hν CM cs hcs IL IM _ hmin' n⁻¹ hinv
  have hl := standardLeviPoints_twistedIntersection_of_functor_eq i ν IL IM _ _ hL
  rw [Subgroup.coe_inv, inv_inv] at hp hu hl
  exact ⟨_, intersectionSubset_subset cs IL IM _, hp, hl, hu⟩

/-- Part (ii), Levi `L` side: for a lift `n` of a minimal double-coset representative `w`,
`L ∩ n⁻¹Pn`, `L ∩ n⁻¹Mn` and `L ∩ n⁻¹Nn` are given by the standard subset
`K' = intersectionSubset cs IM IL w ⊆ IL`. -/
theorem exists_levi_inf_map_conj_inv_eq (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hcs : IsRelativeWeylCoxeterRealization i ν cs)
    (IL IM : Finset (SimpleRoot i ν)) (n : normalizerPoints i)
    (hmin : IsMinimal cs IM IL (QuotientGroup.mk n)) :
    ∃ K' : Finset (SimpleRoot i ν), K' ⊆ IL ∧
      levi i ν IL ⊓ (parabolic i ν IM).map
          (MulAut.conj ((n⁻¹ : normalizerPoints i) : rationalPoints G)).toMonoidHom =
        levi i ν IL ⊓ parabolic i ν K' ∧
      levi i ν IL ⊓ (levi i ν IM).map
          (MulAut.conj ((n⁻¹ : normalizerPoints i) : rationalPoints G)).toMonoidHom =
        levi i ν K' ∧
      levi i ν IL ⊓ (unipotent i ν IM).map
          (MulAut.conj ((n⁻¹ : normalizerPoints i) : rationalPoints G)).toMonoidHom =
        levi i ν IL ⊓ unipotent i ν K' := by
  obtain ⟨hP, hU⟩ :=
    standardSourceTwistedIntersection k G hG T i hi ν hν CM cs hcs IM IL _ hmin n rfl
  obtain ⟨hp, hu⟩ := standardSourcePoints_twistedIntersection_of_functor_eq i ν IM IL _ _ hP hU
  have hL := standardLeviTwistedIntersection k G hG T i hi ν hν CM cs hcs IM IL _ hmin n rfl
  have hl := standardLeviPoints_twistedIntersection_of_functor_eq i ν IM IL _ _ hL
  rw [Subgroup.coe_inv]
  exact ⟨_, intersectionSubset_subset cs IM IL _, hp, hl, hu⟩

end Coxeter

omit [IsAffineHom G.X.hom] [Mono i.hom.hom.left] in
/-- Conjugation by an element of a subgroup maps the subgroup onto itself. -/
theorem map_conj_eq_of_mem {H : Subgroup (rationalPoints G)} {m : rationalPoints G}
    (hm : m ∈ H) : H.map (MulAut.conj m).toMonoidHom = H := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact H.mul_mem (H.mul_mem hm hz) (H.inv_mem hm)
  · intro hy
    refine ⟨m⁻¹ * y * m, H.mul_mem (H.mul_mem (H.inv_mem hm) hy) hm, ?_⟩
    simp [mul_assoc]

omit [IsAffineHom G.X.hom] [Mono i.hom.hom.left] in
/-- Conjugation by a product of normalizer points is the composite of the conjugations. -/
theorem map_conj_mul (H : Subgroup (rationalPoints G)) (n m : normalizerPoints i) :
    H.map (MulAut.conj ((n * m : normalizerPoints i) : rationalPoints G)).toMonoidHom =
      (H.map (MulAut.conj (m : rationalPoints G)).toMonoidHom).map
        (MulAut.conj (n : rationalPoints G)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

end StandardWeylMinimal

open Langlands.Aubert.General.RationalPointFamily
open Langlands.Group.RelativeWeylIndexing
open StandardWeylMinimal

/-- **Renard V.4.6 (Lemma).** Minimal representatives of standard Weyl double cosets and
the intersections of standard parabolic subgroups they produce. -/
theorem standardWeylMinimalRepresentatives : StandardWeylMinimalRepresentativesStatement.{u} := by
  intro k _ _ _ _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν conj WS P0 Wmin WLM IL IM
  obtain ⟨-, -, CM, cs, hcs⟩ := relativeWeylCoxeter k G hG T i hi ν hν
  have hT := relativeTitsSystem k G hG T i hi ν hν
  -- membership in `W^{L,M}` is double-coset minimality, for every realization
  have hWmin : ∀ {C : CoxeterMatrix (SimpleRoot i ν)} (cs' : CoxeterSystem C (relativeWeylGroup i)),
      IsRelativeWeylCoxeterRealization i ν cs' → ∀ v, v ∈ Wmin IL IM ↔ IsMinimal cs' IM IL v :=
    fun cs' hcs' v => exists_conj_le_iff_isMinimal i ν cs' hG hi hν hcs' hT IL IM v
  have hD : ∀ {C : CoxeterMatrix (SimpleRoot i ν)} (cs' : CoxeterSystem C (relativeWeylGroup i)),
      IsRelativeWeylCoxeterRealization i ν cs' → ∀ v w : relativeWeylGroup i,
        (∃ a ∈ WS IM, ∃ b ∈ WS IL, v = a * w * b) ↔ v ∈ doubleCoset cs' IM IL w := by
    intro C cs' hcs' v w
    show (∃ a ∈ standardRelativeWeylGroup i ν (rootSet i ν IM),
      ∃ b ∈ standardRelativeWeylGroup i ν (rootSet i ν IL), v = a * w * b) ↔ _
    rw [← hcs'.2.2.2.2 IM, ← hcs'.2.2.2.2 IL]
    rfl
  -- (i), existence and uniqueness
  have hex : ∀ w : relativeWeylGroup i,
      ∃! v, v ∈ Wmin IL IM ∧ ∃ a ∈ WS IM, ∃ b ∈ WS IL, v = a * w * b := by
    intro w
    obtain ⟨x, hxd, hxmin⟩ := exists_minimal_in_doubleCoset_unrestricted cs IM IL w
    refine ⟨x, ⟨(hWmin cs hcs x).mpr hxmin, (hD cs hcs x w).mpr hxd⟩, ?_⟩
    rintro y ⟨hyW, hyd⟩
    exact minimalRepresentativeUnique_proof cs IM IL w y x ((hD cs hcs y w).mp hyd) hxd
      ((hWmin cs hcs y).mp hyW) hxmin
  refine ⟨hex, ?_, ?_, ?_⟩
  · -- (i), strict length inequality
    intro C cs' hcs' v hv a ha b hb hne
    have hvmin := (hWmin cs' hcs' v).mp hv
    have ha' : a ∈ standardSubgroup cs' IM := by rw [hcs'.2.2.2.2 IM]; exact ha
    have hb' : b ∈ standardSubgroup cs' IL := by rw [hcs'.2.2.2.2 IL]; exact hb
    refine lt_of_le_of_ne (hvmin a ha' b hb') fun heq => hne ?_
    have hmin2 : IsMinimal cs' IM IL (a * v * b) := by
      intro a2 ha2 b2 hb2
      rw [← heq]
      have h := hvmin (a2 * a) (mul_mem ha2 ha') (b * b2) (mul_mem hb' hb2)
      simpa only [mul_assoc] using h
    exact minimalRepresentativeUnique_proof cs' IM IL v _ _ ⟨a, ha', b, hb', rfl⟩
      (mem_doubleCoset_self cs' IM IL v) hmin2 hvmin
  · -- (ii)
    intro n hn
    have hmin := (hWmin cs hcs _).mp hn
    exact ⟨exists_levi_inf_map_conj_eq i ν cs hG hi hν hcs IL IM n hmin,
      exists_levi_inf_map_conj_inv_eq i ν cs hG hi hν hcs IL IM n hmin,
      parabolic_inf_map_parabolic_eq_mul i ν hG hi hν IL IM n,
      parabolic_inf_map_parabolic_eq_mul i ν hG hi hν IM IL n⁻¹,
      unipotent_inf_map_parabolic_eq_mul i ν hG hi hν IL IM n,
      unipotent_inf_map_parabolic_eq_mul i ν hG hi hν IM IL n⁻¹⟩
  · -- (iii)
    intro w hw
    obtain ⟨n, hnw, hnL⟩ := hw
    have hnL' : (levi i ν IL).map (MulAut.conj (n : rationalPoints G)).toMonoidHom =
        levi i ν IM := hnL
    have hcomm : ∀ a ∈ WS IM, ∃ b ∈ WS IL, a * w = w * b := by
      intro a ha
      obtain ⟨m, hmL, rfl⟩ := (mem_standardRelativeWeylGroup_iff i ν).mp ha
      have hmL' : (m : rationalPoints G) ∈
          (levi i ν IL).map (MulAut.conj (n : rationalPoints G)).toMonoidHom := by
        rw [hnL']
        exact hmL
      obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hmL'
      refine ⟨QuotientGroup.mk (n⁻¹ * m * n),
        (mem_standardRelativeWeylGroup_iff i ν).mpr ⟨n⁻¹ * m * n, ?_, rfl⟩, ?_⟩
      · have he : ((n⁻¹ * m * n : normalizerPoints i) : rationalPoints G) = y := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hye]
          simp [mul_assoc]
        rw [he]
        exact hy
      · rw [← hnw]
        show (QuotientGroup.mk (m * n) : relativeWeylGroup i) =
          QuotientGroup.mk (n * (n⁻¹ * m * n))
        congr 1
        group
    obtain ⟨x, ⟨hxW, a, ha, b, hb, hxe⟩, huniq⟩ := hex w
    obtain ⟨b', hb', hab⟩ := hcomm a ha
    refine ⟨⟨x, ⟨hxW, ?_, b' * b, mul_mem hb' hb, by rw [hxe, hab, mul_assoc]⟩, ?_⟩, hcomm⟩
    · obtain ⟨m, hmL, hme⟩ := (mem_standardRelativeWeylGroup_iff i ν).mp (mul_mem hb' hb)
      refine ⟨n * m, ?_, ?_⟩
      · rw [hxe, hab, mul_assoc, ← hme, ← hnw]
        rfl
      · show (levi i ν IL).map
          (MulAut.conj ((n * m : normalizerPoints i) : rationalPoints G)).toMonoidHom = levi i ν IM
        rw [map_conj_mul, map_conj_eq_of_mem hmL, hnL']
    · rintro y ⟨hyW, -, b2, hb2, rfl⟩
      exact huniq _ ⟨hyW, 1, (WS IM).one_mem, b2, hb2, by rw [one_mul]⟩

end Langlands.GroupScheme
