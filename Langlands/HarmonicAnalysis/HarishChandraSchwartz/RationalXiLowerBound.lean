import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeights
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalBounds
import Langlands.BruhatTits.SpecialCompact.JacquetStrictElement

/-! # The minimal modulus on `U₀(F)` and the lower bound of Lemma II.1.1 on actual points

Given one member `H ≤ K` of Renard's V.5.2 basis for the minimal standard parabolic `P₀ = P_∅`
(an ordered Iwahori factorization of `H` and the contraction clauses for a compatible split
component of `M₀`), the modulus `δ₀` is trivial on `U₀(F)`, so the spherical function `Ξ` of
`RationalWeights` is Waldspurger's `∫_K δ₀(m₀(kg))^{1/2} dk`, and `Ξ` satisfies the lower bound
of Lemma II.1.1 on the weak chamber of the split component.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
  {K : Subgroup (rationalPoints G)}
  (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
  {H : Subgroup (rationalPoints G)} (hHK : H ≤ K)
  (hH : StandardParabolicBasisMember i ν ∅ q H)

include hKo hKc hHK hH in
/-- **`δ₀` is trivial on `U₀(F)`.** With a strict element `g` of the split component of `M₀`,
every `u ∈ U₀(F)` is `g^{-n} x g^n` with `x ∈ H ∩ U₀(F) ⊆ K` (strict exhaustion), and `δ₀` is
trivial on `P₀(F) ∩ K`. -/
theorem rationalMinimalModulus_eq_one_of_mem_unipotent (hi : IsMaximalSplitTorus i)
    (hA : IsCompatibleStandardSplitComponent i ν ∅ A q) (p : standardParabolicPoints i ν ∅)
    (hpU : (p : rationalPoints G) ∈ standardUnipotentPoints i ν ∅) :
    rationalMinimalModulus i ν p = 1 := by
  obtain ⟨g, hgM, -, -, hgstrict⟩ :=
    hA.exists_strict_element i ν hi (isStandardCocharacter_empty_self i ν)
  have hgP : g ∈ standardParabolicPoints i ν ∅ := standardLevi_le_standardParabolic i ν ∅ _ hgM
  have hpU' : (p : rationalPoints G) ∈
      (standardUnipotentPoints i ν ∅ : Set (rationalPoints G)) := hpU
  rw [(hH.2.2.2.1 g hgstrict).1] at hpU'
  obtain ⟨n, x, hx, hxp⟩ := Set.mem_iUnion.mp hpU'
  have hxP : x ∈ standardParabolicPoints i ν ∅ :=
    standardUnipotent_le_standardParabolic i ν ∅ _ hx.2
  have hδx : rationalMinimalModulus i ν ⟨x, hxP⟩ = 1 :=
    rationalMinimalModulus_eq_one i ν hKo hKc ⟨x, hxP⟩ (hHK hx.1)
  set a : standardParabolicPoints i ν ∅ := (⟨g, hgP⟩ ^ n)⁻¹ with ha
  have hpeq : p = a * ⟨x, hxP⟩ * a⁻¹ := by
    apply Subtype.ext
    rw [← hxp, ha]
    simp
  rw [hpeq, map_mul, map_mul, hδx, mul_one, ← map_mul, mul_inv_cancel, map_one]

include hKo hKc hHK hH in
/-- `δ₀(u m) = δ₀(m)` for `u ∈ U₀(F)` and `m ∈ M₀(F)`. -/
theorem rationalMinimalModulus_mul_of_mem_unipotent (hi : IsMaximalSplitTorus i)
    (hA : IsCompatibleStandardSplitComponent i ν ∅ A q) {u m : rationalPoints G}
    (hu : u ∈ standardUnipotentPoints i ν ∅) (hm : m ∈ standardLeviPoints i ν ∅) :
    rationalMinimalModulus i ν ⟨u * m, (standardParabolicPoints i ν ∅).mul_mem
        (standardUnipotent_le_standardParabolic i ν ∅ _ hu)
        (standardLevi_le_standardParabolic i ν ∅ _ hm)⟩ =
      rationalMinimalModulus i ν ⟨m, standardLevi_le_standardParabolic i ν ∅ _ hm⟩ := by
  have h1 : (⟨u * m, (standardParabolicPoints i ν ∅).mul_mem
        (standardUnipotent_le_standardParabolic i ν ∅ _ hu)
        (standardLevi_le_standardParabolic i ν ∅ _ hm)⟩ : standardParabolicPoints i ν ∅) =
      ⟨u, standardUnipotent_le_standardParabolic i ν ∅ _ hu⟩ *
        ⟨m, standardLevi_le_standardParabolic i ν ∅ _ hm⟩ := rfl
  rw [h1, map_mul, rationalMinimalModulus_eq_one_of_mem_unipotent hKo hKc hHK hH hi hA _ hu,
    one_mul]

include hKo hKc hHK hH in
/-- **Waldspurger's integrand.** For `g = u m k` with `u ∈ U₀(F)`, `m ∈ M₀(F)`, `k ∈ K`, the
integrand of `Ξ` is `δ₀(m)^{1/2}`, so `rationalXi` is Waldspurger's `∫_K δ₀(m₀(kg))^{1/2} dk`. -/
theorem iwasawaWeight_rationalMinimalModulus (hi : IsMaximalSplitTorus i)
    (hA : IsCompatibleStandardSplitComponent i ν ∅ A q)
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K) {u m k : rationalPoints G}
    (hu : u ∈ standardUnipotentPoints i ν ∅) (hm : m ∈ standardLeviPoints i ν ∅) (hk : k ∈ K) :
    iwasawaWeight hPK (rationalMinimalModulus i ν) (u * m * k) =
      (NNReal.sqrt (rationalMinimalModulus i ν
        ⟨m, standardLevi_le_standardParabolic i ν ∅ _ hm⟩ : ℝ≥0) : ℝ) := by
  rw [iwasawaWeight_mul (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp)
    ((standardParabolicPoints i ν ∅).mul_mem (standardUnipotent_le_standardParabolic i ν ∅ _ hu)
      (standardLevi_le_standardParabolic i ν ∅ _ hm)) hk,
    rationalMinimalModulus_mul_of_mem_unipotent hKo hKc hHK hH hi hA hu hm]

include hKo hHK hH in
/-- **The lower bound of Waldspurger's Lemma II.1.1** on the weak chamber of the split component
of `M₀`: `φ(a) ≤ C Ξ(a)` with `φ(p k) = δ₀(p)^{1/2}` and `C = mes(H)⁻¹`, from the factorization
`H = (H ∩ P₀(F)) (H ∩ Ū₀(F))` and the contraction `a⁻¹ (H ∩ Ū₀(F)) a ⊆ H` of the basis member. -/
theorem rationalXi_lowerBound (hHo : IsOpen (H : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K) :
    XiLowerBound (rationalXi hKc hPK) (standardComponentCAplus i ν ∅ q)
      (iwasawaWeight hPK (rationalMinimalModulus i ν)) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  unfold rationalXi
  refine xiLowerBound_of_factorization
    (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp) hKo hHK hHo
    (V := ((H ⊓ standardOppositeUnipotentPoints i ν ∅ : Subgroup (rationalPoints G)) :
      Set (rationalPoints G))) ?_ ?_
  · intro h hh
    obtain ⟨⟨l, m, n⟩, heq⟩ := hH.1.2 ⟨h⁻¹, H.inv_mem hh⟩
    have heq' : h⁻¹ = (l : rationalPoints G) * m * n := (congrArg Subtype.val heq).symm
    refine ⟨(n : rationalPoints G)⁻¹ * (m : rationalPoints G)⁻¹, ?_, ?_,
      (l : rationalPoints G)⁻¹, ?_, ?_⟩
    · exact (standardParabolicPoints i ν ∅).mul_mem
        ((standardParabolicPoints i ν ∅).inv_mem
          (standardUnipotent_le_standardParabolic i ν ∅ _ n.2.2))
        ((standardParabolicPoints i ν ∅).inv_mem
          (standardLevi_le_standardParabolic i ν ∅ _ m.2.2))
    · exact H.mul_mem (H.inv_mem n.2.1) (H.inv_mem m.2.1)
    · exact ⟨H.inv_mem l.2.1, (standardOppositeUnipotentPoints i ν ∅).inv_mem l.2.2⟩
    · calc h = (h⁻¹)⁻¹ := (inv_inv h).symm
        _ = (n : rationalPoints G)⁻¹ * (m : rationalPoints G)⁻¹ *
            (l : rationalPoints G)⁻¹ := by
          rw [heq']
          group
  · intro g hg v hv
    have h := (hH.2.2.1 g hg).2 ⟨v, hv, rfl⟩
    simp only [inv_inv, SetLike.mem_coe] at h
    exact hHK h.1

include hKo hHK hH in
/-- The lower bound of Lemma II.1.1 in explicit form: `δ₀(a)^{1/2} ≤ C Ξ(a)` for every point `a`
of `P₀(F)` in the weak chamber of the split component of `M₀`. -/
theorem exists_sqrt_rationalMinimalModulus_le_rationalXi
    (hHo : IsOpen (H : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K) :
    ∃ C : ℝ, ∀ (a : rationalPoints G) (ha : a ∈ standardParabolicPoints i ν ∅),
      a ∈ standardComponentCAplus i ν ∅ q →
        (NNReal.sqrt (rationalMinimalModulus i ν ⟨a, ha⟩ : ℝ≥0) : ℝ) ≤
          C * rationalXi hKc hPK a := by
  obtain ⟨C, hC⟩ := rationalXi_lowerBound hKo hKc hHK hH hHo hPK
  refine ⟨C, fun a ha haC => ?_⟩
  have h := iwasawaWeight_mul (hPK := hPK)
    (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp) ha K.one_mem
  rw [mul_one] at h
  rw [← h]
  exact hC a haC

end Langlands.HarishChandraSchwartz
