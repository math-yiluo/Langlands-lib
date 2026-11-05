import Langlands.GroupScheme.Rational.SimplyConnectedCentralizerProductStatement
import Langlands.GroupScheme.Rational.BruhatUnipotentReduction
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Rational.GenericCocharacter

/-! # Actual rational-point reductions for the simply connected centralizer product -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : S.toGrp ⟶ G)

/-- The actual relative-Weyl projection restricted to normalizer points in a subgroup. -/
def subgroupRelativeWeylMap (H : Subgroup (rationalPoints G)) :
    H.subgroupOf (normalizerPoints i) →* relativeWeylGroup i :=
  (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i))).comp
    (H.subgroupOf (normalizerPoints i)).subtype

/-- Surjectivity of the restricted Weyl projection is precisely normalizer factorization. -/
theorem subgroupRelativeWeylMap_surjective_iff (H : Subgroup (rationalPoints G)) :
    Function.Surjective (subgroupRelativeWeylMap i H) ↔
      ∀ n : normalizerPoints i, ∃ h ∈ H, ∃ z ∈ centralizerPoints i,
        (n : rationalPoints G) = h * z := by
  constructor
  · intro hsurj n
    obtain ⟨m, hm⟩ := hsurj (QuotientGroup.mk n)
    change (QuotientGroup.mk m.val : relativeWeylGroup i) = QuotientGroup.mk n at hm
    have hzN : (m.val⁻¹ * n : normalizerPoints i) ∈
        (centralizerPoints i).subgroupOf (normalizerPoints i) :=
      QuotientGroup.eq.mp hm
    have hz : (m.val : rationalPoints G)⁻¹ * (n : rationalPoints G) ∈
        centralizerPoints i := hzN
    exact ⟨m.val.val, m.property, _, hz, by simp⟩
  · intro hfactor w
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨h, hh, z, hz, hn⟩ := hfactor n
    have hhn : h ∈ normalizerPoints i := by
      have : h = (n : rationalPoints G) * z⁻¹ := by rw [hn]; simp
      rw [this]
      exact (normalizerPoints i).mul_mem n.property
        ((normalizerPoints i).inv_mem (centralizerPoints_le_normalizerPoints i hz))
    refine ⟨⟨⟨h, hhn⟩, hh⟩, QuotientGroup.eq.mpr ?_⟩
    change h⁻¹ * (n : rationalPoints G) ∈ centralizerPoints i
    simpa only [hn, inv_mul_cancel_left] using hz

variable (ν : cocharacterLattice S)

/-- A whole-torus centralizer point conjugates dynamic unipotent points to themselves. -/
theorem centralizerPoints_conj_mem_dynamicUnipotent
    {z v : rationalPoints G} (hz : z ∈ centralizerPoints i)
    (hv : v ∈ RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i)) :
    z * v * z⁻¹ ∈ RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i) := by
  have hzL : z ∈ RationalPoint.levi (CommGroupScheme.groupHom ν ≫ i) :=
    torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom ν) _
      (by
        change z ∈ (torusCentralizer i).carrier (Over.mk (𝟙 _))
        rwa [torusCentralizer_carrier_base])
  exact (Subgroup.mem_normalizer_iff.mp
    (RationalPoint.levi_le_normalizer_unipotent _ hzL) v).mp hv

variable [IsAffineHom G.X.hom]

/-- Bruhat covering has the form `U(k) N(k) U(k) Z(k)` once the generic
cocharacter centralizer equals the whole-torus centralizer. -/
theorem exists_unipotent_normalizer_unipotent_centralizer_mul
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (hBr : HasRationalBruhatDecomposition i ν) (g : rationalPoints G) :
    ∃ (a b : RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i))
      (n : normalizerPoints i) (z : centralizerPoints i),
      g = (a : rationalPoints G) * (n : rationalPoints G) *
        (b : rationalPoints G) * (z : rationalPoints G) := by
  obtain ⟨n, hn, p, hp, q, hq, hg⟩ := hBr.1 g
  obtain ⟨⟨a, l⟩, ⟨ha, hl, hp⟩, _⟩ :=
    RationalPoint.existsUnique_unipotent_mul_levi _ hp
  obtain ⟨⟨r, b⟩, ⟨hr, hb, hq⟩, _⟩ :=
    RationalPoint.existsUnique_levi_mul_unipotent _ hq
  have hL := rationalLevi_eq_centralizerPoints_of_eq i ν hZ
  have hlZ : l ∈ centralizerPoints i := hL ▸ hl
  have hrZ : r ∈ centralizerPoints i := hL ▸ hr
  let z : rationalPoints G := (n⁻¹ * l * n) * r
  have hlconj : n⁻¹ * l * n ∈ centralizerPoints i := by
    simpa only [inv_inv] using
      (conj_mem_centralizerPoints i ((normalizerPoints i).inv_mem hn) hlZ)
  have hz : z ∈ centralizerPoints i := (centralizerPoints i).mul_mem
    hlconj hrZ
  refine ⟨⟨a, ha⟩, ⟨z * b * z⁻¹,
    centralizerPoints_conj_mem_dynamicUnipotent i ν hz hb⟩, ⟨n, hn⟩, ⟨z, hz⟩, ?_⟩
  change g = a * n * (z * b * z⁻¹) * z
  rw [hg, hp, hq]
  simp only [z, mul_assoc, mul_inv_rev, inv_inv, mul_inv_cancel_left,
    inv_mul_cancel_left, inv_mul_cancel, mul_one]

/-- If all dynamic unipotent points lie in `H` and `H` supplies every relative-Weyl
class, actual Bruhat covering gives `G(k) = H Z_G(S)(k)`. No normality of `H` is needed. -/
theorem exists_subgroup_mul_centralizer_of_bruhat
    (H : Subgroup (rationalPoints G))
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (hBr : HasRationalBruhatDecomposition i ν)
    (hU : RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i) ≤ H)
    (hW : Function.Surjective (subgroupRelativeWeylMap i H)) (g : rationalPoints G) :
    ∃ h ∈ H, ∃ z ∈ centralizerPoints i, g = h * z := by
  obtain ⟨a, b, n, z, hg⟩ :=
    exists_unipotent_normalizer_unipotent_centralizer_mul i ν hZ hBr g
  obtain ⟨m, hm, t, ht, hn⟩ := (subgroupRelativeWeylMap_surjective_iff i H).mp hW n
  refine ⟨a * m * (t * b * t⁻¹),
    H.mul_mem (H.mul_mem (hU a.property) hm)
      (hU (centralizerPoints_conj_mem_dynamicUnipotent i ν ht b.property)),
    t * z, (centralizerPoints i).mul_mem ht z.property, ?_⟩
  rw [hg, hn]
  simp only [mul_assoc, inv_mul_cancel_left]

/-- The product reduction with the actual simply connected image and any supplied
representative of the whole-torus centralizer. -/
theorem exists_cover_mul_centralizer_of_bruhat
    {Z C D : GroupScheme (Spec (CommRingCat.of k))}
    (j : Z ⟶ G) (d : D ⟶ G) (π : C ⟶ D)
    (hj : (torusCentralizer i).IsRepresentedBy j)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (hBr : HasRationalBruhatDecomposition i ν)
    (hU : RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i) ≤
      (rationalPoints.map (π ≫ d)).range)
    (hW : Function.Surjective
      (subgroupRelativeWeylMap i (rationalPoints.map (π ≫ d)).range))
    (g : rationalPoints G) :
    ∃ c : rationalPoints C, ∃ z : rationalPoints Z,
      g = rationalPoints.map (π ≫ d) c * rationalPoints.map j z := by
  obtain ⟨h, hh, z, hz, hg⟩ :=
    exists_subgroup_mul_centralizer_of_bruhat i ν _ hZ hBr hU hW g
  obtain ⟨c, rfl⟩ := hh
  have hzF : z ∈ (torusCentralizer i).carrier (Over.mk (𝟙 _)) := by
    rwa [torusCentralizer_carrier_base]
  let z' := (hj.pointsEquiv (Over.mk (𝟙 _))).symm ⟨z, hzF⟩
  refine ⟨c, z', hg.trans (congrArg (fun x => rationalPoints.map (π ≫ d) c * x) ?_)⟩
  exact (hj.pointsEquiv_symm_comp ⟨z, hzF⟩).symm

end Langlands.GroupScheme
