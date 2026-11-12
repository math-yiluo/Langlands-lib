import Langlands.Global.AdelicNormOneCompactCover
import Langlands.Global.SplitUnipotentRationalQuotientCompact
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof

/-! # Compact norm-one representatives from a scheme section -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]

/-- The actual norm-one part of the product of kernel representatives and section images. -/
def normOneSectionCompactSet
    {H K V : GroupScheme (Spec (CommRingCat.of F))}
    (j : K ⟶ H) (s : V.X ⟶ H.X)
    (CK : Set (AdelicGroupPoints F K)) (CV : Set (normOneSubgroup F V)) :
    Set (normOneSubgroup F H) :=
  ((↑) : normOneSubgroup F H → AdelicGroupPoints F H) ⁻¹'
    ((map F K H j '' CK) * ((fun v : normOneSubgroup F V => v.val ≫ s) '' CV))

theorem isCompact_normOneSectionCompactSet
    {H K V : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] (j : K ⟶ H) (s : V.X ⟶ H.X)
    {CK : Set (AdelicGroupPoints F K)} {CV : Set (normOneSubgroup F V)}
    (hCK : IsCompact CK) (hCV : IsCompact CV) :
    IsCompact (normOneSectionCompactSet j s CK CV) := by
  apply (isClosed_normOneSubgroup F H).isClosedEmbedding_subtypeVal.isCompact_preimage
  exact (hCK.image (map F K H j).continuous).mul
    (hCV.image ((V.continuous_affinePointPostcomp _ s).comp continuous_subtype_val))

/-- Compact representatives in the full adelic group restrict to compact norm-one
representatives, since every principal rational point has norm one. -/
theorem HasCompactRationalCover.normOne
    {H : GroupScheme (Spec (CommRingCat.of F))} (hH : HasCompactRationalCover H) :
    HasCompactNormOneRationalCover H := by
  obtain ⟨C, hC, hcover⟩ := hH
  refine ⟨((↑) : normOneSubgroup F H → AdelicGroupPoints F H) ⁻¹' C,
    (isClosed_normOneSubgroup F H).isClosedEmbedding_subtypeVal.isCompact_preimage hC, ?_⟩
  intro h
  obtain ⟨_, ⟨q, rfl⟩, hq⟩ := hcover h
  exact ⟨q, hq⟩

/-- A scheme section of a quotient combines a full compact rational cover of the
actual kernel with a norm-one compact rational cover of the actual quotient.
The section need not be a group homomorphism or preserve norm-one points. -/
theorem hasCompactNormOneRationalCover_of_section
    {H K V : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] (j : K ⟶ H) (q : H ⟶ V)
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
    (s : V.X ⟶ H.X) (hs : s ≫ q.hom.hom = 𝟙 V.X)
    (hK : HasCompactRationalCover K) (hV : HasCompactNormOneRationalCover V) :
    HasCompactNormOneRationalCover H := by
  obtain ⟨CK, hCK, hcK⟩ := hK
  obtain ⟨CV, hCV, hcV⟩ := hV
  refine ⟨normOneSectionCompactSet j s CK CV,
    isCompact_normOneSectionCompactSet j s hCK hCV, fun h => ?_⟩
  obtain ⟨rV, hrV⟩ := hcV (mapNormOne F H V q h)
  let c : normOneSubgroup F V :=
    rationalNormOne F V rV * mapNormOne F H V q h
  have hc : (c : AdelicGroupPoints F V) =
      rational F V rV * map F H V q h := rfl
  let g : AdelicGroupPoints F H := rational F H (rV ≫ s)
  have hg : map F H V q g = rational F V rV := by
    simp only [g, map_apply, affinePointsTarget_apply, rational, affinePointMap_apply,
      Category.assoc, hs, Category.comp_id]
  have hcs : map F H V q (c.val ≫ s) = c.val := by
    change (c.val ≫ s) ≫ q.hom.hom = c.val
    rw [Category.assoc, hs, Category.comp_id]
  let h' : AdelicGroupPoints F H := g * h.val * (c.val ≫ s)⁻¹
  have hh' : h' ≫ q.hom.hom = 1 := by
    change map F H V q (g * h.val * (c.val ≫ s)⁻¹) = 1
    rw [map_mul, map_mul, map_inv, hg, hcs, hc, mul_inv_cancel]
  obtain ⟨k, hk⟩ : ∃ k, k ≫ j.hom.hom = h' := by
    have hmem := (mem_range_kernelι_iff q h').mpr hh'
    rw [hq] at hmem
    exact hmem
  obtain ⟨_, ⟨rK, rfl⟩, hrK⟩ := hcK k
  refine ⟨(rK ≫ j.hom.hom) * (rV ≫ s), ?_⟩
  change rational F H ((rK ≫ j.hom.hom) * (rV ≫ s)) * h.val ∈
    (map F K H j '' CK) * ((fun v : normOneSubgroup F V => v.val ≫ s) '' CV)
  refine ⟨map F K H j (rational F K rK * k), ⟨_, hrK, rfl⟩,
    c.val ≫ s, ⟨c, hrV, rfl⟩, ?_⟩
  have hδj : map F K H j (rational F K rK) =
      rational F H (rK ≫ j.hom.hom) := by
    simp only [map_apply, affinePointsTarget_apply, rational, affinePointMap_apply,
      Category.assoc]
  have hkj : map F K H j k = g * h.val * (c.val ≫ s)⁻¹ := hk
  rw [map_mul, hδj, hkj, map_mul]
  change (rational F H (rK ≫ j.hom.hom) *
    (g * h.val * (c.val ≫ s)⁻¹)) * (c.val ≫ s) =
      (rational F H (rK ≫ j.hom.hom) * g) * h.val
  group

/-- For an actual rational Levi decomposition, compact norm-one representatives for the
Levi give compact norm-one representatives for the whole group. The represented geometric
unipotent radical has its full compact rational cover by the proved unipotent results. -/
theorem hasCompactNormOneRationalCover_of_rationalLevi
    {L P : GroupScheme (Spec (CommRingCat.of F))} {l : L ⟶ P}
    (hl : IsRationalLeviSubgroup l) (hL : HasCompactNormOneRationalCover L) :
    HasCompactNormOneRationalCover P := by
  obtain ⟨U, r, q, hr, -, hlq, hkernel⟩ := hl.exists_unipotentRadical_retraction
  have : IsAffineHom P.X.hom := hl.isAffineHom
  have : IsAffine P.X.left := isAffine_of_isAffineHom P.X.hom
  have : IsClosedImmersion r.hom.hom.left := hr.1.isClosedSubgroup
  have : IsAffineHom U.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  have : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  have hU : HasCompactRationalCover U :=
    exists_isCompact_rational_mul_mem_of_split perfectFieldUnipotentSplit
      splitUnipotentAffineTorsorStatement F U hr.1.smooth hr.1.connectedSpace
      hr.1.isUnipotent
  have hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range r := by
    ext T x
    exact (mem_range_kernelι_iff q x).trans (hkernel T x)
  apply hasCompactNormOneRationalCover_of_section r q hq l.hom.hom _ hU hL
  exact congrArg (fun f : L ⟶ L => f.hom.hom) hlq

/-- In particular an actual rational Levi which is a split torus gives compact norm-one
representatives without any reduction-theory or compactness premise. -/
theorem hasCompactNormOneRationalCover_of_splitTorusLevi
    {L P : GroupScheme (Spec (CommRingCat.of F))} {l : L ⟶ P}
    (hl : IsRationalLeviSubgroup l) (hL : IsSplitTorus L) :
    HasCompactNormOneRationalCover P :=
  hasCompactNormOneRationalCover_of_rationalLevi hl
    (hasCompactNormOneRationalCover_of_isSplitTorus F L hL)

end Langlands.Global.AdelicGroupPoints
