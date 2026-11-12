import Langlands.Representation.Plancherel.AvailableRenardCartanStatement
import Langlands.BruhatTits.Cartan.AvailableCartanStatement
import Langlands.Geometry.Building.IwahoriDoubleCosetComponents
import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.Representation.Plancherel.RationalCharacterTopology
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! # Passing from parahoric to maximal-compact Cartan representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.Cartan

namespace Langlands.Plancherel.RenardCartan

section Groups

variable {H C : Type*} [Group H] [Group C]
  (j : C →* H) (P K : Subgroup H) (N : Subgroup C) [N.Normal] (D : Set C)

/-- A larger subgroup has Cartan comparison modulo the larger centralizer kernel
when its centralizer intersection is that kernel and the kernel normalizes the
smaller subgroup. The smaller comparison enters as an explicit premise. -/
theorem compactComparison_of_parahoric
    (hPK : P ≤ K)
    (hNK : ∀ c : C, j c ∈ K ↔ c ∈ N)
    (hNP : ∀ c ∈ N, j c ∈ Subgroup.normalizer (P : Set H))
    (hD : ∀ c ∈ D, ∀ a ∈ N, ∀ b ∈ N, a * c * b ∈ D)
    (hcover : ∀ g : H, ∃ c : D,
      DoubleCoset.mk P P (j c.val) = DoubleCoset.mk P P g)
    (hclass : ∀ a b : D,
      DoubleCoset.mk P P (j a.val) = DoubleCoset.mk P P (j b.val) →
        b.val * a.val⁻¹ ∈ N) :
    (∀ g : H, ∃ c : D,
      DoubleCoset.mk K K (j c.val) = DoubleCoset.mk K K g) ∧
    (∀ a b : D,
      DoubleCoset.mk K K (j a.val) = DoubleCoset.mk K K (j b.val) ↔
        b.val * a.val⁻¹ ∈ N) := by
  have hleft : ∀ k ∈ K, ∃ c ∈ N, ∃ p ∈ P, k = j c * p := by
    intro k hk
    obtain ⟨c, hc⟩ := hcover k
    obtain ⟨p, hp, q, hq, hkq⟩ := DoubleCoset.eq.mp hc
    have hjcK : j c.val ∈ K := by
      have heq : j c.val = p⁻¹ * k * q⁻¹ := by rw [hkq]; group
      rw [heq]
      exact K.mul_mem (K.mul_mem (K.inv_mem (hPK hp)) hk) (K.inv_mem (hPK hq))
    have hcN := (hNK c.val).mp hjcK
    have hp' : (j c.val)⁻¹ * p * j c.val ∈ P := by
      simpa only [inv_inv] using
        ((Subgroup.mem_normalizer_iff.mp
          (Subgroup.inv_mem (Subgroup.normalizer (P : Set H)) (hNP c.val hcN))) p).mp hp
    refine ⟨c.val, hcN, (j c.val)⁻¹ * p * j c.val * q, P.mul_mem hp' hq, ?_⟩
    rw [hkq]
    group
  have hright : ∀ k ∈ K, ∃ p ∈ P, ∃ c ∈ N, k = p * j c := by
    intro k hk
    obtain ⟨c, hc, p, hp, heq⟩ := hleft k⁻¹ (K.inv_mem hk)
    refine ⟨p⁻¹, P.inv_mem hp, c⁻¹, N.inv_mem hc, ?_⟩
    simpa only [mul_inv_rev, inv_inv, map_inv] using congrArg Inv.inv heq
  constructor
  · intro g
    obtain ⟨c, hc⟩ := hcover g
    obtain ⟨p, hp, q, hq, heq⟩ := DoubleCoset.eq.mp hc
    exact ⟨c, DoubleCoset.eq.mpr ⟨p, hPK hp, q, hPK hq, heq⟩⟩
  · intro a b
    constructor
    · intro hab
      obtain ⟨k, hk, l, hl, heq⟩ := DoubleCoset.eq.mp hab
      obtain ⟨p, hp, c, hc, hkc⟩ := hright k hk
      obtain ⟨d, hd, q, hq, hld⟩ := hleft l hl
      let w : D := ⟨c * a.val * d, hD a.val a.property c hc d hd⟩
      have hwb : DoubleCoset.mk P P (j w.val) = DoubleCoset.mk P P (j b.val) := by
        apply DoubleCoset.eq.mpr
        refine ⟨p, hp, q, hq, ?_⟩
        simpa only [w, map_mul, mul_assoc, hkc, hld] using heq
      have hbw := hclass w b hwb
      have hwa : w.val * a.val⁻¹ ∈ N := by
        have hn : a.val * d * a.val⁻¹ ∈ N :=
          (inferInstance : N.Normal).conj_mem d hd a.val
        have heqw : w.val * a.val⁻¹ = c * (a.val * d * a.val⁻¹) := by
          dsimp [w]
          group
        rw [heqw]
        exact N.mul_mem hc hn
      have heqb : b.val * a.val⁻¹ =
          (b.val * w.val⁻¹) * (w.val * a.val⁻¹) := by group
      rw [heqb]
      exact N.mul_mem hbw hwa
    · intro hab
      apply DoubleCoset.eq.mpr
      refine ⟨j (b.val * a.val⁻¹), (hNK _).mpr hab, 1, K.one_mem, ?_⟩
      simp only [map_mul, map_inv, mul_one, inv_mul_cancel_right]

end Groups

section CompactIntersection

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]

open Langlands.AlgebraicGeometry.PointTopology

/-- A compact subgroup pulls back along a closed group immersion to a subgroup
of the actual centralizer norm kernel. -/
theorem compact_comap_le_normKernel (j : Z ⟶ G) (hj : IsClosedSubgroup j)
    (K : Subgroup (rationalPoints G)) :
    let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsCompact (K : Set (rationalPoints G)) →
      K.comap (rationalPoints.map j) ≤ rationalCommonNormKernel Z := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  change IsCompact (K : Set (rationalPoints G)) →
    K.comap (rationalPoints.map j) ≤ rationalCommonNormKernel Z
  intro hK
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsAffine Z.X.left := isAffine_of_isAffineHom j.hom.hom.left
  let : TopologicalSpace (rationalPoints Z) := rationalPointTopology F Z.X
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  apply compactSubgroup_le_rationalCommonNormKernel Z (K.comap (rationalPoints.map j))
  exact (isClosedEmbedding_rationalPointMap F j.hom.hom).isCompact_preimage hK

end CompactIntersection

section ActualComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ParahoricBuildingData G) (ν : cocharacterLattice B.S)
  (x : B.Apartment)

open Langlands.AlgebraicGeometry.PointTopology

/-- The actual centralizer intersection in a compact `K₀` is `Z(F)^1`. -/
theorem specialCompactCentralizer_comap
    (hK : let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact (B.apartment.specialCompactSubgroup x : Set (rationalPoints G))) :
    (B.apartment.specialCompactSubgroup x).comap (rationalPoints.map B.centralizer.j) =
      rationalCommonNormKernel B.centralizer.Z := by
  apply le_antisymm
  · exact compact_comap_le_normKernel B.centralizer.j B.centralizer.isClosedSubgroup _ hK
  · intro z hz
    exact B.isOmegaCompatible.map_mem_compactStabilizer hz x

/-- The centralizer preimage of the same compact subgroup is identified with
the actual norm kernel by the identity on rational centralizer points. -/
def specialCompactCentralizerNormEquiv
    (hK : let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact (B.apartment.specialCompactSubgroup x : Set (rationalPoints G))) :
    (B.apartment.specialCompactSubgroup x).comap (rationalPoints.map B.centralizer.j) ≃*
      rationalCommonNormKernel B.centralizer.Z :=
  MulEquiv.subgroupCongr (specialCompactCentralizer_comap B x hK)

@[simp]
theorem specialCompactCentralizerNormEquiv_val
    (hK : let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact (B.apartment.specialCompactSubgroup x : Set (rationalPoints G)))
    (z : (B.apartment.specialCompactSubgroup x).comap
      (rationalPoints.map B.centralizer.j)) :
    (specialCompactCentralizerNormEquiv B x hK z : rationalPoints B.centralizer.Z) = z :=
  rfl

/-- The actual dominant set is stable under multiplying by norm-kernel points. -/
theorem dominantCentralizer_mul_normKernel
    (z : rationalPoints B.centralizer.Z)
    (hz : z ∈ dominantCentralizer B.i ν B.centralizer.s B.centralizer.bijective)
    (a : rationalPoints B.centralizer.Z) (ha : a ∈ rationalCommonNormKernel B.centralizer.Z)
    (b : rationalPoints B.centralizer.Z) (hb : b ∈ rationalCommonNormKernel B.centralizer.Z) :
    a * z * b ∈ dominantCentralizer B.i ν B.centralizer.s B.centralizer.bijective := by
  rw [← centralizerValuation_ker B.centralizer.s B.centralizer.bijective,
    MonoidHom.mem_ker] at ha hb
  intro α hα
  simpa only [map_mul, ha, hb, one_mul, mul_one] using hz α hα

/-- A published parahoric comparison, compactness and the stated inclusion
give the Renard geometric comparison, once normality of the zero normalizer
has been established. This is a reduction, not a proof of availability. -/
theorem specialCompactCartanComparison_of_parahoric [B.normalizerZero.Normal]
    (hcartan : ParahoricCartanConclusions B ν x)
    (hPK : B.parahoricAt x ≤ B.apartment.specialCompactSubgroup x)
    (hK : let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact (B.apartment.specialCompactSubgroup x : Set (rationalPoints G))) :
    SpecialCompactCartanComparison B.apartment x ν
      B.centralizer.j B.centralizer.s B.centralizer.bijective := by
  let j := rationalPoints.map B.centralizer.j
  let N := rationalCommonNormKernel B.centralizer.Z
  let D := dominantCentralizer B.i ν B.centralizer.s B.centralizer.bijective
  have hNK : ∀ z, j z ∈ B.apartment.specialCompactSubgroup x ↔ z ∈ N := by
    intro z
    change z ∈ (B.apartment.specialCompactSubgroup x).comap j ↔ z ∈ N
    rw [specialCompactCentralizer_comap B x hK]
  have hNP : ∀ z ∈ N, j z ∈ Subgroup.normalizer (B.parahoricAt x : Set (rationalPoints G)) := by
    intro z hz
    apply B.normalizerStabilizer_mem_parahoric_normalizer {x} (B.centralizer.toNormalizer z)
    rw [B.mem_normalizerStabilizer]
    have hfix := B.isOmegaCompatible.smul_eq_self hz x
    simp only [Set.smul_set_singleton, hfix]
  have hcover : ∀ g : rationalPoints G, ∃ z : D,
      DoubleCoset.mk (B.parahoricAt x) (B.parahoricAt x) (j z.val) =
        DoubleCoset.mk (B.parahoricAt x) (B.parahoricAt x) g := by
    intro g
    have hg : g ∈ (B.parahoricAt x : Set (rationalPoints G)) *
        (j '' D) * (B.parahoricAt x : Set (rationalPoints G)) := by
      rw [← hcartan.1]
      exact Set.mem_univ g
    obtain ⟨_, ⟨p, hp, _, ⟨z, hz, rfl⟩, rfl⟩, q, hq, heq⟩ := hg
    exact ⟨⟨z, hz⟩, DoubleCoset.eq.mpr ⟨p, hp, q, hq, heq.symm⟩⟩
  have hclass : ∀ a b : D,
      DoubleCoset.mk (B.parahoricAt x) (B.parahoricAt x) (j a.val) =
          DoubleCoset.mk (B.parahoricAt x) (B.parahoricAt x) (j b.val) →
        b.val * a.val⁻¹ ∈ N := by
    intro a b hab
    exact B.zeroDatum.centralizerZero_le_rationalCommonNormKernel
      ((hcartan.2.1 a b).mp (DoubleCoset.eq''.mp hab))
  exact compactComparison_of_parahoric j (B.parahoricAt x)
    (B.apartment.specialCompactSubgroup x) N D hPK hNK hNP
    (dominantCentralizer_mul_normKernel B ν) hcover hclass

end ActualComparison

end Langlands.Plancherel.RenardCartan
