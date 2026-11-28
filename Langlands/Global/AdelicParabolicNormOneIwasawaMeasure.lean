import Langlands.Analysis.Local.CompactFactorizationHaar
import Langlands.Global.AdelicParabolicModulus
import Langlands.Global.LeftCosetCompactFactorUnfolding

/-! # Iwasawa quotient measures inside the ambient norm-one subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Set Topology
open scoped CategoryTheory.MonObj Pointwise NNReal

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  (p : P ⟶ G)

/-- The image of a parabolic inside the ambient norm-one group. Its norm-one condition is on
characters of `G`. -/
def ambientNormOneParabolicImage : Subgroup (normOneSubgroup F G) :=
  (map F P G p).toMonoidHom.range.subgroupOf (normOneSubgroup F G)

/-- The lift of a compact subgroup into the ambient norm-one group. -/
def compactToNormOne (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsCompact (K : Set (AdelicGroupPoints F G))) : K →* normOneSubgroup F G :=
  K.subtype.codRestrict _ fun k => compactSubgroup_le_normOneSubgroup F G K hK k.2

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem continuous_compactToNormOne (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsCompact (K : Set (AdelicGroupPoints F G))) :
    Continuous (compactToNormOne K hK) := continuous_subtype_val.subtype_mk _

instance ambientNormOneParabolicImage_secondCountable :
    SecondCountableTopology (ambientNormOneParabolicImage p) :=
  TopologicalSpace.secondCountableTopology_induced _ (normOneSubgroup F G) Subtype.val

variable [IsClosedImmersion p.hom.hom.left]

omit [LocallyOfFiniteType G.X.hom] in
/-- The ambient parabolic norm-one image is closed. -/
theorem isClosed_ambientNormOneParabolicImage :
    IsClosed (ambientNormOneParabolicImage p : Set (normOneSubgroup F G)) :=
  (isClosedEmbedding_map F P G p).isClosed_range.preimage continuous_subtype_val

/-- Haar integration in the ambient norm-one group pushes forward from the parabolic norm-one
image and the given compact. A normalization of the parabolic Haar measure makes the formula
exact with Haar probability on the compact. -/
theorem exists_ambientNormOneIwasawaMeasure {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact p K) :
    ∃ m : Measure (ambientNormOneParabolicImage p), m.IsHaarMeasure ∧
      Measure.map (fun z : ambientNormOneParabolicImage p × K => z.1.val * compactToNormOne K hK.isCompact z.2)
        (m.prod (compactHaarProbability F G K hK.isCompact)) =
          (Measure.haar : Measure (normOneSubgroup F G)) := by
  let H := normOneSubgroup F G
  let Q := ambientNormOneParabolicImage p
  let L := K.subgroupOf H
  have hQ : IsClosed (Q : Set H) := isClosed_ambientNormOneParabolicImage p
  have hL : IsCompact (L : Set H) :=
    (isClosed_normOneSubgroup F G).isClosedEmbedding_subtypeVal.isCompact_preimage hK.isCompact
  let e : K ≃ₜ* L :=
    { toFun := fun k => ⟨compactToNormOne K hK.isCompact k, k.2⟩
      invFun := fun k => ⟨k.val.val, k.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun := (continuous_compactToNormOne K hK.isCompact).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  have hQL (g : H) : ∃ q ∈ Q, ∃ k ∈ L, g = q * k := by
    have hg : g.val ∈ Set.range (map F P G p) * (K : Set (AdelicGroupPoints F G)) :=
      hK.range_mul ▸ Set.mem_univ _
    obtain ⟨_, ⟨q, rfl⟩, k, hk, hqk⟩ := hg
    have hq₁ : map F P G p q ∈ H := by
      have he : map F P G p q = g.val * k⁻¹ := by rw [← hqk, mul_inv_cancel_right]
      rw [he]
      exact H.mul_mem g.2 (H.inv_mem (compactSubgroup_le_normOneSubgroup F G K hK.isCompact hk))
    exact ⟨⟨_, hq₁⟩, ⟨q, rfl⟩, compactToNormOne K hK.isCompact ⟨k, hk⟩, hk,
      Subtype.ext hqk.symm⟩
  let : LocallyCompactSpace Q := hQ.locallyCompactSpace
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  let : SecondCountableTopology Q := inferInstanceAs
    (SecondCountableTopology (ambientNormOneParabolicImage p))
  let : SecondCountableTopology L := TopologicalSpace.secondCountableTopology_induced _ H Subtype.val
  let : SecondCountableTopology K := inferInstanceAs
    (SecondCountableTopology (K : Set (AdelicGroupPoints F G)))
  let mK := compactHaarProbability F G K hK.isCompact
  let mL := Measure.map e mK
  let : mL.IsHaarMeasure := e.isHaarMeasure_map mK
  obtain ⟨c, hc, hμ⟩ := Langlands.CompactFactorization.exists_pos_eq_smul_map_mul_prod
    (Measure.haar : Measure H) Q hQ L hL hQL (Measure.haar : Measure Q) mL
  refine ⟨c • (Measure.haar : Measure Q), IsHaarMeasure.nnreal_smul _ hc.ne', ?_⟩
  let mult : Q × L → H := fun z => z.1.val * z.2.val
  have hm : Measurable mult := (continuous_subtype_val.comp continuous_fst |>.mul
    (continuous_subtype_val.comp continuous_snd)).measurable
  have ha : Measurable (fun z : Q × K => z.1.val * compactToNormOne K hK.isCompact z.2) :=
    (continuous_subtype_val.comp continuous_fst |>.mul
      ((continuous_compactToNormOne K hK.isCompact).comp continuous_snd)).measurable
  rw [Measure.prod_smul_left, Measure.map_smul c ha.aemeasurable, hμ]
  congr 1
  change _ = Measure.map mult ((Measure.haar : Measure Q).prod (Measure.map e mK))
  have heMeas : Measurable (e : K → L) := e.continuous.measurable
  have hmap := Measure.map_prod_map (Measure.haar : Measure Q) mK
    (measurable_id (α := Q)) heMeas
  rw [Measure.map_id] at hmap
  rw [hmap, Measure.map_map hm (measurable_id.prodMap heMeas)]
  rfl

/-- The same compatible Haar measure unfolds the quotient of `G(𝔸)¹` by a discrete subgroup
contained in the parabolic. The parabolic coordinate is restricted to a fundamental domain
for the subgroup in the parabolic. -/
theorem exists_ambientNormOneIwasawaQuotientMeasure {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact p K) :
    ∃ m : Measure (ambientNormOneParabolicImage p), m.IsHaarMeasure ∧
      ∀ (Γ : Subgroup (normOneSubgroup F G)) (hΓ : IsDiscrete (Γ : Set (normOneSubgroup F G)))
        (_ : Γ ≤ ambientNormOneParabolicImage p),
        let i := (ambientNormOneParabolicImage p).subtype
        let Δ := Γ.comap i
        let hΔ : IsDiscrete (Δ : Set (ambientNormOneParabolicImage p)) :=
          hΓ.preimage continuous_subtype_val.continuousOn Subtype.val_injective
        LeftCosetSpace.haarQuotientMeasure Γ hΓ =
          Measure.map (fun z : ambientNormOneParabolicImage p × K =>
            LeftCosetSpace.mk Γ (z.1.val * compactToNormOne K hK.isCompact z.2))
            ((m.restrict (LeftCosetSpace.fundamentalDomain Δ hΔ)).prod
              (compactHaarProbability F G K hK.isCompact)) := by
  obtain ⟨m, hm, hprod⟩ := exists_ambientNormOneIwasawaMeasure p hK
  refine ⟨m, hm, ?_⟩
  intro Γ hΓ hle i Δ hΔ
  let : LocallyCompactSpace (ambientNormOneParabolicImage p) :=
    (isClosed_ambientNormOneParabolicImage p).locallyCompactSpace
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  let : SecondCountableTopology K := inferInstanceAs
    (SecondCountableTopology (K : Set (AdelicGroupPoints F G)))
  have hle' : Γ ≤ i.range := by rw [Subgroup.range_subtype]; exact hle
  have hsub : Δ.map i = Γ := Subgroup.map_comap_eq_self hle'
  exact LeftCosetSpace.discreteQuotientMeasure_map_mul_prod i Subtype.val_injective
    continuous_subtype_val.measurable (compactToNormOne K hK.isCompact)
    (continuous_compactToNormOne K hK.isCompact).measurable Δ Γ hΓ Measure.haar m
    (compactHaarProbability F G K hK.isCompact) hsub hprod
    (LeftCosetSpace.measurableSet_fundamentalDomain Δ hΔ) (LeftCosetSpace.fundamentalDomain_unique Δ hΔ)

end Langlands.Global.AdelicGroupPoints
