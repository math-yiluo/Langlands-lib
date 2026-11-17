import Langlands.Representation.CuspidalSupport.StandardLeviFixedVectorSupportStatements
import Langlands.Representation.Jacquet.StandardNormalLevelFixedVectors
import Langlands.Representation.Aubert.General.RationalOppositeChamber

/-! # Compact subgroups inherited by standard Levi subgroups -/

noncomputable section

universe u uF

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.BruhatTits.SpecialCompact Langlands.Jacquet

namespace Langlands.CuspidalSupport

section Groups

variable {H : Type u} [Group H] {K P M U A B L V : Subgroup H}

/-- Restrict the literal ordered decomposition once its opposite factor in
`P` is forced into `M`. -/
private theorem iwahori_intersection
    (hK : HasIwahoriIntersectionDecomposition K L U V)
    (hMP : M ≤ P) (hLM : L ≤ M) (hUP : U ≤ P)
    (hVP : ∀ x : H, x ∈ V → x ∈ P → x ∈ M) :
    HasIwahoriIntersectionDecomposition (K ⊓ M) L (U ⊓ M) (V ⊓ M) := by
  constructor
  · intro a b hab
    let lift (t : ↥((K ⊓ M) ⊓ (V ⊓ M)) × ↥((K ⊓ M) ⊓ L) ×
        ↥((K ⊓ M) ⊓ (U ⊓ M))) : ↥(K ⊓ V) × ↥(K ⊓ L) × ↥(K ⊓ U) :=
      (⟨t.1, t.1.property.1.1, t.1.property.2.1⟩,
        ⟨t.2.1, t.2.1.property.1.1, t.2.1.property.2⟩,
        ⟨t.2.2, t.2.2.property.1.1, t.2.2.property.2.1⟩)
    have he : orderedIntersectionProduct K L U V (lift a) =
        orderedIntersectionProduct K L U V (lift b) :=
      by
        apply Subtype.ext
        exact congrArg (fun t : ↥(K ⊓ M) => (t : H)) hab
    have hab' := hK.injective he
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun t => (t.1 : H)) hab')
    · apply Prod.ext
      · exact Subtype.ext (congrArg (fun t => (t.2.1 : H)) hab')
      · exact Subtype.ext (congrArg (fun t => (t.2.2 : H)) hab')
  · intro k
    obtain ⟨⟨x, y, z⟩, he⟩ := hK.surjective ⟨k, k.property.1⟩
    have hk : (k : H) = (x : H) * (y : H) * (z : H) :=
      (congrArg Subtype.val he).symm
    have hxP : (x : H) ∈ P := by
      have hx : (x : H) = (k : H) * ((y : H) * (z : H))⁻¹ := by
        rw [hk]
        group
      rw [hx]
      exact P.mul_mem (hMP k.property.2)
        (P.inv_mem (P.mul_mem (hMP (hLM y.property.2)) (hUP z.property.2)))
    have hxM := hVP x x.property.2 hxP
    have hzM : (z : H) ∈ M := by
      have hz : (z : H) = ((x : H) * (y : H))⁻¹ * (k : H) := by
        rw [hk]
        group
      rw [hz]
      exact M.mul_mem (M.inv_mem (M.mul_mem hxM (hLM y.property.2))) k.property.2
    refine ⟨(⟨x, ⟨x.property.1, hxM⟩, x.property.2, hxM⟩,
      ⟨y, ⟨y.property.1, hLM y.property.2⟩, y.property.2⟩,
      ⟨z, ⟨z.property.1, hzM⟩, z.property.2, hzM⟩), ?_⟩
    apply Subtype.ext
    exact congrArg (fun t : K => (t : H)) he

variable [TopologicalSpace H]

/-- The projection of a compact normalizing subgroup provides the compact
subgroup and minimal factorization inside a Levi. -/
private theorem compact_levi_image
    (d : IsSemidirectDecomposition P M U) (hd : Continuous d.projection)
    (hP : IsClosed (P : Set H)) (K₀ : Subgroup H)
    (hK₀ : IsCompact (K₀ : Set H)) (hKK₀ : K ≤ K₀)
    (hnormal : K₀ ≤ Subgroup.normalizer K)
    (hprojection : ∀ p : P, (p : H) ∈ K → (d.projection p : H) ∈ K)
    (hAM : A ≤ M) (hBP : B ≤ P)
    (hBprojection : ∀ b : P, (b : H) ∈ B → (d.projection b : H) ∈ B)
    (hIwasawa : ∀ g : H, ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ K₀, g = a * b * c) :
    ∃ Q : Subgroup H, Q ≤ M ∧ IsCompact (Q : Set H) ∧
      (∀ g ∈ M, ∃ a ∈ A, ∃ b ∈ B ⊓ M, ∃ c ∈ Q, g = a * b * c) ∧
      K ⊓ M ≤ Q ∧ Q ≤ Subgroup.normalizer (K ⊓ M) := by
  let f : P →* H := M.subtype.comp d.projection
  let Q := (K₀.comap P.subtype).map f
  have hf : Continuous f := continuous_subtype_val.comp hd
  have hQM : Q ≤ M := by
    rintro _ ⟨p, _, rfl⟩
    exact (d.projection p).property
  refine ⟨Q, hQM, ?_, ?_, ?_, ?_⟩
  · have hc : IsCompact (K₀.comap P.subtype : Set P) :=
      hP.isClosedEmbedding_subtypeVal.isCompact_preimage hK₀
    exact hc.image hf
  · intro g hg
    obtain ⟨a, ha, b, hb, c, hc, he⟩ := hIwasawa g
    have hcP : c ∈ P := by
      have hc' : c = (a * b)⁻¹ * g := by
        rw [he]
        group
      rw [hc']
      exact P.mul_mem (P.inv_mem (P.mul_mem (d.levi_le (hAM ha)) (hBP hb)))
        (d.levi_le hg)
    let ap : P := ⟨a, d.levi_le (hAM ha)⟩
    let bp : P := ⟨b, hBP hb⟩
    let cp : P := ⟨c, hcP⟩
    have he' : (⟨g, d.levi_le hg⟩ : P) = ap * bp * cp := Subtype.ext he
    have hp := congrArg (fun p : P => (d.projection p : H)) he'
    have hpa : d.projection ap = ⟨a, hAM ha⟩ := d.projection_levi ⟨a, hAM ha⟩
    have hpg : d.projection ⟨g, d.levi_le hg⟩ = ⟨g, hg⟩ :=
      d.projection_levi ⟨g, hg⟩
    simp only [map_mul, Subgroup.coe_mul, hpa, hpg] at hp
    exact ⟨a, ha, d.projection bp, ⟨hBprojection bp hb, (d.projection bp).property⟩,
      d.projection cp, ⟨cp, hc, rfl⟩, hp⟩
  · intro x hx
    refine ⟨⟨x, d.levi_le hx.2⟩, hKK₀ hx.1, ?_⟩
    exact congrArg Subtype.val (d.projection_levi ⟨x, hx.2⟩)
  · apply (Subgroup.le_normalizer_iff (H := Q) (K := K ⊓ M)).mpr
    rintro g ⟨p, hp, rfl⟩ x hx
    have hxP := d.levi_le hx.2
    let xp : P := ⟨x, hxP⟩
    have hcK : ((p * xp * p⁻¹ : P) : H) ∈ K :=
      Subgroup.le_normalizer_iff.mp hnormal p hp x hx.1
    have hpr := hprojection (p * xp * p⁻¹) hcK
    have hpx : d.projection xp = ⟨x, hx.2⟩ := d.projection_levi ⟨x, hx.2⟩
    simp only [map_mul, map_inv, hpx, Subgroup.coe_mul, Subgroup.coe_inv] at hpr
    exact ⟨hpr, M.mul_mem (M.mul_mem (d.projection p).property hx.2)
      (M.inv_mem (d.projection p).property)⟩

end Groups

section Standard

variable {F : Type uF} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

private theorem rootSet_exists (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) {J : Set (characterLattice S)}
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    ∃ T : Finset (SimpleRoot i ν), rootSet i ν T = J := by
  classical
  let := finite_simpleRoot hG hi ν
  let := Fintype.ofFinite (SimpleRoot i ν)
  refine ⟨Finset.univ.filter (fun α => α.val ∈ J), ?_⟩
  ext α
  constructor
  · rintro ⟨β, hβ, rfl⟩
    exact (Finset.mem_filter.mp hβ).2
  · intro hα
    exact ⟨⟨α, hJ hα⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩, rfl⟩

/-- The nested standard radicals give exactly the containment needed to
restrict an ordered Iwahori product. -/
private theorem standard_nested_structure
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {I J : Set (characterLattice S)}
    (hI : I ⊆ simpleRelativeRoots i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    (hIJ : I ⊆ J)
    (hstandard : ∃ ζ, IsStandardCocharacter i ν J ζ)
    (d : IsSemidirectDecomposition (standardParabolicPoints i ν J)
      (standardLeviPoints i ν J) (standardUnipotentPoints i ν J)) :
    standardLeviPoints i ν I ≤ standardLeviPoints i ν J ∧
      standardUnipotentPoints i ν I ≤ standardParabolicPoints i ν J ∧
      (∀ x : rationalPoints G, x ∈ standardOppositeUnipotentPoints i ν I →
        x ∈ standardParabolicPoints i ν J → x ∈ standardLeviPoints i ν J) := by
  have hnest := standardLeviIntersection F G hG S i hi ν hν I J hI hJ hIJ
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact ((hnest.1 (Over.mk (𝟙 _))).2.1 hx).1
  · intro x hx
    change x ∈ (standardUnipotentPoints i ν I : Set (rationalPoints G)) at hx
    rw [hnest.2] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    exact (standardParabolicPoints i ν J).mul_mem (d.levi_le ha.1) (d.unipotent_le hb)
  · have hneg := relativeRootNegation F G hG S i hi
    have hIneg : Neg.neg '' I ⊆ simpleRelativeRoots i (-ν) := by
      rintro _ ⟨α, hα, rfl⟩
      exact neg_mem_simpleRelativeRoots i ν hneg (hI hα)
    have hJneg : Neg.neg '' J ⊆ simpleRelativeRoots i (-ν) := by
      rintro _ ⟨α, hα, rfl⟩
      exact neg_mem_simpleRelativeRoots i ν hneg (hJ hα)
    obtain ⟨ζ, hζ⟩ := hstandard
    have hM : standardLeviPoints i (-ν) (Neg.neg '' J) =
        standardLeviPoints i ν J :=
      congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _)))
        (standardSubgroups_reversedChamber i ν standardCocharacter hG hi hν hneg hζ).2.1
    have hprod := (standardLeviIntersection F G hG S i hi (-ν) (hν.neg i ν)
      (Neg.neg '' I) (Neg.neg '' J) hIneg hJneg (Set.image_mono hIJ)).2
    change (standardOppositeUnipotentPoints i ν I : Set (rationalPoints G)) =
      (standardLeviPoints i (-ν) (Neg.neg '' J) ⊓ standardOppositeUnipotentPoints i ν I :
        Set (rationalPoints G)) *
      (standardOppositeUnipotentPoints i ν J : Set (rationalPoints G)) at hprod
    rw [hM] at hprod
    intro x hx hxP
    change x ∈ (standardOppositeUnipotentPoints i ν I : Set (rationalPoints G)) at hx
    rw [hprod] at hx
    obtain ⟨a, ha, b, hb, he⟩ := Set.mem_mul.mp hx
    have hbP : b ∈ standardParabolicPoints i ν J := by
      have hb' : b = a⁻¹ * x := by
        rw [← he]
        group
      rw [hb']
      exact (standardParabolicPoints i ν J).mul_mem
        ((standardParabolicPoints i ν J).inv_mem (d.levi_le ha.1)) hxP
    have hb1 := eq_one_of_mem_standardOppositeUnipotent_of_mem_standardParabolic
      i ν hneg ⟨ζ, hζ⟩ hb hbP
    rw [hb1, mul_one] at he
    exact he ▸ ha.1

private theorem standard_projection_minimal
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    (d : IsSemidirectDecomposition (standardParabolicPoints i ν J)
      (standardLeviPoints i ν J) (standardUnipotentPoints i ν J))
    (p : standardParabolicPoints i ν J)
    (hp : (p : rationalPoints G) ∈ standardUnipotentPoints i ν ∅) :
    (d.projection p : rationalPoints G) ∈ standardUnipotentPoints i ν ∅ := by
  have hprod := (standardLeviIntersection F G hG S i hi ν hν ∅ J
    (Set.empty_subset _) hJ (Set.empty_subset _)).2
  change (p : rationalPoints G) ∈
    (standardUnipotentPoints i ν ∅ : Set (rationalPoints G)) at hp
  rw [hprod] at hp
  obtain ⟨a, ha, b, hb, he⟩ := Set.mem_mul.mp hp
  have hp' : p =
      (⟨a, d.levi_le ha.1⟩ : standardParabolicPoints i ν J) *
        ⟨b, d.unipotent_le hb⟩ := Subtype.ext he.symm
  rw [hp', d.projection_mul ⟨a, ha.1⟩ ⟨b, hb⟩]
  exact ha.2

end Standard

/-- Renard VI.10.6: the compact open subgroup inherits the standard
normalizing, Iwasawa and Iwahori properties inside every standard Levi. -/
theorem standardLeviCompactInheritance :
    StandardLeviCompactInheritanceStatement.{uF} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro S i hi ν hν hstandard K₀ hK₀ hIwasawa K hK hKK₀ hnormal hIwahori J hJ
  obtain ⟨T, rfl⟩ := rootSet_exists i ν hG hi hJ
  let family := standardBernsteinFamily i ν hG hi hν
  let d := family.decomposition T
  have hMclosed := isClosed_levi_of_isNonarchimedeanLocalField i ν T
  have hPclosed := isClosed_standard_parabolic i ν standardCocharacter hG hi hν T
  have hd : Continuous d.projection :=
    continuous_standard_projection i ν standardCocharacter hG hi hν T
  have hminimal := standard_nested_structure i ν hG hi hν (Set.empty_subset _)
    (rootSet_subset i ν T) (Set.empty_subset _) (hstandard _ (rootSet_subset i ν T)) d
  refine ⟨K.isOpen.preimage continuous_subtype_val,
    hMclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hK, ?_, ?_⟩
  · exact compact_levi_image d hd hPclosed K₀ hK₀ hKK₀ hnormal
      (standard_projection_mem_of_iwahoriIntersection i ν family T K.toSubgroup
        (hIwahori _ (rootSet_subset i ν T)))
      hminimal.1 hminimal.2.1 (standard_projection_minimal i ν hG hi hν
        (rootSet_subset i ν T) d) hIwasawa
  · intro I hIJ
    have hI : I ⊆ simpleRelativeRoots i ν := hIJ.trans (rootSet_subset i ν T)
    have hnested := standard_nested_structure i ν hG hi hν hI
      (rootSet_subset i ν T) hIJ (hstandard _ (rootSet_subset i ν T)) d
    exact iwahori_intersection (hIwahori I hI) d.levi_le hnested.1
      hnested.2.1 hnested.2.2

end Langlands.CuspidalSupport
