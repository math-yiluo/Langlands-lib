import Langlands.Global.AdelicIwasawaIntegrationProof
import Langlands.GroupScheme.Rational.StandardLeviIntersectionReduction
import Langlands.GroupScheme.Rational.StandardLeviFamilyRestriction
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof

/-! # Compact unipotent factors in an actual standard Levi -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory NumberField Set Topology
open scoped Classical CategoryTheory.MonObj Pointwise

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

section Compactness

variable {F : Type u} [Field F] [NumberField F]
  {G P L U V : GroupScheme (Spec (CommRingCat.of F))}
  [IsSeparated G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left] [IsAffine L.X.left]
  [IsAffine U.X.left]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} {p : P ⟶ G} {l : L ⟶ G} {v : V ⟶ G}
  (hp : (Dynamic.parabolic χ).IsRepresentedBy p)
  (hl : (Dynamic.centralizer χ).IsRepresentedBy l)
  (hv : (Dynamic.unipotent χ).IsRepresentedBy v)
  (j : U ⟶ L) [IsClosedImmersion j.hom.hom.left]

include hp hl hv in
/-- The compactness argument uses only the closed parabolic and inner radical
embeddings and the continuous Levi projection. -/
private theorem exists_compact_levi_factor
    (D : Set (AdelicGroupPoints F G)) (hD : IsCompact D)
    (hfact : ∀ w ∈ D, ∃ (y : AdelicGroupPoints F U) (n : AdelicGroupPoints F V),
      w = map F U G (j ≫ l) y * map F V G v n) :
    ∃ C : Set (AdelicGroupPoints F U), IsCompact C ∧ ∀ w ∈ D,
      ∃ y ∈ C, ∃ n : AdelicGroupPoints F V, w = map F U G (j ≫ l) y * map F V G v n := by
  let A := AdelicGroupPoints F G
  let Pg := (map F P G p).toMonoidHom.range
  let D₀ := (Subtype.val : Pg → A) ⁻¹' D
  have hPg : IsClosed (Pg : Set A) := (isClosedEmbedding_map_parabolic F hp).isClosed_range
  have hD₀ : IsCompact D₀ := hPg.isClosedEmbedding_subtypeVal.isCompact_preimage hD
  let mU := map F U L j
  let C := mU ⁻¹' (leviProjection F hp hl '' D₀)
  have hC : IsCompact C := (isClosedEmbedding_map F U L j).isCompact_preimage
    (hD₀.image (continuous_leviProjection F hp hl))
  refine ⟨C, hC, fun w hw => ?_⟩
  obtain ⟨y, n, he⟩ := hfact w hw
  refine ⟨y, ?_, n, he⟩
  refine ⟨leviMul F hp hl hv (mU y, n), ?_, leviProjection_leviMul F hp hl hv _⟩
  change (leviMul F hp hl hv (mU y, n) : A) ∈ D
  have hprod : (leviMul F hp hl hv (mU y, n) : A) = w := by
    rw [coe_leviMul, he]
    congr 1
  rwa [hprod]

end Compactness

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  {ν : cocharacterLattice T} (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (J K : Set (characterLattice T))

local notation "A" => AdelicGroupPoints F G
local notation "L" => Standard.leviScheme i ν J
local notation "iL" => standardLeviTorusFactor i ν J (Standard.isRepresentedBy_leviHom i ν J)
local notation "U" => Standard.unipotentScheme iL ν (J ∩ K)
local notation "V" => Standard.unipotentScheme i ν J
local notation "jU" => Standard.unipotentHom iL ν (J ∩ K)
local notation "jL" => Standard.leviHom i ν J
local notation "jV" => Standard.unipotentHom i ν J
local notation "jK" => Standard.unipotentHom i ν K

private local instance (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom_source

include hG hi hν in
omit [NumberField F] in
private theorem exists_standardLevi_unipotent_factors_on_points
    (hJ : J ⊆ simpleRelativeRoots i ν) (hK : K ⊆ simpleRelativeRoots i ν)
    (Q : Over (Spec (CommRingCat.of F))) {w : Q ⟶ G.X}
    (hw : w ∈ (standardUnipotent i ν K).carrier Q) :
    ∃ y : Q ⟶ (U).X, ∃ n : Q ⟶ (V).X,
      w = (y ≫ (jU ≫ jL).hom.hom) * (n ≫ (jV).hom.hom) := by
  let W := J ∩ K
  have hW : W ⊆ simpleRelativeRoots i ν := inter_subset_left.trans hJ
  have hOrdJ := (standardParabolicOrder F G hG T i hi ν hν).1 W J hW hJ
  have hOrdK := (standardParabolicOrder F G hG T i hi ν hν).1 W K hW hK
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G hG T i hi ν hν J hJ
  obtain ⟨_, hl, hu⟩ := hcompare ζ hζ
  have hsplit := StandardLeviIntersection.standardUnipotent_eq_leviInter_mul i ν
    ⟨hζ, hl.ge, hu.ge⟩ (hOrdJ.1.mp inter_subset_left) ((hOrdJ.2 inter_subset_left).2) Q
  have hwW : w ∈ (standardUnipotent i ν W).carrier Q :=
    (hOrdK.2 inter_subset_right).2 Q hw
  change w ∈ (↑((standardUnipotent i ν W).carrier Q) : Set (Q ⟶ G.X)) at hwW
  rw [hsplit] at hwW
  obtain ⟨a, ⟨haL, haW⟩, n₀, hn₀, hab⟩ := Set.mem_mul.mp hwW
  rw [← (Standard.isRepresentedBy_leviHom i ν J).2] at haL
  obtain ⟨aL, haL⟩ := haL
  change Q ⟶ (L).X at aL
  change aL ≫ (jL).hom.hom = a at haL
  have hInner : standardUnipotent iL ν W = (standardUnipotent i ν W).comap jL := by
    simpa only [W, ← Set.inter_assoc, Set.inter_self] using
      (standardLeviStandardFamilies_inter_canonical i ν hG hi hν J W hJ hW).2.2
  have haInner : aL ∈ (standardUnipotent iL ν W).carrier Q := by
    rwa [hInner, SubgroupFunctor.mem_comap, haL]
  rw [← (Standard.isRepresentedBy_unipotentHom iL ν W).2] at haInner
  obtain ⟨y, hy⟩ := haInner
  change Q ⟶ (U).X at y
  change y ≫ (jU).hom.hom = aL at hy
  rw [← (Standard.isRepresentedBy_unipotentHom i ν J).2] at hn₀
  obtain ⟨n, hn⟩ := hn₀
  change Q ⟶ (V).X at n
  change n ≫ (jV).hom.hom = n₀ at hn
  refine ⟨y, n, ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, hy, haL, hn]
  exact hab.symm

/-- For a compact set in a standard radical, its factors in an ambient
standard Levi may be taken in one compact set in the intrinsic radical of
the intersection parabolic. -/
def AdelicStandardLeviUnipotentFactorsStatement (J K : Set (characterLattice T)) : Prop :=
  J ⊆ simpleRelativeRoots i ν → K ⊆ simpleRelativeRoots i ν →
  ∀ D : Set A, IsCompact D → D ⊆ (map F _ G (Standard.unipotentHom i ν K)).toMonoidHom.range →
    ∃ C : Set (AdelicGroupPoints F (Standard.unipotentScheme
        (standardLeviTorusFactor i ν J (Standard.isRepresentedBy_leviHom i ν J)) ν (J ∩ K))),
      IsCompact C ∧ ∀ w ∈ D, ∃ y ∈ C, ∃ n : AdelicGroupPoints F (Standard.unipotentScheme i ν J),
        w = map F _ G (Standard.unipotentHom
          (standardLeviTorusFactor i ν J (Standard.isRepresentedBy_leviHom i ν J)) ν (J ∩ K) ≫
            Standard.leviHom i ν J) y * map F _ G (Standard.unipotentHom i ν J) n

include hG hi hν in
/-- The Levi projection on the larger parabolic is continuous, and the
intrinsic radical embeds as a closed subgroup of the Levi. -/
theorem adelicStandardLeviUnipotentFactors : AdelicStandardLeviUnipotentFactorsStatement (F := F)
    (i := i) (ν := ν) J K := by
  intro hJ hK D hD hDK
  let P := Standard.parabolicScheme i ν J
  let jP := Standard.parabolicHom i ν J
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine P.X.left := @isAffine_of_isAffineHom _ _ P.X.hom
    (Standard.isClosedSubgroup_parabolicHom i ν J).isAffineHom_source inferInstance
  let : IsAffine (L).X.left := isAffine_of_isAffineHom (L).X.hom
  let : IsAffine (U).X.left := @isAffine_of_isAffineHom _ _ (U).X.hom
    (Standard.isClosedSubgroup_unipotentHom iL ν (J ∩ K)).isAffineHom_source inferInstance
  let : IsClosedImmersion (jU).hom.hom.left :=
    Standard.isClosedSubgroup_unipotentHom iL ν (J ∩ K)
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G hG T i hi ν hν J hJ
  let χ := CommGroupScheme.groupHom ζ ≫ i
  have hp : (Dynamic.parabolic χ).IsRepresentedBy jP := by
    rw [← (hcompare ζ hζ).1]
    exact Standard.isRepresentedBy_parabolicHom i ν J
  have hl : (Dynamic.centralizer χ).IsRepresentedBy jL := by
    rw [← (hcompare ζ hζ).2.1]
    exact Standard.isRepresentedBy_leviHom i ν J
  have hu : (Dynamic.unipotent χ).IsRepresentedBy jV := by
    rw [← (hcompare ζ hζ).2.2]
    exact Standard.isRepresentedBy_unipotentHom i ν J
  apply exists_compact_levi_factor hp hl hu jU D hD
  intro w hw
  let Q := (algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F (Adeles F)))
  have hwK := (mem_range_map_iff_of_isRepresentedBy F (Standard.isRepresentedBy_unipotentHom i ν K) w).mp
    (hDK hw)
  exact exists_standardLevi_unipotent_factors_on_points hG hi hν J K hJ hK Q hwK

end Langlands.Global.AdelicGroupPoints
