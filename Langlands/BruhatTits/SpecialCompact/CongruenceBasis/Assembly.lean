import Langlands.BruhatTits.SpecialCompact.CongruenceBasis.ModelCocharacter
import Langlands.BruhatTits.SpecialCompact.MoyPrasadIwahoriProduct
import Langlands.BruhatTits.SpecialCompact.CompatibleApartmentProperties
import Langlands.BruhatTits.SpecialCompact.AvailableBasisStatement
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsNegation
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.Representation.Aubert.General.RationalOppositeChamber

/-! # The simultaneous standard basis from the congruence tower of an integral model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.BruhatTits.SpecialCompact.CongruenceGL

open Langlands.GroupScheme Langlands.GroupScheme.IntegralModel Langlands.Geometry.Building
  Langlands.BruhatTits.SpecialCompact Langlands.AlgebraicGeometry.PointTopology

section Standard

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- Points of the torus normalize every standard unipotent subgroup. -/
theorem map_conj_mem_standardUnipotentPoints {J : Set (characterLattice S)}
    (t : rationalPoints S.toGrp) {g : rationalPoints G}
    (hg : g ∈ standardUnipotentPoints i ν J) :
    rationalPoints.map i t * g * (rationalPoints.map i t)⁻¹ ∈
      standardUnipotentPoints i ν J := by
  have htc : rationalPoints.map i t ∈ (torusCentralizer i).carrier (Over.mk (𝟙 _)) :=
    range_le_torusCentralizer i (Over.mk (𝟙 _)) ⟨t, rfl⟩
  apply (mem_standardUnipotent i ν).mpr
  intro ζ hζ
  have hz := torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom ζ) _ htc
  exact Dynamic.conj_mem_unipotent _ (Dynamic.centralizer_le_parabolic _ _ hz)
    ((mem_standardUnipotent i ν).mp hg ζ hζ)

variable {i ν}

/-- A cocharacter orthogonal to `J` and nonnegative on all simple roots is standard for the set
of simple roots on which it vanishes, and this set contains `J`. -/
theorem isStandardCocharacter_zeroSet {J : Set (characterLattice S)}
    (hJ : J ⊆ simpleRelativeRoots i ν) {y : cocharacterLattice S}
    (hyJ : ∀ α ∈ J, latticePairing S α y = 0)
    (hy : ∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α y) :
    IsStandardCocharacter i ν
        {α | α ∈ simpleRelativeRoots i ν ∧ latticePairing S α y = 0} y ∧
      J ⊆ {α | α ∈ simpleRelativeRoots i ν ∧ latticePairing S α y = 0} :=
  ⟨⟨fun _ h => h.1, fun _ h => h.2, fun α hα hn =>
      lt_of_le_of_ne (hy α hα) (fun h => hn ⟨hα, h.symm⟩)⟩,
    fun α hα => ⟨hJ hα, hyJ α hα⟩⟩

/-- **The standard radical lies in the parabolic of a dominant cocharacter orthogonal to `J`.**
-/
theorem mem_parabolic_of_mem_standardUnipotentPoints (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {y : cocharacterLattice S} (hyJ : ∀ α ∈ J, latticePairing S α y = 0)
    (hy : ∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α y)
    {g : rationalPoints G} (hg : g ∈ standardUnipotentPoints i ν J) :
    g ∈ (Dynamic.parabolic (CommGroupScheme.groupHom y ≫ i)).carrier (Over.mk (𝟙 _)) := by
  obtain ⟨hy', hJJ'⟩ := isStandardCocharacter_zeroSet hJ hyJ hy
  have hP : g ∈ standardParabolicPoints i ν J :=
    standardUnipotent_le_standardParabolic i ν J (Over.mk (𝟙 _)) hg
  have hP' := ((standardParabolicOrder F G hG S i hi ν hν).1 J _ hJ hy'.1).1.mp hJJ'
    (Over.mk (𝟙 _)) hP
  exact (mem_standardParabolic i ν).1 hP' y hy'

end Standard

section Model

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (M : IntegralModel ↥𝒪[F] F G)

/-- The chosen uniformizer of `F` is integral. -/
theorem uniformizer_mem_integer : LocalField.uniformizer F ∈ 𝒪[F] :=
  (FML.ord_nonneg_iff_mem_integer F _).1 (by rw [LocalField.ord_uniformizer]; decide)

/-- The chosen uniformizer of `F`, as an element of the valuation ring `𝒪[F]`. -/
def integralUniformizer : ↥𝒪[F] :=
  ⟨LocalField.uniformizer F, uniformizer_mem_integer⟩

omit [IsAffineHom G.X.hom] in
/-- The uniformizer power of a cocharacter is the image of the uniformizer under the composite
cocharacter of `G`. -/
theorem uniformizerPowers_eq (y : cocharacterLattice S) :
    Aubert.General.uniformizerPowers i (.ofAdd y) =
      rationalPoints.map (CommGroupScheme.groupHom y ≫ i)
        ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm
          (SplitTorusValuation.uniformizerUnit F)) :=
  rfl

/-- **Weak contraction in one direction.** If every cocharacter of the maximal split torus lifts to
the integral model, conjugation by a weak-chamber point of a compatible split component preserves
the intersection of each congruence subgroup with the standard radical. -/
theorem conj_mem_congruenceSubgroupAt_inf_standardUnipotentPoints
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hχ : ∀ y : cocharacterLattice S,
      ∃ χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group,
        M.genericCocharacter χ = CommGroupScheme.groupHom y ≫ i)
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    {m : rationalPoints G} (hm : m ∈ standardComponentCAplus i ν J q) (n : ℕ+)
    {g : rationalPoints G} (hg : g ∈ M.congruenceSubgroupAt n ⊓ standardUnipotentPoints i ν J) :
    m * g * m⁻¹ ∈ M.congruenceSubgroupAt n ⊓ standardUnipotentPoints i ν J := by
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨y, rfl, hyJ, hy⟩ := hA.exists_eq_uniformizerPowers hJ hm
  obtain ⟨χ, hχy⟩ := hχ y
  obtain ⟨N, ρ, e, hcl, hdiag, hK⟩ := exists_model_linearCongruence M hG χ
  rw [hχy] at hdiag
  let : IsClosedImmersion ρ.hom.hom.left := hcl
  have hgP := mem_parabolic_of_mem_standardUnipotentPoints hG hi hν hJ hyJ hy hg.2
  refine ⟨?_, ?_⟩
  · have hgK := hg.1
    rw [hK n] at hgK ⊢
    rw [uniformizerPowers_eq]
    exact conj_mem_linearCongruence ρ (algebraMap ↥𝒪[F] F) _ hdiag Subtype.val_injective
      (SplitTorusValuation.uniformizerUnit F) (integralUniformizer (F := F)) rfl hgK hgP
  · exact map_conj_mem_standardUnipotentPoints i ν _ hg.2

/-- **Weak contraction of the congruence tower.** -/
theorem weakChamberContraction_congruenceSubgroupAt
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hχ : ∀ y : cocharacterLattice S,
      ∃ χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group,
        M.genericCocharacter χ = CommGroupScheme.groupHom y ≫ i)
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
    (hA : IsCompatibleStandardSplitComponent i ν J A q) (n : ℕ+) :
    WeakChamberContraction (M.congruenceSubgroupAt n) (standardUnipotentPoints i ν J)
      (standardOppositeUnipotentPoints i ν J) (standardComponentCAplus i ν J q) := by
  intro m hm
  have hneg := relativeRootNegation F G hG S i hi
  have hJrev : Neg.neg '' J ⊆ simpleRelativeRoots i (-ν) := by
    rintro _ ⟨a, ha, rfl⟩
    exact neg_mem_simpleRelativeRoots i ν hneg (hJ ha)
  constructor
  · rintro _ ⟨g, hg, rfl⟩
    exact conj_mem_congruenceSubgroupAt_inf_standardUnipotentPoints M hG hi hν hχ hJ hA hm n hg
  · rintro _ ⟨g, hg, rfl⟩
    exact conj_mem_congruenceSubgroupAt_inf_standardUnipotentPoints M hG hi hν.neg hχ hJrev
      (hA.reversed i ν hG hi hν hJ) (inv_mem_standardComponentCAplus_reversed ν hneg hm) n hg

/-- **Iwahori factorization of the congruence tower.** -/
theorem hasIwahoriIntersectionDecomposition_congruenceSubgroupAt
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hχ : ∀ y : cocharacterLattice S,
      ∃ χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group,
        M.genericCocharacter χ = CommGroupScheme.groupHom y ≫ i)
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν) (n : ℕ+) :
    HasIwahoriIntersectionDecomposition (M.congruenceSubgroupAt n) (standardLeviPoints i ν J)
      (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J) := by
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have hneg := relativeRootNegation F G hG S i hi
  obtain ⟨ζ, hζ⟩ := (standardCocharacter F G hG S i hi ν hν J hJ).1
  obtain ⟨-, hZ, hU⟩ := (standardCocharacter F G hG S i hi ν hν J hJ).2 ζ hζ
  have hUbar := (standard_eq_dynamic_of_relativeRootNegation relativeRootNegation F G hG S i hi
    (-ν) hν.neg (Neg.neg '' J) (-ζ) (hζ.neg i ν hneg)).2.2
  rw [groupHom_neg_comp_eq_oppositeCocharacter i ζ] at hUbar
  obtain ⟨χ, hχζ⟩ := hχ ζ
  obtain ⟨N, ρ, e, hcl, hdiag, hK⟩ := exists_model_linearCongruence M hG χ
  rw [hχζ] at hdiag
  let : IsClosedImmersion ρ.hom.hom.left := hcl
  set K := M.congruenceSubgroupAt n with hKdef
  refine hasIwahoriIntersectionDecomposition_of_surjective K _ _ _
    (K ⊓ standardUnipotentPoints i ν J) (K ⊓ standardOppositeUnipotentPoints i ν J)
    inf_le_left inf_le_left inf_le_right inf_le_right
    (standardTripleProduct_injective i ν hneg hζ) ?_
  rintro ⟨g, hg⟩
  have hg' := hg
  rw [hKdef, hK n] at hg'
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := exists_linearCongruence_triple ρ (algebraMap ↥𝒪[F] F)
    _ hdiag (Ideal.pow_le_self (PNat.ne_zero n)) hg'
  have hK' : K = linearCongruence ρ (algebraMap ↥𝒪[F] F)
      (IsLocalRing.maximalIdeal ↥𝒪[F] ^ (n : ℕ)) := hK n
  refine ⟨(⟨a, hK' ▸ ha.1, ?_⟩, ⟨b, hK' ▸ hb.1, ?_⟩, ⟨c, hK' ▸ hc.1, ?_⟩), rfl⟩
  · change a ∈ (standardUnipotent i (-ν) (Neg.neg '' J)).carrier _
    rw [hUbar]
    exact ha.2
  · change b ∈ (standardLevi i ν J).carrier _
    rw [hZ]
    exact hb.2
  · change c ∈ (standardUnipotent i ν J).carrier _
    rw [hU]
    exact hc.2

/-- **The simultaneous standard basis of an integral model.** If every cocharacter of the maximal
split torus lifts to a cocharacter of the integral model, the congruence tower of the model gives
the simultaneous standard basis at the integral points. -/
theorem simultaneousStandardBasisAt_integralPoints
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hχ : ∀ y : cocharacterLattice S,
      ∃ χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group,
        M.genericCocharacter χ = CommGroupScheme.groupHom y ≫ i) :
    SimultaneousStandardBasisAt i ν M.integralPoints := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  apply simultaneousStandardBasisAt_of_cofinal_weakIwahoriNormalFamily i ν hG hi hν
    (standardSplitComponentFamily i ν hG hi hν) M.integralPoints
  intro W hW
  obtain ⟨-, -, hcn, hcof⟩ := LocalFieldIntegralModel.congruenceNeighborhoodBasis_proof F G M
  obtain ⟨n, hn⟩ := hcof W hW
  refine ⟨M.congruenceSubgroupAt n, ⟨⟨M.congruenceSubgroupAt_le_integralPoints n, (hcn n).2.2,
    (hcn n).2.1, (hcn n).1⟩, fun J hJ => ⟨?_, ?_⟩⟩, hn⟩
  · exact hasIwahoriIntersectionDecomposition_congruenceSubgroupAt M hG hi hν hχ hJ n
  · exact weakChamberContraction_congruenceSubgroupAt M hG hi hν hχ hJ
      ((standardSplitComponentFamily i ν hG hi hν).compatible J hJ) n

end Model

section Available

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- **The simultaneous standard basis at a special vertex of an available KP assignment.** -/
theorem available_simultaneousStandardBasisAt (𝔅 : KPBuildingAssignment.{u})
    (hG : IsConnectedReductive G) (h𝔅 : 𝔅.IsAvailableFor F G hG)
    (ν : cocharacterLattice (𝔅.datum F G hG).base.S)
    (hν : IsGenericCocharacter (𝔅.datum F G hG).base.i ν)
    (x : (𝔅.datum F G hG).base.Apartment)
    (hx : (𝔅.datum F G hG).base.apartment.IsSpecialApartmentVertex x) :
    SimultaneousStandardBasisAt (𝔅.datum F G hG).base.i ν
      ((𝔅.datum F G hG).base.apartment.specialCompactSubgroup x) := by
  obtain ⟨M, hM, hχ⟩ := exists_specialVertexModel 𝔅 hG h𝔅 x hx
  rw [← hM]
  exact simultaneousStandardBasisAt_integralPoints M hG
    (𝔅.datum F G hG).base.isMaximalSplitTorus hν hχ

end Available

end Langlands.BruhatTits.SpecialCompact.CongruenceGL
