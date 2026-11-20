import Langlands.Representation.Plancherel.CompactIwasawaOrbitalMass
import Langlands.Representation.Plancherel.CommonLeviDisplacementWeights
import Langlands.Representation.Plancherel.RegularCompactCocharacter
import Langlands.Representation.Plancherel.DynamicCommonLeviCompact
import Langlands.Representation.Plancherel.DynamicOppositeConjugateDomain
import Langlands.GroupScheme.Dynamic.OppositeParabolicComparison
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.BruhatTits.Unipotent.CocharacterEscape

/-! # The compact Iwasawa scale for actual common-Levi parabolics -/

noncomputable section

set_option maxHeartbeats 1400000

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal NNReal

namespace Langlands.Plancherel.ActualCommonLeviIwasawa

open GroupScheme Langlands.AlgebraicGeometry.PointTopology
  DynamicOppositeStandardIntertwining DynamicCommonLeviComposition DynamicCommonLeviCompact
  Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
  Langlands.BruhatTits.DynamicUnipotentContainment Langlands.Haar Langlands.HaarModulus
  LeviInvariantIwasawaExchange Langlands.HaarModulus.VectorFiltration

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  Langlands.HaarModulus.subgroupMeasurableSpace
  Langlands.HaarModulus.subgroupBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance : MeasurableSpace (RationalPoint F G.X) := borel _
local instance : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance : SecondCountableTopology (RationalPoint F G.X) :=
  Langlands.AlgebraicGeometry.PointTopology.rationalPoint_secondCountableTopology F G
local instance (S : Subgroup (RationalPoint F G.X)) : SecondCountableTopology S :=
  TopologicalSpace.Subtype.secondCountableTopology (S : Set (RationalPoint F G.X))
local instance (φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    LocallyCompactSpace (radical φ) := (radical_isClosed φ).locallyCompactSpace

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

/-- One compact central point and the positive finite value of its orbital test
in both actual radical Haar normalizations. -/
structure CompactOrbitalWitness where
  value : RationalPoint F G.X
  mem_compact : value ∈ K
  commutes : ∀ m : levi ψ, Commute (m : RationalPoint F G.X) value
  mass : ℝ≥0∞
  mass_ne_zero : mass ≠ 0
  mass_ne_top : mass ≠ ⊤
  source_mass : radicalHaar ψ K hK (compactConjugationPreimage K value (radical ψ)) = mass
  target_mass : radicalHaar ψ' K hK (compactConjugationPreimage K value (radical ψ')) = mass

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem fieldUnit_displacement_product_ne_zero
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (ζ eta : cocharacterLattice T)
    (hEq : Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) =
      Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i))
    (s : Fˣ)
    (hs : ∀ α : characterLattice T, weightSpace i α ≠ ⊥ →
      latticePairing T α ζ ≠ 0 → s ^ latticePairing T α ζ ≠ 1) :
    positiveWeightProduct hT i eta
      (fun α => 1 - ((s ^ latticePairing T α ζ : Fˣ) : F)) ≠ 0 := by
  unfold positiveWeightProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro α hα
  have hα' := (hT.finite_weightSupport i).mem_toFinset.mp hα
  split_ifs with hpos
  · have hζ : latticePairing T α ζ ≠ 0 := fun h => (ne_of_gt hpos)
      ((latticePairing_eq_zero_iff_of_centralizer_eq hT i ζ eta hEq α hα').mp h)
    exact pow_ne_zero _ (sub_ne_zero.mpr (fun he => hs α hα' hζ (Units.ext he.symm)))
  · simpa only [pow_zero] using (one_ne_zero : (1 : F) ≠ 0)

private theorem exists_compactOrbitalWitness
    (hG : IsConnectedReductive G) (hEq : Dynamic.centralizer ψ = Dynamic.centralizer ψ') :
    Nonempty (CompactOrbitalWitness K hK ψ ψ') := by
  classical
  have hcomm : SubgroupFunctor.range ψ' ≤ Dynamic.centralizer ψ :=
    hEq.symm ▸ Dynamic.range_le_centralizer ψ'
  obtain ⟨T, i, ζ, eta, hi, hζ, heta⟩ :=
    exists_common_maximalSplitTorus_of_range_le_centralizer ψ ψ' hcomm
  subst ψ
  subst ψ'
  let ψ := CommGroupScheme.groupHom ζ ≫ i
  let ψ' := CommGroupScheme.groupHom eta ≫ i
  change Dynamic.centralizer ψ = Dynamic.centralizer ψ' at hEq
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  let hT := hi.isSplitSubtorus.1
  have : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  have : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have hroot := relativeRootSystem F G hG T i hi
  let D := (hT.finite_weightSupport i).toFinset.image (fun α => latticePairing T α ζ)
  obtain ⟨s, hsK, hsNorm, hs⟩ := exists_normOne_cocharPoint_mem ψ K D
  have hs' (α : characterLattice T) (hα : weightSpace i α ≠ ⊥)
      (hne : latticePairing T α ζ ≠ 0) : s ^ latticePairing T α ζ ≠ 1 :=
    hs _ (Finset.mem_image.mpr ⟨α, (hT.finite_weightSupport i).mem_toFinset.mpr hα, rfl⟩) hne
  let Z := Dynamic.Affine.centralizerScheme ψ
  let iZ := Dynamic.Affine.centralizerHom ψ
  let U := Dynamic.Affine.unipotentScheme ψ
  let iU := Dynamic.Affine.unipotentHom ψ
  let V := Dynamic.Affine.unipotentScheme ψ'
  let iV := Dynamic.Affine.unipotentHom ψ'
  have hZ : (Dynamic.centralizer ψ).IsRepresentedBy iZ := Dynamic.Affine.isRepresentedBy_centralizerHom ψ
  have hZ' : (Dynamic.centralizer ψ').IsRepresentedBy iZ := hEq ▸ hZ
  have hU : (Dynamic.unipotent ψ).IsRepresentedBy iU := Dynamic.Affine.isRepresentedBy_unipotentHom ψ
  have hV : (Dynamic.unipotent ψ').IsRepresentedBy iV := Dynamic.Affine.isRepresentedBy_unipotentHom ψ'
  obtain ⟨-, -, hUa, -, -, -, -, -, -, -, -, -, -, d, ⟨c⟩⟩ :=
    dynamicAdjointDeterminantStructure F G hG ψ _ Z U (Dynamic.Affine.parabolicHom ψ) iZ iU
      (Dynamic.Affine.isRepresentedBy_parabolicHom ψ) hZ hU
  obtain ⟨-, -, hVa, -, -, -, -, -, -, -, -, -, -, d', ⟨c'⟩⟩ :=
    dynamicAdjointDeterminantStructure F G hG ψ' _ Z V (Dynamic.Affine.parabolicHom ψ') iZ iV
      (Dynamic.Affine.isRepresentedBy_parabolicHom ψ') hZ' hV
  let j := hZ.liftOfLE i (range_le_centralizer_groupHom_comp i ζ)
  have hj : j ≫ iZ = i := hZ.liftOfLE_comp i (range_le_centralizer_groupHom_comp i ζ)
  let t := CocharacterUniformizer.cocharacterPoints F T ζ s
  let m : rationalPoints Z := t ≫ j.hom.hom
  let a := (cocharPoint ψ s)⁻¹
  have hm : m ≫ iZ.hom.hom = a⁻¹ := by
    change (t ≫ j.hom.hom) ≫ iZ.hom.hom = (cocharPoint ψ s)⁻¹⁻¹
    rw [Category.assoc, ← Grp.comp_hom_hom, hj, inv_inv]
    exact (cocharPoint_comp_eq_map_cocharacterPoints i ζ s).symm
  have ht (α : characterLattice T) :
      Lie.characterValue α (Dynamic.GradedCoordinates.toBase (Dynamic.GradedCoordinates.baseTest F) ≫ t) =
        s ^ latticePairing T α ζ := by
    have hv := CocharacterUniformizer.rationalCharacterEval_cocharacterPoints F T α ζ s
    rw [rationalCharacterEval_eq_affineUnitsEquiv, Dynamic.GradedCoordinates.rationalPointEquiv_eq_toBase,
      affinePointsTarget_apply] at hv
    exact hv
  let f (α : characterLattice T) : F := 1 - ((s ^ latticePairing T α ζ : Fˣ) : F)
  have hId : unipotentDisplacementDeterminant hZ hU m = positiveWeightProduct hT i ζ f := by
    rw [unipotentDisplacementDeterminant_eq_positiveWeightProduct hT i ζ hZ hU j hj c t]
    simp only [f, ht]
  have hId' : unipotentDisplacementDeterminant hZ' hV m = positiveWeightProduct hT i eta f := by
    rw [unipotentDisplacementDeterminant_eq_positiveWeightProduct hT i eta hZ' hV j hj c' t]
    simp only [f, ht]
  have hd : unipotentDisplacementDeterminant hZ hU m ≠ 0 := by
    rw [hId]
    exact fieldUnit_displacement_product_ne_zero hT i ζ ζ rfl s hs'
  have hd' : unipotentDisplacementDeterminant hZ' hV m ≠ 0 := by
    rw [hId']
    exact fieldUnit_displacement_product_ne_zero hT i ζ eta hEq s hs'
  let D₀ : Fˣ := Units.mk0 _ hd
  let D₁ : Fˣ := Units.mk0 _ hd'
  have hnorm : distribHaarChar F D₀ = distribHaarChar F D₁ := by
    rw [show distribHaarChar F D₀ = scalingWithZero (unipotentDisplacementDeterminant hZ hU m) from
        (scalingWithZero_of_ne_zero hd).symm,
      show distribHaarChar F D₁ = scalingWithZero (unipotentDisplacementDeterminant hZ' hV m) from
        (scalingWithZero_of_ne_zero hd').symm, hId, hId']
    have hp (ν : cocharacterLattice T) :
        scalingWithZero (positiveWeightProduct hT i ν f) =
          positiveWeightProduct hT i ν (fun α => fieldUnitDisplacementNorm s (latticePairing T α ζ)) := by
      unfold positiveWeightProduct
      rw [map_prod]
      simp only [map_pow, f, fieldUnitDisplacementNorm]
    rw [hp, hp]
    apply hroot.positiveWeightProduct_eq_of_centralizer_eq hT ζ eta hEq
    intro α
    rw [map_neg, LinearMap.neg_apply, fieldUnitDisplacementNorm_neg s hsNorm]
  have haK : a ∈ K := K.inv_mem hsK
  have ha (x : levi ψ) : Commute (x : RationalPoint F G.X) a :=
    (commute_cocharPoint ψ x.2 s).inv_right
  have hZmem : m ≫ iZ.hom.hom ∈ (Dynamic.centralizer ψ).carrier (Over.mk (𝟙 _)) :=
    hZ.2 ▸ SubgroupFunctor.mem_range.mpr ⟨m, rfl⟩
  have hmU : m ≫ iZ.hom.hom ∈ Subgroup.normalizer (radical ψ : Set (RationalPoint F G.X)) :=
    Dynamic.centralizer_le_normalizer_unipotent ψ _ hZmem
  have hmV : m ≫ iZ.hom.hom ∈ Subgroup.normalizer (radical ψ' : Set (RationalPoint F G.X)) :=
    Dynamic.centralizer_le_normalizer_unipotent ψ' _ (hEq ▸ hZmem)
  let b₀ : (radical ψ) ≃ₜ* (radical ψ) := normalizerConj _ ⟨m ≫ iZ.hom.hom, hmU⟩
  let b₁ : (radical ψ') ≃ₜ* (radical ψ') := normalizerConj _ ⟨m ≫ iZ.hom.hom, hmV⟩
  let mass : ℝ≥0∞ := ((distribHaarChar F D₀ : ℝ≥0∞))⁻¹
  have hx0 : (distribHaarChar F D₀ : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast ((Group.isUnit D₀).map (distribHaarChar F)).ne_zero
  refine ⟨⟨a, haK, ha, mass, ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top,
    ENNReal.inv_ne_top.mpr hx0, ?_, ?_⟩⟩
  · apply measure_compactConjugationPreimage_of_map K a b₀
      (fun x => by change (m ≫ iZ.hom.hom) * (x : RationalPoint F G.X) *
        (m ≫ iZ.hom.hom)⁻¹ = a⁻¹ * (x : RationalPoint F G.X) * a
                   rw [hm, inv_inv])
      _ (subgroupCompactOpenHaar_mass _ _ _ _) mass
    exact map_dynamicUnipotentDisplacement hZ hU m hG (radical_isClosed ψ) hmU hd _
  · apply measure_compactConjugationPreimage_of_map K a b₁
      (fun x => by change (m ≫ iZ.hom.hom) * (x : RationalPoint F G.X) *
        (m ≫ iZ.hom.hom)⁻¹ = a⁻¹ * (x : RationalPoint F G.X) * a
                   rw [hm, inv_inv])
      _ (subgroupCompactOpenHaar_mass _ _ _ _) mass
    rw [show mass = ((distribHaarChar F D₁ : ℝ≥0∞))⁻¹ by rw [← hnorm]]
    exact map_dynamicUnipotentDisplacement hZ' hV m hG (radical_isClosed ψ') hmV hd' _

/-- Select an orbital test witnessing equality of the actual compact radical masses. -/
def compactOrbitalWitness (hG : IsConnectedReductive G)
    (hEq : Dynamic.centralizer ψ = Dynamic.centralizer ψ') : CompactOrbitalWitness K hK ψ ψ' :=
  Classical.choice (exists_compactOrbitalWitness K hK ψ ψ' hG hEq)

/-- In the literal common-Levi setting, the two compact Iwasawa pushforwards
have the same normalization for the original compact open subgroup. -/
theorem iwasawaExchangeRatio_eq_one
    (hG : IsConnectedReductive G) (hEq : Dynamic.centralizer ψ = Dynamic.centralizer ψ')
    (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (leviMeasure : Measure (levi ψ)) [leviMeasure.IsHaarMeasure]
    [leviMeasure.IsMulRightInvariant] [SFinite leviMeasure] :
    LeviInvariantIwasawaExchange.iwasawaExchangeRatio K leviMeasure
      (radicalHaar ψ K hK) (radicalHaar ψ' K hK) = 1 := by
  let w := compactOrbitalWitness K hK ψ ψ' hG hEq
  let h := decomposition ψ
  let h' := commonDecomposition ψ ψ' hEq.symm
  exact iwasawaExchangeRatio_eq_one_of_compactConjugation K w.value h h' leviMeasure
    (radicalHaar ψ K hK) (radicalHaar ψ' K hK) (RankinSelberg.normalizedCompactOpenHaar K hK)
    (DynamicOppositeCanonicalScalar.parabolic_isClosed ψ)
    (DynamicOppositeCanonicalScalar.parabolic_isClosed ψ') hK
    (DynamicOppositeCanonicalScalar.projection_continuous ψ)
    (commonProjection_continuous ψ ψ' hEq.symm)
    (OppositeIntertwiningHermitianAdjunction.exists_levi_unipotent_compact h K hψK)
    (OppositeIntertwiningHermitianAdjunction.exists_levi_unipotent_compact h' K hψ'K)
    w.commutes w.mem_compact (w.target_mass.trans w.source_mass.symm)
    (w.source_mass ▸ w.mass_ne_zero) (w.source_mass ▸ w.mass_ne_top)

/-- The two compact-coordinate masses in the original common Levi are equal. -/
theorem iwasawaCompactMass_eq
    (hG : IsConnectedReductive G) (hEq : Dynamic.centralizer ψ = Dynamic.centralizer ψ')
    (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (leviMeasure : Measure (levi ψ)) [leviMeasure.IsHaarMeasure]
    [leviMeasure.IsMulRightInvariant] [SFinite leviMeasure] :
    iwasawaCompactMass K leviMeasure (radicalHaar ψ K hK) =
      iwasawaCompactMass K leviMeasure (radicalHaar ψ' K hK) := by
  let x := iwasawaCompactMass K leviMeasure (radicalHaar ψ K hK)
  let y := iwasawaCompactMass K leviMeasure (radicalHaar ψ' K hK)
  have hr : y * x⁻¹ = 1 :=
    iwasawaExchangeRatio_eq_one K hK ψ ψ' hG hEq hψK hψ'K leviMeasure
  have hx0 : x ≠ 0 := iwasawaCompactMass_ne_zero K leviMeasure (radicalHaar ψ K hK)
  have hxT : x ≠ ⊤ := iwasawaCompactMass_ne_top (decomposition ψ) K leviMeasure
    (radicalHaar ψ K hK) (DynamicOppositeCanonicalScalar.parabolic_isClosed ψ) hK
    (DynamicOppositeCanonicalScalar.projection_continuous ψ)
  change x = y
  calc
    x = (y * x⁻¹) * x := by rw [hr, one_mul]
    _ = y := by rw [mul_assoc, ENNReal.inv_mul_cancel hx0 hxT, mul_one]

end Langlands.Plancherel.ActualCommonLeviIwasawa
