import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCartanIwasawaWeightComparisonStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicDeterminantLine
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiLevi
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof
import Langlands.GroupScheme.Dynamic.CommonTorusIntersectionDeterminants
import Langlands.GroupScheme.Dynamic.AdjointDeterminantCentralizerRestrictionProof
import Langlands.GroupScheme.Dynamic.ParabolicCharacters
import Langlands.GroupScheme.Lie.HomogeneousCoordinates
import Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.Representation.Aubert.General.CentralizingUnipotentHaarDeterminant
import Langlands.Representation.Aubert.General.RationalGeometricEpsilonBalance
import Langlands.Representation.Aubert.General.RationalUniformizerContraction
import Langlands.Representation.Plancherel.RationalCompactLatticePolynomialBoundProof

/-! # The actual Cartan-to-Iwasawa weight comparison -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory Matrix
open scoped CategoryTheory.MonObj NNReal ENNReal Pointwise Matrix WithZero
open Langlands.GroupScheme Langlands.GroupScheme.Dynamic
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The minors of a diagonal operator have norm bounded by the product of
all the expanding entries, with any norm-one entries allowed in the product. -/
private theorem exteriorGL_entryNorm_le {F : Type*} [NormedField F]
    {N d : ℕ} [Nonempty (Set.powersetCard (Fin N) d)]
    (A : GL (Fin N) F) (eigenvalue : Fin N → F)
    (hA : (A : Matrix (Fin N) (Fin N) F) = Matrix.diagonal eigenvalue)
    (s : Finset (Fin N)) (hs : ∀ i ∈ s, 1 ≤ ‖eigenvalue i‖) (hc : ∀ i ∉ s, ‖eigenvalue i‖ ≤ 1) :
    entryNorm (Chevalley.exteriorGL N d F A :
      Matrix (Set.powersetCard (Fin N) d) (Set.powersetCard (Fin N) d) F) ≤
        ∏ i ∈ s, ‖eigenvalue i‖ := by
  classical
  let b := Chevalley.matrixExteriorBasis N d F
  let ℓ := Matrix.toLin' (A : Matrix (Fin N) (Fin N) F)
  have hℓ (i : Fin N) : ℓ (Pi.basisFun F (Fin N) i) = eigenvalue i • Pi.basisFun F (Fin N) i := by
    change Matrix.toLin' (A : Matrix (Fin N) (Fin N) F) _ = _
    rw [hA, Matrix.toLin'_apply]
    ext j
    rw [Matrix.mulVec_diagonal]
    by_cases h : j = i
    · subst j
      simp [Pi.basisFun_apply]
    · simp [Pi.basisFun_apply, h]
  refine entryNorm_le fun p q => ?_
  let f := Set.powersetCard.ofFinEmbEquiv.symm q
  have hq : exteriorPower.map d ℓ (b q) = (∏ j, eigenvalue (f j)) • b q := by
    change exteriorPower.map d ℓ ((Pi.basisFun F (Fin N)).exteriorPower d q) = _
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.map_apply_ιMulti]
    change exteriorPower.ιMulti F d (fun j => ℓ (Pi.basisFun F (Fin N) (f j))) = _
    simp only [hℓ]
    rw [AlternatingMap.map_smul_univ]
    congr 1
    rw [show b q = (Pi.basisFun F (Fin N)).exteriorPower d q from rfl,
      exteriorPower.basis_apply, exteriorPower.ιMulti_family]
    rfl
  have hentry : (Chevalley.exteriorGL N d F A :
      Matrix (Set.powersetCard (Fin N) d) (Set.powersetCard (Fin N) d) F) p q =
      (b.repr ((exteriorPower.map d ℓ) (b q))) p := by
    rw [Chevalley.exteriorGL_val, LinearMap.toMatrix_apply]
  rw [hentry, hq, map_smul]
  by_cases hpq : p = q
  · subst p
    rw [Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
      mul_one, norm_prod]
    let t := Finset.univ.map f.toEmbedding
    let bound := fun i => if i ∈ s then ‖eigenvalue i‖ else 1
    rw [← show ∏ i ∈ t, ‖eigenvalue i‖ = ∏ j, ‖eigenvalue (f j)‖ from Finset.prod_map _ _ _]
    calc
      ∏ i ∈ t, ‖eigenvalue i‖ ≤ ∏ i ∈ t, bound i := by
        refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
        by_cases hi : i ∈ s
        · simp [bound, hi]
        · simpa [bound, hi] using hc i hi
      _ ≤ ∏ i, bound i := by
        refine Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _) ?_ ?_
        · intro i _
          dsimp [bound]
          split_ifs <;> positivity
        · intro i _ _
          by_cases hi : i ∈ s
          · simpa [bound, hi] using hs i hi
          · simp [bound, hi]
      _ = ∏ i ∈ s, ‖eigenvalue i‖ := by
        rw [← Finset.prod_filter]
        simp
  · simp only [Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_of_ne hpq,
      smul_zero, norm_zero]
    exact Finset.prod_nonneg fun i _ => norm_nonneg _

section Adjoint

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {S : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : S.toGrp ⟶ G) {d : ℕ} (c : Lie.FiniteCoordinates G d)
  (q : HomogeneousLieBasis (AutomorphicAction.conjugation (𝟙 G)) i)

private theorem adjointMatrix_inBasis_diagonal (t : rationalPoints S.toGrp) :
    ((Lie.adjointRepresentation (c.inBasis q.basis)).rationalMatrix
      (rationalPoints.map i t) : Matrix (Fin q.dimension) (Fin q.dimension) F) =
    Matrix.diagonal (fun j => (Lie.characterValue (q.weight j)
      (rationalPointEquiv F S.X t) : F)) := by
  classical
  let A := CommAlgCat.of (CommRingCat.of F) F
  let t' : Lie.AffinePoints S.toGrp A := rationalPointEquiv F S.X t
  rw [Plancherel.rationalMatrix_eq_affineMatrix, rationalPointEquiv_map]
  set M := (Lie.adjointRepresentation (c.inBasis q.basis)).affineMatrix A (t' ≫ i.hom.hom) with hM
  have hact (v : Fin q.dimension → F) (j : Fin q.dimension) :
      ((M : Matrix _ _ F) *ᵥ v) j = (Lie.characterValue (q.weight j) t' : F) * v j := by
    rw [hM, ← MatrixRepresentation.affineAction_apply]
    let x := ((c.inBasis q.basis).equiv A).symm v
    have hx : (c.inBasis q.basis).equiv A x = v := LinearEquiv.apply_symm_apply _ _
    rw [← hx, Lie.adjointRepresentation_affineAction]
    have h := q.differential_coordinates c A t' x j
    simpa only [AutomorphicAction.differential_conjugation, Grp.id_hom_hom,
      Category.comp_id] using h
  ext j l
  have h := hact (Pi.single l 1) j
  simpa [Matrix.mulVec_single, Matrix.diagonal_apply, Pi.single_apply,
    eq_comm] using h

end Adjoint

section PositiveWeights

variable {F : Type u} [Field F] {G U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffineHom U.X.hom] [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine S.X.left]
  {iU : U ⟶ G} {N d : ℕ}

/-- In suitable homogeneous coordinates, the determinant on the radical is the
product over exactly the ambient basis vectors of positive cocharacter weight. -/
private theorem exists_homogeneousBasis_unipotent_determinant
    (i : S.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp) (ν : cocharacterLattice S)
    (hU : (unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy iU)
    (cG : Lie.FiniteCoordinates G N) (cU : Lie.FiniteCoordinates U d) :
    ∃ q : HomogeneousLieBasis (AutomorphicAction.conjugation (𝟙 G)) i,
      ∀ t : rationalPoints S.toGrp,
        rationalCharacterEval
          ((centralizingUnipotentAction (CommGroupScheme.groupHom ν ≫ i) i
            (range_le_centralizer_groupHom_comp i ν) hU).determinantCharacter cU) t =
          ∏ j ∈ Finset.univ.filter (fun j => decide (0 < latticePairing S (q.weight j) ν)),
            Lie.characterValue (q.weight j) (rationalPointEquiv F S.X t) := by
  classical
  let χ := CommGroupScheme.groupHom ν ≫ i
  let hZ := range_le_centralizer_groupHom_comp i ν
  let a := centralizingUnipotentAction χ i hZ hU
  let b := AutomorphicAction.conjugation (𝟙 G)
  let positive : characterLattice S → Prop := fun α => 0 < latticePairing S α ν
  have ha : (a.restrict (𝟙 S.toGrp)).IsEquivariant (AutomorphicAction.conjugation i) iU :=
    restrict_isEquivariant_conjugation_of_act_comp i i (𝟙 S.toGrp) (Category.id_comp i)
      a (centralizingUnipotentAction_act_comp χ i hZ hU)
  have hdim (α : characterLattice S) :
      Module.finrank F (a.lieWeightSpace (𝟙 S.toGrp) α) =
        if positive α then Module.finrank F (b.lieWeightSpace i α) else 0 := by
    rw [show b.lieWeightSpace i α = weightSpace i α by
      rw [AutomorphicAction.lieWeightSpace_conjugation, Category.comp_id]]
    have h := finrank_lieWeightSpace_of_tangentRegion i a (𝟙 S.toGrp) hU ha positive
      (fun β => by
        rw [weightSpace_inf_tangentSubmodule_unipotent hS i ν]
        by_cases hβ : 0 < latticePairing S β ν <;> simp [positive, hβ]) α
    by_cases hα : positive α
    · rw [ite_eq_left hα] at h ⊢
      exact h
    · rw [ite_eq_right hα] at h ⊢
      exact h
  let : FiniteDimensional F (Additive (lieKernel U F)) :=
    (cU.equiv (.of (CommRingCat.of F) F)).symm.finiteDimensional
  let : FiniteDimensional F (Additive (lieKernel G F)) :=
    (cG.equiv (.of (CommRingCat.of F) F)).symm.finiteDimensional
  have hsupp (α : characterLattice S) : a.lieWeightSpace (𝟙 S.toGrp) α ≠ ⊥ ↔
      b.lieWeightSpace i α ≠ ⊥ ∧ positive α := by
    simp only [ne_eq, ← Submodule.finrank_eq_zero, hdim]
    by_cases h : positive α <;> simp [h]
  let I := b.lieWeightBasisIndex i
  let J := a.lieWeightBasisIndex (𝟙 S.toGrp)
  let : Finite I := b.finite_lieWeightBasisIndex cG hS i
  let : Finite J := a.finite_lieWeightBasisIndex cU hS (𝟙 S.toGrp)
  let : Fintype I := Fintype.ofFinite I
  let : Fintype J := Fintype.ofFinite J
  let e := Fintype.equivFin I
  let q : HomogeneousLieBasis b i := {
    dimension := Fintype.card I
    basis := (b.lieWeightBasis cG hS i).reindex e
    weight := fun j => (e.symm j).1.val
    mem_weight := fun j => by
      rw [Module.Basis.reindex_apply]
      exact b.lieWeightBasis_mem cG hS i (e.symm j)
  }
  let eU : J ≃ {j : I // positive j.1.val} := {
    toFun := fun j =>
      let hj := (hsupp j.1.val).mp j.1.property
      ⟨⟨⟨j.1.val, hj.1⟩, Fin.cast ((hdim j.1.val).trans (ite_eq_left hj.2)) j.2⟩, hj.2⟩
    invFun := fun j =>
      ⟨⟨j.val.1.val, (hsupp _).mpr ⟨j.val.1.property, j.property⟩⟩,
        Fin.cast ((hdim j.val.1.val).trans (ite_eq_left j.property)).symm j.val.2⟩
    left_inv := by rintro ⟨⟨α, hα⟩, j⟩; rfl
    right_inv := by rintro ⟨⟨⟨α, hα⟩, j⟩, hj⟩; rfl
  }
  let eP : J ≃ {j : Fin q.dimension // positive (q.weight j)} :=
    eU.trans (e.subtypeEquiv fun j => by simp [q])
  refine ⟨q, fun t => ?_⟩
  let A := CommAlgCat.of (CommRingCat.of F) F
  let t' : Lie.AffinePoints S.toGrp A := rationalPointEquiv F S.X t
  rw [rationalCharacterEval_eq_affineUnitsEquiv]
  refine (a.determinantCharacter_affinePoints cU A t').trans ?_
  have hdet := a.differential_det_lieWeightBasis cU hS (𝟙 S.toGrp) A t'
  rw [Grp.id_hom_hom, Category.comp_id] at hdet
  rw [hdet]
  have he (j : J) : q.weight (eP j).val = j.1.val := by
    change (e.symm (e _)).1.val = _
    rw [Equiv.symm_apply_apply]
    rfl
  calc
    (∏ j : J, Lie.characterValue j.1.val t') =
        ∏ j : {j : Fin q.dimension // positive (q.weight j)},
          Lie.characterValue (q.weight j.val) t' := by
      rw [← eP.prod_comp]
      exact Finset.prod_congr rfl (fun j _ => congrArg (fun α => Lie.characterValue α t') (he j).symm)
    _ = _ := by
      exact (Finset.prod_subtype _ (fun j => by simp [positive])
        (fun j => Lie.characterValue (q.weight j) t')).symm

end PositiveWeights

section HaarScalar

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Compare the scalar pushforward formula with the intrinsic forward Haar
character on the compact open valuation ring. -/
private theorem coe_distribHaarChar_eq_abs (a : Fˣ) :
    ((distribHaarChar F a : ℝ≥0) : ℝ) =
      LocalField.residueNormalizedAbsoluteValue F (a : F) := by
  let ϖ := SplitTorusValuation.uniformizerUnit F
  let v := ValuativeRel.valuation F
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have hπ : e (v (ϖ : F)) = WithZero.exp (-1) := by
    have h := FML.ord_of_ne_zero F (LocalField.uniformizer_ne_zero F)
    rw [LocalField.ord_uniformizer] at h
    change (1 : WithTop ℤ) = ((-WithZero.log (e (v (ϖ : F))) : ℤ) : WithTop ℤ) at h
    have hlog : WithZero.log (e (v (ϖ : F))) = -1 := by
      have h' := WithTop.coe_inj.mp h
      omega
    rw [← hlog, WithZero.exp_log]
    exact (FML.normalizedMultiplicativeValuation F).ne_zero_iff.mpr ϖ.ne_zero
  have hunif : GeneralLinear.Iwasawa.IsUniformizingElement v ϖ := by
    refine ⟨?_, fun x hx => ?_⟩
    · rw [← e.strictMono.lt_iff_lt, hπ, map_one, WithZero.exp_lt_one_iff]
      norm_num
    · refine ⟨-WithZero.log (e (v x)), e.injective ?_⟩
      rw [map_zpow₀]
      change e (v x) = e (v (ϖ : F)) ^ (-WithZero.log (e (v x)))
      rw [hπ, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one, neg_neg]
      exact (WithZero.exp_log ((FML.normalizedMultiplicativeValuation F).ne_zero_iff.mpr hx)).symm
  have hval (x : F) (hx : v x = 1) : LocalField.residueNormalizedAbsoluteValue F x = 1 := by
    have hx0 : x ≠ 0 := v.ne_zero_iff.mp (hx.trans_ne one_ne_zero)
    rw [LocalField.residueNormalizedAbsoluteValue_of_ne_zero F hx0]
    change (LocalField.residueCardinality F : ℝ) ^ WithZero.log (e (v x)) = 1
    simp [hx]
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let mH : Measure F := Measure.addHaar
  have : mH.IsAddHaarMeasure := by dsimp [mH]; infer_instance
  let O : Set F := FML.ringOfIntegers F
  have hOo : IsOpen O := HarmonicAnalysis.GeneralLocalField.isOpen_integer F
  have hOc : IsCompact O := HarmonicAnalysis.GeneralLocalField.isCompact_integer F
  have hO0 : mH O ≠ 0 := (hOo.measure_pos mH ⟨0, (FML.ringOfIntegers F).zero_mem⟩).ne'
  have hOtop : mH O ≠ ∞ := hOc.measure_ne_top
  let abv := LocalField.residueNormalizedAbsoluteValue F
  have hscale := HarmonicAnalysis.generalScalarHaarScalingStatement F
    (LocalField.residueCardinality F) rfl abv ϖ hunif
    (LocalField.residueNormalizedAbsoluteValue_of_ord_one F (LocalField.ord_uniformizer F))
    hval mH a⁻¹
  have h := congrArg (fun m : Measure F => m O) hscale
  change (mH.map (fun x => a⁻¹ • x)) O = _ at h
  rw [Measure.map_apply (measurable_const_smul a⁻¹) hOo.measurableSet, Set.preimage_smul,
    inv_inv, ← distribHaarChar_mul mH, Measure.smul_apply] at h
  simp only [map_inv, Units.val_inv_eq_inv_val, inv_inv] at h
  have h' : distribHaarChar F a = (Shahidi.absUnits abv a : ℝ≥0) :=
    ENNReal.coe_injective ((ENNReal.mul_left_inj hO0 hOtop).mp h)
  exact (congrArg (fun r : ℝ≥0 => (r : ℝ)) h').trans (Shahidi.absUnits_apply abv a)

end HaarScalar

section Chamber

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem pairing_nonneg_of_dominant {y : cocharacterLattice S}
    (hy : ∀ β : Aubert.General.RationalPointFamily.SimpleRoot i ν,
      0 ≤ Aubert.General.simpleRootPairing i ν β y)
    {α : characterLattice S} (hα : α ∈ positiveRelativeRoots i ν) :
    0 ≤ latticePairing S α y :=
  positiveRelativeRoots_induction i ν (P := fun β => 0 ≤ latticePairing S β y)
    (fun β hβ => hy ⟨β, hβ⟩)
    (fun _ _ _ _ hβ hγ => by simpa using add_nonneg hβ hγ) hα

private theorem norm_characterValue_inverseUniformizer
    (α : characterLattice S) (y : cocharacterLattice S) :
    letI := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
    ‖(Lie.characterValue α (rationalPointEquiv F S.X
      ((Plancherel.RenardCartan.uniformizerSection S (.ofAdd y))⁻¹)) : F)‖ =
        (LocalField.residueCardinality F : ℝ) ^ latticePairing S α y := by
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  rw [← map_inv, show (Multiplicative.ofAdd y)⁻¹ = Multiplicative.ofAdd (-y) from rfl]
  rw [Dynamic.GradedCoordinates.rationalPointEquiv_eq_toBase]
  change ‖(Lie.characterValue α
    (Aubert.General.RepresentedParabolic.ConeContraction.affPt
      (Plancherel.RenardCartan.uniformizerSection S (.ofAdd (-y)))) : F)‖ = _
  rw [Aubert.General.UniformizerContraction.characterValue_uniformizerSection, norm_zpow]
  change LocalField.residueNormalizedAbsoluteValue F (LocalField.uniformizer F) ^
    latticePairing S α (-y) = _
  rw [LocalField.residueNormalizedAbsoluteValue_uniformizer, ← _root_.zpow_mul]
  simp

private theorem entryNorm_adjointExterior_inverse_uniformizer_le
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {N d : ℕ} (c : Lie.FiniteCoordinates G N)
    (q : HomogeneousLieBasis (AutomorphicAction.conjugation (𝟙 G)) i)
    [Nonempty (Set.powersetCard (Fin q.dimension) d)]
    (y : cocharacterLattice S)
    (hy : ∀ β : Aubert.General.RationalPointFamily.SimpleRoot i ν,
      0 ≤ Aubert.General.simpleRootPairing i ν β y) :
    letI := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
    entryNorm ((adjointExteriorRepresentation (c.inBasis q.basis) (d := d)).rationalMatrix
      (Aubert.General.uniformizerPowers i (.ofAdd y))⁻¹ :
      Matrix (Set.powersetCard (Fin q.dimension) d) (Set.powersetCard (Fin q.dimension) d) F) ≤
        ∏ j ∈ Finset.univ.filter (fun j => decide (0 < latticePairing S (q.weight j) ν)),
          ‖(Lie.characterValue (q.weight j) (rationalPointEquiv F S.X
            (Plancherel.RenardCartan.uniformizerSection S (.ofAdd y))⁻¹) : F)‖ := by
  classical
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  let t := Plancherel.RenardCartan.uniformizerSection S (.ofAdd y)
  have hroot (j : Fin q.dimension) (hj : q.weight j ≠ 0) : q.weight j ∈ relativeRoots i := by
    refine mem_relativeRoots.mpr ⟨hj, fun h => q.basis.ne_zero j ?_⟩
    have hm := q.mem_weight j
    rwa [AutomorphicAction.lieWeightSpace_conjugation, Category.comp_id, h,
      Submodule.mem_bot] at hm
  have hQ : (1 : ℝ) ≤ LocalField.residueCardinality F := by
    exact_mod_cast (LocalField.residueCardinality_gt_one F).le
  rw [adjointExteriorRepresentation, Plancherel.rationalMatrix_eq_affineMatrix,
    Chevalley.exteriorRepresentation_affineMatrix, ← Plancherel.rationalMatrix_eq_affineMatrix]
  change entryNorm (Chevalley.exteriorGL q.dimension d F
    ((Lie.adjointRepresentation (c.inBasis q.basis)).rationalMatrix
      ((rationalPoints.map i) t)⁻¹)).val ≤ _
  rw [← map_inv (rationalPoints.map i)]
  apply exteriorGL_entryNorm_le _ _ (adjointMatrix_inBasis_diagonal i c q t⁻¹)
  · intro j hj
    have hjpos : 0 < latticePairing S (q.weight j) ν := by simpa using hj
    have hj0 : q.weight j ≠ 0 := by
      intro h
      simp [h] at hjpos
    rw [norm_characterValue_inverseUniformizer]
    exact one_le_zpow₀ hQ (pairing_nonneg_of_dominant hy ⟨hroot j hj0, hjpos⟩)
  · intro j hj
    rw [norm_characterValue_inverseUniformizer]
    apply zpow_le_one_of_nonpos₀ hQ
    by_cases hj0 : q.weight j = 0
    · simp [hj0]
    have hjle : latticePairing S (q.weight j) ν ≤ 0 := by simpa using hj
    have hjlt := lt_of_le_of_ne hjle (hν _ (hroot j hj0))
    have hjneg : -q.weight j ∈ positiveRelativeRoots i ν :=
      ⟨relativeRootNegation F G hG S i hi _ (hroot j hj0), by simpa using neg_pos.mpr hjlt⟩
    have h := pairing_nonneg_of_dominant hy hjneg
    simpa using h

end Chamber

section MinimalModulus

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  {ν : cocharacterLattice S}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

private local instance : NonarchimedeanGroup (rationalPoints G) :=
  Plancherel.rationalPoints_nonarchimedeanGroup G

private theorem rationalMinimalModulus_eq_norm_centralizingDeterminant
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {Z U : GroupScheme (Spec (CommRingCat.of F))} (iZ : Z ⟶ G) {iU : U ⟶ G}
    [IsAffine Z.X.left] [IsAffineHom U.X.hom]
    (hZ : SubgroupFunctor.range iZ ≤ centralizer (CommGroupScheme.groupHom ν ≫ i))
    (hU : (unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy iU)
    {d : ℕ} (cU : Lie.FiniteCoordinates U d) (z : rationalPoints Z)
    (hz : rationalPoints.map iZ z ∈ standardParabolicPoints i ν ∅) :
    letI := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
    ((rationalMinimalModulus i ν ⟨_, hz⟩ : ℝ≥0) : ℝ) =
      ‖(rationalCharacterEval
        ((centralizingUnipotentAction
          (CommGroupScheme.groupHom ν ≫ i) iZ hZ hU).determinantCharacter cU) z : F)‖ := by
  let : T2Space (RationalPoint F G.X) := rationalPoint_t2Space F G
  let χ := CommGroupScheme.groupHom ν ≫ i
  have hUeq : standardUnipotentPoints i ν ∅ = (unipotent χ).rationalPoints :=
    congrArg SubgroupFunctor.rationalPoints (standardUnipotent_empty_eq_dynamic i ν hG hi)
  have hUc := isClosed_standardUnipotentPoints i ν ∅
  have hVc : IsClosed ((unipotent χ).rationalPoints : Set (rationalPoints G)) := hUeq ▸ hUc
  have h := Aubert.General.RationalPointFamily.centralizingUnipotentHaarDeterminant hG
    χ iZ hZ hU cU hVc z
  have htransport : rationalMinimalModulus i ν ⟨_, hz⟩ =
      HaarModulus.closedNormalizerCharacter _ hVc
        (centralizingUnipotentNormalizerHom χ iZ hZ z) :=
    Aubert.General.RationalPointFamily.closedNormalizerCharacter_congr'
      hUeq hUc hVc
      ⟨rationalPoints.map iZ z, standardParabolicPoints_le_normalizer_standardUnipotentPoints
        i ν ∅ hz⟩ (centralizingUnipotentNormalizerHom χ iZ hZ z) rfl
  rw [htransport, h]
  exact coe_distribHaarChar_eq_abs F _

private theorem rationalMinimalModulus_eq_norm_parabolicDeterminant
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {P Z U : GroupScheme (Spec (CommRingCat.of F))} {iP : P ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
    [IsAffine P.X.left] [IsAffine Z.X.left] [IsAffineHom U.X.hom]
    (hP : (parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy iP)
    (hPc : IsClosedSubgroup iP)
    (hZ : (centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy iZ)
    (hU : (unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy iU)
    {d : ℕ} (cU : Lie.FiniteCoordinates U d)
    (x : rationalPoints P) (hx : rationalPoints.map iP x ∈ standardParabolicPoints i ν ∅) :
    letI := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
    ((rationalMinimalModulus i ν ⟨_, hx⟩ : ℝ≥0) : ℝ) =
      ‖(rationalCharacterEval (adjointDeterminantCharacter hP hU cU) x : F)‖ := by
  let χ := CommGroupScheme.groupHom ν ≫ i
  let z := rationalPoints.map (limitGroupHom hP hZ) x
  have hPpts : standardParabolicPoints i ν ∅ = (parabolic χ).rationalPoints :=
    congrArg SubgroupFunctor.rationalPoints (standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν)
  have hz : rationalPoints.map iZ z ∈ standardParabolicPoints i ν ∅ := by
    rw [hPpts]
    exact centralizer_le_parabolic χ _ (hZ.2 ▸ SubgroupFunctor.mem_range.mpr ⟨z, rfl⟩)
  let p : standardParabolicPoints i ν ∅ := ⟨_, hx⟩
  let m : standardParabolicPoints i ν ∅ := ⟨_, hz⟩
  have humem : ((p * m⁻¹ : standardParabolicPoints i ν ∅) : rationalPoints G) ∈
      standardUnipotentPoints i ν ∅ := by
    have hUeq : standardUnipotentPoints i ν ∅ = (unipotent χ).rationalPoints :=
      congrArg SubgroupFunctor.rationalPoints (standardUnipotent_empty_eq_dynamic i ν hG hi)
    rw [hUeq]
    change (x ≫ iP.hom.hom) * ((x ≫ (limitGroupHom hP hZ).hom.hom) ≫ iZ.hom.hom)⁻¹ ∈ _
    rw [limitGroupHom_comp hP hZ]
    exact mul_inv_limit_mem_unipotent χ (hP.pointsEquiv _ x)
  have hmod : rationalMinimalModulus i ν p = rationalMinimalModulus i ν m := by
    have h := rationalMinimalModulus_eq_one_of_mem_standardUnipotent hG hi hν (p * m⁻¹) humem
    simpa only [map_mul, h, one_mul] using
      congrArg (rationalMinimalModulus i ν) (show p = (p * m⁻¹) * m by group)
  have hZr : SubgroupFunctor.range iZ ≤ centralizer χ := hZ.2.le
  let DZ := (centralizingUnipotentAction χ iZ hZr hU).determinantCharacter cU
  have hres : characterRestrict (centralizerToParabolic hP hZ)
      (adjointDeterminantCharacter hP hU cU) = DZ := by
    rw [adjointDeterminantCentralizerRestriction χ hP hZ hU cU]
    simpa only [characterRestrict_id, AddMonoidHom.id_apply] using
      characterRestrict_centralizerAdjointDeterminant_eq_centralizing
        χ iZ hZr hZ hU (𝟙 Z) (Category.id_comp _) cU
  have hdet : adjointDeterminantCharacter hP hU cU =
      characterRestrict (limitGroupHom hP hZ) DZ := by
    simpa only [parabolicCharacterEquiv_apply, parabolicCharacterEquiv_symm_apply, hres] using
      ((parabolicCharacterEquiv hP hPc hZ).symm_apply_apply
        (adjointDeterminantCharacter hP hU cU)).symm
  change ((rationalMinimalModulus i ν p : ℝ≥0) : ℝ) = _
  rw [hmod, hdet, rationalCharacterEval_characterRestrict]
  exact rationalMinimalModulus_eq_norm_centralizingDeterminant hG hi iZ hZr hU cU z hz

end MinimalModulus

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

set_option maxRecDepth 1024 in
/-- On the dominant chamber, the inverse exterior action and the determinant
on the minimal unipotent radical give the Cartan-to-Iwasawa comparison. -/
theorem rationalCartanIwasawaWeightComparison :
    RationalCartanIwasawaWeightComparisonStatement.{u} := by
  classical
  intro F _ _ _ _ G _ _ hG S i hi ν hν K0 hK0c F0 K hKo hKc hPK
  let χ := CommGroupScheme.groupHom ν ≫ i
  let iP := Affine.parabolicHom χ
  let iZ := Affine.centralizerHom χ
  let iU := Affine.unipotentHom χ
  have hP := Affine.isRepresentedBy_parabolicHom χ
  have hZ := Affine.isRepresentedBy_centralizerHom χ
  have hU := Affine.isRepresentedBy_unipotentHom χ
  have hPc := Affine.isClosedSubgroup_parabolicHom χ
  have : IsClosedImmersion iP.hom.hom.left := hPc
  have : IsClosedImmersion iZ.hom.hom.left := Affine.isClosedSubgroup_centralizerHom χ
  have : IsClosedImmersion iU.hom.hom.left := Affine.isClosedSubgroup_unipotentHom χ
  have : IsAffine (Affine.parabolicScheme χ).X.left :=
    isAffine_of_isAffineHom iP.hom.hom.left
  have : IsAffine (Affine.centralizerScheme χ).X.left :=
    isAffine_of_isAffineHom iZ.hom.hom.left
  have : IsAffineHom (Affine.unipotentScheme χ).X.hom := by
    rw [← Over.w iU.hom.hom]
    infer_instance
  have : LocallyOfFiniteType (Affine.unipotentScheme χ).X.hom := by
    rw [← Over.w iU.hom.hom]
    infer_instance
  have : IsAffineHom S.X.hom := hi.isSplitSubtorus.1.isAffineHom
  have : IsAffine S.X.left := isAffine_of_isAffineHom S.X.hom
  let cG := Lie.finiteCoordinates G
  let cU := Lie.finiteCoordinates (Affine.unipotentScheme χ)
  obtain ⟨q, hdet⟩ :=
    exists_homogeneousBasis_unipotent_determinant i hi.isSplitSubtorus.1 ν hU cG cU
  let c := cG.inBasis q.basis
  let τ := adjointExteriorRepresentation c (d := Lie.dimension (Affine.unipotentScheme χ))
  let v := adjointExteriorCoordinates c cU iU (CommAlgCat.of _ F)
  have : Mono iU.hom.hom := hU.1
  have hv : v ≠ 0 :=
    adjointExteriorCoordinates_ne_zero c cU (CommAlgCat.of _ F) (Field.toIsField F)
  let : Nonempty (Set.powersetCard (Fin q.dimension) (Lie.dimension (Affine.unipotentScheme χ))) :=
    not_isEmpty_iff.mp (fun h => hv (funext fun j => h.elim j))
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  let : IsUltrametricDist F :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (LocalField.residueNormalizedAbsoluteValue_add_le_max F)
  let E (g : rationalPoints G) := entryNorm (τ.rationalMatrix g).val
  have hE0 (g : rationalPoints G) : 0 ≤ E g := entryNorm_nonneg _
  have hEmul (g h : rationalPoints G) : E (g * h) ≤ E g * E h := by
    simpa only [E, map_mul, Units.val_mul] using
      entryNorm_mul_le (τ.rationalMatrix g).val (τ.rationalMatrix h).val
  let A := (K : Set (rationalPoints G)) * (K0 : Set (rationalPoints G))⁻¹
  let T := ((↑) : centralizerPoints i → rationalPoints G) '' (F0 : Set (centralizerPoints i))
  let B := ((K0 : Set (rationalPoints G)) * T)⁻¹
  have hAc : IsCompact A := hKc.mul hK0c.inv
  have hTc : IsCompact T := (F0.finite_toSet.image _).isCompact
  have hBc : IsCompact B := (hK0c.mul hTc).inv
  obtain ⟨C, hC, hEC⟩ :=
    τ.exists_rationalMatrixNorm_bound (A ∪ B) (hAc.union hBc)
      ((hAc.union hBc).image continuous_inv)
  have hE (g : rationalPoints G) (hg : g ∈ A ∪ B) : E g ≤ C :=
    (le_max_left _ _).trans (hEC g hg)
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  refine ⟨C, hCpos, fun y hy g hg => ?_⟩
  obtain ⟨k₁, hk₁, k₂, hk₂, f, hf, hcell⟩ := hg
  let p := iwasawaFactor hPK g
  obtain ⟨k, hk, hgpk⟩ := exists_iwasawaFactor hPK g
  let t := Plancherel.RenardCartan.uniformizerSection S (.ofAdd y)
  let a := Aubert.General.uniformizerPowers i (.ofAdd y)
  have hat : rationalPoints.map i t = a := rfl
  have haT : a ∈ Aubert.General.RationalPointFamily.torusPoints i :=
    (Aubert.General.RationalPointFamily.mem_torusPoints i _).mpr ⟨t, hat⟩
  have hcomm : (f : rationalPoints G) * a = a * f :=
    (Aubert.General.RationalPointFamily.centralizerPoints_le_pointCentralizer i
      f.property _ haT).symm
  have hpinv : (p : rationalPoints G)⁻¹ = (k * k₂⁻¹) * a⁻¹ * (k₁ * f)⁻¹ := by
    have hp : (p : rationalPoints G) = ((k₁ * f) * a * k₂) * k⁻¹ := by
      calc
        (p : rationalPoints G) = g * k⁻¹ := by rw [hgpk, mul_inv_cancel_right]
        _ = _ := by rw [hcell, mul_assoc k₁ a, ← hcomm, ← mul_assoc k₁]
    rw [hp]
    group
  have hPpts : standardParabolicPoints i ν ∅ = (parabolic χ).rationalPoints :=
    congrArg SubgroupFunctor.rationalPoints (standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν)
  have haP : a ∈ standardParabolicPoints i ν ∅ := by
    rw [hPpts, ← hat]
    exact centralizer_le_parabolic χ _ (range_le_centralizer_groupHom_comp i ν _
      (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩))
  let ap : standardParabolicPoints i ν ∅ := ⟨a, haP⟩
  let δ (b : standardParabolicPoints i ν ∅) :=
    ((rationalMinimalModulus i ν b : ℝ≥0) : ℝ)
  have hinv (b : standardParabolicPoints i ν ∅) : δ b⁻¹ * δ b = 1 := by
    simp only [δ, ← NNReal.coe_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, NNReal.coe_one]
  have haInv : E a⁻¹ ≤ δ ap⁻¹ := by
    have h := entryNorm_adjointExterior_inverse_uniformizer_le
      (d := Lie.dimension (Affine.unipotentScheme χ)) hG hi hν cG q y hy
    have hta : rationalPoints.map i t⁻¹ = a⁻¹ := by rw [map_inv, hat]
    have htP : rationalPoints.map i t⁻¹ ∈ standardParabolicPoints i ν ∅ := by
      rw [hta]
      exact (standardParabolicPoints i ν ∅).inv_mem haP
    have htEq : (⟨rationalPoints.map i t⁻¹, htP⟩ : standardParabolicPoints i ν ∅) = ap⁻¹ :=
      Subtype.ext hta
    let DT := (centralizingUnipotentAction χ i
      (range_le_centralizer_groupHom_comp i ν) hU).determinantCharacter cU
    have haMod : δ ⟨_, htP⟩ = ‖(rationalCharacterEval DT t⁻¹ : F)‖ :=
      rationalMinimalModulus_eq_norm_centralizingDeterminant hG hi i
        (range_le_centralizer_groupHom_comp i ν) hU cU t⁻¹ htP
    rw [htEq] at haMod
    dsimp only [DT] at haMod
    rw [haMod, hdet, Units.coe_prod, norm_prod]
    exact h
  have hpInv : δ p⁻¹ ≤ E (p : rationalPoints G)⁻¹ := by
    have hpP : (p : rationalPoints G)⁻¹ ∈ (parabolic χ).rationalPoints := by
      rw [← hPpts]
      exact (standardParabolicPoints i ν ∅).inv_mem p.property
    rw [SubgroupFunctor.rationalPoints_eq_range hP] at hpP
    obtain ⟨x, hx⟩ := hpP
    have hxp : rationalPoints.map iP x ∈ standardParabolicPoints i ν ∅ := by
      rw [hx]
      exact (standardParabolicPoints i ν ∅).inv_mem p.property
    let z : F := rationalCharacterEval (adjointDeterminantCharacter hP hU cU) x
    have hδ : δ ⟨_, hxp⟩ = ‖z‖ :=
      rationalMinimalModulus_eq_norm_parabolicDeterminant hG hi hν hP hPc hZ hU cU x hxp
    have hpEq : (⟨rationalPoints.map iP x, hxp⟩ : standardParabolicPoints i ν ∅) = p⁻¹ :=
      Subtype.ext hx
    rw [hpEq] at hδ
    have hact := adjointExteriorCoordinates_rational_action hP hU c cU x
    rw [hx] at hact
    change (τ.rationalMatrix (p : rationalPoints G)⁻¹).val *ᵥ v = z • v at hact
    rw [hδ]
    apply le_of_mul_le_mul_right _ (norm_pos_iff.mpr hv)
    calc
      ‖z‖ * ‖v‖ = ‖z • v‖ := (norm_smul z v).symm
      _ = ‖(τ.rationalMatrix (p : rationalPoints G)⁻¹).val *ᵥ v‖ :=
        congrArg (fun w => ‖w‖) hact.symm
      _ ≤ E (p : rationalPoints G)⁻¹ * ‖v‖ := norm_mulVec_le _ _
  have hleft : E (k * k₂⁻¹) ≤ C :=
    hE _ (Or.inl (Set.mul_mem_mul hk (Set.inv_mem_inv.mpr hk₂)))
  have hright : E (k₁ * f)⁻¹ ≤ C :=
    hE _ (Or.inr (Set.inv_mem_inv.mpr (Set.mul_mem_mul hk₁ ⟨f, hf, rfl⟩)))
  have hbound : δ p⁻¹ ≤ C * δ ap⁻¹ * C := calc
    δ p⁻¹ ≤ E (p : rationalPoints G)⁻¹ := hpInv
    _ ≤ (E (k * k₂⁻¹) * E a⁻¹) * E (k₁ * f)⁻¹ := by
      rw [hpinv]
      exact (hEmul _ _).trans (mul_le_mul_of_nonneg_right (hEmul _ _) (hE0 _))
    _ ≤ C * δ ap⁻¹ * C :=
      mul_le_mul (mul_le_mul hleft haInv (hE0 _) hCpos.le) hright (hE0 _)
        (mul_nonneg hCpos.le (NNReal.coe_nonneg _))
  have hmod : δ ap ≤ C ^ 2 * δ p := calc
    δ ap = (δ p⁻¹ * δ ap) * δ p := by
      rw [mul_comm (δ p⁻¹), mul_assoc, hinv, mul_one]
    _ ≤ ((C * δ ap⁻¹ * C) * δ ap) * δ p :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbound (NNReal.coe_nonneg _))
        (NNReal.coe_nonneg _)
    _ = C ^ 2 * δ p := by
      rw [show C * δ ap⁻¹ * C * δ ap = C ^ 2 * (δ ap⁻¹ * δ ap) by ring, hinv, mul_one]
  have hw := iwasawaWeight_mul (hPK := hPK)
    (fun b hb => rationalMinimalModulus_eq_one i ν hKo hKc b hb) haP K.one_mem
  rw [mul_one] at hw
  change iwasawaWeight hPK (rationalMinimalModulus i ν) a ≤ _
  rw [hw]
  simp only [iwasawaWeight, Real.coe_sqrt]
  change Real.sqrt (δ ap) ≤ C * Real.sqrt (δ p)
  exact (Real.sqrt_le_sqrt hmod).trans_eq (by rw [Real.sqrt_mul (sq_nonneg C),
    Real.sqrt_sq hCpos.le])

end Langlands.HarishChandraSchwartz
