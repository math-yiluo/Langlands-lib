import Langlands.GroupScheme.Reductive.SplitRankZeroIsomorphism
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement
import Langlands.GroupScheme.Dynamic.CentralizerRootsProof
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Reductive.RankOnePositiveRootStatement
import Langlands.GroupScheme.Reductive.SplitRootLieLineStatement
import Langlands.GroupScheme.Rational.PositiveTorusTriangularCoordinatesProof
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.Rational.TorusActionPoints
import Langlands.GroupScheme.Rational.SemigroupOrderedSemidirect
import Langlands.GroupScheme.Rational.RootFiniteness
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Absolute.TripleCell
import Langlands.GroupScheme.Rational.AbsoluteRootRestriction

/-! # Cell data in semisimple rank one

Let `i : T ⟶ G` be a split maximal torus of a connected reductive group in which any two roots
are linearly dependent, let `α` be a root and `ν` a cocharacter with `⟨α, ν⟩ > 0`. Then the
dynamic centralizer of `ν` is `T`, and the dynamic unipotent subgroup of `ν` is a copy of
`𝔾ₐ` on which `T` acts through `α`. The opposite cocharacter gives a copy of `𝔾ₐ` with weight
`-α`. The proofs take the published statements on dynamic centralizers, on uniqueness of the
positive root in rank one and on root lines as explicit hypotheses. See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RankOneCellData

/-! ### Line coordinates on an affine group -/

section LineCoordinates

variable {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom]

/-- Pulling back along the affinization unit is the identification of the global functions of
a spectrum. -/
theorem unit_appTop_eq (U : Over (Spec (CommRingCat.of k)))
    (z : Γ(Spec (CommRingCat.of ((algΓ (CommRingCat.of k)).obj U).unop), ⊤)) :
    ((algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app U).left.appTop z =
      (Scheme.ΓSpecIso (CommRingCat.of ((algΓ (CommRingCat.of k)).obj U).unop)).hom z := by
  have h := Corepresented.unit_appTop_ΓSpecIso_inv U
    ((Scheme.ΓSpecIso (CommRingCat.of ((algΓ (CommRingCat.of k)).obj U).unop)).hom z)
  rw [Iso.hom_inv_id_apply] at h
  exact h

variable [IsAffine H.X.left]

/-- The value at a point of the global function attached to the coordinate `c`. -/
def lineValue (c : CharacterUnits.Coord H) {U : Over (Spec (CommRingCat.of k))}
    (v : U ⟶ H.X) : Γ(U.left, ⊤) :=
  v.left.appTop (CharacterUnits.coordToSections H c)

/-- The value of the global function attached to a coordinate at the pullback of an affine
point along the affinization unit is the coordinate of that affine point. -/
theorem lineValue_unit_comp (U : Over (Spec (CommRingCat.of k)))
    (x : Lie.AffinePoints H ((algΓ (CommRingCat.of k)).obj U).unop)
    (c : CharacterUnits.Coord H) :
    lineValue c ((algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app U ≫ x) =
      Lie.pointCoordinates H x c := by
  change ((algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app U).left.appTop
      (x.left.appTop (CharacterUnits.coordToSections H c)) = _
  exact (unit_appTop_eq U _).trans
    (CharacterUnits.affinePointEvaluation_coordToSections' H _ x c)

theorem lineValue_eq (c : CharacterUnits.Coord H) {U : Over (Spec (CommRingCat.of k))}
    (v : U ⟶ H.X) :
    lineValue c v = Lie.pointCoordinates H (A := ((algΓ (CommRingCat.of k)).obj U).unop)
      (Lie.affinizationFactor H v) c := by
  have h := lineValue_unit_comp U (Lie.affinizationFactor H v) c
  rwa [Lie.unit_affinizationFactor] at h

variable {c : CharacterUnits.Coord H}

/-- An additive coordinate on affine points is additive on all points. -/
theorem lineValue_mul
    (hadd : ∀ (B : Type u) [CommRing B] [Algebra k B] (x y : Lie.AffinePoints H B),
      Lie.pointCoordinates H (x * y) c =
        Lie.pointCoordinates H x c + Lie.pointCoordinates H y c)
    {U : Over (Spec (CommRingCat.of k))} (v w : U ⟶ H.X) :
    lineValue c (v * w) = lineValue c v + lineValue c w := by
  have hvw : v * w = (algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app U ≫
      (Lie.affinizationFactor H v * Lie.affinizationFactor H w) := by
    rw [MonObj.comp_mul, Lie.unit_affinizationFactor, Lie.unit_affinizationFactor]
  rw [hvw, lineValue_unit_comp, hadd, lineValue_eq, lineValue_eq]
  rfl

/-- A coordinate that generates the coordinate algebra freely gives a bijection from the points
over every test scheme to its global functions. -/
theorem lineValue_bijective
    (hc : Function.Bijective
      (aeval (fun _ : Fin 1 => c) : MvPolynomial (Fin 1) k →ₐ[k] CharacterUnits.Coord H))
    (U : Over (Spec (CommRingCat.of k))) :
    Function.Bijective (fun v : U ⟶ H.X => lineValue c v) := by
  constructor
  · intro v w hvw
    simp only [lineValue_eq] at hvw
    have h1 : (Lie.pointCoordinates H (A := ((algΓ (CommRingCat.of k)).obj U).unop)
          (Lie.affinizationFactor H v)).comp (aeval fun _ : Fin 1 => c) =
        (Lie.pointCoordinates H (A := ((algΓ (CommRingCat.of k)).obj U).unop)
          (Lie.affinizationFactor H w)).comp (aeval fun _ : Fin 1 => c) := by
      apply MvPolynomial.algHom_ext
      intro j
      simp only [AlgHom.comp_apply, aeval_X]
      exact hvw
    have h2 : Lie.pointCoordinates H (A := ((algΓ (CommRingCat.of k)).obj U).unop)
          (Lie.affinizationFactor H v) =
        Lie.pointCoordinates H (A := ((algΓ (CommRingCat.of k)).obj U).unop)
          (Lie.affinizationFactor H w) := by
      ext f
      obtain ⟨p, rfl⟩ := hc.2 f
      exact DFunLike.congr_fun h1 p
    have h3 := (Lie.pointCoordinates H).injective h2
    calc v = (algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app U ≫
          Lie.affinizationFactor H v := (Lie.unit_affinizationFactor H v).symm
      _ = (algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app U ≫
          Lie.affinizationFactor H w := by rw [h3]
      _ = w := Lie.unit_affinizationFactor H w
  · intro a
    let e := AlgEquiv.ofBijective _ hc
    let a' : ((algΓ (CommRingCat.of k)).obj U).unop := a
    let φ : CharacterUnits.Coord H →ₐ[k] ((algΓ (CommRingCat.of k)).obj U).unop :=
      (aeval fun _ : Fin 1 => a').comp e.symm.toAlgHom
    refine ⟨(algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app U ≫
      (Lie.pointCoordinates H (A := ((algΓ (CommRingCat.of k)).obj U).unop)).symm φ, ?_⟩
    have he : e.symm c = X 0 := by
      rw [AlgEquiv.symm_apply_eq]
      simp [e]
    change lineValue c _ = a
    rw [lineValue_unit_comp, Equiv.apply_symm_apply]
    change (aeval fun _ : Fin 1 => a') (e.symm c) = a
    rw [he, aeval_X]

/-- The coordinate system of a group whose coordinate algebra is a polynomial algebra on one
additive coordinate. -/
def lineCoordinates
    (hc : Function.Bijective
      (aeval (fun _ : Fin 1 => c) : MvPolynomial (Fin 1) k →ₐ[k] CharacterUnits.Coord H))
    (hadd : ∀ (B : Type u) [CommRing B] [Algebra k B] (x y : Lie.AffinePoints H B),
      Lie.pointCoordinates H (x * y) c =
        Lie.pointCoordinates H x c + Lie.pointCoordinates H y c)
    (U : Over (Spec (CommRingCat.of k))) :
    (U ⟶ H.X) ≃* Multiplicative (Fin 1 → Γ(U.left, ⊤)) :=
  MulEquiv.ofBijective
    (MonoidHom.mk' (fun v => Multiplicative.ofAdd fun _ => lineValue c v) fun v w => by
      apply Multiplicative.toAdd.injective
      funext j
      exact lineValue_mul hadd v w)
    (by
      constructor
      · intro v w hvw
        apply (lineValue_bijective hc U).1
        exact congrFun (congrArg Multiplicative.toAdd hvw) 0
      · intro m
        obtain ⟨v, hv⟩ := (lineValue_bijective hc U).2 (m.toAdd 0)
        refine ⟨v, ?_⟩
        apply Multiplicative.toAdd.injective
        funext j
        rw [Subsingleton.elim j 0]
        exact hv)

variable (hc : Function.Bijective
      (aeval (fun _ : Fin 1 => c) : MvPolynomial (Fin 1) k →ₐ[k] CharacterUnits.Coord H))
    (hadd : ∀ (B : Type u) [CommRing B] [Algebra k B] (x y : Lie.AffinePoints H B),
      Lie.pointCoordinates H (x * y) c =
        Lie.pointCoordinates H x c + Lie.pointCoordinates H y c)

theorem lineCoordinates_apply {U : Over (Spec (CommRingCat.of k))} (v : U ⟶ H.X) (j : Fin 1) :
    (lineCoordinates hc hadd U v).toAdd j = lineValue c v :=
  rfl

/-- The line coordinates are natural in the test scheme. -/
theorem isNaturalVectorCoordinates_lineCoordinates :
    RelativeRoot.IsNaturalVectorCoordinates (lineCoordinates hc hadd) :=
  fun _ _ _ _ => rfl

omit [IsAffine H.X.left] in
/-- Through the affinization unit, the value of a character at a torus point over a test
scheme is its value at the affinized point. -/
theorem pointsEquiv_unit_comp {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (χ : characterLattice S) (U : Over (Spec (CommRingCat.of k)))
    (s : Lie.AffinePoints S.toGrp ((algΓ (CommRingCat.of k)).obj U).unop) :
    (Gm.pointsEquiv _ U ((algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app U ≫ s ≫
        (CommGroupScheme.groupHom χ).hom.hom) : Γ(U.left, ⊤)) =
      (Lie.characterValue χ s : ((algΓ (CommRingCat.of k)).obj U).unop) := by
  rw [Gm.pointsEquiv_naturality, Units.coe_map]
  exact unit_appTop_eq U _

/-- A `χ`-eigenfunction gives line coordinates on which the torus acts through `χ` over every
test scheme. -/
theorem lineValue_act {S : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffineHom S.X.hom]
    (b : AutomorphicAction S.toGrp H) (χ : characterLattice S)
    (hcχ : c ∈ CoordinateWeights.weightSpace b χ) {U : Over (Spec (CommRingCat.of k))}
    (s : U ⟶ S.X) (v : U ⟶ H.X) :
    lineValue c (b.act s v) =
      (Gm.pointsEquiv _ U (s ≫ (CommGroupScheme.groupHom χ).hom.hom) : Γ(U.left, ⊤)) *
        lineValue c v := by
  have hs := Lie.unit_affinizationFactor S.toGrp s
  have hv := Lie.unit_affinizationFactor H v
  have hact : b.act s v = (algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app U ≫
      b.act (Lie.affinizationFactor S.toGrp s) (Lie.affinizationFactor H v) := by
    rw [b.naturality, hs, hv]
  have hcχ' : CoordinateWeights.IsEigenfunction b χ c := hcχ
  rw [hact, lineValue_unit_comp, hcχ', lineValue_eq]
  congr 1
  conv_rhs => rw [← hs, Category.assoc]
  exact (pointsEquiv_unit_comp χ U _).symm

/-- The line coordinates are weight coordinates for the action. -/
theorem isWeightVectorCoordinates_lineCoordinates
    {S : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffineHom S.X.hom]
    (b : AutomorphicAction S.toGrp H) (χ : characterLattice S)
    (hcχ : c ∈ CoordinateWeights.weightSpace b χ) :
    RelativeRoot.IsWeightVectorCoordinates b χ (lineCoordinates hc hadd) := by
  refine ⟨isNaturalVectorCoordinates_lineCoordinates hc hadd, fun U s v => ?_⟩
  funext j
  exact lineValue_act b χ hcχ s v

end LineCoordinates

end RankOneCellData

open RankOneCellData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-! ### The centralizer -/

/-- In semisimple rank one, a cocharacter pairing nonzero with a root pairs nonzero with
every root. -/
theorem latticePairing_ne_zero_of_rankOne (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hrank : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    {α : characterLattice T} (hα : haveI := hG.isAffineHom; α ∈ roots i)
    {ν : cocharacterLattice T} (hν : latticePairing T α ν ≠ 0)
    {β : characterLattice T} (hβ : haveI := hG.isAffineHom; β ∈ roots i) :
    latticePairing T β ν ≠ 0 := by
  have := hG.isAffineHom
  intro hβν
  have hdep := hrank α hα β hβ
  rw [LinearIndependent.pair_iff] at hdep
  push Not at hdep
  obtain ⟨s, t, hst, hne⟩ := hdep
  have hpair := congrArg (fun δ => latticePairing T δ ν) hst
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, hβν, mul_zero,
    add_zero, map_zero, LinearMap.zero_apply, smul_eq_mul] at hpair
  have hs : s = 0 := (mul_eq_zero.mp hpair).resolve_right hν
  have ht : t ≠ 0 := hne hs
  rw [hs, zero_smul, zero_add] at hst
  apply hβ.1
  apply hT.character_toRat_injective
  have h1 := congrArg LinearAlgebra.RationalSpan.toRat hst
  rw [map_zsmul, map_zero, ← Int.cast_smul_eq_zsmul ℚ, smul_eq_zero] at h1
  rw [map_zero]
  exact h1.resolve_left (Int.cast_ne_zero.mpr ht)

/-- **The centralizer in semisimple rank one.** If `⟨α, ν⟩ ≠ 0` for a root `α`, the dynamic
centralizer of `ν` is represented by the maximal torus. -/
theorem rankOne_centralizer_isRepresentedBy (hDCR : DynamicCentralizerReductiveStatement.{u})
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i)
    (hrank : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (α : characterLattice T) (hα : haveI := hG.isAffineHom; α ∈ roots i)
    (ν : cocharacterLattice T) (hν : latticePairing T α ν ≠ 0) :
    (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy i := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ := CommGroupScheme.groupHom ν ≫ i
  let z := Dynamic.Affine.centralizerHom χ
  have hz : IsClosedSubgroup z := Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  have hrep : (Dynamic.centralizer χ).IsRepresentedBy z :=
    Dynamic.Affine.isRepresentedBy_centralizerHom χ
  let t := hrep.liftOfLE i (range_le_centralizer_groupHom_comp i ν)
  have htz : t ≫ z = i := hrep.liftOfLE_comp i _
  have hZ : IsConnectedReductive (Dynamic.Affine.centralizerScheme χ) :=
    hDCR k G hG χ _ z hz hrep
  have hit : IsMaximalTorus t := IsMaximalTorus.of_comp hz (htz.symm ▸ hi)
  have hroots := dynamicCentralizerRoots k G hG T hT i hi ν _ z hz hrep hZ t htz
  have hempty : (haveI := hZ.isAffineHom; roots t) = ∅ := by
    rw [hroots]
    ext β
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun hβ => latticePairing_ne_zero_of_rankOne hG hT i hrank hα hν hβ
  have : IsIso t := hZ.isIso_of_roots_eq_empty hT hit hempty
  have h := hrep.precomp_iso (asIso t)
  rwa [asIso_hom, htz] at h

/-! ### The root groups -/

/-- **The positive root group in semisimple rank one.** If `⟨α, ν⟩ > 0` for a root `α`, the
dynamic unipotent subgroup of `ν` is represented by a homomorphism `x : 𝔾ₐ ⟶ G` on which `T`
acts by conjugation through `α`. -/
theorem rankOne_exists_rootGroup (hPRU : RankOnePositiveRootUniquenessStatement.{u})
    (hLL : SplitRootLieLineStatement.{u})
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i)
    (hrank : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (α : characterLattice T) (hα : haveI := hG.isAffineHom; α ∈ roots i)
    (ν : cocharacterLattice T) (hν : 0 < latticePairing T α ν) :
    ∃ x : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G,
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy x ∧
      ∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ T.X)
        (a : U ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
        (t ≫ i.hom.hom) * (a ≫ x.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
          VectorGroup.weightPointAction α U t a ≫ x.hom.hom := by
  have := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom T.X.hom := hi.2.1.isAffineHom
  let N := Standard.unipotentScheme i ν ∅
  let incl := Standard.unipotentHom i ν ∅
  have : IsAffine N.X.left := isAffine_of_isAffineHom N.X.hom
  have : Smooth N.X.hom := Standard.smooth_unipotentScheme_empty i ν hT
  let b := Standard.unipotentAction i ν hT
  obtain ⟨d, w, t, ht, htw, hε, hw, hmono⟩ :=
    TorusUnipotence.exists_positiveWeight_coordinates hT b ν
      (fun χ hχ => Standard.pairing_pos_of_mem_support i ν hT hχ)
  obtain ⟨P, hP, hmul⟩ := TorusUnipotence.exists_triangular_mul hT b ν ht htw hε hw hmono
  -- Every weight of the coordinates is `α`.
  have hwα : ∀ j, w j = α := by
    intro j
    have hj : w j ∈ positiveRelativeRoots i ν := by
      refine (Standard.actionWeightSpace_unipotentAction_ne_bot_iff i ν hT (w j)).mp
        fun hbot => ?_
      have h := TorusUnipotence.finrank_actionWeightSpace hT b ht htw hε (w j)
      rw [hbot, finrank_bot] at h
      have : Nonempty {j' // w j' = w j} := ⟨⟨j, rfl⟩⟩
      have : 0 < Nat.card {j' // w j' = w j} := Nat.card_pos
      omega
    exact hPRU k G hG T hT i hi hrank ν (w j) hj.1 α hα hj.2 hν
  -- There is exactly one coordinate.
  have hd : d = 1 := by
    have h1 := TorusUnipotence.finrank_actionWeightSpace hT b ht htw hε α
    rw [Standard.finrank_actionWeightSpace_unipotentAction i ν hT ⟨hα, hν⟩] at h1
    obtain ⟨eα⟩ := hLL k G hG T hT i hi α hα
    rw [← eα.finrank_eq, Module.finrank_self] at h1
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hwα), Nat.card_eq_fintype_card,
      Fintype.card_fin] at h1
    exact h1.symm
  subst hd
  -- The single coordinate is additive.
  have hP0 : ∀ (B : Type u) [CommRing B] [Algebra k B] (f : Fin 1 ⊕ Fin 1 → B),
      aeval f (P 0) = algebraMap k B (constantCoeff (P 0)) := by
    intro B _ _ f
    apply MvPolynomial.aeval_eq_constantCoeff_of_vars
    intro v hv
    exact absurd (hP 0 v hv) (Fin.not_lt_zero _)
  have h0 : Lie.coordinateOrigin (Standard.unipotentScheme i ν ∅) (t 0) = 0 := hε 0
  have hcc : constantCoeff (P 0) = 0 := by
    have h := hmul k 1 1 0
    rw [mul_one, hP0, Lie.pointCoordinates_one] at h
    simpa [h0] using h.symm
  have hadd : ∀ (B : Type u) [CommRing B] [Algebra k B] (x y : Lie.AffinePoints N B),
      Lie.pointCoordinates N (x * y) (t 0) =
        Lie.pointCoordinates N x (t 0) + Lie.pointCoordinates N y (t 0) := by
    intro B _ _ x y
    rw [hmul B x y 0, hP0, hcc, map_zero, add_zero]
  have hc : Function.Bijective
      (aeval (fun _ : Fin 1 => t 0) : MvPolynomial (Fin 1) k →ₐ[k] CharacterUnits.Coord N) := by
    have ht' : t = fun _ => t 0 := funext fun j => by rw [Subsingleton.elim j 0]
    rwa [ht'] at ht
  have hcα : t 0 ∈ CoordinateWeights.weightSpace b α := hwα 0 ▸ htw 0
  -- The vector group.
  let e := lineCoordinates hc hadd
  have he : RelativeRoot.IsNaturalVectorCoordinates e :=
    isNaturalVectorCoordinates_lineCoordinates hc hadd
  let Φ := RelativeRoot.vectorGroupIso e he
  have ehi : Φ.inv.hom.hom ≫ Φ.hom.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) Φ.inv_hom_id
  have ehi' : Φ.hom.hom.hom ≫ Φ.inv.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) Φ.hom_inv_id
  refine ⟨Φ.inv ≫ incl, (Standard.isRepresentedBy_unipotentHom_empty i ν hT).precomp_iso Φ.symm,
    fun U s a => ?_⟩
  let n : U ⟶ N.X := a ≫ Φ.inv.hom.hom
  have hna : n ≫ Φ.hom.hom.hom = a := by
    change (a ≫ Φ.inv.hom.hom) ≫ Φ.hom.hom.hom = a
    rw [Category.assoc, ehi, Category.comp_id]
  have key : b.act s n ≫ Φ.hom.hom.hom = VectorGroup.weightPointAction α U s a := by
    apply VectorGroup.points_ext
    intro j
    rw [RelativeRoot.coordinates_comp_vectorGroupIso_hom,
      VectorGroup.coordinates_weightPointAction, ← hna,
      RelativeRoot.coordinates_comp_vectorGroupIso_hom]
    exact lineValue_act b α hcα s n
  have hact : b.act s n = VectorGroup.weightPointAction α U s a ≫ Φ.inv.hom.hom := by
    rw [← key, Category.assoc, ehi', Category.comp_id]
  have hcomp : ∀ y : U ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X,
      y ≫ (Φ.inv ≫ incl).hom.hom = (y ≫ Φ.inv.hom.hom) ≫ incl.hom.hom := fun y => by
    rw [Grp.comp_hom_hom, Category.assoc]
  rw [hcomp, hcomp, ← hact]
  exact (Standard.unipotentAction_act_comp i ν hT s n).symm

/-- **The opposite root group in semisimple rank one.** If `⟨α, ν⟩ > 0` for a root `α` whose
negative is a root, the dynamic unipotent subgroup of the opposite of `ν` is represented by a
homomorphism `x' : 𝔾ₐ ⟶ G` on which `T` acts by conjugation through `-α`. -/
theorem rankOne_exists_oppositeRootGroup (hPRU : RankOnePositiveRootUniquenessStatement.{u})
    (hLL : SplitRootLieLineStatement.{u})
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i)
    (hrank : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (α : characterLattice T) (hα' : haveI := hG.isAffineHom; -α ∈ roots i)
    (ν : cocharacterLattice T) (hν : 0 < latticePairing T α ν) :
    ∃ x' : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G,
      (Dynamic.unipotent (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy x' ∧
      ∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ T.X)
        (a : U ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
        (t ≫ i.hom.hom) * (a ≫ x'.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
          VectorGroup.weightPointAction (-α) U t a ≫ x'.hom.hom := by
  have hν' : 0 < latticePairing T (-α) (-ν) := by simpa using hν
  have hχ : CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
      CommGroupScheme.groupHom ν ≫ i = CommGroupScheme.groupHom (-ν) ≫ i := by
    have hneg : Gm.powerHom (Spec (CommRingCat.of k)) (-1) ≫ ν = -ν := by
      simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
    rw [← Category.assoc]
    change CommGroupScheme.groupHom (Gm.powerHom _ (-1) ≫ ν) ≫ i = _
    rw [hneg]
  rw [hχ]
  exact rankOne_exists_rootGroup hPRU hLL hG hT i hi hrank (-α) hα' (-ν) hν'

/-- **Cell data in semisimple rank one.** For a root `α` and a cocharacter `ν` with
`⟨α, ν⟩ > 0`, the maximal torus represents the dynamic centralizer of `ν`, and the dynamic
unipotent subgroup of `ν` is represented by a homomorphism `x : 𝔾ₐ ⟶ G` on which `T` acts by
conjugation through `α`. -/
theorem rankOneCellData (hDCR : DynamicCentralizerReductiveStatement.{u})
    (hPRU : RankOnePositiveRootUniquenessStatement.{u}) (hLL : SplitRootLieLineStatement.{u})
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i)
    (hrank : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (α : characterLattice T) (hα : haveI := hG.isAffineHom; α ∈ roots i)
    (ν : cocharacterLattice T) (hν : 0 < latticePairing T α ν) :
    (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy i ∧
      ∃ x : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G,
        (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy x ∧
        ∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ T.X)
          (a : U ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
          (t ≫ i.hom.hom) * (a ≫ x.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
            VectorGroup.weightPointAction α U t a ≫ x.hom.hom :=
  ⟨rankOne_centralizer_isRepresentedBy hDCR hG hT i hi hrank α hα ν hν.ne',
    rankOne_exists_rootGroup hPRU hLL hG hT i hi hrank α hα ν hν⟩

/-! ### The open cell -/

/-- **The open cell in semisimple rank one.** If `α` and `-α` are roots and `⟨α, ν⟩ > 0`, there
are homomorphisms `xp xm : 𝔾ₐ ⟶ G` representing the dynamic unipotent subgroups of `ν` and of
its opposite, on which `T` acts by conjugation through `α` and `-α`, such that the
multiplication `(Y, t, X) ↦ xm(Y) t xp(X)` is an open immersion. -/
theorem rankOne_exists_cell (hDCR : DynamicCentralizerReductiveStatement.{u})
    (hPRU : RankOnePositiveRootUniquenessStatement.{u}) (hLL : SplitRootLieLineStatement.{u})
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i)
    (hrank : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (α : characterLattice T) (hα : haveI := hG.isAffineHom; α ∈ roots i)
    (hα' : haveI := hG.isAffineHom; -α ∈ roots i)
    (ν : cocharacterLattice T) (hν : 0 < latticePairing T α ν) :
    ∃ xp xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G,
      (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy i ∧
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy xp ∧
      (Dynamic.unipotent (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy xm ∧
      (∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ T.X)
          (a : U ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
        (t ≫ i.hom.hom) * (a ≫ xp.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
          VectorGroup.weightPointAction α U t a ≫ xp.hom.hom) ∧
      (∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ T.X)
          (b : U ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
        (t ≫ i.hom.hom) * (b ≫ xm.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
          VectorGroup.weightPointAction (-α) U t b ≫ xm.hom.hom) ∧
      IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left := by
  have := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have hZ := rankOne_centralizer_isRepresentedBy hDCR hG hT i hi hrank α hα ν hν.ne'
  obtain ⟨xp, hxp, hxpc⟩ := rankOne_exists_rootGroup hPRU hLL hG hT i hi hrank α hα ν hν
  obtain ⟨xm, hxm, hxmc⟩ :=
    rankOne_exists_oppositeRootGroup hPRU hLL hG hT i hi hrank α hα' ν hν
  exact ⟨xp, xm, hZ, hxp, hxm, hxpc, hxmc,
    Dynamic.isOpenImmersion_tripleCellMultiplication _ hxm hZ hxp⟩

/-- **The open cell of a root in semisimple rank one.** For a root datum `P` of `i` and an index
`r`, the cell data of `rankOne_exists_cell` exist for the root `P.root r` and its coroot. -/
theorem rankOne_exists_rootCell (hDCR : DynamicCentralizerReductiveStatement.{u})
    (hPRU : RankOnePositiveRootUniquenessStatement.{u}) (hLL : SplitRootLieLineStatement.{u})
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) {J : Type*}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hrank : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (r : J) :
    ∃ xp xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G,
      (Dynamic.centralizer (CommGroupScheme.groupHom (P.coroot r) ≫ i)).IsRepresentedBy i ∧
      (Dynamic.unipotent (CommGroupScheme.groupHom (P.coroot r) ≫ i)).IsRepresentedBy xp ∧
      (Dynamic.unipotent (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        CommGroupScheme.groupHom (P.coroot r) ≫ i)).IsRepresentedBy xm ∧
      (∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ T.X)
          (a : U ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
        (t ≫ i.hom.hom) * (a ≫ xp.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
          VectorGroup.weightPointAction (P.root r) U t a ≫ xp.hom.hom) ∧
      (∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ T.X)
          (b : U ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
        (t ≫ i.hom.hom) * (b ≫ xm.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
          VectorGroup.weightPointAction (-P.root r) U t b ≫ xm.hom.hom) ∧
      IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left := by
  have := hG.isAffineHom
  have hα : P.root r ∈ roots i := hP.2.1 ▸ Set.mem_range_self r
  have hν : 0 < latticePairing T (P.root r) (P.coroot r) := by
    rw [← hP.1, P.root_coroot_two r]
    norm_num
  exact rankOne_exists_cell hDCR hPRU hLL hG hT i hi hrank (P.root r) hα
    (hP.neg_mem_roots hα) (P.coroot r) hν

end Langlands.GroupScheme
