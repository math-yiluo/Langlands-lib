import Langlands.GroupScheme.MatrixRepresentation.TorusEigenlineDiagonalization
import Langlands.GroupScheme.MatrixRepresentation.ParabolicEigenlineWeights
import Langlands.Representation.Plancherel.RationalMatrixNormComparison
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof

/-! # Strict orbit weights of an actual parabolic eigenline -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Matrix
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G U P : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The universal diagonal-character equation gives the same diagonal on
the actual identity-test rational points. -/
theorem HasTorusCharacterDiagonal.rationalMatrix_eq_diagonal
    {ρ : MatrixRepresentation G n} {i : T.toGrp ⟶ G}
    {χ : n → rationalCharacters T.toGrp}
    (h : HasTorusCharacterDiagonal ρ i χ) (a : rationalPoints T.toGrp) :
    (ρ.rationalMatrix (rationalPoints.map i a) : Matrix n n k) =
      Matrix.diagonal (fun j => (rationalCharacterEval (χ j) a : k)) := by
  rw [Langlands.Plancherel.rationalMatrix_eq_affineMatrix]
  have hm : rationalPointEquiv k G.X (rationalPoints.map i a) =
      rationalPointEquiv k T.X a ≫ i.hom.hom := by
    apply RingPoint.ext
    change (rationalPointEquiv k G.X (rationalPoints.map i a)).left =
      (rationalPointEquiv k T.X a).left ≫ i.hom.hom.left
    rw [rationalPointEquiv_left, rationalPointEquiv_left]
    rfl
  rw [hm, h (CommAlgCat.of k k) (rationalPointEquiv k T.X a)]
  apply congrArg Matrix.diagonal
  funext j
  exact congrArg Units.val (rationalCharacterEval_eq_affineUnitsEquiv T.toGrp (χ j) a).symm

/-- Every active orbit coordinate other than the original line has strictly
smaller cocharacter weight. Inactive equal or larger coordinates vanish
on every scheme test. -/
def HasStrictOrbitWeightUpperBound (ρ : MatrixRepresentation G n) (e : n → ℤ)
    (j : n) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of k))) (g : Z ⟶ G.X) (a : n),
    a ≠ j → e j ≤ e a → (ρ.pointMatrix Z g : Matrix n n Γ(Z.left, ⊤)) a j = 0

variable (ρ : MatrixRepresentation G n)
  (χc : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (e : n → ℤ)
  (hχc : χc ≫ ρ = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)
  (iU : U ⟶ G) (iP : P ⟶ G)
  (hU : (Dynamic.unipotent (Dynamic.oppositeCocharacter χc)).IsRepresentedBy iU)
  (hP : (Dynamic.parabolic χc).IsRepresentedBy iP)

include hχc hU in
private theorem oppositeCell_entry_eq_zero_of_weight_ge (j : n)
    (hline : (ρ.restrict iP).PreservesCoordinateLine j)
    {a : n} (hne : a ≠ j) (ha : e j ≤ e a) :
    (ρ.pointMatrix (U.X ⊗ P.X)
      ((fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom)) :
        Matrix n n Γ((U.X ⊗ P.X).left, ⊤)) a j = 0 := by
  let Z := U.X ⊗ P.X
  let u : Z ⟶ G.X := fst U.X P.X ≫ iU.hom.hom
  let p : Z ⟶ G.X := snd U.X P.X ≫ iP.hom.hom
  have hu : u ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χc)).carrier Z :=
    (hU.pointsEquiv Z (fst U.X P.X)).property
  obtain ⟨c, hc⟩ := hline Z (snd U.X P.X)
  rw [pointMatrix_restrict] at hc
  have huz := ρ.pointMatrix_entry_eq_one_of_mem_opposite_unipotent χc e hχc hu ha
  rw [Matrix.one_apply_ne hne] at huz
  have hact := congrFun (congrArg
    (fun v : n → Γ(Z.left, ⊤) => (ρ.pointMatrix Z u : Matrix n n Γ(Z.left, ⊤)) *ᵥ v) hc) a
  simp only [Matrix.mulVec_smul, Matrix.mulVec_single_one, Matrix.col_apply,
    Pi.smul_apply, smul_eq_mul, huz, mul_zero] at hact
  change (ρ.pointMatrix Z (u * p) : Matrix n n Γ(Z.left, ⊤)) a j = 0
  rw [map_mul, Units.val_mul, Matrix.mul_apply]
  simpa only [Matrix.mulVec, dotProduct, Matrix.col_apply, p] using hact

include hχc hU hP in
/-- Density of the actual opposite open cell proves strict orbit weights,
including the vanishing of all other coordinates of the top weight. -/
theorem hasStrictOrbitWeightUpperBound_of_parabolic_eigenline
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (j : n) (hline : (ρ.restrict iP).PreservesCoordinateLine j) :
    ρ.HasStrictOrbitWeightUpperBound e j := by
  have hgeom : GeometricallyIntegral G.X.hom :=
    smoothConnectedAffineGeometry.1 k G inferInstance inferInstance inferInstance
  have : IsIntegral G.X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton G.X.hom
  let c : U.X ⊗ P.X ⟶ G.X :=
    (fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom)
  have hc : IsOpenImmersion c.left := oppositeCellStatement k G χc U P iU iP hU hP
  have hne : (Set.range c.left).Nonempty := by
    let z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X ⊗ P.X := lift 1 1
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
    exact ⟨c.left (z.left x), ⟨z.left x, rfl⟩⟩
  have : IsDominant c.left := ⟨c.left.isOpenEmbedding.isOpen_range.dense hne⟩
  intro Z g a haj ha
  let f : G.X ⟶ coefficientSpace Unit (CommRingCat.of k) :=
    coefficientPoint G.X (fun _ =>
      (ρ.pointMatrix G.X (𝟙 _) : Matrix n n Γ(G.X.left, ⊤)) a j)
  let z : G.X ⟶ coefficientSpace Unit (CommRingCat.of k) := coefficientPoint G.X 0
  have he : f = z := by
    apply Over.OverMorphism.ext
    apply ext_of_isDominant_of_isSeparated (coefficientSpace Unit (CommRingCat.of k)).hom
      ((Over.w f).trans (Over.w z).symm) c.left
    change (c ≫ f).left = (c ≫ z).left
    congr 1
    apply coefficientCoordinates_injective
    ext b
    have hm := ρ.pointMatrix_naturality c (𝟙 G.X)
    have hz := ρ.oppositeCell_entry_eq_zero_of_weight_ge χc e hχc iU iP hU j hline haj ha
    simpa only [f, z, coefficientCoordinates_comp, coefficientCoordinates_coefficientPoint,
      Category.comp_id, Pi.zero_apply, map_zero, Matrix.GeneralLinearGroup.map_apply,
      Matrix.map_apply] using (congrArg (fun M : GL n Γ((U.X ⊗ P.X).left, ⊤) =>
        (M : Matrix n n Γ((U.X ⊗ P.X).left, ⊤)) a j) hm).symm.trans hz
  have hz := congrArg (fun q => coefficientCoordinates q ()) he
  simp only [f, z, coefficientCoordinates_coefficientPoint, Pi.zero_apply] at hz
  have hm := ρ.pointMatrix_naturality g (𝟙 G.X)
  have heval := congrArg (fun M : GL n Γ(Z.left, ⊤) => (M : Matrix n n Γ(Z.left, ⊤)) a j) hm
  simpa only [Category.comp_id, Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply,
    hz, map_zero] using heval

section Relative

variable [IsAffineHom G.X.hom]

/-- Active coordinates of a minimal-parabolic eigenline have nonnegative
weight difference on the whole closed cocharacter chamber. Boundary
directions are obtained through all integral interior translates. -/
theorem orbitPairing_nonneg_of_simpleRootPairings_nonneg
    (i : T.toGrp ⟶ G) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    {characters : n → rationalCharacters T.toGrp}
    (hdiag : ρ.HasTorusCharacterDiagonal i characters)
    (j : n) (hline : (ρ.restrict (Standard.parabolicHom i ν ∅)).PreservesCoordinateLine j)
    (Z : Over (Spec (CommRingCat.of k))) (g : Z ⟶ G.X) (r : n)
    (hactive : (ρ.pointMatrix Z g : Matrix n n Γ(Z.left, ⊤)) r j ≠ 0)
    (d : cocharacterLattice T)
    (hd : ∀ β ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing T β d) :
    0 ≤ latticePairing T
      ((rationalCharacters.equivCharacterLattice T) (characters j) -
        (rationalCharacters.equivCharacterLattice T) (characters r)) d := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hi.isSplitSubtorus.mono
  let delta := (rationalCharacters.equivCharacterLattice T) (characters j) -
    (rationalCharacters.equivCharacterLattice T) (characters r)
  have htest : ∀ N : ℕ, 0 ≤ latticePairing T delta (N • d + ν) := by
    intro N
    let v := N • d + ν
    have hv : IsStandardCocharacter i ν ∅ v := by
      refine ⟨Set.empty_subset _, by simp, ?_⟩
      intro β hβ _
      dsimp only [v]
      rw [map_add, map_nsmul, nsmul_eq_mul]
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (Int.natCast_nonneg N) (hd β hβ)) hβ.1.2
    let cv := CommGroupScheme.groupHom v ≫ i
    let ev : n → ℤ := fun a =>
      latticePairing T ((rationalCharacters.equivCharacterLattice T) (characters a)) v
    have hcv : cv ≫ ρ = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) ev :=
      (Category.assoc _ _ _).trans (hdiag.cocharacter v)
    have hp : (Dynamic.parabolic cv).IsRepresentedBy (Standard.parabolicHom i ν ∅) := by
      rw [← ((standardCocharacter k G hG T i hi ν hν ∅ (Set.empty_subset _)).2 v hv).1]
      exact Standard.isRepresentedBy_parabolicHom i ν ∅
    have hupper := ρ.hasOrbitWeightUpperBound_of_parabolic_eigenline cv ev hcv
      (Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter cv))
      (Standard.parabolicHom i ν ∅)
      (Dynamic.Affine.isRepresentedBy_unipotentHom (Dynamic.oppositeCocharacter cv))
      hp j hline
    by_contra hnot
    have hdiff : latticePairing T delta v = ev j - ev r := by
      simp only [delta, ev, map_sub, LinearMap.sub_apply]
    have hlt : ev j < ev r := by
      change ¬0 ≤ latticePairing T delta v at hnot
      omega
    exact hactive (hupper Z g r hlt)
  change 0 ≤ latticePairing T delta d
  by_contra hnot
  have hx : latticePairing T delta d ≤ -1 := by omega
  have ht := htest (|latticePairing T delta ν| + 1).toNat
  have hcast : (((|latticePairing T delta ν| + 1).toNat : ℕ) : ℤ) =
      |latticePairing T delta ν| + 1 :=
    Int.toNat_of_nonneg (by positivity)
  rw [map_add, map_nsmul, nsmul_eq_mul, hcast] at ht
  have habs := le_abs_self (latticePairing T delta ν)
  have hnonneg := abs_nonneg (latticePairing T delta ν)
  nlinarith

/-- The omitted simple-root coordinate controls every active off-line
orbit weight. The integer constant is the positive pairing of that root
with a chosen standard cocharacter for its maximal parabolic face. -/
theorem maximalParabolic_orbitPairing_gap
    (i : T.toGrp ⟶ G) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    {characters : n → rationalCharacters T.toGrp}
    (hdiag : ρ.HasTorusCharacterDiagonal i characters)
    (j : n) (hline0 : (ρ.restrict (Standard.parabolicHom i ν ∅)).PreservesCoordinateLine j)
    (α : characterLattice T) (hα : α ∈ simpleRelativeRoots i ν)
    (zeta : cocharacterLattice T)
    (hzeta : IsStandardCocharacter i ν (simpleRelativeRoots i ν \ {α}) zeta)
    (hline : (ρ.restrict
      (Standard.parabolicHom i ν (simpleRelativeRoots i ν \ {α}))).PreservesCoordinateLine j)
    (Z : Over (Spec (CommRingCat.of k))) (g : Z ⟶ G.X) (r : n) (hr : r ≠ j)
    (hactive : (ρ.pointMatrix Z g : Matrix n n Γ(Z.left, ⊤)) r j ≠ 0)
    (c : cocharacterLattice T)
    (hc : ∀ β ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing T β c) :
    latticePairing T α c ≤ latticePairing T α zeta *
      latticePairing T
        ((rationalCharacters.equivCharacterLattice T) (characters j) -
          (rationalCharacters.equivCharacterLattice T) (characters r)) c := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hi.isSplitSubtorus.mono
  let delta := (rationalCharacters.equivCharacterLattice T) (characters j) -
    (rationalCharacters.equivCharacterLattice T) (characters r)
  let m := latticePairing T α zeta
  have hm : 0 < m := hzeta.2.2 α hα (by simp)
  let czeta := CommGroupScheme.groupHom zeta ≫ i
  let ezeta : n → ℤ := fun a =>
    latticePairing T ((rationalCharacters.equivCharacterLattice T) (characters a)) zeta
  have hczeta : czeta ≫ ρ =
      GeneralLinear.diagonalCocharacter n (CommRingCat.of k) ezeta :=
    (Category.assoc _ _ _).trans (hdiag.cocharacter zeta)
  have hp : (Dynamic.parabolic czeta).IsRepresentedBy
      (Standard.parabolicHom i ν (simpleRelativeRoots i ν \ {α})) := by
    rw [← ((standardCocharacter k G hG T i hi ν hν
      (simpleRelativeRoots i ν \ {α}) Set.sdiff_subset).2 zeta hzeta).1]
    exact Standard.isRepresentedBy_parabolicHom i ν _
  have hstrict := ρ.hasStrictOrbitWeightUpperBound_of_parabolic_eigenline
    czeta ezeta hczeta
    (Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter czeta))
    (Standard.parabolicHom i ν (simpleRelativeRoots i ν \ {α}))
    (Dynamic.Affine.isRepresentedBy_unipotentHom (Dynamic.oppositeCocharacter czeta))
    hp j hline
  have hdelta : 0 < latticePairing T delta zeta := by
    have hlt : ezeta r < ezeta j := by
      by_contra hnot
      exact hactive (hstrict Z g r hr (by omega))
    simpa only [delta, ezeta, map_sub, LinearMap.sub_apply, sub_pos] using hlt
  let d := m • c - latticePairing T α c • zeta
  have hd : ∀ β ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing T β d := by
    intro β hβ
    dsimp only [d]
    rw [map_sub, map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul]
    by_cases hβα : β = α
    · subst β
      dsimp only [m]
      nlinarith
    · rw [hzeta.2.1 β ⟨hβ, by simpa only [Set.mem_singleton_iff] using hβα⟩, mul_zero,
        sub_zero]
      exact mul_nonneg hm.le (hc β hβ)
  have hbound := ρ.orbitPairing_nonneg_of_simpleRootPairings_nonneg i hG hi ν hν
    hdiag j hline0 Z g r hactive d hd
  change 0 ≤ latticePairing T delta d at hbound
  dsimp only [d] at hbound
  rw [map_sub, map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul] at hbound
  change latticePairing T α c ≤ m * latticePairing T delta c
  have hαc := hc α hα
  nlinarith

/-- The required maximal-parabolic orbit coordinates and their positive
omitted-root gap exist for every actual connected-reductive setup.
No line representation or weight-gap premise is left as an input. -/
theorem exists_maximalParabolic_orbitPairing_gap [LocallyOfFiniteType G.X.hom]
    (i : T.toGrp ⟶ G) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : α ∈ simpleRelativeRoots i ν) :
    ∃ (d : ℕ) (j : Fin (d + 1)) (tau : MatrixRepresentation G (Fin (d + 1)))
      (characters : Fin (d + 1) → rationalCharacters T.toGrp) (zeta : cocharacterLattice T),
      tau.HasExactCoordinateLineStabilizer
        (standardParabolic i ν (simpleRelativeRoots i ν \ {α})) j ∧
      tau.HasTorusCharacterDiagonal i characters ∧
      IsStandardCocharacter i ν (simpleRelativeRoots i ν \ {α}) zeta ∧
      0 < latticePairing T α zeta ∧
      ∀ (Z : Over (Spec (CommRingCat.of k))) (g : Z ⟶ G.X) (r : Fin (d + 1)),
        r ≠ j → (tau.pointMatrix Z g : Matrix (Fin (d + 1)) (Fin (d + 1))
          Γ(Z.left, ⊤)) r j ≠ 0 →
        ∀ c : cocharacterLattice T,
          (∀ β ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing T β c) →
          latticePairing T α c ≤ latticePairing T α zeta *
            latticePairing T
              ((rationalCharacters.equivCharacterLattice T) (characters j) -
                (rationalCharacters.equivCharacterLattice T) (characters r)) c := by
  have := hi.isSplitSubtorus.mono
  let J := simpleRelativeRoots i ν \ {α}
  have hJ : J ⊆ simpleRelativeRoots i ν := Set.sdiff_subset
  obtain ⟨d, j₀, tau₀, h₀⟩ := Chevalley.exists_line_stabilizer k G
    (Standard.parabolicScheme i ν J) (Standard.parabolicHom i ν J)
    (Standard.isClosedSubgroup_parabolicHom i ν J)
  have hstab : tau₀.HasExactCoordinateLineStabilizer (standardParabolic i ν J) j₀ := by
    simpa only [HasExactCoordinateLineStabilizer,
      (Standard.isRepresentedBy_parabolicHom i ν J).2] using h₀
  have hTline : (tau₀.restrict i).PreservesCoordinateLine j₀ := by
    intro Z x
    have hx : x ≫ i.hom.hom ∈ (standardParabolic i ν J).carrier Z :=
      ((range_le_standardLevi i ν J).trans (standardLevi_le_standardParabolic i ν J))
        Z ⟨x, rfl⟩
    simpa only [pointMatrix_restrict] using (hstab Z (x ≫ i.hom.hom)).mp hx
  let D := torusEigenlineDiagonalization tau₀ i hi.isSplitSubtorus.1 j₀ hTline
  let tau := tau₀.basisConjugate D.basisMatrix
  have hstab' : tau.HasExactCoordinateLineStabilizer (standardParabolic i ν J) D.lineIndex :=
    hstab.basisConjugate D.basisMatrix D.lineIndex D.lineBasis
  have hlineJ : (tau.restrict (Standard.parabolicHom i ν J)).PreservesCoordinateLine
      D.lineIndex := by
    intro Z x
    have hx := ((Standard.isRepresentedBy_parabolicHom i ν J).pointsEquiv Z x).property
    simpa only [pointMatrix_restrict] using
      (hstab' Z (x ≫ (Standard.parabolicHom i ν J).hom.hom)).mp hx
  have hP0 : standardParabolic i ν ∅ ≤ standardParabolic i ν J :=
    ((standardParabolicOrder k G hG T i hi ν hν).1 ∅ J
      (Set.empty_subset _) hJ).1.mp (Set.empty_subset _)
  have hline0 : (tau.restrict (Standard.parabolicHom i ν ∅)).PreservesCoordinateLine
      D.lineIndex := by
    intro Z x
    have hx := ((Standard.isRepresentedBy_parabolicHom i ν ∅).pointsEquiv Z x).property
    simpa only [pointMatrix_restrict] using
      (hstab' Z (x ≫ (Standard.parabolicHom i ν ∅).hom.hom)).mp (hP0 Z hx)
  obtain ⟨zeta, hzeta⟩ := (standardCocharacter k G hG T i hi ν hν J hJ).1
  refine ⟨d, D.lineIndex, tau, D.characters, zeta, hstab', D.diagonal,
    hzeta, hzeta.2.2 α hα (by simp [J]), ?_⟩
  intro Z g r hr hactive c hc
  exact tau.maximalParabolic_orbitPairing_gap i hG hi ν hν D.diagonal D.lineIndex
    hline0 α hα zeta hzeta hlineJ Z g r hr hactive c hc

end Relative

end Langlands.GroupScheme.MatrixRepresentation
