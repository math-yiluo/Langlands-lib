import Langlands.GroupScheme.Reductive.CanonicalRhoDynamics
import Langlands.GroupScheme.Rational.DominantHighestWeight
import Langlands.GroupScheme.MatrixRepresentation.CharacterSpanEmbedding
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.Rational.GeneralLinearCharacterAdapters
import Langlands.GroupScheme.MatrixRepresentationDual

/-! # Extremal coordinates from a supplied highest-weight representation -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Module
open scoped CategoryTheory.MonObj Matrix Classical

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {n : Type} [Fintype n] [DecidableEq n]

/-- An affine-test diagonal character formula holds on every relative scheme test. -/
theorem pointMatrix_diagonal_of_affineMatrix
    (ρ : MatrixRepresentation G n) (χ : n → rationalCharacters G)
    (hd : ∀ (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A),
      (ρ.affineMatrix A x : Matrix n n A) =
        Matrix.diagonal (fun a =>
          (Gm.affineUnitsEquiv (CommRingCat.of k) A (x ≫ (χ a).toMul.hom.hom) : A)))
    (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ G.X) :
    (ρ.pointMatrix V x : Matrix n n Γ(V.left, ⊤)) =
      Matrix.diagonal (fun a => (characterEval (χ a) V x : Γ(V.left, ⊤))) := by
  let A := CharacterUnits.Coord G
  let U := (algSpec (CommRingCat.of k)).obj (op A)
  let z := CharacterUnits.universalPoint G
  have hz : (ρ.pointMatrix U z : Matrix n n Γ(U.left, ⊤)) =
      Matrix.diagonal (fun a => (characterEval (χ a) U z : Γ(U.left, ⊤))) := by
    rw [pointMatrix_eq_affineMatrix]
    change (ρ.affineMatrix A z : Matrix n n A).map
      (Corepresented.affineSectionsIso A).inv.hom.toRingHom = _
    rw [hd]
    ext a b
    simp only [Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs
    · exact congrArg Units.val
        (GeneralLinear.gm_pointsEquiv_eq_affinePointsEquiv A
          (z ≫ (χ a).toMul.hom.hom)).symm
    · exact map_zero _
  let f : V ⟶ U := x ≫ (Lie.coordinateIso G).inv
  have hf : f ≫ z = x := by
    simp [f, z, CharacterUnits.universalPoint_eq]
  have h := congrArg (fun M : Matrix n n Γ(U.left, ⊤) =>
    M.map f.left.appTop.hom) hz
  rw [← hf, pointMatrix_naturality]
  ext a b
  have he := congrFun (congrFun h a) b
  simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply, Matrix.diagonal_apply,
    characterEval_naturality, Units.coe_map, apply_ite, map_zero] at he ⊢
  exact he

/-- In a character basis, a one-dimensional character space occupies exactly
one basis coordinate. -/
theorem exists_unique_characterBasis_index
    (ρ : MatrixRepresentation G n) (b : Basis n k (n → k))
    (χ : n → rationalCharacters G) (hb : ∀ a, b a ∈ ρ.characterSpace (χ a))
    (lam : rationalCharacters G) (hlam : Module.finrank k (ρ.characterSpace lam) = 1) :
    ∃ a : n, χ a = lam ∧ ∀ c : n, χ c = lam → c = a := by
  have hs : ρ.characterSpace lam ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hlam
    exact Nat.zero_ne_one hlam
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
  have hex : ∃ a, χ a = lam := by
    by_contra hn
    have hp : ρ.characterProjector lam = 0 := by
      apply b.ext
      intro a
      rw [characterProjector_of_mem ρ lam (χ a) (hb a)]
      split_ifs with h
      · exact False.elim (hn ⟨a, h⟩)
      · rfl
    have h := characterProjector_of_mem ρ lam lam hv
    simp only [hp, LinearMap.zero_apply] at h
    exact hv0 h.symm
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ha, ?_⟩
  intro c hc
  by_contra hca
  have ha' : b a ∈ ρ.characterSpace lam := ha ▸ hb a
  have hc' : b c ∈ ρ.characterSpace lam := hc ▸ hb c
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hlam ha' (b.ne_zero a)] at hc'
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hc'
  have h := congrArg (fun w => b.repr w c) hr
  simp [hca] at h

omit [IsAffineHom G.X.hom] in
/-- The actual dual of a character-diagonal representation has the negative
characters on every relative test scheme. -/
theorem dual_pointMatrix_diagonal
    (ρ : MatrixRepresentation G n) (χ : n → rationalCharacters G)
    (hd : ∀ (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ G.X),
      (ρ.pointMatrix V x : Matrix n n Γ(V.left, ⊤)) =
        Matrix.diagonal (fun a => (characterEval (χ a) V x : Γ(V.left, ⊤))))
    (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ G.X) :
    (ρ.dual.pointMatrix V x : Matrix n n Γ(V.left, ⊤)) =
      Matrix.diagonal (fun a => (characterEval (-χ a) V x : Γ(V.left, ⊤))) := by
  rw [dual_pointMatrix, GeneralLinear.matrixContragredient_coe, ← map_inv,
    hd V x⁻¹, Matrix.diagonal_transpose]
  congr 1
  funext a
  rw [map_inv, characterEval_neg]

omit [IsAffineHom G.X.hom] in
/-- The all-test diagonal character formula identifies every cocharacter
matrix with its lattice-pairing exponents. -/
theorem cocharacter_eq_diagonal_of_pointMatrix
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ G)
    (ρ : MatrixRepresentation G n) (χ : n → rationalCharacters T.toGrp)
    (hd : ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ T.toGrp.X),
      (ρ.pointMatrix V (t ≫ j.hom.hom) : Matrix n n Γ(V.left, ⊤)) =
        Matrix.diagonal (fun a => (characterEval (χ a) V t : Γ(V.left, ⊤))))
    (nu : cocharacterLattice T) :
    (CommGroupScheme.groupHom nu ≫ j) ≫ ρ =
      GeneralLinear.diagonalCocharacter n (CommRingCat.of k)
        (fun a => latticePairing T (rationalCharacters.equivCharacterLattice T (χ a)) nu) := by
  apply hom_ext_points
  intro V x
  apply (GeneralLinear.pointsEquiv n (CommRingCat.of k) V).injective
  apply Units.ext
  change (ρ.pointMatrix V ((x ≫ (CommGroupScheme.groupHom nu).hom.hom) ≫ j.hom.hom) :
      Matrix n n Γ(V.left, ⊤)) = _
  rw [hd, GeneralLinear.pointsEquiv_diagonalCocharacter,
    GeneralLinear.coe_diagonalUnits]
  congr 1
  funext a
  have he : nu ≫ rationalCharacters.equivCharacterLattice T (χ a) =
      (gmEndEquiv k).symm
        (latticePairing T (rationalCharacters.equivCharacterLattice T (χ a)) nu) := by
    rw [latticePairing_apply, AddEquiv.symm_apply_apply]
  change (Gm.pointsEquiv _ V
      ((x ≫ (CommGroupScheme.groupHom nu).hom.hom) ≫
        (CommGroupScheme.groupHom (rationalCharacters.equivCharacterLattice T (χ a))).hom.hom) :
          Γ(V.left, ⊤)) = _
  rw [← comp_groupHom_comp, he, gmEndEquiv_symm_comp, map_zpow]

end MatrixRepresentation

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) [Fintype p.rootIndex]
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)

/-- Polarized rho is strictly positive on every nonzero nonnegative combination
of the supplied simple roots. -/
theorem pairing_polarization_rho_pos_of_mem_positiveRootMonoid
    {mu : characterLattice p.torus} (hmu : mu ∈ p.positiveRootMonoid)
    (hne : mu ≠ 0) :
    0 < p.rootDatum.toLinearMap mu
      (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)) := by
  let f := (p.rootDatum.toLinearMap.flip
    (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)))
  have hm : 0 ≤ f mu ∧ (f mu = 0 → mu = 0) := by
    clear hne
    change mu ∈ AddSubmonoid.closure _ at hmu
    induction hmu using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have hp := (IntegralWeylVector.pairing_root_polarization_rho_pos_iff
        p.rootDatum p.base hspan a).mpr (p.base.isPos_of_mem_support a.property)
      change 0 < f (p.rootDatum.root a) at hp
      exact ⟨le_of_lt hp, fun h => False.elim (ne_of_gt hp h)⟩
    | zero => simp only [map_zero, le_refl, implies_true, and_self]
    | add x y _ _ hx hy =>
      rw [map_add]
      refine ⟨add_nonneg hx.1 hy.1, ?_⟩
      intro h
      have hx0 : f x = 0 := by omega
      have hy0 : f y = 0 := by omega
      rw [hx.2 hx0, hy.2 hy0, zero_add]
  exact lt_of_le_of_ne hm.1 (fun h => hne (hm.2 h.symm))

/-- A supplied highest-weight representation has a character basis with one
highest coordinate, strictly above all other coordinates for polarized rho. -/
theorem exists_highestWeight_characterBasis
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) {lam : characterLattice p.torus}
    (hρ : p.IsHighestWeight ρ lam) :
    ∃ (b : Basis n k (n → k)) (mu : n → characterLattice p.torus) (a : n),
      (∀ c, b c ∈ p.representationWeightSpace ρ (mu c)) ∧
      mu a = lam ∧
      ∀ c, c ≠ a →
        p.rootDatum.toLinearMap (mu c)
            (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)) <
          p.rootDatum.toLinearMap lam
            (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)) := by
  let := p.isSplitTorus.isAffineHom
  obtain ⟨b, χ, hb⟩ := MatrixRepresentation.exists_characterBasis
    (ρ.restrict p.inclusion) (by exact hρ.2.1)
  obtain ⟨a, ha, hu⟩ := MatrixRepresentation.exists_unique_characterBasis_index
    (ρ.restrict p.inclusion) b χ hb
    ((rationalCharacters.equivCharacterLattice p.torus).symm lam) hρ.2.2.1
  let mu := fun c => rationalCharacters.equivCharacterLattice p.torus (χ c)
  have hba : mu a = lam := by
    exact congrArg (rationalCharacters.equivCharacterLattice p.torus) ha
  refine ⟨b, mu, a, hb, hba, ?_⟩
  intro c hca
  have hc : mu c ≠ lam := by
    intro h
    exact hca (hu c h)
  have hn : p.representationWeightSpace ρ (mu c) ≠ ⊥ := by
    intro h
    have hv := hb c
    change b c ∈ p.representationWeightSpace ρ (mu c) at hv
    rw [h] at hv
    exact b.ne_zero c (by simpa only [Submodule.mem_bot] using hv)
  have hp := p.pairing_polarization_rho_pos_of_mem_positiveRootMonoid hspan
    (hρ.2.2.2 (mu c) hn) (sub_ne_zero.mpr hc.symm)
  simpa only [map_sub, LinearMap.sub_apply, sub_pos] using hp

/-- Conjugating a supplied highest-weight representation and taking its actual
dual gives precisely the canonical negative-rho extremal representation data. -/
theorem exists_negativeRho_extremalRepresentation
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n)
    (hρ : p.IsHighestWeight ρ (IntegralWeylVector.rho p.rootDatum p.base hspan)) :
    ∃ (σ : MatrixRepresentation G n) (e : n → ℤ) (a : n),
      (CommGroupScheme.groupHom
        (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)) ≫
          p.inclusion) ≫ σ =
            GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e ∧
      (∀ c, c ≠ a → e a < e c) ∧
      ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ p.torus.toGrp.X),
        (σ.pointMatrix V (t ≫ p.inclusion.hom.hom) : Matrix n n Γ(V.left, ⊤)) a a =
          (characterEval ((rationalCharacters.equivCharacterLattice p.torus).symm
            (-IntegralWeylVector.rho p.rootDatum p.base hspan)) V t : Γ(V.left, ⊤)) := by
  let := p.isSplitTorus.isAffineHom
  obtain ⟨b, mu, a, hb, ha, hmax⟩ :=
    p.exists_highestWeight_characterBasis hspan ρ hρ
  let χ := fun c => (rationalCharacters.equivCharacterLattice p.torus).symm (mu c)
  let σ₀ := ρ.conjugate (MatrixRepresentation.basisCoordinatePoint b)
  have hd : ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ p.torus.toGrp.X),
      (σ₀.pointMatrix V (t ≫ p.inclusion.hom.hom) : Matrix n n Γ(V.left, ⊤)) =
        Matrix.diagonal (fun c => (characterEval (χ c) V t : Γ(V.left, ⊤))) := by
    intro V t
    have h := MatrixRepresentation.pointMatrix_diagonal_of_affineMatrix
      ((ρ.restrict p.inclusion).conjugate (MatrixRepresentation.basisCoordinatePoint b))
      χ (MatrixRepresentation.conjugate_basisCoordinatePoint_affineMatrix
        (ρ.restrict p.inclusion) b χ hb) V t
    simpa only [MatrixRepresentation.conjugate_restrict,
      MatrixRepresentation.pointMatrix_restrict] using h
  let σ := σ₀.dual
  have hdual : ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ p.torus.toGrp.X),
      (σ.pointMatrix V (t ≫ p.inclusion.hom.hom) : Matrix n n Γ(V.left, ⊤)) =
        Matrix.diagonal (fun c => (characterEval (-χ c) V t : Γ(V.left, ⊤))) := by
    intro V t
    have h := MatrixRepresentation.dual_pointMatrix_diagonal
      (σ₀.restrict p.inclusion) χ hd V t
    simpa only [MatrixRepresentation.dual_restrict,
      MatrixRepresentation.pointMatrix_restrict] using h
  let nu := p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)
  let e : n → ℤ := fun c => p.rootDatum.toLinearMap (-mu c) nu
  refine ⟨σ, e, a, ?_, ?_, ?_⟩
  · have h := MatrixRepresentation.cocharacter_eq_diagonal_of_pointMatrix
      p.inclusion σ (fun c => -χ c) hdual nu
    simpa only [χ, e, map_neg, LinearMap.neg_apply, AddEquiv.apply_symm_apply,
      ← p.isRootDatum.1] using h
  · intro c hca
    have h := hmax c hca
    dsimp only [e]
    rw [map_neg, LinearMap.neg_apply, map_neg, LinearMap.neg_apply, ha]
    exact neg_lt_neg h
  · intro V t
    rw [hdual, Matrix.diagonal_apply_eq]
    simp only [χ, ha, ← map_neg]

/-- Actual representation data with the three canonical negative-rho laws.
This type makes no assertion that such a representation exists. -/
structure NegativeRhoExtremalRepresentationData
    (n : Type) [Fintype n] [DecidableEq n] where
  representation : MatrixRepresentation G n
  exponents : n → ℤ
  index : n
  cocharacter_eq : (CommGroupScheme.groupHom
    (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)) ≫
      p.inclusion) ≫ representation =
        GeneralLinear.diagonalCocharacter n (CommRingCat.of k) exponents
  isMinimum : ∀ c, c ≠ index → exponents index < exponents c
  weight : ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ p.torus.toGrp.X),
    (representation.pointMatrix V (t ≫ p.inclusion.hom.hom) :
      Matrix n n Γ(V.left, ⊤)) index index =
        (characterEval ((rationalCharacters.equivCharacterLattice p.torus).symm
          (-IntegralWeylVector.rho p.rootDatum p.base hspan)) V t : Γ(V.left, ⊤))

/-- Select the actual conjugated-dual witnesses obtained from a supplied
highest-weight representation at integral rho. -/
def negativeRhoExtremalRepresentationData
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n)
    (hρ : p.IsHighestWeight ρ (IntegralWeylVector.rho p.rootDatum p.base hspan)) :
    p.NegativeRhoExtremalRepresentationData hspan n :=
  Classical.choice (by
    obtain ⟨σ, e, a, hnu, ha, hw⟩ :=
      p.exists_negativeRho_extremalRepresentation hspan ρ hρ
    exact ⟨⟨σ, e, a, hnu, ha, hw⟩⟩)

end SplitPinning

end Langlands.GroupScheme
