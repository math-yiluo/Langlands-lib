import Langlands.GroupScheme.Reductive.HighestWeightExtremal
import Langlands.GroupScheme.Reductive.CanonicalRhoCovariance
import Langlands.GroupScheme.Reductive.ExtremalMatrixCoefficient
import Langlands.GroupScheme.Dynamic.ParabolicCharacters
import Langlands.GroupScheme.HomogeneousCharacterProducts
import Langlands.GroupScheme.MatrixRepresentation.RationalDualConjugateIrreducibility

/-! # Negative scalar-rho eigen-rows from supplied highest-weight modules -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) [Fintype p.rootIndex]
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)

/-- A supplied highest-weight representation has a conjugated dual with a unique
minimum of weight minus the highest weight, preserving rational irreducibility. -/
theorem exists_highestWeight_dual_extremalRepresentation
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n)
    {lam : characterLattice p.torus} (hρ : p.IsHighestWeight ρ lam) :
    ∃ (σ : MatrixRepresentation G n) (e : n → ℤ) (a : n),
      (CommGroupScheme.groupHom
        (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)) ≫
          p.inclusion) ≫ σ =
            GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e ∧
      (∀ c, c ≠ a → e a < e c) ∧
      (∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ p.torus.toGrp.X),
        (σ.pointMatrix V (t ≫ p.inclusion.hom.hom) : Matrix n n Γ(V.left, ⊤)) a a =
          (characterEval ((rationalCharacters.equivCharacterLattice p.torus).symm
            (-lam)) V t : Γ(V.left, ⊤))) ∧
      (σ.rationalRepresentation.IsIrreducible ↔ ρ.rationalRepresentation.IsIrreducible) := by
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
  refine ⟨σ, e, a, ?_, ?_, ?_, ?_⟩
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

  · exact (MatrixRepresentation.dual_rationalRepresentation_isIrreducible_iff σ₀).trans
      (MatrixRepresentation.conjugate_rationalRepresentation_isIrreducible_iff ρ _)

local notation "ν₀" =>
  p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)
local notation "λ₀" => CommGroupScheme.groupHom ν₀ ≫ p.inclusion

local instance highestWeightScalarRhoEigenrowIsAffine {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

attribute [local irreducible] RootPairing.Polarization

local instance highestWeightScalarRhoEigenrowIsAffineHom : IsAffineHom (Dynamic.Affine.parabolicScheme λ₀).X.hom := by
  let : IsClosedImmersion (Dynamic.Affine.parabolicHom λ₀).hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_parabolicHom λ₀
  rw [← Over.w (Dynamic.Affine.parabolicHom λ₀).hom.hom]
  infer_instance

local notation "χ₀" => Dynamic.negativeRhoCoordinate
  (Dynamic.Affine.isRepresentedBy_parabolicHom λ₀)
  (p.isRootDatum.isRepresentedBy_centralizer_polarization_rho p.base hspan
    p.isConnectedReductive p.isSplitTorus p.isMaximalTorus)
  p.rootDatum p.base hspan

/-- A supplied rationally irreducible highest-weight module at m rho gives a
nonzero coordinate eigen-row for the m-th power of the canonical character,
on every relative test scheme. The source coordinate dimension is preserved. -/
theorem exists_scalarRho_eigenrow
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (m : ℕ)
    (hρ : p.IsHighestWeight ρ (m • IntegralWeylVector.rho p.rootDatum p.base hspan))
    (hrat : ρ.rationalRepresentation.IsIrreducible) :
    ∃ (σ : MatrixRepresentation G n) (a : n),
      σ.rationalRepresentation.IsIrreducible ∧
      (Pi.single a 1 : n → k) ≠ 0 ∧
      ∀ (V : Over (Spec (CommRingCat.of k)))
        (h : V ⟶ (Dynamic.Affine.parabolicScheme λ₀).X),
        (fun c => scalarMap V ((Pi.single a 1 : n → k) c)) ᵥ*
            (σ.pointMatrix V (h ≫ (Dynamic.Affine.parabolicHom λ₀).hom.hom) :
              Matrix n n Γ(V.left, ⊤)) =
          AffineCoordinates.pointValue (Dynamic.Affine.parabolicScheme λ₀) V h (χ₀ ^ m) •
            fun c => scalarMap V ((Pi.single a 1 : n → k) c) := by
  obtain ⟨σ, e, a, hnu, hmin, hw, hirr⟩ :=
    p.exists_highestWeight_dual_extremalRepresentation hspan ρ hρ
  let hP := Dynamic.Affine.isRepresentedBy_parabolicHom λ₀
  let hT := p.isRootDatum.isRepresentedBy_centralizer_polarization_rho p.base hspan
    p.isConnectedReductive p.isSplitTorus p.isMaximalTorus
  let θ := MatrixRepresentation.minimumWeightCharacter σ λ₀ e hnu
    (Dynamic.Affine.parabolicHom λ₀) hP a hmin
  have hθ : θ = m • Dynamic.negativeRhoCharacter hP hT p.rootDatum p.base hspan := by
    apply (Dynamic.character_eq_iff_restrict_eq hP
      (Dynamic.Affine.isClosedSubgroup_parabolicHom λ₀) hT _ _).mpr
    rw [map_nsmul]
    apply rationalCharacters.ext_characterEval
    intro V t
    apply Units.ext
    rw [characterEval_characterRestrict, MatrixRepresentation.minimumWeightCharacter_eval,
      Category.assoc, ← Grp.comp_hom_hom, Dynamic.centralizerToParabolic_comp, hw]
    simp only [Dynamic.negativeRhoCharacter, map_nsmul,
      Dynamic.restrict_extendCentralizerCharacter, map_neg, neg_nsmul]
  refine ⟨σ, a, hirr.mpr hrat, ?_, ?_⟩
  · intro hz
    have he := congrFun hz a
    simp at he
  · intro V h
    rw [AffineCoordinates.scalarMap_single_one]
    have hact := MatrixRepresentation.minimumWeightCharacter_action σ λ₀ e hnu
      (Dynamic.Affine.parabolicHom λ₀) hP a hmin V h
    change (Pi.single a 1 : n → Γ(V.left, ⊤)) ᵥ* _ = _
    rw [AffineCoordinates.pointValue, Dynamic.negativeRhoCoordinate,
      ← AffineCoordinates.characterCoordinate_nsmul,
      AffineCoordinates.pointAlgebraHom_characterCoordinate, ← hθ]
    exact hact

/-- A rationally irreducible representation on the original coordinate index
with a nonzero standard row of the prescribed canonical scalar-rho weight. -/
structure ScalarRhoEigenrowData (n : Type) [Fintype n] [DecidableEq n] (m : ℕ) where
  representation : MatrixRepresentation G n
  index : n
  isIrreducible : representation.rationalRepresentation.IsIrreducible
  row_ne_zero : (Pi.single index 1 : n → k) ≠ 0
  eigenrow : ∀ (V : Over (Spec (CommRingCat.of k)))
    (h : V ⟶ (Dynamic.Affine.parabolicScheme λ₀).X),
    (fun c => scalarMap V ((Pi.single index 1 : n → k) c)) ᵥ*
        (representation.pointMatrix V (h ≫ (Dynamic.Affine.parabolicHom λ₀).hom.hom) :
          Matrix n n Γ(V.left, ⊤)) =
      AffineCoordinates.pointValue (Dynamic.Affine.parabolicScheme λ₀) V h (χ₀ ^ m) •
        fun c => scalarMap V ((Pi.single index 1 : n → k) c)

/-- Select the complete eigen-row data from a supplied rationally irreducible
highest-weight representation at the prescribed scalar multiple of rho. -/
def scalarRhoEigenrowData
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (m : ℕ)
    (hρ : p.IsHighestWeight ρ (m • IntegralWeylVector.rho p.rootDatum p.base hspan))
    (hrat : ρ.rationalRepresentation.IsIrreducible) :
    p.ScalarRhoEigenrowData hspan n m := by
  have hdata : Nonempty (p.ScalarRhoEigenrowData hspan n m) := by
    obtain ⟨σ, a, hirr, hrow, heigen⟩ := p.exists_scalarRho_eigenrow hspan ρ m hρ hrat
    exact ⟨⟨σ, a, hirr, hrow, heigen⟩⟩
  exact Classical.choice hdata

end Langlands.GroupScheme.SplitPinning
