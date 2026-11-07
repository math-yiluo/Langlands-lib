import Langlands.GroupScheme.Reductive.CanonicalRhoDynamics
import Langlands.GroupScheme.Reductive.ExtremalUnitCell
import Langlands.GroupScheme.Reductive.SteinbergBigCellData

/-! # Canonical rho geometric data from an actual extremal representation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

local instance {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

/-- The actual witnesses and first six laws of the Steinberg big-cell conclusion. -/
structure SteinbergBigCellGeometricData (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] where
  Λ : Type u
  [latticeGroup : AddCommGroup Λ]
  j : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G
  H : GroupScheme (Spec (CommRingCat.of k))
  [affineH : IsAffineHom H.X.hom]
  i : H ⟶ G
  n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X
  χ : AffineCoordinates.algebra H
  d : AffineCoordinates.algebra G
  left_covariant : d ∈ AffineCoordinates.leftCovariantSubspace i χ
  right_covariant :
    ∀ (V : Over (Spec (CommRingCat.of k))) (h : V ⟶ H.X) (g : V ⟶ G.X),
      AffineCoordinates.pointAlgebraHom G V
          (g * (h ≫ (i ≫ (G.innerIso n).hom).hom.hom)⁻¹) d =
        AffineCoordinates.pointAlgebraHom H V h χ *
          AffineCoordinates.pointAlgebraHom G V g d
  identity_value :
    AffineCoordinates.pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) 1 d = 1
  nonZeroDivisor : d ∈ nonZeroDivisors (AffineCoordinates.algebra G)
  unit_factors :
    ∀ (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X),
      IsUnit (AffineCoordinates.pointAlgebraHom G V g d) →
        ∃ c c' : V ⟶ H.X,
          g = (c ≫ i.hom.hom) * (c' ≫ (i ≫ (G.innerIso n).hom).hom.hom)⁻¹
  intersection :
    ∀ (V : Over (Spec (CommRingCat.of k))) (c c' : V ⟶ H.X),
      c ≫ i.hom.hom = c' ≫ (i ≫ (G.innerIso n).hom).hom.hom →
        ∃ t : V ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp.X,
          c ≫ i.hom.hom = t ≫ j.hom.hom

attribute [instance] SteinbergBigCellGeometricData.latticeGroup
  SteinbergBigCellGeometricData.affineH

/-- Supplying the remaining entire-space irreducibility law preserves all witnesses. -/
def SteinbergBigCellGeometricData.withIrreduciblePowers
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (D : SteinbergBigCellGeometricData G)
    (hirr : ∀ e : ℕ, ∃ e' : ℕ, e ≤ e' ∧ ∃ (m : ℕ)
      (bX : Module.Basis (Fin m) k
        (AffineCoordinates.leftCovariantSubspace D.i (D.χ ^ e'))),
      (Chevalley.affineRegularRepresentation G _ bX
        (fun f _ hv => AffineCoordinates.rightAct_mem_leftCovariantSubspace D.i
          (D.χ ^ e') f hv)).rationalRepresentation.IsIrreducible) :
    SteinbergBigCellData G where
  Λ := D.Λ
  j := D.j
  H := D.H
  i := D.i
  n := D.n
  χ := D.χ
  d := D.d
  conditions := ⟨D.left_covariant, D.right_covariant, D.identity_value,
    D.nonZeroDivisor, D.unit_factors, D.intersection, hirr⟩

namespace MatrixRepresentation

variable {n : Type} [Fintype n] [DecidableEq n]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (ρ : MatrixRepresentation G n)
    (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (e : n → ℤ)
    (hν : ν ≫ ρ = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)
    (i : H ⟶ G) (hH : (Dynamic.parabolic ν).IsRepresentedBy i)
    (a : n) (ha : ∀ c, c ≠ a → e a < e c)
    (jT : T.toGrp ⟶ G) (jH : T.toGrp ⟶ H) (hfactor : jH ≫ i = jT)
    (weight : characterLattice T)

include hfactor

/-- The torus weight of a distinguished diagonal entry identifies the restricted
minimum-weight character, without an assumed parabolic character identity. -/
theorem restrict_minimumWeightCharacter_eq_of_diagonal_entry
    (hweight : ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ T.toGrp.X),
      (ρ.pointMatrix V (t ≫ jT.hom.hom) : Matrix n n Γ(V.left, ⊤)) a a =
        (characterEval ((rationalCharacters.equivCharacterLattice T).symm weight) V t :
          Γ(V.left, ⊤))) :
    rationalCharacters.equivCharacterLattice T
      (characterRestrict jH (minimumWeightCharacter ρ ν e hν i hH a ha)) = weight := by
  apply (rationalCharacters.equivCharacterLattice T).symm.injective
  simp only [AddEquiv.symm_apply_apply]
  apply rationalCharacters.ext_characterEval
  intro V t
  apply Units.ext
  rw [characterEval_characterRestrict, minimumWeightCharacter_eval]
  simpa only [Category.assoc, ← Grp.comp_hom_hom, hfactor] using hweight V t

end MatrixRepresentation

namespace Dynamic

open AffineCoordinates MatrixRepresentation

variable {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (i : H ⟶ G) (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j)
    {J : Type u} [Fintype J]
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hroot : IsRootDatumOf j P) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)
    (ν : cocharacterLattice T)
    (hH : (parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy i)
    (hZ : (centralizer (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy j)
    (hc : IsClosedSubgroup i)
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (e : n → ℤ)
    (hν : (CommGroupScheme.groupHom ν ≫ j) ≫ ρ =
      GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)
    (a : n) (ha : ∀ c, c ≠ a → e a < e c)
    (hweight : ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ T.toGrp.X),
      (ρ.pointMatrix V (t ≫ j.hom.hom) : Matrix n n Γ(V.left, ⊤)) a a =
        (characterEval ((rationalCharacters.equivCharacterLattice T).symm
          (-IntegralWeylVector.rho P b hspan)) V t : Γ(V.left, ⊤)))
    (w : normalizerPoints j)
    (hanti : characterAut (normalizingAut j w) (-IntegralWeylVector.rho P b hspan) =
      IntegralWeylVector.rho P b hspan)
    (hQ : (parabolic (oppositeCocharacter (CommGroupScheme.groupHom ν ≫ j))).IsRepresentedBy
      (i ≫ (G.innerIso w.val).hom))
    [IsAlgClosed k] (hcover : BorelTorusBruhatCovering i j)

include hG hT hj hroot hH hZ hc hν ha hweight hanti hQ hcover

/-- Assemble the six geometric laws from the actual supplied extremal representation. -/
def extremalNegativeRhoBigCellGeometricData : SteinbergBigCellGeometricData G := by
  let model := hT.diagonalizableModel
  have hw := restrict_minimumWeightCharacter_eq_of_diagonal_entry ρ
    (CommGroupScheme.groupHom ν ≫ j) e hν i hH a ha j
    (centralizerToParabolic hH hZ) (centralizerToParabolic_comp hH hZ)
    (-IntegralWeylVector.rho P b hspan) hweight
  refine {
    Λ := model.index → ℤ
    j := model.embedding j
    H := H
    i := i
    n := w.val
    χ := negativeRhoCoordinate hH hZ P b hspan
    d := diagonalMatrixCoefficient ρ a
    left_covariant := ?_
    right_covariant := ?_
    identity_value := pointAlgebraHom_one_diagonalMatrixCoefficient ρ a _
    nonZeroDivisor := diagonalMatrixCoefficient_mem_nonZeroDivisors hG ρ a
    unit_factors := ?_
    intersection := ?_
  }
  · exact diagonalMatrixCoefficient_mem_leftCovariant_negativeRho ρ
      (CommGroupScheme.groupHom ν ≫ j) e hν i hH j hZ hc a ha P b hspan hw
  · exact pointAlgebraHom_mul_inv_diagonalMatrixCoefficient_negativeRho ρ
      (CommGroupScheme.groupHom ν ≫ j) e hν i hH j hZ hc a ha P b hspan hw w hQ hanti
  · intro V g hg
    exact exists_opposite_factors_of_unit_diagonalMatrixCoefficient hG hT
      i j hj P hroot b hspan ν hH hZ hc ρ e hν a ha hw w hanti hQ hcover g hg
  · intro V c c' he
    exact model.exists_point_of_opposite_parabolic_eq
      (CommGroupScheme.groupHom ν ≫ j) j hH hQ hZ c c' he

end Dynamic

namespace IsRootDatumOf

open AffineCoordinates MatrixRepresentation Langlands.GroupScheme.Dynamic

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {j : T.toGrp ⟶ G}
    {J : Type u} [Fintype J]
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} [P.IsReduced]
    (hP : IsRootDatumOf j P) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (hj : IsMaximalTorus j)

local notation "ν₀" => P.Polarization (IntegralWeylVector.rho P b hspan)
local notation "λ₀" => CommGroupScheme.groupHom ν₀ ≫ j

variable [IsAlgClosed k]
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (e : n → ℤ)
    (hν : (CommGroupScheme.groupHom
      (P.Polarization (IntegralWeylVector.rho P b hspan)) ≫ j) ≫ ρ =
        GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)
    (a : n) (ha : ∀ c, c ≠ a → e a < e c)
    (hweight : ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ T.toGrp.X),
      (ρ.pointMatrix V (t ≫ j.hom.hom) : Matrix n n Γ(V.left, ⊤)) a a =
        (characterEval ((rationalCharacters.equivCharacterLattice T).symm
          (-IntegralWeylVector.rho P b hspan)) V t : Γ(V.left, ⊤)))
    (hcover : BorelTorusBruhatCovering
      (k := k) (G := G) (B := Affine.parabolicScheme (CommGroupScheme.groupHom
        (P.Polarization (IntegralWeylVector.rho P b hspan)) ≫ j)) (T := T)
      (Affine.parabolicHom (CommGroupScheme.groupHom
        (P.Polarization (IntegralWeylVector.rho P b hspan)) ≫ j)) j)

include hP hG hT hj hν ha hweight hcover

attribute [local irreducible] RootPairing.Polarization
set_option backward.isDefEq.respectTransparency true

/-- Construct all six geometric laws using the canonical rho parabolic and
opposition point, and a diagonalizable presentation of the original torus.
The extremal representation and Bruhat covering remain supplied inputs. -/
def canonicalRhoBigCellGeometricData : SteinbergBigCellGeometricData G := by
  letI : IsClosedImmersion j.hom.hom.left := hj.2.1
  letI : IsClosedImmersion (Affine.parabolicHom λ₀).hom.hom.left :=
    Affine.isClosedSubgroup_parabolicHom λ₀
  letI : IsAffineHom (Affine.parabolicScheme λ₀).X.hom := by
    rw [← Over.w (Affine.parabolicHom λ₀).hom.hom]
    infer_instance
  have assemble := extremalNegativeRhoBigCellGeometricData
    (G := G) (H := Affine.parabolicScheme λ₀) (T := T) (J := J) (n := n)
    hG hT (Affine.parabolicHom λ₀) j hj
    P hP b hspan ν₀ (Affine.isRepresentedBy_parabolicHom λ₀)
    (hP.isRepresentedBy_centralizer_polarization_rho b hspan hG hT hj)
    (Affine.isClosedSubgroup_parabolicHom λ₀) ρ e
  exact assemble hν a ha hweight
    (hP.oppositionRepresentative b hspan)
    (hP.oppositionRepresentative_neg_rho b hspan)
    (hP.oppositionRepresentative_parabolic b hspan
      (Affine.isRepresentedBy_parabolicHom λ₀)) hcover

end IsRootDatumOf

end Langlands.GroupScheme
