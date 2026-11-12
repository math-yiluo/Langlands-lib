import Langlands.GroupScheme.MatrixRepresentation.CoordinateLineWeightPositivity
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion

/-! # Positive rank-one root relations for actual parabolic line characters -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H U P : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- A positive integral character multiple is an ambient restriction plus a
positive integral root multiple. -/
def HasPositiveIntegralRootCharacterRelation (i : T.toGrp ⟶ G)
    (α ψ : characterLattice T) : Prop :=
  ∃ d b : ℕ, 0 < d ∧ 0 < b ∧ ∃ eta : rationalCharacters G,
    d • ψ = torusCharacterRestrict i eta + b • α

namespace MatrixRepresentation

/-- Restriction preserves the actual algebraic character on a fixed coordinate line. -/
theorem coordinateLineCharacter_restrict
    (ρ : MatrixRepresentation G n) (f : H ⟶ G) (j : n)
    (hG : ρ.PreservesCoordinateLine j)
    (hH : (ρ.restrict f).PreservesCoordinateLine j) :
    (ρ.restrict f).coordinateLineCharacter j hH = f ≫ ρ.coordinateLineCharacter j hG := by
  apply hom_ext_points
  intro Z x
  apply (Gm.pointsEquiv (Spec (CommRingCat.of k)) Z).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, coordinateLineCharacter_scalar,
    coordinateLineCharacter_scalar]
  apply Units.ext
  simp only [coordinateLineScalar_val, pointMatrix_restrict]

/-- The actual torus character on the specified coordinate eigenline. -/
def torusCoordinateLineCharacter (ρ : MatrixRepresentation G n) (i : T.toGrp ⟶ G)
    (j : n) (hline : (ρ.restrict i).PreservesCoordinateLine j) : characterLattice T :=
  (rationalCharacters.equivCharacterLattice T)
    ((ρ.restrict i).coordinateLineRationalCharacter j hline)

/-- The integer of the restricted Gm line character is exactly the original
torus lattice pairing. -/
theorem coordinateLineCocharacterWeight_eq_latticePairing
    (ρ : MatrixRepresentation G n) (i : T.toGrp ⟶ G)
    (ζ : cocharacterLattice T) (j : n)
    (hT : (ρ.restrict i).PreservesCoordinateLine j)
    (hζ : (ρ.restrict (CommGroupScheme.groupHom ζ ≫ i)).PreservesCoordinateLine j) :
    (ρ.restrict (CommGroupScheme.groupHom ζ ≫ i)).coordinateLineCocharacterWeight j hζ =
      latticePairing T (ρ.torusCoordinateLineCharacter i j hT) ζ := by
  have hζ' : ((ρ.restrict i).restrict (CommGroupScheme.groupHom ζ)).PreservesCoordinateLine j := by
    rw [restrict_comp]
    exact hζ
  have hc := (ρ.restrict i).coordinateLineCharacter_restrict
    (CommGroupScheme.groupHom ζ) j hT hζ'
  have hc' : (ρ.restrict (CommGroupScheme.groupHom ζ ≫ i)).coordinateLineCharacter j hζ =
      CommGroupScheme.groupHom ζ ≫ (ρ.restrict i).coordinateLineCharacter j hT := by
    simpa only [restrict_comp] using hc
  unfold coordinateLineCocharacterWeight
  rw [latticePairing_apply]
  apply congrArg (gmEndEquiv k)
  exact congrArg Additive.ofMul hc'

/-- A torus whose image lies in this cocharacter's centralizer inherits
coordinate-line preservation from the represented dynamic parabolic. -/
theorem preservesCoordinateLine_torus_of_parabolic
    (ρ : MatrixRepresentation G n) (i : T.toGrp ⟶ G)
    (ζ : cocharacterLattice T) (iP : P ⟶ G)
    (hP : (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy iP)
    (j : n) (hline : (ρ.restrict iP).PreservesCoordinateLine j) :
    (ρ.restrict i).PreservesCoordinateLine j := by
  have hr : SubgroupFunctor.range i ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) :=
    (range_le_centralizer_groupHom_comp i ζ).trans (Dynamic.centralizer_le_parabolic _)
  let f := hP.liftOfLE i hr
  have hf : f ≫ iP = i := hP.liftOfLE_comp i hr
  intro Z x
  obtain ⟨c, hc⟩ := hline Z (x ≫ f.hom.hom)
  refine ⟨c, ?_⟩
  simpa only [pointMatrix_restrict, Category.assoc, ← Grp.comp_hom_hom, hf] using hc

variable [IsAffineHom G.X.hom] (ρ : MatrixRepresentation G n)
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [Fintype (relativeWeylGroup i)]

/-- In actual relative rank one, a proper parabolic coordinate eigenline has
positive torus-character pairing on the Weyl norm-kernel direction. -/
theorem latticePairing_torusCoordinateLineCharacter_normKernel_pos
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : simpleRelativeRoots i ν = {α})
    (iU : U ⟶ G) (iP : P ⟶ G)
    (hU : (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom (normKernelCocharacter i ν) ≫ i))).IsRepresentedBy iU)
    (hP : (Dynamic.parabolic
      (CommGroupScheme.groupHom (normKernelCocharacter i ν) ≫ i)).IsRepresentedBy iP)
    (j : n) (hline : ρ.HasProperParabolicEigenline iP j)
    (hTline : (ρ.restrict i).PreservesCoordinateLine j) :
    0 < latticePairing T (ρ.torusCoordinateLineCharacter i j hTline)
      (normKernelCocharacter i ν) := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let ζ := normKernelCocharacter i ν
  let χ := CommGroupScheme.groupHom ζ ≫ i
  have hχline := ρ.preservesCoordinateLine_cocharacter_of_parabolic χ iP hP j hline.1
  obtain ⟨s, hs⟩ := hasReversingNormalizer_normKernelCocharacter i hG hi ν hν α hα
  have hpos := ρ.coordinateLineCocharacterWeight_pos_of_proper_parabolic_eigenline
    χ iU iP hU hP j hline hχline (reversesCocharacter_of_normalizingAut_neg i ζ s hs)
  rwa [ρ.coordinateLineCocharacterWeight_eq_latticePairing i ζ j hTline hχline] at hpos

/-- The actual parabolic line character is a positive root multiple modulo
ambient characters after clearing a positive integral denominator. -/
theorem positiveIntegralRootCharacterRelation_torusCoordinateLineCharacter
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : simpleRelativeRoots i ν = {α})
    (iU : U ⟶ G) (iP : P ⟶ G)
    (hU : (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom (normKernelCocharacter i ν) ≫ i))).IsRepresentedBy iU)
    (hP : (Dynamic.parabolic
      (CommGroupScheme.groupHom (normKernelCocharacter i ν) ≫ i)).IsRepresentedBy iP)
    (j : n) (hline : ρ.HasProperParabolicEigenline iP j)
    (hTline : (ρ.restrict i).PreservesCoordinateLine j) :
    HasPositiveIntegralRootCharacterRelation i α (ρ.torusCoordinateLineCharacter i j hTline) := by
  exact exists_pos_nsmul_eq_restrict_add_pos_nsmul_of_normKernel_pairing
    i hG hi ν hν α hα _
    (ρ.latticePairing_torusCoordinateLineCharacter_normKernel_pos
      i hG hi ν hν α hα iU iP hU hP j hline hTline)

end MatrixRepresentation
end Langlands.GroupScheme
