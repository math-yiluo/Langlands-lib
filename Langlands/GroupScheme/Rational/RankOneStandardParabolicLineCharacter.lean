import Langlands.GroupScheme.Rational.RankOneParabolicLineCharacter
import Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison
import Langlands.GroupScheme.Rational.RankOneOppositeParabolics
import Langlands.GroupScheme.Rational.TorusUnipotenceProof
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.Chevalley.ActualLineStabilizer

/-! # Actual standard rank-one parabolic lines with positive root characters -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G P : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

namespace MatrixRepresentation

/-- The actual subgroup functor is exactly the selected unit-scalar line stabilizer. -/
def HasExactCoordinateLineStabilizer (ρ : MatrixRepresentation G n)
    (F : SubgroupFunctor G) (j : n) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of k))) (g : Z ⟶ G.X),
    g ∈ F.carrier Z ↔ ∃ c : Γ(Z.left, ⊤)ˣ,
      (ρ.pointMatrix Z g : Matrix n n Γ(Z.left, ⊤)) *ᵥ Pi.single j 1 =
        (c : Γ(Z.left, ⊤)) • (Pi.single j 1 : n → Γ(Z.left, ⊤))

/-- A proper exact line stabilizer gives subgroup line preservation and rules
out global line preservation. -/
theorem HasExactCoordinateLineStabilizer.hasProperParabolicEigenline
    {ρ : MatrixRepresentation G n} {F : SubgroupFunctor G} {j : n}
    (hstab : ρ.HasExactCoordinateLineStabilizer F j)
    (iP : P ⟶ G) (hP : F.IsRepresentedBy iP) (hne : F ≠ ⊤) :
    ρ.HasProperParabolicEigenline iP j := by
  constructor
  · intro Z p
    have hp : p ≫ iP.hom.hom ∈ F.carrier Z := (hP.pointsEquiv Z p).property
    simpa only [pointMatrix_restrict] using (hstab Z (p ≫ iP.hom.hom)).mp hp
  · intro hglobal
    apply hne
    ext Z g
    exact ⟨fun _ => Subgroup.mem_top _, fun _ => (hstab Z g).mpr (hglobal Z g)⟩

end MatrixRepresentation

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G)
  [Mono i.hom.hom.left] [Fintype (relativeWeylGroup i)]

omit [IsAffineHom G.X.hom] in
/-- The actual Weyl norm-kernel correction preserves the full dynamic
parabolic on all tests, for every connected reductive maximal-split setup. -/
theorem Dynamic.parabolic_normKernelCocharacter_of_connectedReductive
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) :
    Dynamic.parabolic (CommGroupScheme.groupHom (normKernelCocharacter i ν) ≫ i) =
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hroots := relativeRootSystem k G hG T i hi
  have hcard : (0 : ℤ) < Fintype.card (relativeWeylGroup i) := by
    exact_mod_cast Fintype.card_pos
  apply le_antisymm
  · apply ((relativeRootSignInclusions k G hG T i hi (normKernelCocharacter i ν) ν).1).mpr
    intro α hα hnonneg
    rw [latticePairing_normKernelCocharacter_root_of_relativeRootSystem
      i hi.1.1 hroots ν α hα, nsmul_eq_mul] at hnonneg
    exact (mul_nonneg_iff_of_pos_left hcard).mp hnonneg
  · apply ((relativeRootSignInclusions k G hG T i hi ν (normKernelCocharacter i ν)).1).mpr
    intro α hα hnonneg
    rw [latticePairing_normKernelCocharacter_root_of_relativeRootSystem
      i hi.1.1 hroots ν α hα, nsmul_eq_mul]
    exact mul_nonneg hcard.le hnonneg

namespace MatrixRepresentation

/-- An exact line stabilizer equal to the actual standard rank-one parabolic
has the positive integral simple-root relation. All positivity premises are proved. -/
theorem positiveRootRelation_of_exact_emptyStandardParabolic_stabilizer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : simpleRelativeRoots i ν = {α})
    (ρ : MatrixRepresentation G n) (j : n)
    (hstab : ρ.HasExactCoordinateLineStabilizer (standardParabolic i ν ∅) j) :
    ∃ hTline : (ρ.restrict i).PreservesCoordinateLine j,
      HasPositiveIntegralRootCharacterRelation i α (ρ.torusCoordinateLineCharacter i j hTline) := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let ζ := normKernelCocharacter i ν
  let χ := CommGroupScheme.groupHom ζ ≫ i
  have hχ : Dynamic.parabolic χ = standardParabolic i ν ∅ :=
    (Dynamic.parabolic_normKernelCocharacter_of_connectedReductive i hG hi ν).trans
      (standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν).symm
  have hP : (Dynamic.parabolic χ).IsRepresentedBy (Standard.parabolicHom i ν ∅) := by
    rw [hχ]
    exact Standard.isRepresentedBy_parabolicHom i ν ∅
  have hαsimple : α ∈ simpleRelativeRoots i ν := by rw [hα]; rfl
  have hproper : standardParabolic i ν ∅ ≠ ⊤ := by
    rw [standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν]
    exact Dynamic.parabolic_ne_top_of_root_pairing_ne_zero
      RelativeRoot.torusActionUnipotence hG.hasTrivialUnipotentRadical
      i ν hαsimple.1.1 hαsimple.1.2.ne'
  have hline := hstab.hasProperParabolicEigenline
    (Standard.parabolicHom i ν ∅) (Standard.isRepresentedBy_parabolicHom i ν ∅) hproper
  have hTline := ρ.preservesCoordinateLine_torus_of_parabolic i ζ
    (Standard.parabolicHom i ν ∅) hP j hline.1
  refine ⟨hTline, ?_⟩
  exact ρ.positiveIntegralRootCharacterRelation_torusCoordinateLineCharacter
    i hG hi ν hν α hα
    (Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χ))
    (Standard.parabolicHom i ν ∅)
    (Dynamic.Affine.isRepresentedBy_unipotentHom (Dynamic.oppositeCocharacter χ))
    hP j hline hTline

/-- Actual finite-coordinate representations with the standard rank-one
parabolic as exact line stabilizer and the positive root relation exist. -/
theorem exists_exact_emptyStandardParabolic_stabilizer_positiveRootRelation
    [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : simpleRelativeRoots i ν = {α}) :
    ∃ (d : ℕ) (j : Fin (d + 1)) (ρ : MatrixRepresentation G (Fin (d + 1)))
      (hTline : (ρ.restrict i).PreservesCoordinateLine j),
      ρ.HasExactCoordinateLineStabilizer (standardParabolic i ν ∅) j ∧
        HasPositiveIntegralRootCharacterRelation i α
          (ρ.torusCoordinateLineCharacter i j hTline) := by
  obtain ⟨d, j, ρ, hρ⟩ := Chevalley.exists_line_stabilizer k G
    (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅)
    (Standard.isClosedSubgroup_parabolicHom i ν ∅)
  have hstab : ρ.HasExactCoordinateLineStabilizer (standardParabolic i ν ∅) j := by
    simpa only [HasExactCoordinateLineStabilizer,
      (Standard.isRepresentedBy_parabolicHom i ν ∅).2] using hρ
  obtain ⟨hTline, hrel⟩ :=
    positiveRootRelation_of_exact_emptyStandardParabolic_stabilizer i hG hi ν hν α hα ρ j hstab
  exact ⟨d, j, ρ, hTline, hstab, hrel⟩

end MatrixRepresentation
end Langlands.GroupScheme
