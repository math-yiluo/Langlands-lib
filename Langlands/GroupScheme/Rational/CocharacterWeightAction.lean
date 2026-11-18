import Langlands.GroupScheme.MatrixRepresentation.CharacterDifferential
import Langlands.GroupScheme.Lie.CocharacterTangent
import Langlands.GroupScheme.Rational.FundamentalRepresentations
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.Lie.PrimePowerFieldExtension
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # Cocharacter tangent actions on actual representation weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)
    {n : Type} [Fintype n] [DecidableEq n]

local instance : IsAffineHom p.torus.toGrp.X.hom := p.isSplitTorus.isAffineHom

/-- The endomorphism obtained by differentiating an actual cocharacter in a representation. -/
def representationCocharacterAction (r : MatrixRepresentation G n)
    (y : cocharacterLattice p.torus) : Module.End k (n → k) :=
  Matrix.toLin' (r.tangentMatrix k (Lie.targetMap p.inclusion k (Lie.cocharacterTangent y)))

/-- A cocharacter tangent acts on every actual weight space by its integral lattice pairing. -/
theorem representationCocharacterAction_apply
    (r : MatrixRepresentation G n) (y : cocharacterLattice p.torus)
    (mu : characterLattice p.torus) {v : n → k}
    (hv : v ∈ p.representationWeightSpace r mu) :
    p.representationCocharacterAction r y v =
      ((p.rootDatum.toLinearMap mu y : ℤ) : k) • v := by
  have h := MatrixRepresentation.tangentMatrix_mulVec_of_mem_characterSpace
    (r.restrict p.inclusion) ((rationalCharacters.equivCharacterLattice p.torus).symm mu)
    hv (Lie.cocharacterTangent y)
  have hs : MatrixRepresentation.characterTangentScalar
      ((rationalCharacters.equivCharacterLattice p.torus).symm mu)
      (Lie.cocharacterTangent y) = ((p.rootDatum.toLinearMap mu y : ℤ) : k) := by
    change (Lie.characterValue mu (Lie.cocharacterTangent y).val : DualNumber k).snd = _
    rw [Lie.characterValue_cocharacterTangent_snd, p.isRootDatum.1]
  rw [hs, MatrixRepresentation.tangentMatrix_restrict] at h
  exact h

/-- In characteristic zero, a monomorphic representation detects every nonzero cocharacter
on one of its actual torus weight spaces. -/
theorem exists_weight_pairing_ne_zero_of_mono [CharZero k]
    {N : ℕ} (sigma : MatrixRepresentation G (Fin N)) (hsigma : Mono sigma.hom.hom)
    (y : cocharacterLattice p.torus) (hy : y ≠ 0) :
    ∃ mu : characterLattice p.torus,
      p.representationWeightSpace sigma mu ≠ ⊥ ∧ p.rootDatum.toLinearMap mu y ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hle : (⨆ mu, p.representationWeightSpace sigma mu) ≤
      LinearMap.ker (p.representationCocharacterAction sigma y) := by
    apply iSup_le
    intro mu v hv
    rw [LinearMap.mem_ker, p.representationCocharacterAction_apply sigma y mu hv]
    by_cases hbot : p.representationWeightSpace sigma mu = ⊥
    · have hv0 : v = 0 := by simpa only [hbot, Submodule.mem_bot] using hv
      rw [hv0, smul_zero]
    · rw [h mu hbot, Int.cast_zero, zero_smul]
  rw [p.iSup_representationWeightSpace_eq_top] at hle
  have hact : p.representationCocharacterAction sigma y = 0 :=
    LinearMap.ker_eq_top.mp (top_le_iff.mp hle)
  have hmat : sigma.tangentMatrix k
      (Lie.targetMap p.inclusion k (Lie.cocharacterTangent y)) = 0 := by
    apply Matrix.toLin'.injective
    simpa only [representationCocharacterAction, map_zero] using hact
  have hX : Lie.targetMap p.inclusion k (Lie.cocharacterTangent y) = 1 :=
    sigma.tangentMatrix_injective hsigma k (hmat.trans (sigma.tangentMatrix_one k).symm)
  let : Mono p.inclusion.hom.hom := p.isMaximalTorus.2.1.mono_overHom
  have hY : Lie.cocharacterTangent y = (1 : lieKernel p.torus.toGrp k) :=
    (lieKernelHom_injective p.inclusion) (hX.trans (map_one _).symm)
  have hzero : Lie.cocharacterTangent (0 : cocharacterLattice p.torus) =
      (1 : lieKernel p.torus.toGrp k) := by
    apply Subtype.ext
    exact comp_groupHom_zero _
  exact hy (Lie.cocharacterTangent_injective p.isSplitTorus (hY.trans hzero.symm))

/-- Closed embeddings satisfy the faithful weight detection used by the pair Lie interface. -/
theorem exists_weight_pairing_ne_zero_of_isClosedSubgroup [CharZero k]
    {N : ℕ} (sigma : MatrixRepresentation G (Fin N)) (hsigma : IsClosedSubgroup sigma)
    (y : cocharacterLattice p.torus) (hy : y ≠ 0) :
    ∃ mu : characterLattice p.torus,
      p.representationWeightSpace sigma mu ≠ ⊥ ∧ p.rootDatum.toLinearMap mu y ≠ 0 :=
  p.exists_weight_pairing_ne_zero_of_mono sigma hsigma.mono_overHom y hy

end Langlands.GroupScheme.SplitPinning
