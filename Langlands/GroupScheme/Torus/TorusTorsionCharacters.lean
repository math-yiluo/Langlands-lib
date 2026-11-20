import Langlands.AbelianScheme.TorsionFunctor
import Langlands.GroupScheme.Torus.ConnectedReductive
import Langlands.GroupScheme.Torus.MultiplicativeTypeAbsoluteExactnessProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Langlands.GroupScheme.Torus.SplitMultiplication
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Absolute characters of the torsion subgroup of a torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace characterLattice

variable {k : Type u} [Field k] (T : CommGroupScheme (Spec (CommRingCat.of k)))

local notation "Ω" => SeparableClosure k
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap k Ω)
local notation "X" => characterLattice (Functor.obj (BC) T)
local notation "Tₙ" n =>
  Functor.obj (CommGroupScheme.torsionFunctor (S := Spec (CommRingCat.of k)) n) T

/-- Restriction of geometric characters to the actual torsion subgroup. -/
def torusTorsionRestriction (n : ℤ) : X →ₗ[ℤ] characterLattice ((BC).obj (Tₙ n)) :=
  (precompose ((BC).map ((CommGroupScheme.torsionInclusion n).app T))).toIntLinearMap

/-- The actual torsion subgroup of a torus has multiplicative type. -/
theorem isMultiplicativeType_torusTorsion (hT : IsTorus T.toGrp) (n : ℤ) :
    IsMultiplicativeType (Tₙ n).toGrp := by
  let : IsAffineHom T.X.hom := hT.isConnectedReductive_of_fieldSplitting.isAffineHom
  exact hT.isMultiplicativeType.of_isClosedSubgroup (torsionι T.toGrp n)
    (show IsClosedImmersion (torsionι T.toGrp n).hom.hom.left from inferInstance)

private theorem torusTorsionCharacter_exact
    (hT : IsTorus T.toGrp) {n : ℤ} (hn : n ≠ 0) :
    Function.Exact (n • (LinearMap.id : X →ₗ[ℤ] X)) (torusTorsionRestriction T n) ∧
      Function.Surjective (torusTorsionRestriction T n) := by
  let i := torsionι T.toGrp n
  let q := multiplication T.toGrp n
  let : IsAffineHom T.X.hom := hT.isConnectedReductive_of_fieldSplitting.isAffineHom
  let : Smooth T.X.hom := hT.smooth
  have hclosed : IsClosedSubgroup i := show IsClosedImmersion i.hom.hom.left from inferInstance
  let E := hT.splittingExtension
  let b := Spec.map (CommRingCat.ofHom (algebraMap k E.carrier))
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k E.carrier
  let : Surjective b := hsurj
  let : Flat b := hflat
  let : QuasiCompact b := hqc
  have hp := baseChange_map_isPullback b q
  have hb : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Limits.pullback.fst T.X.hom b) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hsplit : IsSplitTorus ((CommGroupScheme.baseChange b).obj T).toGrp := E.isSplitTorus
  obtain ⟨hqflat, hqsurj⟩ := hsplit.flat_and_surjective_multiplication hn
  have hqbase : (GroupScheme.baseChange b).map q =
      multiplication ((CommGroupScheme.baseChange b).obj T).toGrp n :=
    multiplication_baseChange b T.toGrp n
  rw [← hqbase] at hqflat hqsurj
  have hfp : LocallyOfFinitePresentation q.hom.hom.left := by
    have : LocallyOfFiniteType (q.hom.hom.left ≫ T.X.hom) := by
      rw [Over.w q.hom.hom]
      infer_instance
    let : LocallyOfFiniteType q.hom.hom.left :=
      locallyOfFiniteType_of_comp q.hom.hom.left T.X.hom
    let : IsLocallyNoetherian T.X.left := LocallyOfFiniteType.isLocallyNoetherian T.X.hom
    infer_instance
  have hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q :=
    ⟨MorphismProperty.of_isPullback_of_descendsAlong hp hb hqflat,
      MorphismProperty.of_isPullback_of_descendsAlong hp hb hqsurj, hfp, rfl⟩
  let T' : MultiplicativeTypeGroup k := ⟨T, hT.isMultiplicativeType⟩
  let Z' : MultiplicativeTypeGroup k := ⟨Tₙ n, isMultiplicativeType_torusTorsion T hT n⟩
  let i' : Z' ⟶ T' := ObjectProperty.homMk ((CommGroupScheme.torsionInclusion n).app T)
  let q' : T' ⟶ T' := ObjectProperty.homMk (n • 𝟙 T)
  have hex := (multiplicativeTypeAbsoluteExactness k Z' T' T' i' q').mp ⟨hclosed, hq⟩
  change _ ∧ Function.Exact (fun χ : X => (BC).map (n • 𝟙 T) ≫ χ)
      (torusTorsionRestriction T n) ∧ Function.Surjective (torusTorsionRestriction T n) at hex
  have hmul : (BC).map (n • 𝟙 T) = n • 𝟙 ((BC).obj T) := by
    rw [Functor.map_zsmul, (BC).map_id T]
  change Function.Exact (fun χ : X => n • χ) (torusTorsionRestriction T n) ∧
    Function.Surjective (torusTorsionRestriction T n)
  simpa only [hmul, Preadditive.zsmul_comp, Category.id_comp] using hex.2

/-- The kernel of restriction to torsion is the full subgroup of multiples. -/
theorem ker_torusTorsionRestriction (hT : IsTorus T.toGrp) {n : ℤ} (hn : n ≠ 0) :
    (torusTorsionRestriction T n).ker = (n • (LinearMap.id : X →ₗ[ℤ] X)).range := by
  ext χ
  exact (torusTorsionCharacter_exact T hT hn).1 χ

/-- Restriction identifies the torsion character lattice with the character lattice
of the torus modulo all integer multiples by the torsion exponent. -/
def torusTorsionCharacterEquiv (hT : IsTorus T.toGrp) {n : ℤ} (hn : n ≠ 0) :
    (X ⧸ (n • (LinearMap.id : X →ₗ[ℤ] X)).range) ≃ₗ[ℤ]
      characterLattice ((BC).obj (Tₙ n)) :=
  (Submodule.quotEquivOfEq _ _ (ker_torusTorsionRestriction T hT hn).symm).trans
    ((torusTorsionRestriction T n).quotKerEquivOfSurjective
      (torusTorsionCharacter_exact T hT hn).2)

@[simp]
theorem torusTorsionCharacterEquiv_mk (hT : IsTorus T.toGrp) {n : ℤ} (hn : n ≠ 0) (χ : X) :
    torusTorsionCharacterEquiv T hT hn (Submodule.Quotient.mk χ) =
      torusTorsionRestriction T n χ := rfl

/-- On representatives the quotient comparison intertwines the canonical Galois
actions. -/
theorem torusTorsionCharacterEquiv_galois_mk (hT : IsTorus T.toGrp) {n : ℤ} (hn : n ≠ 0)
    (σ : Ω ≃ₐ[k] Ω) (χ : X) :
    torusTorsionCharacterEquiv T hT hn
        (Submodule.Quotient.mk (galoisRepresentation k Ω T σ χ)) =
      galoisRepresentation k Ω (Tₙ n) σ
        (torusTorsionCharacterEquiv T hT hn (Submodule.Quotient.mk χ)) := by
  simp only [torusTorsionCharacterEquiv_mk]
  exact (galoisRepresentation_precompose k Ω ((CommGroupScheme.torsionInclusion n).app T) σ χ).symm

end characterLattice

end Langlands.GroupScheme
