import Langlands.GroupScheme.Torus.FiniteGaloisCharacterDescent
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Torus.LatticeBaseInvariants
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.GroupScheme.Rational.LeviCocenterRootModelStatement
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # The split quotient whose characters are all Galois invariants -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme
namespace TorusAnisotropicPart

variable (k E : Type u) [Field k] [Field E] [Algebra k E]
  [FiniteDimensional k E] [IsGalois k E]

omit [FiniteDimensional k E] [IsGalois k E] in
/-- Every geometric character of a ground-field split torus is Galois fixed. -/
theorem split_character_fixed
    (Q : CommGroupScheme (Spec (CommRingCat.of k))) (hQ : IsSplitTorus Q.toGrp)
    (σ : E ≃ₐ[k] E)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj Q)) :
    characterLattice.galoisRepresentation k E Q σ χ = χ := by
  obtain ⟨ψ, rfl⟩ := (hQ.characterLattice_baseChange_bijective (algebraBaseMap k E) Q).2 χ
  exact characterLattice.galoisRepresentation_baseChange k E Q σ ψ

/-- A split quotient realizing the entire integral invariant character lattice. -/
theorem exists_splitQuotient
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp) :
    ∃ (Q : CommGroupScheme (Spec (CommRingCat.of k))) (q : T ⟶ Q),
      IsSplitTorus Q.toGrp ∧
      Function.Injective (characterLattice.baseChangePullback k E q) ∧
      (characterLattice.baseChangePullback k E q).range =
        (characterLattice.galoisRepresentation k E T).invariants := by
  classical
  let bc := CommGroupScheme.baseChange (algebraBaseMap k E)
  let M := characterLattice (bc.obj T)
  obtain ⟨J, hJ, ⟨eT⟩⟩ := hT
  let := hJ
  let cT : M ≃+ (J → ℤ) :=
    (characterLattice.congr (CommGroupScheme.isoOfGroupIso eT)).trans
      (splitTorus.characterLatticeEquiv E J)
  let : Module.Free ℤ M := Module.Free.of_equiv cT.symm.toIntLinearEquiv
  let : Module.Finite ℤ M := Module.Finite.equiv cT.symm.toIntLinearEquiv
  let : Module.IsTorsionFree ℤ M :=
    cT.injective.moduleIsTorsionFree cT (fun r m => cT.toIntLinearEquiv.map_smul r m)
  let : IsNoetherian ℤ M := isNoetherian_of_isNoetherianRing_of_finite ℤ M
  let N : Submodule ℤ M := (characterLattice.galoisRepresentation k E T).invariants
  let : Module.Finite ℤ N := Module.Finite.of_injective N.subtype N.injective_subtype
  let : Module.IsTorsionFree ℤ N := inferInstance
  let : Module.Free ℤ N := Module.free_of_finite_type_torsion_free'
  let I := Module.Free.ChooseBasisIndex ℤ N
  let b : Module.Basis I ℤ N := Module.Free.chooseBasis ℤ N
  let Q := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I
  have hQ : IsSplitTorus Q.toGrp := isSplitTorus_splitTorus I
  let cQ : characterLattice (bc.obj Q) ≃+ N :=
    ((characterLattice.baseChangeEquiv (algebraBaseMap k E) Q hQ).symm.trans
      (splitTorus.characterLatticeEquiv k I)).trans b.equivFun.symm.toAddEquiv
  let F : characterLattice (bc.obj Q) →+ M :=
    N.subtype.toAddMonoidHom.comp cQ.toAddMonoidHom
  have hF : ∀ (σ : E ≃ₐ[k] E) (χ : characterLattice (bc.obj Q)),
      F (characterLattice.galoisRepresentation k E Q σ χ) =
        characterLattice.galoisRepresentation k E T σ (F χ) := by
    intro σ χ
    rw [split_character_fixed k E Q hQ σ χ]
    exact ((cQ χ).property σ).symm
  obtain ⟨q, hq, -⟩ := (hQ.baseChange (algebraBaseMap k E)).existsUnique_hom_of_equivariant_characterMap F hF
  have hqF (χ : characterLattice (bc.obj Q)) :
      characterLattice.baseChangePullback k E q χ = F χ := hq χ
  refine ⟨Q, q, hQ, ?_, ?_⟩
  · intro χ ψ h
    apply cQ.injective
    apply Subtype.ext
    change F χ = F ψ
    simpa only [hqF] using h
  · ext χ
    constructor
    · rintro ⟨ψ, rfl⟩
      rw [hqF]
      exact (cQ ψ).property
    · intro hχ
      obtain ⟨ψ, hψ⟩ := cQ.surjective ⟨χ, hχ⟩
      exact ⟨ψ, (hqF ψ).trans (congrArg Subtype.val hψ)⟩

/-- A ground-field split quotient carrying precisely the invariant geometric characters. -/
structure SplitQuotientData
    (T : CommGroupScheme (Spec (CommRingCat.of k))) where
  quotient : CommGroupScheme (Spec (CommRingCat.of k))
  hom : T ⟶ quotient
  isSplit : IsSplitTorus quotient.toGrp
  injective_pullback : Function.Injective (characterLattice.baseChangePullback k E hom)
  range_pullback : (characterLattice.baseChangePullback k E hom).range =
    (characterLattice.galoisRepresentation k E T).invariants

/-- Choose the split quotient constructed by descent of invariant characters. -/
def splitQuotient
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp) :
    SplitQuotientData k E T :=
  Classical.choice <| by
    obtain ⟨Q, q, hQ, hi, hr⟩ := exists_splitQuotient k E T hT
    exact ⟨⟨Q, q, hQ, hi, hr⟩⟩

end TorusAnisotropicPart
end Langlands.GroupScheme
