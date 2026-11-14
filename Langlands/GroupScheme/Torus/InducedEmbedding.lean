import Langlands.GroupScheme.Torus.GaloisLatticeRealizationProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.InducedPermutationBasis
import Langlands.GroupScheme.Rational.ClassFunctionsTorusSeparationReduction
import Langlands.GroupScheme.Absolute.CocharacterDescentGroup

/-! # Every torus embeds into an induced torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace InducedEmbedding

open GaloisLatticeRealization

variable {k E : Type u} [Field k] [Field E] [Algebra k E]

/-- The coordinate obtained by letting `σ` act on the embedding of a coordinate. -/
def actCoord {J : Type u}
    (σ : E ≃ₐ[k] E) (c : Coord k E J) : Coord k E J :=
  ⟨c.1, σ.toAlgHom.comp c.2⟩

/-- The permutation representation sends a standard basis vector to a standard
basis vector. -/
theorem permRep_single {J : Type u} [DecidableEq (Coord k E J)] (σ : E ≃ₐ[k] E)
    (c : Coord k E J) :
    permRep J σ (Pi.single c 1) = Pi.single (actCoord σ c) 1 := by
  funext j
  rw [permRep_apply]
  by_cases h : j = actCoord σ c
  · subst h
    have hc : (⟨(actCoord σ c).1, σ.symm.toAlgHom.comp (actCoord σ c).2⟩ : Coord k E J) = c := by
      refine Sigma.ext ?_ ?_
      · rfl
      · apply heq_of_eq
        apply AlgHom.ext
        intro x
        simp [actCoord]
    rw [hc, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h]
    apply Pi.single_eq_of_ne
    intro hj
    apply h
    subst hj
    refine Sigma.ext ?_ ?_
    · rfl
    · apply heq_of_eq
      apply AlgHom.ext
      intro x
      simp [actCoord]

variable [FiniteDimensional k E] [IsGalois k E]

/-- The permutation torus is induced. -/
theorem permTorus_isInduced (J : Type u) [Fintype J] [DecidableEq J] :
    IsInducedTorus (permTorus k E J) := by
  classical
  let eR := WeilGm.productEmbeddingCharacterEquiv k E (topFamily k E J)
  refine isInducedTorus_of_equivariant_basis (permTorus k E J) E (permTorus_isSplit k E J)
    (permRep J) (Pi.basisFun ℤ (Coord k E J)) eR.symm.toIntLinearEquiv ?_ ?_
  · intro σ x
    exact (permTorus_equiv_symm_galois k E J σ x).symm
  · intro σ c
    refine ⟨actCoord σ c, ?_⟩
    rw [Pi.basisFun_apply, Pi.basisFun_apply]
    exact permRep_single σ c

end InducedEmbedding

open GaloisLatticeRealization InducedEmbedding in
/-- Every torus over a field admits a homomorphism into an induced torus that is a
monomorphism of the underlying schemes over the base. -/
theorem IsTorus.exists_mono_inducedTorus {k : Type u} [Field k]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp) :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of k))) (φ : T ⟶ S),
      IsInducedTorus S ∧ Mono (CommGroupScheme.groupHom φ).hom.hom := by
  classical
  obtain ⟨E, _, _, _, _, hsplit⟩ := torusFiniteGaloisSplitting k T.toGrp hT
  let bc := CommGroupScheme.baseChange (algebraBaseMap k E)
  have hTE : IsSplitTorus (bc.obj T).toGrp := hsplit
  obtain ⟨J, _, ⟨eT⟩⟩ := hTE
  let : Fintype J := Fintype.ofFinite J
  let cT : characterLattice (bc.obj T) ≃+ (J → ℤ) :=
    (characterLattice.congr (CommGroupScheme.isoOfGroupIso
      (U := splitTorus.commGroupScheme (Spec (CommRingCat.of E)) J) eT)).trans
      (splitTorus.characterLatticeEquiv E J)
  let b : Module.Basis J ℤ (characterLattice (bc.obj T)) :=
    (Pi.basisFun ℤ J).map cT.symm.toIntLinearEquiv
  let ρ := characterLattice.galoisRepresentation k E T
  let R := permTorus k E J
  have hR : IsSplitTorus (bc.obj R).toGrp := permTorus_isSplit k E J
  let eR := WeilGm.productEmbeddingCharacterEquiv k E (topFamily k E J)
  let F : characterLattice (bc.obj R) →+ characterLattice (bc.obj T) :=
    (sumMap ρ b).toAddMonoidHom.comp eR.toAddMonoidHom
  have hF : ∀ (σ : E ≃ₐ[k] E) (χ : characterLattice (bc.obj R)),
      F (characterLattice.galoisRepresentation k E R σ χ) =
        characterLattice.galoisRepresentation k E T σ (F χ) := by
    intro σ χ
    change sumMap ρ b (eR (characterLattice.galoisRepresentation k E R σ χ)) =
      ρ σ (sumMap ρ b (eR χ))
    rw [permTorus_equiv_galois k E J σ χ, sumMap_permRep]
  have hFs : Function.Surjective F := by
    intro χ
    obtain ⟨m, rfl⟩ := sumMap_surjective_of_basis ρ b χ
    refine ⟨eR.symm m, ?_⟩
    change sumMap ρ b (eR (eR.symm m)) = sumMap ρ b m
    rw [AddEquiv.apply_symm_apply]
  obtain ⟨φ, hφ, -⟩ := hR.existsUnique_hom_of_equivariant_characterMap F hF
  refine ⟨R, φ, permTorus_isInduced J, ⟨fun {U} x y h => ?_⟩⟩
  let := GaloisCocharacterDescent.faithful_algebraPullback k E
  let P := Over.pullback (algebraBaseMap k E)
  apply P.map_injective
  apply IsSplitTorus.point_ext_characters (T := bc.obj T) hsplit
  intro χ
  obtain ⟨χ', rfl⟩ := hFs χ
  rw [← hφ χ']
  change P.map x ≫ P.map (CommGroupScheme.groupHom φ).hom.hom ≫
      (CommGroupScheme.groupHom χ').hom.hom =
    P.map y ≫ P.map (CommGroupScheme.groupHom φ).hom.hom ≫
      (CommGroupScheme.groupHom χ').hom.hom
  rw [← Functor.map_comp_assoc, h, Functor.map_comp_assoc]

end Langlands.GroupScheme
