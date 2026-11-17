import Langlands.GroupScheme.Torus.InducedTorusQuotientStatement
import Langlands.GroupScheme.Torus.GaloisLatticeRealizationProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.CharacterFaithfullyFlat
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Mathlib.RingTheory.Etale.Field

/-! # Every torus is a quotient of an induced torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace InducedTorusQuotient

open GaloisLatticeRealization

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  [FiniteDimensional k E]
  {J V : Type u} [Fintype J] [AddCommGroup V]

/-- Embed a lattice into the regular permutation lattice by all translates of its coordinates. -/
def coordinateMap (ρ : Representation ℤ (E ≃ₐ[k] E) V) (b : Module.Basis J ℤ V) :
    V →ₗ[ℤ] (Coord k E J → ℤ) :=
  LinearMap.pi fun c => (LinearMap.proj c.1).comp
    (b.equivFun.toLinearMap.comp (ρ (gal k E c.2)⁻¹))

/-- Translation of a vector becomes inverse pullback on permutation coordinates. -/
theorem coordinateMap_equivariant
    (ρ : Representation ℤ (E ≃ₐ[k] E) V) (b : Module.Basis J ℤ V)
    (σ : E ≃ₐ[k] E) (x : V) :
    coordinateMap ρ b (ρ σ x) = permRep J σ (coordinateMap ρ b x) := by
  funext c
  change b.equivFun (ρ (gal k E c.2)⁻¹ (ρ σ x)) c.1 =
    b.equivFun (ρ (gal k E (σ.symm.toAlgHom.comp c.2))⁻¹ x) c.1
  rw [gal_comp, show σ.symm = σ⁻¹ from rfl, mul_inv_rev, inv_inv, map_mul]
  rfl

/-- Coordinates at the identity embedding recover the vector. -/
theorem coordinateMap_injective
    (ρ : Representation ℤ (E ≃ₐ[k] E) V) (b : Module.Basis J ℤ V) :
    Function.Injective (coordinateMap ρ b) := by
  intro x y h
  apply b.equivFun.injective
  funext j
  have hj := congrFun h (⟨j, (⊤ : IntermediateField k E).val⟩ : Coord k E J)
  change b.equivFun (ρ (gal k E (⊤ : IntermediateField k E).val)⁻¹ x) j =
    b.equivFun (ρ (gal k E (⊤ : IntermediateField k E).val)⁻¹ y) j at hj
  simpa only [gal_val, inv_one, map_one, Module.End.one_apply] using hj

end InducedTorusQuotient

open GaloisLatticeRealization InducedTorusQuotient in
/-- Every field torus is a faithfully flat quotient of the multiplicative group
restricted from a finite étale algebra. -/
theorem inducedTorusQuotient : InducedTorusQuotientStatement.{u} := by
  classical
  intro k _ T hT
  let Tc : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { T with comm := hT.isCommMonObj }
  obtain ⟨E, _, _, _, _, hsplit⟩ := torusFiniteGaloisSplitting k T hT
  let bc := CommGroupScheme.baseChange (algebraBaseMap k E)
  have hTE : IsSplitTorus (bc.obj Tc).toGrp := hsplit
  obtain ⟨J, _, ⟨eT⟩⟩ := hsplit
  let : Fintype J := Fintype.ofFinite J
  let cT : characterLattice (bc.obj Tc) ≃+ (J → ℤ) :=
    (characterLattice.congr (CommGroupScheme.isoOfGroupIso
      (U := splitTorus.commGroupScheme (Spec (CommRingCat.of E)) J) eT)).trans
      (splitTorus.characterLatticeEquiv E J)
  let b : Module.Basis J ℤ (characterLattice (bc.obj Tc)) :=
    (Pi.basisFun ℤ J).map cT.symm.toIntLinearEquiv
  let ρ := characterLattice.galoisRepresentation k E Tc
  let R := permTorus k E J
  have hRE : IsSplitTorus (bc.obj R).toGrp := permTorus_isSplit k E J
  let eR := WeilGm.productEmbeddingCharacterEquiv k E (topFamily k E J)
  let F : characterLattice (bc.obj Tc) →+ characterLattice (bc.obj R) :=
    eR.symm.toAddMonoidHom.comp (coordinateMap ρ b).toAddMonoidHom
  have hF : ∀ (σ : E ≃ₐ[k] E) (χ : characterLattice (bc.obj Tc)),
      F (characterLattice.galoisRepresentation k E Tc σ χ) =
        characterLattice.galoisRepresentation k E R σ (F χ) := by
    intro σ χ
    change eR.symm (coordinateMap ρ b (ρ σ χ)) =
      characterLattice.galoisRepresentation k E R σ (eR.symm (coordinateMap ρ b χ))
    rw [coordinateMap_equivariant, permTorus_equiv_symm_galois]
  have hFi : Function.Injective F :=
    eR.symm.injective.comp (coordinateMap_injective ρ b)
  obtain ⟨φ, hφ, -⟩ := hTE.existsUnique_hom_of_equivariant_characterMap F hF
  let q : WeilGm.groupScheme (CommRingCat.of k) (∀ j, topFamily k E J j) ⟶ T :=
    CommGroupScheme.groupHom φ
  have hqE : Function.Injective
      (characterLattice.comapHom (CommGroupScheme.groupHom (bc.map φ))) := by
    intro χ ψ h
    apply hFi
    exact (hφ χ).symm.trans (h.trans (hφ ψ))
  obtain ⟨hf, hs⟩ := hRE.flat_and_surjective_of_injective_characterPullback hTE
    (CommGroupScheme.groupHom (bc.map φ)) hqE
  let B := ∀ j, topFamily k E J j
  have : Algebra.FormallyEtale k (⊤ : IntermediateField k E) :=
    Algebra.FormallyEtale.of_isSeparable k _
  have : Algebra.Etale k (⊤ : IntermediateField k E) :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  have : Algebra.Etale k B := inferInstance
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, q, ?_⟩
  let a := algebraBaseMap k E
  have : Surjective a := (fieldExtension_fpqc k E).1
  have : Flat a := (fieldExtension_fpqc k E).2.1
  have : QuasiCompact a := (fieldExtension_fpqc k E).2.2
  have hp := baseChange_map_isPullback a q
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (pullback.fst T.X.hom a) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact ⟨MorphismProperty.of_isPullback_of_descendsAlong hp hQ hf,
    MorphismProperty.of_isPullback_of_descendsAlong hp hQ hs⟩

end Langlands.GroupScheme
