import Langlands.GroupScheme.MatrixRepresentation.NormalCharacterSpan
import Langlands.GroupScheme.Rational.FundamentalRepresentations
import Langlands.GroupScheme.Rational.SteinbergRootProduct
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Rational.SubquotientSpectralIntegrality

/-! # Actual normalizer matrices on universal torus character spaces -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    {σ : T ≅ T} (hg : IsNormalizingPoint i g σ)

include hg

/-- Normalizer matrices intertwine the torus action with its inverse transport. -/
theorem affineMatrix_normalizer_commutation (A : CommAlgCat.{u} k)
    (t : GroupScheme.affinePoints T.toGrp A) :
    ((ρ.restrict i).affineMatrix A t : Matrix n n A) *
        ((ρ.rationalMatrix g : Matrix n n k).map (algebraMap k A)) =
      ((ρ.rationalMatrix g : Matrix n n k).map (algebraMap k A)) *
        ((ρ.restrict i).affineMatrix A
          (t ≫ (CommGroupScheme.groupHom σ.inv).hom.hom) : Matrix n n A) := by
  let t' := t ≫ (CommGroupScheme.groupHom σ.inv).hom.hom
  have hσ : (CommGroupScheme.groupHom σ.inv).hom.hom ≫
      (CommGroupScheme.groupHom σ.hom).hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom]
    exact (congrArg (fun f => (CommGroupScheme.groupHom f).hom.hom) σ.inv_hom_id).trans
      (Grp.id_hom_hom _)
  have hpt := hg.conj_comp ((algSpec (CommRingCat.of k)).obj (op A)) t'
  have hcomp : (t' ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) ≫ i.hom.hom =
      t ≫ i.hom.hom := by
    simp only [t', Category.assoc, hσ, Category.id_comp]
  rw [hcomp] at hpt
  have h := congrArg (ρ.affineMatrix A) hpt
  simp only [map_mul, map_inv] at h
  have hmul := ((mul_inv_eq_iff_eq_mul).mp h).symm
  rw [affineMatrix_constantPoint] at hmul
  exact congrArg Units.val hmul

variable [IsAffineHom T.X.hom]

/-- A rational normalizing point carries an actual torus weight to its Weyl transport. -/
theorem rationalMatrix_mem_characterSpace (lam : characterLattice T) {v : n → k}
    (hv : v ∈ (ρ.restrict i).characterSpace
      ((rationalCharacters.equivCharacterLattice T).symm lam)) :
    (ρ.rationalMatrix g : Matrix n n k) *ᵥ v ∈ (ρ.restrict i).characterSpace
      ((rationalCharacters.equivCharacterLattice T).symm (characterAut σ lam)) := by
  let A := CharacterUnits.Coord T.toGrp
  let H := ρ.restrict i
  let B := (ρ.rationalMatrix g : Matrix n n k)
  let t : GroupScheme.affinePoints T.toGrp (CommAlgCat.of k A) :=
    CharacterUnits.universalPoint T.toGrp
  let t' : GroupScheme.affinePoints T.toGrp (CommAlgCat.of k A) :=
    t ≫ (CommGroupScheme.groupHom σ.inv).hom.hom
  have hv' := characterSpace_affine hv (CommAlgCat.of k A) t'
  have hchar : (Lie.characterValue lam t' : A) =
      (CharacterUnits.unit
        ((rationalCharacters.equivCharacterLattice T).symm (characterAut σ lam)) : A) := by
    rw [show t' = t ≫ (CommGroupScheme.groupHom σ.inv).hom.hom from rfl,
      ← Lie.characterValue_comp]
    rfl
  change (H.affineMatrix (CommAlgCat.of k A) t' : Matrix n n A) *ᵥ
      universalVector v = (Lie.characterValue lam t' : A) • universalVector v at hv'
  have hcov := ρ.affineMatrix_normalizer_commutation i hg (CommAlgCat.of k A) t
  change H.universalCharacterMatrix * B.map (algebraMap k A) =
    B.map (algebraMap k A) * (H.affineMatrix (CommAlgCat.of k A) t' : Matrix n n A) at hcov
  have hmap : universalVector (B *ᵥ v) =
      B.map (algebraMap k A) *ᵥ universalVector v := by
    funext j
    exact (algebraMap k A).map_mulVec B v j
  change H.universalCharacterMatrix *ᵥ universalVector (B *ᵥ v) =
    (CharacterUnits.unit
      ((rationalCharacters.equivCharacterLattice T).symm (characterAut σ lam)) : A) •
        universalVector (B *ᵥ v)
  rw [hmap, Matrix.mulVec_mulVec, hcov, ← Matrix.mulVec_mulVec, hv',
    Matrix.mulVec_smul, hchar]


/-- Restrict the actual rational normalizer matrix to its transported character spaces. -/
def normalizerWeightMap (lam : characterLattice T) :
    (ρ.restrict i).characterSpace ((rationalCharacters.equivCharacterLattice T).symm lam) →ₗ[k]
      (ρ.restrict i).characterSpace
        ((rationalCharacters.equivCharacterLattice T).symm (characterAut σ lam)) where
  toFun v := ⟨(ρ.rationalMatrix g : Matrix n n k) *ᵥ v,
    ρ.rationalMatrix_mem_characterSpace i hg lam v.property⟩
  map_add' v w := Subtype.ext (Matrix.mulVec_add _ (v : n → k) w)
  map_smul' c v := Subtype.ext (Matrix.mulVec_smul _ c (v : n → k))

@[simp] theorem normalizerWeightMap_apply (lam : characterLattice T)
    (v : (ρ.restrict i).characterSpace ((rationalCharacters.equivCharacterLattice T).symm lam)) :
    (ρ.normalizerWeightMap i hg lam v : n → k) =
      (ρ.rationalMatrix g : Matrix n n k) *ᵥ v := rfl

/-- Rational normalizing matrices identify the original and transported weight spaces. -/
def normalizerWeightEquiv (lam : characterLattice T) :
    (ρ.restrict i).characterSpace ((rationalCharacters.equivCharacterLattice T).symm lam) ≃ₗ[k]
      (ρ.restrict i).characterSpace
        ((rationalCharacters.equivCharacterLattice T).symm (characterAut σ lam)) :=
  LinearEquiv.ofBijective (ρ.normalizerWeightMap i hg lam) (by
    constructor
    · intro v w h
      apply Subtype.ext
      apply Matrix.mulVec_injective_of_isUnit (Units.isUnit (ρ.rationalMatrix g))
      exact congrArg Subtype.val h
    · intro w
      have hinv := ρ.rationalMatrix_mem_characterSpace i hg.inv (characterAut σ lam) w.property
      simp only [characterAut_apply, Iso.symm_inv, ← Category.assoc,
        Iso.hom_inv_id, Category.id_comp] at hinv
      refine ⟨⟨(ρ.rationalMatrix g⁻¹ : Matrix n n k) *ᵥ w, hinv⟩, ?_⟩
      apply Subtype.ext
      change (ρ.rationalMatrix g : Matrix n n k) *ᵥ
        ((ρ.rationalMatrix g⁻¹ : Matrix n n k) *ᵥ (w : n → k)) = (w : n → k)
      rw [map_inv, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mulVec])

@[simp] theorem normalizerWeightEquiv_apply (lam : characterLattice T)
    (v : (ρ.restrict i).characterSpace ((rationalCharacters.equivCharacterLattice T).symm lam)) :
    (ρ.normalizerWeightEquiv i hg lam v : n → k) =
      (ρ.rationalMatrix g : Matrix n n k) *ᵥ v := rfl

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.SplitPinning.SimpleReflectionRepresentative

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {a : p.base.support}
    (s : p.SimpleReflectionRepresentative a)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)

/-- A supplied simple-reflection representative sends each actual weight to its reflection. -/
theorem rationalMatrix_mem_representationWeightSpace (lam : characterLattice p.torus)
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam) :
    (ρ.rationalMatrix s.point : Matrix n n k) *ᵥ v ∈
      p.representationWeightSpace ρ (p.rootDatum.reflection a lam) := by
  let := p.isSplitTorus.isAffineHom
  have h := ρ.rationalMatrix_mem_characterSpace p.inclusion s.normalizes lam hv
  change (ρ.rationalMatrix s.point : Matrix n n k) *ᵥ v ∈
    (ρ.restrict p.inclusion).characterSpace
      ((rationalCharacters.equivCharacterLattice p.torus).symm (p.rootDatum.reflection a lam))
  simpa only [s.characterAut_eq] using h

include s in
/-- Supplied simple reflections preserve actual weight multiplicities. -/
theorem finrank_representationWeightSpace_reflection (lam : characterLattice p.torus) :
    Module.finrank k (p.representationWeightSpace ρ (p.rootDatum.reflection a lam)) =
      Module.finrank k (p.representationWeightSpace ρ lam) := by
  let := p.isSplitTorus.isAffineHom
  have h : Module.finrank k ((ρ.restrict p.inclusion).characterSpace
      ((rationalCharacters.equivCharacterLattice p.torus).symm lam)) =
      Module.finrank k ((ρ.restrict p.inclusion).characterSpace
        ((rationalCharacters.equivCharacterLattice p.torus).symm (characterAut s.torusAut lam))) :=
    (ρ.normalizerWeightEquiv p.inclusion s.normalizes lam).finrank_eq
  rw [s.characterAut_eq] at h
  change Module.finrank k ((ρ.restrict p.inclusion).characterSpace
      ((rationalCharacters.equivCharacterLattice p.torus).symm (p.rootDatum.reflection a lam))) =
    Module.finrank k ((ρ.restrict p.inclusion).characterSpace
      ((rationalCharacters.equivCharacterLattice p.torus).symm lam))
  exact h.symm

end Langlands.GroupScheme.SplitPinning.SimpleReflectionRepresentative
