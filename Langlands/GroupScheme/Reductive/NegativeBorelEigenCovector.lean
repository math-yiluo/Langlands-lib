import Langlands.GroupScheme.Reductive.SplitBorelCell
import Langlands.GroupScheme.MatrixRepresentation.NormalFixedRepresentation
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.Reductive.CovariantRegularWeights
import Langlands.GroupScheme.HopfPrimitiveQuotient
import Langlands.GroupScheme.Dynamic.SplitContractingSubgroup
import Langlands.GroupScheme.Reductive.EigenMatrixCoefficient

/-! # Eigen-covectors of the negative Borel subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)
    {n : Type} [Fintype n] [DecidableEq n]

local instance negativeBorelEigenCovectorInst1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- The negative unipotent subgroup `U_G(ν⁻¹)` contracted by the reversed positive
cocharacter. -/
abbrev negativeUnipotent : GroupScheme (Spec (CommRingCat.of k)) :=
  Dynamic.Affine.unipotentScheme (Dynamic.oppositeCocharacter p.positiveGm)

local instance negativeBorelEigenCovectorInst2 : IsAffineHom p.negativeUnipotent.X.hom :=
  (Dynamic.Affine.isClosedSubgroup_unipotentHom _).isAffineHom

local instance negativeBorelEigenCovectorInst3 : IsAffineHom p.torus.toGrp.X.hom :=
  p.isSplitTorus.isAffineHom

/-- The negative unipotent subgroup as the kernel of the limit map on the negative
Borel subgroup. -/
def negativeUnipotentToBorel : p.negativeUnipotent ⟶ p.negativeBorel :=
  (Dynamic.unipotentIsoKernel (hP := p.isRepresentedBy_negativeBorelHom)
    (hZ := p.isRepresentedBy_centralizer_opposite)
    (Dynamic.Affine.isRepresentedBy_unipotentHom _)).hom ≫ kernelι p.negativeBorelToTorus

/-- The negative unipotent subgroup has the same points as the kernel of the limit map. -/
theorem range_negativeUnipotentToBorel :
    SubgroupFunctor.range p.negativeUnipotentToBorel =
      SubgroupFunctor.range (kernelι p.negativeBorelToTorus) :=
  SubgroupFunctor.range_iso_comp _ _

/-- The negative unipotent subgroup is normal in the negative Borel subgroup. -/
theorem isNormal_range_negativeUnipotentToBorel :
    (SubgroupFunctor.range p.negativeUnipotentToBorel).IsNormal := by
  rw [range_negativeUnipotentToBorel]
  exact HopfPrimitive.isNormal_range_kernelι _

/-- The negative unipotent subgroup is unipotent. -/
theorem isUnipotent_negativeUnipotent : IsUnipotent p.negativeUnipotent := by
  have := p.isConnectedReductive.smooth
  exact Dynamic.isUnipotent_of_isRepresentedBy_unipotent _
    (Dynamic.Affine.isRepresentedBy_unipotentHom _)
    (Dynamic.Affine.isClosedSubgroup_unipotentHom _)

/-- Every point of the negative Borel subgroup is its torus part times a point of the
negative unipotent subgroup. -/
theorem exists_negativeUnipotent_factor (T : Over (Spec (CommRingCat.of k)))
    (b : T ⟶ p.negativeBorel.X) :
    ∃ y : T ⟶ p.negativeUnipotent.X,
      (b ≫ p.negativeBorelToTorus.hom.hom ≫ p.torusToNegativeBorel.hom.hom) *
        (y ≫ p.negativeUnipotentToBorel.hom.hom) = b := by
  set t := b ≫ p.negativeBorelToTorus.hom.hom ≫ p.torusToNegativeBorel.hom.hom with ht_def
  have hsec : p.torusToNegativeBorel.hom.hom ≫ p.negativeBorelToTorus.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) p.torusToNegativeBorel_comp_negativeBorelToTorus
  have ht : t ≫ p.negativeBorelToTorus.hom.hom = b ≫ p.negativeBorelToTorus.hom.hom := by
    rw [ht_def, Category.assoc, Category.assoc, hsec, Category.comp_id]
  have hu : (t⁻¹ * b) ≫ p.negativeBorelToTorus.hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, ht, inv_mul_cancel]
  have hmem : t⁻¹ * b ∈ (SubgroupFunctor.range p.negativeUnipotentToBorel).carrier T := by
    rw [range_negativeUnipotentToBorel, mem_range_kernelι_iff]
    exact hu
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hmem
  exact ⟨y, by rw [hy, mul_inv_cancel_left]⟩

/-- Every nonempty finite representation has a nonzero covector on which the negative
Borel subgroup acts, on every test scheme, through the extension of a torus character. -/
theorem exists_negativeBorel_eigenCovector [Nonempty n] (ρ : MatrixRepresentation G n) :
    ∃ (ξ : n → k) (lam : characterLattice p.torus), ξ ≠ 0 ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ p.negativeBorel.X),
        (fun a => scalarMap T (ξ a)) ᵥ*
            (ρ.pointMatrix T (h ≫ p.negativeBorelHom.hom.hom) : Matrix n n Γ(T.left, ⊤)) =
          AffineCoordinates.pointValue p.negativeBorel T h (p.borelCharacterCoordinate lam) •
            fun a => scalarMap T (ξ a) := by
  classical
  let σ := ρ.dual.restrict p.negativeBorelHom
  let D := MatrixRepresentation.normalFixedSubrepresentation σ p.negativeUnipotentToBorel
    p.isNormal_range_negativeUnipotentToBorel
  obtain ⟨v, hv0, hv⟩ := p.isUnipotent_negativeUnipotent n (σ.restrict p.negativeUnipotentToBorel)
  have hd : Nontrivial (Fin D.dimension → k) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    apply hv0
    rw [← D.projection v hv, ← Matrix.mulVec_mulVec, Subsingleton.elim (D.retraction *ᵥ v) 0,
      Matrix.mulVec_zero]
  let τ := D.representation.restrict p.torusToNegativeBorel
  have htop := MatrixRepresentation.iSup_characterSpace_eq_top_of_isSplitTorus p.isSplitTorus τ
  obtain ⟨χ, hχ⟩ : ∃ χ, τ.characterSpace χ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    rw [iSup_eq_bot.mpr hcon] at htop
    exact bot_ne_top htop
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  -- The fixed-space representation acts on `w` through the extended character.
  have hD : ∀ (T : Over (Spec (CommRingCat.of k))) (b : T ⟶ p.negativeBorel.X),
      (D.representation.pointMatrix T b : Matrix _ _ Γ(T.left, ⊤)) *ᵥ
          (fun r => scalarMap T (w r)) =
        (characterEval (characterRestrict p.negativeBorelToTorus χ) T b : Γ(T.left, ⊤)) •
          fun r => scalarMap T (w r) := by
    intro T b
    obtain ⟨y, hy⟩ := p.exists_negativeUnipotent_factor T b
    have hk := D.kills_subgroup T y
    have ht := MatrixRepresentation.characterSpace_points hw T (b ≫ p.negativeBorelToTorus.hom.hom)
    rw [MatrixRepresentation.pointMatrix_restrict, Category.assoc] at ht
    have hb : D.representation.pointMatrix T b = D.representation.pointMatrix T
        (b ≫ p.negativeBorelToTorus.hom.hom ≫ p.torusToNegativeBorel.hom.hom) := by
      conv_lhs => rw [← hy]
      rw [map_mul, hk, mul_one]
    rw [characterEval_characterRestrict, hb]
    exact ht
  -- Its image in the dual coordinates.
  let eta := D.inclusion *ᵥ w
  have heta : ∀ T : Over (Spec (CommRingCat.of k)),
      (fun r => scalarMap T (eta r)) =
        D.inclusion.map (scalarMap T) *ᵥ fun j => scalarMap T (w j) := by
    intro T
    funext r
    exact (scalarMap T).map_mulVec _ _ _
  have hσ : ∀ (T : Over (Spec (CommRingCat.of k))) (b : T ⟶ p.negativeBorel.X),
      (σ.pointMatrix T b : Matrix n n Γ(T.left, ⊤)) *ᵥ (fun r => scalarMap T (eta r)) =
        (characterEval (characterRestrict p.negativeBorelToTorus χ) T b : Γ(T.left, ⊤)) •
          fun r => scalarMap T (eta r) := by
    intro T b
    rw [heta, Matrix.mulVec_mulVec, D.intertwines T b, ← Matrix.mulVec_mulVec, hD T b,
      Matrix.mulVec_smul]
  have heta0 : eta ≠ 0 := by
    intro h0
    apply hw0
    have h1 : D.retraction *ᵥ eta = w := by
      change D.retraction *ᵥ (D.inclusion *ᵥ w) = w
      rw [Matrix.mulVec_mulVec, D.left_inverse, Matrix.one_mulVec]
    rw [← h1, h0, Matrix.mulVec_zero]
  refine ⟨eta, -(rationalCharacters.equivCharacterLattice p.torus χ), heta0, ?_⟩
  intro T h
  have hlam : p.borelCharacter (-(rationalCharacters.equivCharacterLattice p.torus χ)) =
      -characterRestrict p.negativeBorelToTorus χ := by
    rw [borelCharacter, AddEquiv.map_neg, AddEquiv.symm_apply_apply, map_neg]
  have h1 := hσ T h⁻¹
  rw [MatrixRepresentation.pointMatrix_restrict, MatrixRepresentation.dual_pointMatrix,
    GrpObj.inv_comp, map_inv, map_inv] at h1
  change ((ρ.pointMatrix T (h ≫ p.negativeBorelHom.hom.hom) : Matrix n n Γ(T.left, ⊤))ᵀ) *ᵥ
      _ = _ at h1
  rw [Matrix.mulVec_transpose, map_inv] at h1
  rw [AffineCoordinates.pointValue, p.pointAlgebraHom_borelCharacterCoordinate, hlam,
    characterEval_neg]
  exact h1

end SplitPinning

end Langlands.GroupScheme
