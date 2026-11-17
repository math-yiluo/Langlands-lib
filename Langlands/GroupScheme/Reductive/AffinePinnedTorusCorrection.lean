import Langlands.GroupScheme.Reductive.AffinePinnedAffineExistence

/-! # Pinned correction by a target torus section -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable (N : AffinePinnedModel.{u}) (A : Type u) [CommRing A] [Algebra N.ring A]
  {W : Scheme.{u}} (p : W ⟶ Spec (CommRingCat.of A))

/-- A torus point over the cover, in the normalized split torus over that cover. -/
def normalizedTorusBasePoint
    (t : Over.mk p ⟶ (splitTorus (Spec (CommRingCat.of A)) N.coordinates).X) :
    Over.mk (𝟙 W) ⟶ (splitTorus W N.coordinates).X :=
  (baseChangeBasePointsEquiv p (splitTorus (Spec (CommRingCat.of A)) N.coordinates)).symm t ≫
    (splitTorus.baseChangeIso p N.coordinates).hom.hom.hom

/-- The image of the normalized torus section has exactly the supplied
scalar-model point under the normalized projection. -/
theorem normalizedTorusBasePoint_image
    (t : Over.mk p ⟶ (splitTorus (Spec (CommRingCat.of A)) N.coordinates).X) :
    normalizedTorusBasePoint N A p t ≫ (N.inclusionOver
      (p ≫ algebraBaseMap N.ring A)).hom.hom =
      (normalizedBasePointsEquiv N A p).symm
        (t ≫ (N.inclusionOver (algebraBaseMap N.ring A)).hom.hom) := by
  apply (normalizedBasePointsEquiv N A p).injective
  rw [MulEquiv.apply_symm_apply]
  rw [← N.inclusionOver_pull (algebraBaseMap N.ring A) p]
  simp only [normalizedTorusBasePoint, BasedBorelTransport.baseChangeInclusion,
    Grp.comp_hom_hom, Category.assoc]
  apply Over.OverMorphism.ext
  rw [normalizedBasePointsEquiv_left]
  simp only [Over.comp_left, Category.assoc]
  rw [← Category.assoc
    (baseChangeCompIso (algebraBaseMap N.ring A) p N.group).inv.hom.hom.left,
    ← Over.comp_left, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom]
  simp only [Over.id_left, Category.id_comp]
  have hs := congrArg (fun k => k.hom.hom.left)
    (splitTorus.baseChangeIso p N.coordinates).hom_inv_id
  simp only [Grp.comp_hom_hom, Over.comp_left, Grp.id_hom_hom, Over.id_left] at hs
  erw [reassoc_of% hs]
  have hm : ((baseChange p).map (N.inclusionOver (algebraBaseMap N.ring A))).hom.hom.left ≫
      pullback.fst (N.groupOver (algebraBaseMap N.ring A)).X.hom p =
    pullback.fst (splitTorus (Spec (CommRingCat.of A)) N.coordinates).X.hom p ≫
      (N.inclusionOver (algebraBaseMap N.ring A)).hom.hom.left := by
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    exact pullback.lift_fst _ _ _
  rw [hm, ← Category.assoc,
    ← baseChangeBasePointsEquiv_left, MulEquiv.apply_symm_apply]

/-- A section of the normalized target torus acts trivially on that torus. -/
theorem inclusionOver_comp_torusInner
    (f : W ⟶ N.base)
    (t : Over.mk (𝟙 W) ⟶ (splitTorus W N.coordinates).X) :
    N.inclusionOver f ≫ ((N.groupOver f).innerIso
      (t ≫ (N.inclusionOver f).hom.hom)).hom = N.inclusionOver f := by
  rw [← innerIso_hom_comp]
  have hi : ((splitTorus W N.coordinates).innerIso t).hom = 𝟙 _ := by
    apply hom_ext_points
    intro U x
    rw [comp_innerIso_hom]
    apply (splitTorus.pointsEquiv N.coordinates U).injective
    simp only [map_mul, map_inv, Grp.id_hom_hom, Category.comp_id]
    rw [mul_comm (splitTorus.pointsEquiv N.coordinates U
      ((splitTorus W N.coordinates).constantPoint t U)), mul_assoc,
      mul_inv_cancel, mul_one]
  rw [hi, Category.id_comp]

/-- Target torus conjugation preserves both the actual torus and the canonical
positive-coroot cocharacter. -/
theorem torusInner_preserves
    (f : W ⟶ N.base)
    (t : Over.mk (𝟙 W) ⟶ (splitTorus W N.coordinates).X) :
    PreservesTorus ((N.groupOver f).innerIso
      (t ≫ (N.inclusionOver f).hom.hom)) ∧
    PreservesCocharacter ((N.groupOver f).innerIso
      (t ≫ (N.inclusionOver f).hom.hom)) := by
  have hi := inclusionOver_comp_torusInner N f t
  refine ⟨⟨Iso.refl _, ?_⟩, ?_⟩
  · simpa using hi
  · change (BasedBorelTransport.cocharacter (N.inclusionOver f) N.rootDatum N.basis) ≫
      ((N.groupOver f).innerIso (t ≫ (N.inclusionOver f).hom.hom)).hom = _
    unfold BasedBorelTransport.cocharacter
    rw [Category.assoc, hi]
    rfl

/-- An aligned affine comparison admits an actual fppf target correction that
preserves the torus, the cocharacter, and all local pinning vectors. -/
theorem exists_fppf_pinnedCorrection_of_aligned
    (M N : AffinePinnedModel.{u}) (A : Type u) [CommRing A]
    [Algebra M.ring A] [Algebra N.ring A]
    (τ : splitTorus.commGroupScheme (Spec (CommRingCat.of A)) M.coordinates ≅
      splitTorus.commGroupScheme (Spec (CommRingCat.of A)) N.coordinates)
    (e : Comparison (algebraBaseMap M.ring A) (algebraBaseMap N.ring A))
    (hτ : M.inclusionOver (algebraBaseMap M.ring A) ≫ e.hom =
      CommGroupScheme.groupHom τ.hom ≫ N.inclusionOver (algebraBaseMap N.ring A))
    (σ : M.basis.support ≃ N.basis.support)
    (hχ : ∀ s : M.basis.support,
      characterLattice.congr τ
        (splitTorus.exponentCharacter (Spec (CommRingCat.of A)) M.coordinates
          (M.rootDatum.root s)) =
        splitTorus.exponentCharacter (Spec (CommRingCat.of A)) N.coordinates
          (N.rootDatum.root (σ s)))
    (hcochar : PreservesCocharacter e) :
    ∃ (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of A))
      (z : Over.mk (𝟙 W) ⟶ (N.groupOver (p ≫ algebraBaseMap N.ring A)).X),
      Flat p ∧ Surjective p ∧ LocallyOfFinitePresentation p ∧
      IsLocallyPinned (pullComparison e p ≪≫
        (N.groupOver (p ≫ algebraBaseMap N.ring A)).innerIso z) := by
  let c := pinningUnitDiscrepancies M N A τ e hτ σ hχ
  have hc := pinningUnitDiscrepancies_spec M N A τ e hτ σ hχ
  obtain ⟨W, p, t, hf, hs, hl, ht⟩ :=
    exists_fppf_inverse_simpleRoot_values N A (fun s => c (σ.symm s))
  let z := (normalizedBasePointsEquiv N A p).symm
    (t ≫ (N.inclusionOver (algebraBaseMap N.ring A)).hom.hom)
  have hp : PreservesLocalPinning (pullComparison e p ≪≫
      (N.groupOver (p ≫ algebraBaseMap N.ring A)).innerIso z) :=
    preservesLocalPinning_corrected M A p e σ c hc t (by
      intro B _ _ a hA s
      simpa only [Equiv.symm_apply_apply] using ht B a hA (σ s))
  have hi := torusInner_preserves N (p ≫ algebraBaseMap N.ring A)
    (normalizedTorusBasePoint N A p t)
  rw [normalizedTorusBasePoint_image] at hi
  let τg : splitTorus (Spec (CommRingCat.of A)) M.coordinates ≅
      splitTorus (Spec (CommRingCat.of A)) N.coordinates :=
    { hom := CommGroupScheme.groupHom τ.hom
      inv := CommGroupScheme.groupHom τ.inv
      hom_inv_id := congrArg Additive.toMul τ.hom_inv_id
      inv_hom_id := congrArg Additive.toMul τ.inv_hom_id }
  have heT : PreservesTorus e := ⟨τg, hτ⟩
  exact ⟨W, p, z, hf, hs, hl, (heT.pull p).trans hi.1, (hcochar.pull p).trans hi.2, hp⟩

/-- The affine geometric correction input, with the alignment hypotheses made
explicit on the actual torus and simple characters. -/
def AlignedAffinePinnedCorrectionStatement : Prop :=
  ∀ (M N : AffinePinnedModel.{u}) (A : Type u) [CommRing A]
    [Algebra M.ring A] [Algebra N.ring A]
    (τ : splitTorus.commGroupScheme (Spec (CommRingCat.of A)) M.coordinates ≅
      splitTorus.commGroupScheme (Spec (CommRingCat.of A)) N.coordinates)
    (e : Comparison (algebraBaseMap M.ring A) (algebraBaseMap N.ring A)),
    (M.inclusionOver (algebraBaseMap M.ring A) ≫ e.hom =
      CommGroupScheme.groupHom τ.hom ≫ N.inclusionOver (algebraBaseMap N.ring A)) →
    ∀ σ : M.basis.support ≃ N.basis.support,
    (∀ s : M.basis.support,
      characterLattice.congr τ
        (splitTorus.exponentCharacter (Spec (CommRingCat.of A)) M.coordinates
          (M.rootDatum.root s)) =
        splitTorus.exponentCharacter (Spec (CommRingCat.of A)) N.coordinates
          (N.rootDatum.root (σ s))) →
    PreservesCocharacter e →
    ∃ (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of A))
      (z : Over.mk (𝟙 W) ⟶ (N.groupOver (p ≫ algebraBaseMap N.ring A)).X),
      Flat p ∧ Surjective p ∧ LocallyOfFinitePresentation p ∧
      IsLocallyPinned (pullComparison e p ≪≫
        (N.groupOver (p ≫ algebraBaseMap N.ring A)).innerIso z)

theorem alignedAffinePinnedCorrectionStatement : AlignedAffinePinnedCorrectionStatement.{u} :=
  fun M N A _ _ _ τ e hτ σ hχ hcochar =>
    exists_fppf_pinnedCorrection_of_aligned M N A τ e hτ σ hχ hcochar

end Langlands.GroupScheme.AffinePinnedModel
