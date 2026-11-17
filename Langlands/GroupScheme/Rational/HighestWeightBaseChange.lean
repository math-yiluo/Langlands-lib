import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterBaseChange
import Langlands.GroupScheme.Reductive.PinningFieldBaseChange
import Langlands.GroupScheme.Rational.DominantHighestWeight

/-! # Highest-weight spaces under arbitrary field extension -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace MatrixRepresentation

/-- Scalar extension commutes with restriction along an actual group morphism. -/
theorem baseChange_restrict {R R' : CommRingCat.{u}}
    {G H : GroupScheme (Spec R)} {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (f : H ⟶ G) (b : Spec R' ⟶ Spec R) :
    (ρ.restrict f).baseChange b =
      (ρ.baseChange b).restrict ((GroupScheme.baseChange b).map f) := by
  simp only [restrict, baseChange, Functor.map_comp, Category.assoc]

end MatrixRepresentation

namespace SplitPinning

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : SplitPinning G) {n : ℕ}

local notation "bc" => algebraBaseMap k K

local instance highestWeightBaseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange bc).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom bc)
  infer_instance

local instance highestWeightTorusAffine : IsAffineHom p.torus.toGrp.X.hom :=
  p.isSplitTorus.isAffineHom

local instance highestWeightChangedTorusAffine :
    IsAffineHom (((CommGroupScheme.baseChange bc).obj p.torus).toGrp).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd p.torus.toGrp.X.hom bc)
  infer_instance

local instance highestWeightChangedGroupAffine :
    IsAffineHom ((GroupScheme.baseChange bc).obj p.torus.toGrp).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd p.torus.toGrp.X.hom bc)
  infer_instance

/-- Canonical character pullback carries the positive-root monoid to the new one. -/
theorem map_positiveRootMonoid_baseChangeField :
    p.positiveRootMonoid.map (characterLattice.baseChange bc p.torus) =
      (p.baseChangeField (K := K)).positiveRootMonoid := by
  change (AddSubmonoid.closure
    (Set.range (fun a : p.base.support => p.rootDatum.root a))).map
      (characterLattice.baseChange bc p.torus) =
    AddSubmonoid.closure (Set.range (fun a : (p.baseChangeBase (F := K)).support =>
      (p.baseChangeRootDatum (F := K)).root a))
  rw [AddMonoidHom.map_mclosure]
  apply congrArg AddSubmonoid.closure
  ext χ
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨p.baseChangeSimpleEquiv (F := K) a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨p.rootDatum.root ((p.baseChangeSimpleEquiv (F := K)).symm a),
      ⟨(p.baseChangeSimpleEquiv (F := K)).symm a, rfl⟩, rfl⟩

/-- Positivity of a character is preserved and reflected under every field extension. -/
theorem mem_positiveRootMonoid_baseChangeField_iff (χ : characterLattice p.torus) :
    characterLattice.baseChange bc p.torus χ ∈
      (p.baseChangeField (K := K)).positiveRootMonoid ↔ χ ∈ p.positiveRootMonoid := by
  rw [← map_positiveRootMonoid_baseChangeField (K := K) p]
  constructor
  · rintro ⟨ψ, hψ, heq⟩
    exact (p.isSplitTorus.characterLattice_baseChange_bijective bc p.torus).injective heq ▸ hψ
  · intro hχ
    exact ⟨χ, hχ, rfl⟩

/-- Dominance is preserved and reflected by the canonical character-lattice pullback. -/
theorem isDominantWeight_baseChangeField_iff (lam : characterLattice p.torus) :
    (p.baseChangeField (K := K)).IsDominantWeight
        (characterLattice.baseChange bc p.torus lam) ↔ p.IsDominantWeight lam := by
  constructor
  · intro h a
    have ha := h (p.baseChangeSimpleEquiv (F := K) a)
    change 0 ≤ (SplitRootDatum.baseChange bc p.torus p.isSplitTorus p.rootDatum).toLinearMap
      (characterLattice.baseChange bc p.torus lam)
      (cocharacterLattice.baseChange bc p.torus (p.rootDatum.coroot a)) at ha
    rwa [SplitRootDatum.baseChange_pairing] at ha
  · intro h a
    obtain ⟨b, rfl⟩ := (p.baseChangeSimpleEquiv (F := K)).surjective a
    change 0 ≤ (SplitRootDatum.baseChange bc p.torus p.isSplitTorus p.rootDatum).toLinearMap
      (characterLattice.baseChange bc p.torus lam)
      (cocharacterLattice.baseChange bc p.torus (p.rootDatum.coroot b))
    rw [SplitRootDatum.baseChange_pairing]
    exact h b

/-- The actual pinning weight space agrees with the scalar-extended restricted character space. -/
theorem representationWeightSpace_baseChangeField_eq_latticeCharacterSpace
    (ρ : MatrixRepresentation G (Fin n)) (lam : characterLattice p.torus) :
    (p.baseChangeField (K := K)).representationWeightSpace (ρ.baseChange bc)
        (characterLattice.baseChange bc p.torus lam) =
      ((ρ.restrict p.inclusion).baseChange bc).latticeCharacterSpace
        (characterLattice.baseChange bc p.torus lam) := by
  change ((ρ.baseChange bc).restrict ((GroupScheme.baseChange bc).map p.inclusion)).characterSpace _ = _
  rw [← MatrixRepresentation.baseChange_restrict]
  rfl

/-- Tensor extension gives the actual weight space of the base-changed split pinning. -/
def representationWeightSpaceBaseChangeFieldEquiv
    (ρ : MatrixRepresentation G (Fin n)) (lam : characterLattice p.torus) :
    K ⊗[k] p.representationWeightSpace ρ lam ≃ₗ[K]
      (p.baseChangeField (K := K)).representationWeightSpace (ρ.baseChange bc)
        (characterLattice.baseChange bc p.torus lam) :=
  (MatrixRepresentation.latticeCharacterSpaceBaseChangeEquiv
    (K := K) p.isSplitTorus (ρ.restrict p.inclusion) lam).trans
      (LinearEquiv.ofEq _ _
        (representationWeightSpace_baseChangeField_eq_latticeCharacterSpace (K := K) p ρ lam).symm)

/-- Every weight multiplicity is preserved by field extension. -/
theorem finrank_representationWeightSpace_baseChangeField
    (ρ : MatrixRepresentation G (Fin n)) (lam : characterLattice p.torus) :
    Module.finrank K ((p.baseChangeField (K := K)).representationWeightSpace (ρ.baseChange bc)
        (characterLattice.baseChange bc p.torus lam)) =
      Module.finrank k (p.representationWeightSpace ρ lam) := by
  rw [← (representationWeightSpaceBaseChangeFieldEquiv (K := K) p ρ lam).finrank_eq,
    Module.finrank_baseChange]

/-- The nonzero weight support is preserved and reflected by field extension. -/
theorem representationWeightSpace_baseChangeField_ne_bot_iff
    (ρ : MatrixRepresentation G (Fin n)) (lam : characterLattice p.torus) :
    (p.baseChangeField (K := K)).representationWeightSpace (ρ.baseChange bc)
        (characterLattice.baseChange bc p.torus lam) ≠ ⊥ ↔
      p.representationWeightSpace ρ lam ≠ ⊥ := by
  have hdim := finrank_representationWeightSpace_baseChangeField (K := K) p ρ lam
  exact not_congr (Submodule.finrank_eq_zero.symm.trans
    ((iff_of_eq (congrArg (fun d : ℕ => d = 0) hdim)).trans Submodule.finrank_eq_zero))

/-- A highest weight is preserved as soon as the extended representation is irreducible. -/
theorem IsHighestWeight.baseChangeField_of_isIrreducible
    {p : SplitPinning G} {ρ : MatrixRepresentation G (Fin n)}
    {lam : characterLattice p.torus} (hρ : p.IsHighestWeight ρ lam)
    (hirr : (ρ.baseChange bc).IsIrreducible) :
    (p.baseChangeField (K := K)).IsHighestWeight (ρ.baseChange bc)
      (characterLattice.baseChange bc p.torus lam) := by
  refine ⟨hirr, (p.baseChangeField (K := K)).iSup_representationWeightSpace_eq_top (ρ.baseChange bc),
    ?_, ?_⟩
  · exact (finrank_representationWeightSpace_baseChangeField (K := K) p ρ lam).trans hρ.2.2.1
  · intro mu hmu
    obtain ⟨ν, rfl⟩ :=
      (p.isSplitTorus.characterLattice_baseChange_bijective bc p.torus).surjective mu
    have hν := (representationWeightSpace_baseChangeField_ne_bot_iff (K := K) p ρ ν).mp hmu
    have hpos := (mem_positiveRootMonoid_baseChangeField_iff (K := K) p (lam - ν)).mpr
      (hρ.2.2.2 ν hν)
    simpa only [map_sub] using hpos

section Algebraic

variable [Algebra.IsAlgebraic k K]

/-- Algebraic-extension specialization of the actual weight-space comparison. -/
theorem representationWeightSpace_baseChange_eq_latticeCharacterSpace
    (ρ : MatrixRepresentation G (Fin n)) (lam : characterLattice p.torus) :
    (p.baseChange (F := K)).representationWeightSpace (ρ.baseChange bc)
        (characterLattice.baseChange bc p.torus lam) =
      ((ρ.restrict p.inclusion).baseChange bc).latticeCharacterSpace
        (characterLattice.baseChange bc p.torus lam) :=
  representationWeightSpace_baseChangeField_eq_latticeCharacterSpace (K := K) p ρ lam

/-- The tensor equivalence for the published algebraic-extension pinning. -/
def representationWeightSpaceBaseChangeEquiv
    (ρ : MatrixRepresentation G (Fin n)) (lam : characterLattice p.torus) :
    K ⊗[k] p.representationWeightSpace ρ lam ≃ₗ[K]
      (p.baseChange (F := K)).representationWeightSpace (ρ.baseChange bc)
        (characterLattice.baseChange bc p.torus lam) :=
  representationWeightSpaceBaseChangeFieldEquiv (K := K) p ρ lam

/-- Algebraic-extension specialization of weight multiplicity preservation. -/
theorem finrank_representationWeightSpace_baseChange
    (ρ : MatrixRepresentation G (Fin n)) (lam : characterLattice p.torus) :
    Module.finrank K ((p.baseChange (F := K)).representationWeightSpace (ρ.baseChange bc)
        (characterLattice.baseChange bc p.torus lam)) =
      Module.finrank k (p.representationWeightSpace ρ lam) :=
  finrank_representationWeightSpace_baseChangeField (K := K) p ρ lam

/-- Algebraic-extension specialization of nonzero weight-support comparison. -/
theorem representationWeightSpace_baseChange_ne_bot_iff
    (ρ : MatrixRepresentation G (Fin n)) (lam : characterLattice p.torus) :
    (p.baseChange (F := K)).representationWeightSpace (ρ.baseChange bc)
        (characterLattice.baseChange bc p.torus lam) ≠ ⊥ ↔
      p.representationWeightSpace ρ lam ≠ ⊥ :=
  representationWeightSpace_baseChangeField_ne_bot_iff (K := K) p ρ lam

/-- A highest weight for the published algebraic pullback follows from extended irreducibility. -/
theorem IsHighestWeight.baseChange_of_isIrreducible
    {p : SplitPinning G} {ρ : MatrixRepresentation G (Fin n)}
    {lam : characterLattice p.torus} (hρ : p.IsHighestWeight ρ lam)
    (hirr : (ρ.baseChange bc).IsIrreducible) :
    (p.baseChange (F := K)).IsHighestWeight (ρ.baseChange bc)
      (characterLattice.baseChange bc p.torus lam) :=
  hρ.baseChangeField_of_isIrreducible hirr

end Algebraic

end SplitPinning
end Langlands.GroupScheme
