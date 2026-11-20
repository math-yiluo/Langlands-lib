import Langlands.Representation.Aubert.General.DynamicUnipotentDisplacementHaar
import Langlands.GroupScheme.Dynamic.EqualCentralizerDeterminantBalance

/-! # Relative weight formula for a radical displacement determinant -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

open RelativeRoot Dynamic.GradedCoordinates
open Langlands.Aubert.General.RationalPointFamily

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)

/-- The product over the finite actual adjoint weight support, with the
multiplicities of the weights positive on the chosen cocharacter. -/
def positiveWeightProduct {B : Type*} [CommMonoid B]
    (ζ : cocharacterLattice T) (f : characterLattice T → B) : B :=
  ∏ α ∈ (hT.finite_weightSupport i).toFinset,
    f α ^ (if 0 < latticePairing T α ζ then Module.finrank k (weightSpace i α) else 0)

section Balance

variable {i} [Mono i.hom.hom.left] (hroot : HasRelativeRootSystem i)

include hroot in
/-- Two cocharacters with the same actual centralizer give the same weighted
product for any factor invariant under weight negation. -/
theorem HasRelativeRootSystem.positiveWeightProduct_eq_of_centralizer_eq
    {B : Type*} [CommMonoid B] (ζ eta : cocharacterLattice T)
    (hEq : Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) =
      Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i))
    (f : characterLattice T → B) (hf : ∀ α, f (-α) = f α) :
    positiveWeightProduct hT i ζ f = positiveWeightProduct hT i eta f := by
  classical
  let S := (hT.finite_weightSupport i).toFinset
  let positive (τ : cocharacterLattice T) (α : characterLattice T) :=
    0 < latticePairing T α τ
  let factor (α : characterLattice T) := f α ^ Module.finrank k (weightSpace i α)
  have hprod (τ : cocharacterLattice T) :
      positiveWeightProduct hT i τ f = ∏ α ∈ S.filter (positive τ), factor α := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro α _
    by_cases hα : positive τ α <;> simp [positive, factor, hα]
  have hcommon : (S.filter (positive ζ)).filter (positive eta) =
      (S.filter (positive eta)).filter (positive ζ) := by
    rw [Finset.filter_filter, Finset.filter_filter]
    congr 1
    funext α
    exact propext (and_comm ..)
  have : FiniteDimensional k (Additive (lieKernel G k)) := Lie.finiteDimensional_lieKernel G
  have hsneg (α : characterLattice T) : α ∈ S ↔ -α ∈ S := by
    have h (β : characterLattice T) :
        weightSpace i β ≠ ⊥ ↔ Module.finrank k (weightSpace i β) ≠ 0 :=
      not_congr Submodule.finrank_eq_zero.symm
    simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, h, hroot.finrank_weightSpace_neg hT]
  have hmix :
      ∏ α ∈ (S.filter (positive ζ)).filter (fun α => ¬positive eta α), factor α =
      ∏ α ∈ (S.filter (positive eta)).filter (fun α => ¬positive ζ α), factor α := by
    apply Finset.prod_equiv (Equiv.neg (characterLattice T))
    · intro α
      simp only [Equiv.neg_apply, Finset.mem_filter, positive, ← hsneg α,
        map_neg, LinearMap.neg_apply, neg_pos]
      constructor
      · rintro ⟨⟨hα, hζ⟩, heta⟩
        have hn := latticePairing_eq_zero_iff_of_centralizer_eq hT i ζ eta hEq α
          ((hT.finite_weightSupport i).mem_toFinset.mp hα)
        exact ⟨⟨hα, by omega⟩, by omega⟩
      · rintro ⟨⟨hα, heta⟩, hζ⟩
        have hn := latticePairing_eq_zero_iff_of_centralizer_eq hT i ζ eta hEq α
          ((hT.finite_weightSupport i).mem_toFinset.mp hα)
        exact ⟨⟨hα, by omega⟩, by omega⟩
    · intro α _
      simp only [factor, Equiv.neg_apply, hroot.finrank_weightSpace_neg hT, hf]
  rw [hprod, hprod, ← Finset.prod_filter_mul_prod_filter_not (S.filter (positive ζ)) (positive eta),
    ← Finset.prod_filter_mul_prod_filter_not (S.filter (positive eta)) (positive ζ), hcommon, hmix]

end Balance

section Determinant

variable {H U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom U.X.hom]
  (a : AutomorphicAction H U) {d : ℕ} (c : Lie.FiniteCoordinates U d) (j : T.toGrp ⟶ H)

include c hT in
/-- In the actual weight basis the displacement has diagonal entries
`1 - α(t)`, each repeated by the weight multiplicity. -/
theorem AutomorphicAction.det_id_sub_differential_lieWeightBasis
    [Fintype (a.lieWeightBasisIndex j)] [DecidableEq (a.lieWeightBasisIndex j)]
    (A : CommAlgCat.{u} (CommRingCat.of k)) (t : Lie.AffinePoints T.toGrp A) :
    LinearMap.det (LinearMap.id - (a.differential (t ≫ j.hom.hom)).toLinearMap) =
      ∏ b : a.lieWeightBasisIndex j, (1 - (Lie.characterValue b.1.val t : A)) := by
  rw [← LinearMap.det_toMatrix (c.baseChangeBasis (a.lieWeightBasis c hT j) A),
    map_sub, LinearMap.toMatrix_id, a.differential_toMatrix_lieWeightBasis c hT j A t,
    ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.det_diagonal]

end Determinant

section Radical

variable (ζ : cocharacterLattice T)
  {Z U : GroupScheme (Spec (CommRingCat.of k))} {iZ : Z ⟶ G} {iU : U ⟶ G}
  (hZ : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy iZ)
  (hU : (Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy iU)
  [IsAffineHom U.X.hom] (j : T.toGrp ⟶ Z) (hj : j ≫ iZ = i)
  {d : ℕ} (c : Lie.FiniteCoordinates U d)

include c hj in
/-- Evaluate the actual displacement determinant by the positive adjoint
weights at the given torus point. -/
theorem unipotentDisplacementDeterminant_eq_positiveWeightProduct
    (t : rationalPoints T.toGrp) :
    unipotentDisplacementDeterminant hZ hU (t ≫ j.hom.hom) =
      positiveWeightProduct hT i ζ
        (fun α => 1 - (Lie.characterValue α (toBase (baseTest k) ≫ t) : k)) := by
  classical
  let a := Dynamic.centralizerAdjointAction hZ hU
  let S := {α : characterLattice T | a.lieWeightSpace j α ≠ ⊥}
  have hS : S.Finite := a.finite_lieWeightSupport_of_finiteCoordinates c hT j
  let : Fintype (Subtype S) := hS.fintype
  let : Fintype (a.lieWeightBasisIndex j) := by
    change Fintype (Σ α : Subtype S, Fin (Module.finrank k (a.lieWeightSpace j α.val)))
    infer_instance
  let f (α : characterLattice T) : k := 1 - (Lie.characterValue α (toBase (baseTest k) ≫ t) : k)
  have hdet := a.det_id_sub_differential_lieWeightBasis hT c j (baseTest k) (toBase (baseTest k) ≫ t)
  have hbase : unipotentDisplacementDeterminant hZ hU (t ≫ j.hom.hom) =
      ∏ b : a.lieWeightBasisIndex j, f b.1.val := by
    simpa only [unipotentDisplacementDeterminant, a, f, Category.assoc] using hdet
  have hdim (α : characterLattice T) : Module.finrank k (a.lieWeightSpace j α) =
      if 0 < latticePairing T α ζ then Module.finrank k (weightSpace i α) else 0 :=
    finrank_lieWeightSpace_centralizerAdjointAction hT i ζ hZ hU j hj α
  let : FiniteDimensional k (Additive (lieKernel U k)) := (c.equiv (baseTest k)).symm.finiteDimensional
  have hsub : hS.toFinset ⊆ (hT.finite_weightSupport i).toFinset := by
    intro α hα
    have hne : a.lieWeightSpace j α ≠ ⊥ := hS.mem_toFinset.mp hα
    rw [Set.Finite.mem_toFinset]
    intro hab
    have h0 := hdim α
    rw [hab, finrank_bot, ite_self] at h0
    exact hne (Submodule.finrank_eq_zero.mp h0)
  rw [hbase]
  change (∏ b : (Σ α : Subtype S, Fin (Module.finrank k (a.lieWeightSpace j α.val))), f b.1.val) =
    positiveWeightProduct hT i ζ f
  rw [Fintype.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  let term (α : characterLattice T) := f α ^ Module.finrank k (a.lieWeightSpace j α)
  change (∏ α : Subtype S, term α.val) = positiveWeightProduct hT i ζ f
  rw [← Finset.prod_subtype (p := S) (F := (inferInstance : Fintype (Subtype S)))
    hS.toFinset (fun α => hS.mem_toFinset) term]
  simp only [term, hdim]
  unfold positiveWeightProduct
  apply Finset.prod_subset hsub
  intro α _ hα
  have hz : a.lieWeightSpace j α = ⊥ := by
    by_contra h
    exact hα (hS.mem_toFinset.mpr h)
  rw [← hdim, hz, finrank_bot, pow_zero]

end Radical

end Langlands.GroupScheme
