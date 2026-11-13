import Langlands.GroupScheme.SimplyConnected.LocalOuterTypeAHermitianModelStatement
import Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitarySplitPresentationStatement
import Langlands.GroupScheme.Examples.HermitianLocalPresentation
import Langlands.Algebra.CentralSimple.UnitaryDivisionSplitting

/-! # Local outer type A Hermitian models from the unitary splitting statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- If the vertex set of an actual Tits index is numbered by `Fin n` and the actual star
action moves some vertex, then `2 ≤ n`. -/
theorem two_le_of_star_moves {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {d : TitsIndexData G} {n : ℕ}
    (e : d.Vertex ≃ Fin n)
    (hstar : ∃ (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
      d.star σ a ≠ a) : 2 ≤ n := by
  obtain ⟨σ, a, ha⟩ := hstar
  by_contra hn
  have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.2 (by omega)
  exact ha (e.injective (Subsingleton.elim _ _))

/-- **Assembly of the local outer type `A` Hermitian model.** The general-field
presentation statement for outer forms of type `A` under unitary splitting, together with
the local statement that central division algebras with a unitary involution over a
separable quadratic extension of a nonarchimedean local field are commutative, implies
`LocalOuterTypeAHermitianModelStatement`. -/
theorem localOuterTypeAHermitianModel_of_unitarySplitting
    (hP : OuterTypeAUnitarySplitPresentationStatement.{u})
    (hD : LocalUnitaryDivisionCommutativeStatement.{u}) :
    LocalOuterTypeAHermitianModelStatement.{u} := by
  intro K _ _ _ _ G _ _ d n hsc has hA hstar
  have hsplit : UnitaryInvolutionSplitting K :=
    Algebra.CentralSimple.unitaryDivisionSplitting K (hD K)
  obtain ⟨L, _, _, _, _, J, ⟨e⟩⟩ := hP K hsplit G d n hsc has hA hstar
  obtain ⟨numbering, -⟩ := hA
  have hn : 2 ≤ n := two_le_of_star_moves numbering hstar
  obtain ⟨H, w, hw, hiso⟩ := e.exists_local_rootIso_of_card_eq_succ hn (Fintype.card_fin _)
  exact ⟨L, _, _, _, _, H, w, hw, hiso⟩

end Langlands.GroupScheme
