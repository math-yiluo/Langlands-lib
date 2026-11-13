import Langlands.GroupScheme.SimplyConnected.LocalRankOneClassificationStatement
import Langlands.GroupScheme.SimplyConnected.InnerTypeARankOneReduction
import Langlands.GroupScheme.SimplyConnected.OuterTypeARankOneHermitianStatement
import Langlands.GroupScheme.SimplyConnected.TypeCRankOneQuaternionicStatement
import Langlands.GroupScheme.SimplyConnected.TypeDRankOneSpinStatement
import Langlands.GroupScheme.Reductive.TitsIndexChoiceStatement

/-!
# The local rank-one classification from actual Tits indices

This module reduces `LocalRankOneClassificationStatement` to the existence of
actual Tits-index data, the enumeration of the local rank-one indices and one
identification statement per family of indices. Each input is a published,
unproved proposition and is an explicit hypothesis of the reduction.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A simply connected field group is smooth, hence locally of finite type. -/
theorem IsSimplyConnected.locallyOfFiniteType {K : Type u} [Field K]
    {G : GroupScheme (Spec (CommRingCat.of K))} (hsc : IsSimplyConnected G) :
    LocallyOfFiniteType G.X.hom := by
  have := hsc.isSemisimple.isConnectedReductive.smooth
  infer_instance

/-- The seven unproved inputs of the local rank-one classification: the
existence of actual Tits-index data, the local enumeration of rank-one indices,
and the identification statements for inner type `A` (with the split rank of
`SL_m(D)`), outer type `A`, type `C` and type `D`. -/
def LocalRankOneClassificationIndexInputs : Prop :=
  TitsIndexExistenceStatement.{u} ∧ LocalRankOneTitsIndexStatement.{u} ∧
    InnerTypeANormOneStatement.{u} ∧
      CentralSimpleUnits.MatrixNormOneSplitRankStatement.{u} ∧
        OuterTypeARankOneHermitianStatement.{u} ∧
          TypeCRankOneQuaternionicStatement.{u} ∧ TypeDRankOneSpinStatement.{u}

/-- The classification of absolutely almost-simple simply connected groups of
split rank one over nonarchimedean local fields follows from the existence of
actual Tits-index data, the local enumeration of rank-one indices, and the
identification statements for inner type `A`, outer type `A`, type `C` and
type `D`. -/
theorem localRankOneClassification_of_indexStatements
    (hexist : TitsIndexExistenceStatement.{u})
    (henum : LocalRankOneTitsIndexStatement.{u})
    (hinner : InnerTypeANormOneStatement.{u})
    (hrank : CentralSimpleUnits.MatrixNormOneSplitRankStatement.{u})
    (houter : OuterTypeARankOneHermitianStatement.{u})
    (htypeC : TypeCRankOneQuaternionicStatement.{u})
    (htypeD : TypeDRankOneSpinStatement.{u}) :
    LocalRankOneClassificationStatement.{u} := by
  intro K _ _ _ _ G _ hsc habs hG
  have : LocallyOfFiniteType G.X.hom := hsc.locallyOfFiniteType
  obtain ⟨d⟩ := hexist K G hsc.isSemisimple
  rcases henum K G d hsc habs hG with
    ⟨degree, hA⟩ | ⟨n, hA⟩ | ⟨n, hC⟩ | hD4 | hD5
  · -- inner type `A`: the binary model `SL₂(D)`
    exact Or.inl (exists_binary_model_of_innerTypeA hinner hrank G d (2 * degree - 1)
      hsc habs hA.hasInnerTypeA hG)
  · -- outer type `A`: a Hermitian model in `(n - 1) + 2` variables
    obtain ⟨L, i1, i2, i3, i4, H, w, hw, hH, he⟩ := houter K G d n hsc habs hA hG
    have hn : n - 1 = 1 ∨ n - 1 = 2 := by
      rcases hA.1 with h | h <;> subst h <;> simp
    exact Or.inr (Or.inl ⟨L, i1, i2, i3, i4, n - 1, hn, H, w, hw, hH, he⟩)
  · -- type `C`: a quaternionic symplectic group in `n` variables
    obtain ⟨D, i1, i2, i3, i4, hD, σ, hσ, hn, H, hH, hu, hwitt, he⟩ :=
      htypeC K G d n hsc habs hC hG
    exact Or.inr (Or.inr ⟨D, i1, i2, i3, i4, hD, σ, hσ,
      Or.inl ⟨n, hn, hC.1, H, hH, hu, hwitt, he⟩⟩)
  · -- outer type `D_4`: a quaternionic spin cover in 4 variables
    obtain ⟨D, i1, i2, i3, i4, hD, σ, hσ, q, hq, hwitt, π, hπ⟩ :=
      htypeD K G d 4 hsc habs (Or.inl ⟨rfl, hD4⟩) hG
    exact Or.inr (Or.inr ⟨D, i1, i2, i3, i4, hD, σ, hσ,
      Or.inr ⟨4, Or.inl rfl, q, hq, hwitt, π, hπ⟩⟩)
  · -- inner type `D_5`: a quaternionic spin cover in 5 variables
    obtain ⟨D, i1, i2, i3, i4, hD, σ, hσ, q, hq, hwitt, π, hπ⟩ :=
      htypeD K G d 5 hsc habs (Or.inr ⟨rfl, hD5⟩) hG
    exact Or.inr (Or.inr ⟨D, i1, i2, i3, i4, hD, σ, hσ,
      Or.inr ⟨5, Or.inr rfl, q, hq, hwitt, π, hπ⟩⟩)

/-- The bundled inputs give the local rank-one classification. -/
theorem localRankOneClassification_of_indexInputs
    (h : LocalRankOneClassificationIndexInputs.{u}) :
    LocalRankOneClassificationStatement.{u} := by
  obtain ⟨hexist, henum, hinner, hrank, houter, htypeC, htypeD⟩ := h
  exact localRankOneClassification_of_indexStatements hexist henum hinner hrank houter
    htypeC htypeD

end Langlands.GroupScheme
