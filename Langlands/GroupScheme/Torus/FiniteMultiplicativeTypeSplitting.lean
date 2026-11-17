import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.FiniteFlatLocalNilpotentDiagonalizable
import Langlands.GroupScheme.Torus.FiniteSeparableSplitting
import Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.SplittingDescentHelpers
import Langlands.RingTheory.Coalgebra.SeparablyClosedGroupLikeSpanningProof

/-! # Finite separable splitting of finite multiplicative-type field groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A finite multiplicative-type group over a separably closed field is
relatively diagonalizable, including its nonsmooth finite factors. -/
theorem IsMultiplicativeType.isDiagonalizable_of_isSepClosed
    {k : Type u} [Field k] [IsSepClosed k]
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsFinite H.X.hom]
    (hH : IsMultiplicativeType H) : RelativeMultiplicativeType.IsDiagonalizable H := by
  have : IsAffine H.X.left := hH.isAffine
  have : Flat H.X.hom := inferInstance
  apply Diagonalizable.isDiagonalizable_of_groupLike_span
  obtain ⟨K, hK, hA, Λ, hΛ, hfg, ⟨e⟩⟩ := hH
  let A := AffineCoordinates.hopfAlgebra H
  let e' := SplittingAssembly.scalarExtensionCoordinatesIso H ≪≫ e ≪≫
    (Diagonalizable.hopfSpecIso (CommRingCat.of K) Λ).symm
  have hspan := SplittingAssembly.span_of_hopfSpecIso
    (HopfCoordinates.scalarExtension k K A)
    (Diagonalizable.hopfAlgebra (CommRingCat.of K) Λ) e'
    AddMonoidAlgebra.span_isGroupLikeElem
  exact Langlands.CoalgebraDescent.separablyClosedGroupLikeSpanning k A K hspan

/-- Every finite multiplicative-type field group becomes relatively
 diagonalizable over a finite separable extension. -/
theorem IsMultiplicativeType.exists_finiteSeparable_splitting
    {k : Type u} [Field k]
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsFinite H.X.hom]
    (hH : IsMultiplicativeType H) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
        RelativeMultiplicativeType.IsDiagonalizable
          ((GroupScheme.baseChange (Spec.algebraMap k K)).obj H) := by
  have : IsAffine H.X.left := hH.isAffine
  let L := SeparableClosure k
  have : IsFinite ((GroupScheme.baseChange (Spec.algebraMap k L)).obj H).X.hom := by
    change IsFinite (CategoryTheory.Limits.pullback.snd _ _)
    infer_instance
  have hsplit := (MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic k L H hH).isDiagonalizable_of_isSepClosed
  obtain ⟨Λ, hΛ, hfg, ⟨e⟩⟩ := hsplit
  let D := (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp
  have : LocallyOfFinitePresentation D.X.hom := inferInstance
  let d := e ≪≫ Diagonalizable.baseChangeIso
    (Gm.toSpecZ (Spec (CommRingCat.of L))) Λ ≪≫
    (Diagonalizable.baseChangeIso (Spec.algebraMap k L) Λ).symm
  obtain ⟨E, ⟨eE⟩⟩ := exists_finiteIntermediateField_iso k L H D d
  refine ⟨E.1, inferInstance, inferInstance, E.2, inferInstance, ?_⟩
  refine ⟨Λ, hΛ, hfg, ?_⟩
  exact ⟨eE ≪≫ Diagonalizable.baseChangeIso (Spec.algebraMap k E.1) Λ ≪≫
    (Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec (CommRingCat.of E.1))) Λ).symm⟩

/-- An actual finite separable splitting field with its reduced group presentation. -/
structure FiniteMultiplicativeTypeSplittingData
    (k : Type u) [Field k] (H : GroupScheme (Spec (CommRingCat.of k))) where
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra k carrier]
  [finite : FiniteDimensional k carrier]
  [separable : Algebra.IsSeparable k carrier]
  split : RelativeMultiplicativeType.IsDiagonalizable
    ((GroupScheme.baseChange (Spec.algebraMap k carrier)).obj H)

attribute [instance] FiniteMultiplicativeTypeSplittingData.field
  FiniteMultiplicativeTypeSplittingData.algebra FiniteMultiplicativeTypeSplittingData.finite
  FiniteMultiplicativeTypeSplittingData.separable

/-- Choose a finite separable splitting field of an actual finite
 multiplicative-type field group. -/
def IsMultiplicativeType.finiteSeparableSplitting
    {k : Type u} [Field k]
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsFinite H.X.hom]
    (hH : IsMultiplicativeType H) : FiniteMultiplicativeTypeSplittingData k H := by
  refine Classical.choice (α := FiniteMultiplicativeTypeSplittingData k H) ?_
  obtain ⟨K, hK, hA, hfin, hsep, hs⟩ := hH.exists_finiteSeparable_splitting
  exact ⟨{
    carrier := K
    field := hK
    algebra := hA
    finite := hfin
    separable := hsep
    split := hs }⟩

end Langlands.GroupScheme
