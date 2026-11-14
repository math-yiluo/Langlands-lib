import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalSupport
import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetSubquotientStatement
import Langlands.AllFieldBZ.Representation.Parabolic.NormalizedJacquetExactnessProof
import Langlands.Representation.CuspidalSupport.JacquetSubquotientProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.JacquetSubquotientProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.JacquetSubquotientProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding NormalizedJacquetEquivalenceTheorem NormalizedJacquetSubquotientTheorem normalizedJacquetEquivalence normalizedJacquetSubquotient
open Langlands.GeneralLinear
open Representation
universe uF uV uW

/-- Descending an injective/surjective presentation gives an actual Jacquet subquotient. -/
theorem normalizedJacquetSubquotient : NormalizedJacquetSubquotientTheorem.{uF, uV} := by
  intro F T n B
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro A D hD
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hD
  refine SmoothRep.isSubquotient_iff_exists.mpr
    ⟨(T.normalizedJacquetFunctor B).obj C, (T.normalizedJacquetFunctor B).map i,
      (T.normalizedJacquetFunctor B).map q, ?_, ?_⟩
  · change Function.Injective (T.normalizedJacquetMap B (SmoothRep.hom i)).toLinearMap
    rw [T.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap]
    exact coinvariants_map_injective_of_smooth (Parabolic.unipotentFiniteContainment F T B)
      _ hi (Parabolic.isSmooth_radical F T B _ A.isSmooth)
  · change Function.Surjective (T.normalizedJacquetMap B (SmoothRep.hom q)).toLinearMap
    rw [T.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap]
    exact coinvariants_map_surjective _ hq

/-- An intertwining equivalence descends on the actual coinvariant quotients. -/
theorem normalizedJacquetEquivalence : NormalizedJacquetEquivalenceTheorem.{uF, uV, uW} := by
  intro F T n B
  let := T.topology
  intro A D h
  obtain ⟨e⟩ := h
  let f := T.normalizedJacquetMap B e.toIntertwiningMap
  let g := T.normalizedJacquetMap B e.symm.toIntertwiningMap
  have hgf : Function.LeftInverse g f := by
    intro x
    obtain ⟨v, rfl⟩ := B.jacquetMk_surjective A.representation x
    change B.jacquetMk A.representation (e.symm (e v)) = B.jacquetMk A.representation v
    rw [e.symm_apply_apply]
  have hfg : Function.RightInverse g f := by
    intro x
    obtain ⟨v, rfl⟩ := B.jacquetMk_surjective D.representation x
    change B.jacquetMk D.representation (e (e.symm v)) = B.jacquetMk D.representation v
    rw [e.apply_symm_apply]
  exact ⟨f.ofBijective ⟨hgf.injective, hfg.surjective⟩⟩

end Langlands.AllFieldBZ.CuspidalSupport
