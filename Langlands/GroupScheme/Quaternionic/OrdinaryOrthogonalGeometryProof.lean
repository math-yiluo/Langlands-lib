import Langlands.GroupScheme.Quaternionic.OrdinaryOrthogonalGeometryStatement
import Langlands.GroupScheme.OrthogonalMatrix.Comparison
import Langlands.GroupScheme.OrthogonalMatrix.Semisimple
import Langlands.GroupScheme.OrthogonalMatrix.TypeD
import Langlands.GroupScheme.IdentityComponent.AlmostSimpleDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Smoothness and absolute almost simplicity of even orthogonal groups

For a nondegenerate quadratic form `q` of rank `2m ≥ 6` over any field `K`, the orthogonal
group scheme `O(q)` is smooth and its identity component `O(q)⁰` is absolutely almost simple.

Over an algebraic closure of `K`, `O(q)` becomes isomorphic to the split orthogonal group
`O_{2m}` of the hyperbolic form. The split group is smooth, and the identity component of its
base change to any algebraically closed field is semisimple, nontrivial and has a root system
of type `D_m`, so it is almost simple. Smoothness and absolute almost simplicity then descend
along the field extension.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace OrthogonalMatrix

/-- **Absolute almost simplicity of the split special orthogonal group.** Over every field, the
identity component of the split orthogonal group `O_{2l}` is absolutely almost simple when `l`
has at least three elements. -/
theorem isAbsolutelyAlmostSimple_identityComponent (l : Type) [Fintype l] [DecidableEq l]
    (hl : 3 ≤ Fintype.card l) (K : Type u) [Field K] :
    IsAbsolutelyAlmostSimple (identityComponent (groupScheme l (CommRingCat.of K))) := by
  have : Nontrivial l := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact isAbsolutelyAlmostSimple_of_isAlmostSimple l
    (fun k _ _ => isAlmostSimple_identityComponent l k hl (isSemisimple_identityComponent l k)
      (range_id_identityComponent_ne_bot l k)) K

end OrthogonalMatrix

namespace Quaternionic

/-- **Even orthogonal groups.** For a nondegenerate quadratic form `q` of rank `2m ≥ 6` over a
field `K` of any characteristic, the orthogonal group scheme `O(q)` is smooth and its identity
component is absolutely almost simple. -/
theorem ordinaryOrthogonalGeometry : OrdinaryOrthogonalGeometryStatement.{u} := by
  intro K _ m hm q hq
  obtain ⟨Q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [FirstKindInvolution.isNondegenerateQuadratic_scalar_mk_iff] at hq
  obtain ⟨e⟩ := OrthogonalMatrix.nonempty_splittingIso (L := AlgebraicClosure K) (m := m)
    (by rw [Fintype.card_fin]) Q hq
  exact IdentityComponent.smooth_and_isAbsolutelyAlmostSimple_of_fieldExtension_iso e
    (OrthogonalMatrix.isAbsolutelyAlmostSimple_identityComponent (Fin m)
      (by rwa [Fintype.card_fin]) (AlgebraicClosure K))

end Quaternionic

end Langlands.GroupScheme
