import Langlands.GroupScheme.EvenOrthogonalForm.FormDescent
import Langlands.GroupScheme.EvenOrthogonalForm.SplitChart
import Langlands.GroupScheme.OrthogonalInnerForm.OrthogonalInvolutionHermitian
import Langlands.GroupScheme.OrthogonalInnerForm.QuadraticTransport
import Langlands.GroupScheme.Quaternionic.EvenSpecialOrthogonalFormStatement

/-! # Forms of the split `SO_{2n}` from the automorphism theorem

`evenSpecialOrthogonalForm_of_specialOrthogonalAutomorphism` proves Tits's realization of every
form of `SO_{2n}` (`n ≥ 4`) as the identity component of the isometry group of a nondegenerate
quadratic form over a central division algebra with involution of the first kind
(`EvenSpecialOrthogonalFormStatement`), assuming the published statement
`SpecialOrthogonalAutomorphismStatement` (every automorphism of the split `SO_{2n}` is
conjugation by a similitude).

The proof assembles the modules of this directory and of `OrthogonalInnerForm`:

* a finite Galois splitting field `N / K` and local isomorphisms `φ` from `H` to the split
  `SO_{2n}` (`exists_galois_localIso`);
* the similitude cocycle `g_σ` realizing the Galois twists of `φ` (`exists_similitude_cocycle`);
* the fixed algebra `A` of the twisted Galois action, its descended involution `τ`, a base point
  `a₀` with `a₀ + τ a₀ = 1`, and Galois-equivariant charts `χ` from the isometry cut of
  `(A, τ, a₀)` to the split `O_{2n}` (`exists_twistedChart`);
* `A ≅ M_m(D)` with `τ` adjoint to an invertible hermitian `H` (`orthogonalInvolutionHermitian`),
  the nondegenerate quadratic form `q = [φ(a₀) H]` and the isomorphism of the isometry cut with
  `O(q)` (`isNondegenerateQuadratic_mk_mul`, `isometryCutAlgEquivIso`);
* smoothness of `O(q)` and the descended isomorphism `H ≅ O(q)⁰`
  (`smooth_of_localGroupIso`, `smooth_of_groupIso`, `nonempty_iso_identityComponent`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix TensorProduct

namespace Langlands.GroupScheme.EvenOrthogonalForm

open OrthogonalMatrix Quaternionic OrthogonalInnerForm

/-- Tits's realization of forms of `SO_{2n}` as `O(q)⁰`, assuming that every automorphism of
the split `SO_{2n}` is conjugation by a similitude. -/
theorem evenSpecialOrthogonalForm_of_specialOrthogonalAutomorphism
    (hS : SpecialOrthogonalAutomorphismStatement.{u}) :
    EvenSpecialOrthogonalFormStatement.{u} := by
  intro K _ H _ _ n hn ⟨e⟩
  obtain ⟨N, _, _, _, _, ⟨φ⟩⟩ := exists_galois_localIso K H n e
  obtain ⟨g, hsim, hcoc, hconj⟩ := exists_similitude_cocycle φ hS (by omega)
  have : NeZero n := ⟨by omega⟩
  obtain ⟨A, _, _, _, _, _, τ, eA, he, a₀, ha₀, χ, hχ⟩ := exists_twistedChart g hcoc hsim
  obtain ⟨degree, m, _, D, _, _, _, _, hdeg, hmd, hDdim, σ, hσdim, Hm, hHσ, hHu, φA, hφA⟩ :=
    orthogonalInvolutionHermitian τ eA he
  have hq := isNondegenerateQuadratic_mk_mul τ σ φA Hm hφA hHσ hHu ha₀
  have : IsAffineHom (IsometryCut.groupScheme
      (IsometryCut.isStable_alternatingSubspace (τ := τ)) a₀).X.hom := by
    change IsAffineHom (Spec.map _)
    infer_instance
  have : Smooth (IsometryCut.groupScheme
      (IsometryCut.isStable_alternatingSubspace (τ := τ)) a₀).X.hom :=
    smooth_of_localGroupIso χ
  have hsm : Smooth (σ.isometryGroup
      (Submodule.Quotient.mk (φA a₀ * Hm) : σ.QuadraticForms (Fin m))).X.hom :=
    smooth_of_groupIso (isometryCutAlgEquivIso τ σ φA Hm hHσ hHu hφA a₀) this
  obtain ⟨i⟩ := nonempty_iso_identityComponent φ g hconj χ hχ
  exact ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, degree, m, hdeg, hDdim,
    hmd, σ, hσdim, _, hq, hsm,
    ⟨i ≪≫ IdentityComponent.mapIso (isometryCutAlgEquivIso τ σ φA Hm hHσ hHu hφA a₀)⟩⟩

end Langlands.GroupScheme.EvenOrthogonalForm
