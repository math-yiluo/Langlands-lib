import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.OrthogonalMatrix.Subgroups
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.IdentityComponent

/-!
# Forms of the split special orthogonal group `SO_{2n}`: statement

This unproved statement records Tits's realization of the forms of the even
special orthogonal group over an arbitrary field, in every characteristic: a
group scheme over `K` that becomes isomorphic over the separable closure to the
identity component of the split orthogonal group `O_{2n}` is the identity
component `O(q)⁰` of the isometry group of a nondegenerate `σ`-quadratic form
`q` on `D^m`, where `D` is a central division algebra with an involution `σ` of
Tits type 1 and `m * deg D = 2 * n`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Quaternionic

/-- Let `K` be a field, `n ≥ 4`, and `H` an affine group scheme of locally finite type
over `K` whose base change to the separable closure `K^s` is isomorphic to the identity
component `SO_{2n}` of the split orthogonal group `OrthogonalMatrix.groupScheme (Fin n) K^s`
of the hyperbolic quadratic form on `K^s^(2n)`. Then there are a central division
`K`-algebra `D` of degree `degree`, a natural number `m` with `m * degree = 2 * n`, an
involution of the first kind `σ` of `D` of Tits type 1 (its symmetric space has dimension
`degree * (degree + 1) / 2`), and a nondegenerate `σ`-quadratic form `q` on `D^m` such that
the isometry group `O(q)` is smooth and `H` is isomorphic to its identity component `O(q)⁰`.

This is an unproved statement (Tits 1968, §3, Théorème 1 with Remarque 2 and
Proposition 6). There is no characteristic hypothesis. -/
def EvenSpecialOrthogonalFormStatement : Prop :=
  ∀ (K : Type u) [Field K] (H : GroupScheme (Spec (CommRingCat.of K)))
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] (n : ℕ), 4 ≤ n →
    Nonempty ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj H ≅
      identityComponent
        (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of (SeparableClosure K)))) →
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : Algebra.IsCentral K D) (_ : FiniteDimensional K D)
      (degree m : ℕ),
      0 < degree ∧ Module.finrank K D = degree ^ 2 ∧ m * degree = 2 * n ∧
        ∃ σ : FirstKindInvolution K D,
          Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2 ∧
            ∃ q : σ.QuadraticForms (Fin m),
              σ.IsNondegenerateQuadratic q ∧
                ∃ h : Smooth (σ.isometryGroup q).X.hom,
                  haveI := h
                  Nonempty (H ≅ σ.connectedIsometryGroup q)

end Langlands.GroupScheme.Quaternionic
