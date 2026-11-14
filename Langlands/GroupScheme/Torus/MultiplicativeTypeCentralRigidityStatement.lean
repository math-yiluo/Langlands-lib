import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Rational.Characters

/-! # Statement: rigidity of central homomorphisms from groups of multiplicative type -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- **Rigidity of central homomorphisms** (SGA 3, IX, Théorème 5.1 and Corollaires 5.2, 5.3).
Let `S` be a scheme, `H` an `S`-group of multiplicative type and `G` an `S`-group, and assume
that `S` is locally noetherian or that `G` is of finite presentation over `S`. For `s ∈ S`
write `u_s` for the fibre of `u : H ⟶ G` over the residue field `κ(s)`, and `u_U` for the
restriction of `u` over an open `U ⊆ S`.
1. (5.1) If `u_s = v_s` and `u_s` is central, then `u_U = v_U` for some open `U ∋ s`.
2. (5.2) If `u_s` is trivial, then `u_U` is trivial for some open `U ∋ s`.
3. (5.3) If moreover `G` is separated over `S`, the set of `s ∈ S` with `u_s` trivial is an
   open and closed subset `U` of `S`, and `u_U` is trivial. -/
def MultiplicativeTypeCentralRigidityStatement : Prop :=
  ∀ (S : Scheme.{u}) (H G : GroupScheme S), IsMultiplicativeType H →
    (IsLocallyNoetherian S ∨
      (LocallyOfFinitePresentation G.X.hom ∧ QuasiCompact G.X.hom ∧ QuasiSeparated G.X.hom)) →
    (∀ (u v : H ⟶ G) (s : S),
      (GroupScheme.baseChange (S.fromSpecResidueField s)).map u =
          (GroupScheme.baseChange (S.fromSpecResidueField s)).map v →
        IsCentral ((GroupScheme.baseChange (S.fromSpecResidueField s)).map u) →
        ∃ U : S.Opens, s ∈ U ∧
          (GroupScheme.baseChange U.ι).map u = (GroupScheme.baseChange U.ι).map v) ∧
    (∀ (u : H ⟶ G) (s : S),
      ((GroupScheme.baseChange (S.fromSpecResidueField s)).map u).hom.hom = 1 →
        ∃ U : S.Opens, s ∈ U ∧ ((GroupScheme.baseChange U.ι).map u).hom.hom = 1) ∧
    (IsSeparated G.X.hom → ∀ u : H ⟶ G,
      ∃ U : S.Opens, IsClosed (U : Set S) ∧
        (∀ s : S, s ∈ U ↔
          ((GroupScheme.baseChange (S.fromSpecResidueField s)).map u).hom.hom = 1) ∧
        ((GroupScheme.baseChange U.ι).map u).hom.hom = 1)

end Langlands.GroupScheme
