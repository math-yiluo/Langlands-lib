import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Rational.Characters

/-! # Statement: central rigidity for groups of finite presentation from the noetherian case -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- **Reduction of the finitely presented case to the noetherian case** (SGA 3, IX, proof
of Théorème 5.1 b)). Suppose the conclusion of Théorème 5.1 holds over every locally
noetherian base: for every `S`-group `H` of multiplicative type, every `S`-group `G` and all
homomorphisms `u, v : H ⟶ G` with `u_s = v_s` and `u_s` central at a point `s ∈ S`, there
is an open neighbourhood `U` of `s` with `u_U = v_U`. Then the same conclusion holds over an
arbitrary base `S` whenever `G` is of finite presentation over `S` (locally of finite
presentation, quasi-compact and quasi-separated). -/
def MultiplicativeTypeCentralRigidityNoetherianReductionStatement : Prop :=
  (∀ (S : Scheme.{u}) (H G : GroupScheme S), IsLocallyNoetherian S → IsMultiplicativeType H →
    ∀ (u v : H ⟶ G) (s : S),
      (GroupScheme.baseChange (S.fromSpecResidueField s)).map u =
          (GroupScheme.baseChange (S.fromSpecResidueField s)).map v →
        IsCentral ((GroupScheme.baseChange (S.fromSpecResidueField s)).map u) →
        ∃ U : S.Opens, s ∈ U ∧
          (GroupScheme.baseChange U.ι).map u = (GroupScheme.baseChange U.ι).map v) →
    ∀ (S : Scheme.{u}) (H G : GroupScheme S), IsMultiplicativeType H →
      LocallyOfFinitePresentation G.X.hom → QuasiCompact G.X.hom → QuasiSeparated G.X.hom →
      ∀ (u v : H ⟶ G) (s : S),
        (GroupScheme.baseChange (S.fromSpecResidueField s)).map u =
            (GroupScheme.baseChange (S.fromSpecResidueField s)).map v →
          IsCentral ((GroupScheme.baseChange (S.fromSpecResidueField s)).map u) →
          ∃ U : S.Opens, s ∈ U ∧
            (GroupScheme.baseChange U.ι).map u = (GroupScheme.baseChange U.ι).map v

end Langlands.GroupScheme
