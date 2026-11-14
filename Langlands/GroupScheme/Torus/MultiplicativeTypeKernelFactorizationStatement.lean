import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.AbelianScheme.Kernel
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: canonical factorization of homomorphisms from groups of multiplicative type -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- **Canonical factorization** (SGA 3, IX, Théorème 6.8). Let `S` be a scheme and
`u : H ⟶ G` a homomorphism of `S`-groups with `H` of multiplicative type and `G` separated over
`S`, and assume that `S` is locally noetherian or that `G` is of finite presentation over `S`.
Then the kernel `K = Ker u` is of multiplicative type, and `u` factors as `H ⟶ H/K ⟶ G` where
`H/K` is of multiplicative type, the first map `q : H ⟶ H/K` is the canonical quotient map
(an fppf quotient map with kernel `K`), faithfully flat and affine, and the second map is a
monomorphism. -/
def MultiplicativeTypeKernelFactorizationStatement : Prop :=
  ∀ (S : Scheme.{u}) (H G : GroupScheme S) (u : H ⟶ G), IsMultiplicativeType H →
    IsSeparated G.X.hom →
    (IsLocallyNoetherian S ∨
      (LocallyOfFinitePresentation G.X.hom ∧ QuasiCompact G.X.hom ∧ QuasiSeparated G.X.hom)) →
    IsMultiplicativeType (kernel u) ∧
      ∃ (Q : GroupScheme S) (q : H ⟶ Q) (v : Q ⟶ G),
        IsMultiplicativeType Q ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι u)) q ∧
        IsAffineHom q.hom.hom.left ∧ Mono v.hom.hom ∧ q ≫ v = u

end Langlands.GroupScheme
