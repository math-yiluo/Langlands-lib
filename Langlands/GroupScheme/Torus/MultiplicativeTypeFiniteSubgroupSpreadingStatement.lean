import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Statement: closed subgroups of groups of multiplicative type with finite fibre -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- **Closed subgroups of groups of multiplicative type with a finite fibre** (SGA 3, IX,
Théorème 6.4 and Corollaire 6.5). Let `S` be a scheme, `H` an `S`-group of multiplicative type
and `K` a closed subgroup scheme of `H` (given by a homomorphism `k : K ⟶ H` whose underlying
morphism of schemes is a closed immersion) of finite presentation over `S`. Let `s ∈ S`, write
`K_s` for the fibre of `K` over the residue field `κ(s)` and `K_U` for the restriction of `K`
over an open `U ⊆ S`.
1. (6.4) If `K_s` is finite over `κ(s)`, there are an open `U ∋ s` and `n > 0` such that `K_U`
   is contained in `ₙH_U` (every point `x` of `K_U` satisfies `xⁿ = 1`) and `K_U` is finite
   over `U`.
2. (6.5) If `K_s` is the unit group (its structure morphism is an isomorphism), then `K_U` is
   the unit group for some open `U ∋ s`. -/
def MultiplicativeTypeFiniteSubgroupSpreadingStatement : Prop :=
  ∀ (S : Scheme.{u}) (H K : GroupScheme S) (k : K ⟶ H), IsMultiplicativeType H →
    IsClosedImmersion k.hom.hom.left →
    LocallyOfFinitePresentation K.X.hom → QuasiCompact K.X.hom → QuasiSeparated K.X.hom →
    ∀ s : S,
      (IsFinite ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj K).X.hom →
        ∃ U : S.Opens, s ∈ U ∧ ∃ n : ℕ, 0 < n ∧
          (∀ (T : Over U.toScheme) (x : T ⟶ ((GroupScheme.baseChange U.ι).obj K).X),
            x ^ n = 1) ∧
          IsFinite ((GroupScheme.baseChange U.ι).obj K).X.hom) ∧
      (IsIso ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj K).X.hom →
        ∃ U : S.Opens, s ∈ U ∧ IsIso ((GroupScheme.baseChange U.ι).obj K).X.hom)

end Langlands.GroupScheme
