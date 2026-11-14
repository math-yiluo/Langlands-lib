import Langlands.GroupScheme.Torus.RelativeMultiplicativeType

/-! # Statement: monomorphisms from groups of multiplicative type are detected on fibres -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- **Monomorphisms from groups of multiplicative type** (SGA 3, IX, Corollaires 6.6 and 6.7).
Let `S` be a scheme, `H` an `S`-group of multiplicative type, `G` an `S`-group and
`u : H ⟶ G` a homomorphism, and assume that `S` is locally noetherian or that `G` is locally
of finite presentation over `S`. For `s ∈ S` write `u_s` for the fibre of `u` over the residue
field `κ(s)`, and `u_U` for the restriction of `u` over an open `U ⊆ S`.
1. (6.6) If `G` is separated over `S` and `u_s` is a monomorphism, then `u_U` is a
   monomorphism for some open `U ∋ s`.
2. (6.7) If `u_s` is a monomorphism for every `s ∈ S`, then `u` is a monomorphism. -/
def MultiplicativeTypeMonomorphismSpreadingStatement : Prop :=
  ∀ (S : Scheme.{u}) (H G : GroupScheme S), IsMultiplicativeType H →
    (IsLocallyNoetherian S ∨ LocallyOfFinitePresentation G.X.hom) → ∀ u : H ⟶ G,
      (IsSeparated G.X.hom → ∀ s : S,
        Mono ((GroupScheme.baseChange (S.fromSpecResidueField s)).map u).hom.hom →
          ∃ U : S.Opens, s ∈ U ∧ Mono ((GroupScheme.baseChange U.ι).map u).hom.hom) ∧
      ((∀ s : S, Mono ((GroupScheme.baseChange (S.fromSpecResidueField s)).map u).hom.hom) →
        Mono u.hom.hom)

end Langlands.GroupScheme
