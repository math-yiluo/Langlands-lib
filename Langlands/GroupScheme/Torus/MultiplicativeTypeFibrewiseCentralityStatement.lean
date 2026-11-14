import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Rational.Characters
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Statement: centrality of homomorphisms from groups of multiplicative type is fibrewise -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- **Centrality is detected on fibres** (SGA 3, IX, Théorème 5.6 and Corollaire 5.5). Let `S`
be a scheme. For `s ∈ S` write `u_s` for the fibre of a homomorphism `u` over the residue
field `κ(s)`, and `u_U` for the restriction of `u` over an open `U ⊆ S`.
1. (5.6) Let `u : H ⟶ G` be a homomorphism of `S`-groups with `H` of multiplicative type
   and `G` of finite presentation over `S`.
   (a) If `G` has connected fibres and `u_s` is central, then `u_U` is central for some open
       `U ∋ s`.
   (b) If `u_s` is central for every `s ∈ S`, then `u` is central.
2. (5.5) Let `K` be an `S`-group locally of finite type over `S` with connected fibres, and
   `H` a normal subgroup of `K` (given by a homomorphism whose underlying morphism of schemes
   is an immersion) of multiplicative type. Then `H` is central in `K`. -/
def MultiplicativeTypeFibrewiseCentralityStatement : Prop :=
  ∀ S : Scheme.{u},
    (∀ (H G : GroupScheme S), IsMultiplicativeType H →
      LocallyOfFinitePresentation G.X.hom → QuasiCompact G.X.hom → QuasiSeparated G.X.hom →
      ∀ u : H ⟶ G,
        ((∀ t : S, ConnectedSpace
            ((GroupScheme.baseChange (S.fromSpecResidueField t)).obj G).X.left) →
          ∀ s : S, IsCentral ((GroupScheme.baseChange (S.fromSpecResidueField s)).map u) →
            ∃ U : S.Opens, s ∈ U ∧ IsCentral ((GroupScheme.baseChange U.ι).map u)) ∧
        ((∀ s : S, IsCentral ((GroupScheme.baseChange (S.fromSpecResidueField s)).map u)) →
          IsCentral u)) ∧
    (∀ (K H : GroupScheme S) (h : H ⟶ K), LocallyOfFiniteType K.X.hom →
      (∀ t : S, ConnectedSpace
        ((GroupScheme.baseChange (S.fromSpecResidueField t)).obj K).X.left) →
      IsImmersion h.hom.hom.left → IsMultiplicativeType H →
      (SubgroupFunctor.range h).IsNormal → IsCentral h)

end Langlands.GroupScheme
