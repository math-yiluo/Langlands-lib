import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: connected reductivity and pseudo-reductivity under arbitrary field extension -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Reductivity under field extension** (Milne, *Algebraic Groups* (2017), Proposition
19.13). For every field extension `K/k`, a group scheme `G` over `k` is connected reductive if
and only if its base change `G_K` is. -/
def ConnectedReductiveFieldExtensionIffStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G ↔
      IsConnectedReductive
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)

/-- **Pseudo-reductivity descends along every field extension** (derived from the inclusion
`R_{u,k}(G)_K ⊆ R_{u,K}(G_K)` in the proof of Conrad–Gabber–Prasad, Proposition 1.1.9). For
every field extension `K/k`, if the base change `G_K` of a group scheme `G` over `k` is
pseudo-reductive, then `G` is pseudo-reductive. -/
def PseudoReductiveFieldReflectionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsPseudoReductive
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) →
      IsPseudoReductive G

/-- Both statements, packaged as one proposition. -/
def FieldExtensionReflectionStatement : Prop :=
  ConnectedReductiveFieldExtensionIffStatement.{u} ∧
    PseudoReductiveFieldReflectionStatement.{u}

end Langlands.GroupScheme
