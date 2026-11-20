import Langlands.GroupScheme.IdentityJetSheaf

/-! # Statement: identity jets of smooth groups are locally spectra of finite free algebras -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Identity jets of a smooth group are locally finite free** (SGA 3, Exposé XVI,
Proposition 3.1: the `n`-th normal invariant `G(n)` of the unit section is a locally free
`O_S`-module of finite type).

Let `G` be a smooth, separated group scheme over an arbitrary scheme `S`, and let `n` be a
natural number. Every point `s` of `S` has arbitrarily small affine open neighbourhoods
`Spec R ⟶ S` over which the order-`n` identity jet of the base-changed group is, over
`Spec R`, the spectrum of an `R`-algebra which is free of finite rank as an `R`-module. -/
def IdentityJetLocallyFreeStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S),
    Smooth G.X.hom → IsSeparated G.X.hom →
    ∀ (n : ℕ) (s : S) (W : S.Opens), s ∈ W →
      ∃ (R : CommRingCat.{u}) (i : Spec R ⟶ S),
        IsOpenImmersion i ∧ s ∈ Set.range i.base ∧ Set.range i.base ⊆ W ∧
        ∃ (P : CommAlgCat.{u} R)
          (e : IdentityJet.scheme ((GroupScheme.baseChange i).obj G) n ≅
            Spec (CommRingCat.of P)),
          e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) =
            IdentityJet.projection ((GroupScheme.baseChange i).obj G) n ∧
          ∃ m : ℕ, Nonempty (Module.Basis (Fin m) R P)

end Langlands.GroupScheme
