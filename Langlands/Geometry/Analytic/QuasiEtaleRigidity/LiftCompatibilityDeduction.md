# Compatibility of lifts from rigidity and postcomposition

Author: Worker 931.

This is a helper module of `QuasiEtaleLiftCompatibilityProof`. It formalizes
the deduction recorded in `QuasiEtaleLiftCompatibilityStatement.md`
("Correspondence with the sources"), in a form whose analytic inputs are
isolated as hypotheses.

- `IsRigid p`: the uniqueness part of Berkovich's Key Lemma 7.2 for
  commutative diagrams (Berkovich, *Vanishing cycles for formal schemes*,
  1994, §7, printed p.560). There is a finite set `E` of test triples on `U`
  such that any two morphisms `ψ₁ ψ₂ : V ⟶ U` with `ψ₁ ≫ p = ψ₂ ≫ p` that are
  both `E`-near a common morphism `ψ` are equal. Here "`E`-near" means `IsNear τ`
  for every `τ ∈ E`. In Berkovich's §6 (printed p.558), an element of `𝔈(U)` is
  given by finite families of analytic domains, functions and positive numbers,
  and every element is refined by a finite infimum of single triples
  `(U, f, t)`. So a finite set of test triples plays the role of `ε₀` in the
  uniqueness clause of the Key Lemma, here with `g = 1_V`. No `δ` is needed,
  because `ψ₁ ≫ p = ψ₂ ≫ p` is assumed directly.
- `ActionLift.eventually_isNear` and `ActionLift.subgroup_mem_nhds`: by
  continuity of a lift, the elements `g` of its subgroup with
  `IsNear τ (action g).hom (𝟙 U)` form a neighbourhood of `1` in `G`, since the
  subgroup is open.
- `exists_open_subgroup_intertwining`: let `f ≫ p = q`, let `p` be rigid, and
  suppose that for each test triple `τ` on `U` there is a finite set `E_τ` on
  `V` such that `E_τ`-nearness of `φ : V ⟶ V` to `𝟙 V` implies
  `IsNear τ (φ ≫ f) f`. Then for any lifts `a` of `ρ` along `p` and `b` along
  `q`, there is an open subgroup `N ≤ a.subgroup ⊓ b.subgroup` with
  `(b.action g).hom ≫ f = f ≫ (a.action g).hom` for all `g ∈ N`.

Proof of the last statement. `N` is the set of `g` in both subgroups at which
the two composites agree. It is a subgroup: the actions are homomorphisms, and
`Aut` multiplies by composition in reverse order. Consider the neighbourhood
`W` of `1` given by the two subgroups, the `a`-nearness for the finitely many
triples of `E`, and the `b`-nearness for the finitely many triples of the
`E_τ` (`τ ∈ E`). For `g ∈ W`, take `ψ = f`, `ψ₁ = (b g).hom ≫ f` and
`ψ₂ = f ≫ (a g).hom`. Both satisfy `ψᵢ ≫ p = q ≫ (ρ g).hom` by the two
equivariances. Further, `ψ₁` is `E`-near `f` by the hypothesis on `f`, and
`ψ₂` is `E`-near `f` by `IsNear.precomp`. Rigidity gives `ψ₁ = ψ₂`. So `N`
contains `W`, and `Subgroup.isOpen_of_mem_nhds` shows that `N` is open.
