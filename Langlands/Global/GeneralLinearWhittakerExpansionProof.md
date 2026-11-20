# Proof of the Whittaker expansion of smooth cusp forms on `GL_{r+1}`

Module `Langlands.Global.GeneralLinearWhittakerExpansionProof`. The theorem
`Langlands.Global.whittakerExpansion : WhittakerExpansionStatement.{u}` proves the published
proposition `Langlands.Global.WhittakerExpansionStatement` (module
`Langlands.Global.GeneralLinearWhittakerExpansionStatement`) at its full universe-polymorphic
scope. It is the Whittaker expansion of Getz–Hahn, Theorem 11.3.6 and Cogdell 2004,
Theorem 1.1.

Here `φ` is a smooth function on `GL_{r+1}(F) \ GL_{r+1}(𝔸)` of uniform moderate growth whose
constant terms along the standard maximal parabolics vanish. Let `ψ` be a nontrivial continuous
character of `𝔸` trivial on `F`, and let `m_0, …, m_{r-1} ∈ F` be nonzero. Then for every `g`
the family `γ ↦ W_{ψ,m}(φ)(diag(γ, 1) g)` over `N_r(F) \ GL_r(F)` is absolutely summable with
sum `φ(g)`. Moreover, the sums of the absolute values converge uniformly on compact sets.

## The proof

The theorem applies `SmoothWhittakerExpansion.whittakerExpansionStatement_of` (module
`SmoothWhittakerExpansion.Assembly`). That theorem derives `WhittakerExpansionStatement` from
two hypotheses, which are supplied here.

1. `hD`: let `F` be a number field with compact `𝔸 / F`. For every `n`, every element `u` of
   the archimedean enveloping algebra and every cuspidal
   `f : FiniteSmoothRationalFunctions F n`, the derivative `finiteSmoothEnvelopingAction F n u f`
   is cuspidal. This is the Library's `generalLinearCuspidal_envelopingAction` (module
   `Automorphic.GroupSchemeCuspidalEnvelopingAction`). That theorem takes
   `AdelicConstantTermEnvelopingStatement` as its hypothesis, and here it receives that
   statement's proof `adelicConstantTermEnveloping` (module
   `Automorphic.GroupSchemeConstantTermEnvelopingProof`).
2. `hT`: for every standard additive character `ψ` and nonzero `m`, a bijection `σ` of
   `N_r(F) \ GL_r(F)` turns the `(ψ, m)`-Whittaker terms of every function left invariant under
   `GL_{r+1}(F)` into the `(ψ, 1)`-terms. This is
   `SmoothWhittakerExpansion.exists_cosetEquiv_genericCharacter` (module
   `SmoothWhittakerExpansion.Torus`). It conjugates by the rational torus element
   `t = diag(e_0, …, e_{r-1}, 1)` with `e_i / e_{i+1} = m_i`.

Given `hD` and `hT`, `whittakerExpansionStatement_of` argues as follows.

* Continuity and triviality on `F` make `ψ` unitary, so `ψ` is a standard additive character
  (module `Character`).
* The block-vanishing hypothesis on `φ` is cuspidality of its matrix-side function
  (`mem_generalLinearStandardBlockVanishingSubrepresentation_iff`). By `hD`, all of its
  enveloping derivatives are cuspidal.
* Uniform moderate growth gives exponential growth of all derivatives along the archimedean
  torus (module `Growth`). With cuspidality this gives boundedness on determinant bands (module
  `Decay`).
* So the group-scheme functions of all derivatives of `φ` form a `WhittakerDecayClass`. The
  Library's Whittaker expansion core then gives summable majorants of the standard Whittaker
  terms, uniform on compact sets, and the expansion for the standard character (module
  `Expansion`).
* The bijection `σ` from `hT` transfers both to the character `(ψ, m)`. Uniform convergence of
  the sums of absolute values is the Weierstrass M-test `tendstoUniformlyOn_tsum`.
