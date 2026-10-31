# Proof: the finite pairing along a Mumford map is trivial on the diagonal

Module `Langlands.AlgebraicGeometry.Picard.MumfordFiniteWeilAlternationProof`.

## Main theorem

`Langlands.AbelianScheme.mumfordFiniteWeilAlternation :
MumfordFiniteWeilAlternationStatement.{u}` proves the Library statement
`Langlands.AbelianScheme.MumfordFiniteWeilAlternationStatement` (module
`Langlands.AlgebraicGeometry.Picard.MumfordFiniteWeilAlternationStatement`). The statement
concerns a homomorphism `lam : A ⟶ A^∨` whose underlying scheme morphism is the Mumford map
of an actual line bundle `L` on `A` (with normalization data `B`, `evaluationB`, `M`,
`evaluation`). For every `n > 0`, the finite pairing `finiteWeilAlongHomPairing … lam n` on
`A[n]` is trivial on the diagonal:
`prod.lift (𝟙 _) (𝟙 _) ≫ finiteWeilAlongHomPairing … lam n = 1`.

The statement's eight constructor propositions (`preservation`, `square`, `composition`,
`unitCoherence`, `associativity`, `comparison`, `symmetry`, `stability`) are used as
hypotheses, as the statement provides them. The hypothesis `0 < n` is not used. The proof
uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Proof

After introducing the statement's variables, the theorem combines two results.

1. `mumfordFiniteWeil_diagonal_of_trivialization` (published module
   `Langlands.AlgebraicGeometry.Picard.MumfordFiniteWeilAlternationReduction`) reduces the
   conclusion to the geometric input
   `MumfordKernelPointTrivialization preservation A L B evaluationB M evaluation n 𝟙` at
   the universal point `𝟙` of `A[n]`. The input asks for a trivialization of the
   `[n]`-pullback of the pulled-back Mumford module whose restrictions along the unit section
   and along its translate by the point agree.
2. `mumfordKernelPointTrivialization_of_hom` (module
   `Langlands.AlgebraicGeometry.Picard.MumfordAlternationTrivialization`, new in this
   contribution) proves this input for every point `x : T ⟶ A[n]` from `lam` and `hlam`.
   It is applied at `x = 𝟙`.

The geometric argument is in `MumfordAlternationTrivialization.md`. In outline:

- The `[n]`-pullback of the Mumford family `Λ` is isomorphic, compatibly with the
  rigidifications, to its pullback along the parameter map `[n]`. Both are Poincaré
  pullbacks along `[n] ≫ φ`, because `φ` underlies the homomorphism `lam`.
- `Λ` is trivial, compatibly with the rigidification, at the zero parameter
  (`mumfordZeroParameterIso`).
- Composing these gives a trivialization `α` of the `[n]`-pullback of the restriction of `Λ`
  to the parameter `x`.
- Its restrictions along `t ↦ (t, 0)` and `t ↦ (t, x t)` are compared with an exchange-of-factors
  isomorphism of the carrier of `Λ`. The comparison yields two scalars, each a global function
  on `T`, because global functions on `T ×_S A` come from `T` (`universalGlobalFunctions`).
  Evaluation at the unit section shows that their product is `1`, so the two restrictions
  agree.

New supporting modules (integrated with this proof):

- `Langlands.AlgebraicGeometry.Modules.PullbackTransport`: transport of morphisms between
  pullbacks of modules along further maps, and the constancy lemma
  `exists_transport_eq_smul`.
- `Langlands.AlgebraicGeometry.Picard.MumfordAlternationTrivialization`: the geometric
  input described above.
