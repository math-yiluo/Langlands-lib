# Arithmetic transport and Galois conjugacy of actual automorphic realizations

This module is an internal definition. It is a prerequisite for the
Arthur–Clozel cyclic base-change statements in
`Langlands.Automorphic.Unramified.CyclicTransferStatement`. Arthur and Clozel,
*Simple algebras, base change, and the advanced theory of the trace formula*
(1989), Chapter III, Theorem 4.2 (p.202), use `σ`-stable representations `Π`
of `GL_n(𝔸_E)`: clause (d) writes the condition as `Π ≅ Π ∘ σ`, for a
generator `σ` of `Gal(E/F)` acting on `GL_n(𝔸_E)` entrywise. Clauses (b) and
(e) and Lemmas III.6.3 and III.6.4 (p.217) compare a cuspidal representation
with its conjugates `Π^{σ^i}`. This module defines these
relations for the project's actual automorphic realizations. It defines them
for any number-field isomorphism, which a Galois automorphism specializes.

## Objects

`K : Type uK`, `L : Type uL` and `M : Type uM` are number fields in independent
universes, `e : K ≃+* L` is a ring isomorphism and `n` is any natural rank. An
`OperatorRealization K n` is an actual invariant complex subspace `S.Space` of
the stable automorphic functions on `GL_n(𝔸_K)`. It carries three restricted
actions:

- `S.finiteRepresentation`: right translation by `GL_n(𝔸_{K,f})`;
- `S.compactRepresentation`: right translation by `standardInfiniteCompact K n`;
- `S.envelopingAction`: the action of the complex enveloping algebra
  `ArchimedeanGL.EnvelopingAlgebra K n`.

Full equivalence `S.Equivalence T` (module `OperatorEquivalence`) means a
complex linear equivalence that commutes with all three actions.

Arithmetic transport uses these published maps along `e`:

- `AdelicGLTransport.finiteEquiv n e`, entrywise transport
  `GL_n(𝔸_{K,f}) ≃ GL_n(𝔸_{L,f})`;
- `ArchimedeanCompactTransport.compactEquiv n e`, the restriction of entrywise
  infinite transport to the standard compact subgroups (module
  `Langlands.Global.ArchimedeanCompactTransport`, part of this contribution);
- `ArchimedeanLieTransport.envelopingEquiv n e`, the induced isomorphism of
  complex enveloping algebras.

## Definitions

- `OperatorRealization.ArithmeticTransportEquations e S T φ`, for
  `S : OperatorRealization K n`, `T : OperatorRealization L n` and a complex linear
  equivalence `φ : S.Space ≃ₗ[ℂ] T.Space`, is the conjunction of
  `φ (S(d) f) = T(finiteEquiv n e d) (φ f)` for every finite adelic `d`,
  `φ (S(k) f) = T(compactEquiv n e k) (φ f)` for every standard compact `k`, and
  `φ (a · f) = envelopingEquiv n e a · φ f` for every enveloping-algebra
  element `a`.
- `OperatorRealization.IsArithmeticTransport e S T` asserts that some such `φ`
  exists. Thus `T` is isomorphic to `S ∘ e⁻¹`: `T` acts on `e(g)` as `S` acts
  on `g`.
- `CuspidalOperatorRealization.IsArithmeticTransport e S T` is the same relation
  between the underlying realizations of actual irreducible cuspidal
  realizations of rank `r + 1`.
- `CuspidalOperatorRealization.IsoClass.IsArithmeticTransport e c d` descends
  this relation to the published classes of cuspidal realizations up to full
  equivalence. It is defined by `Quotient.liftOn₂` and chooses no
  representative.
- For a field `F` with `[Algebra F K]` and `σ : K ≃ₐ[F] K`,
  `IsoClass.IsGaloisConjugate σ c d` is `IsArithmeticTransport σ.toRingEquiv c d`:
  `d` is the class of `c ∘ σ⁻¹`. `IsoClass.IsGaloisStable σ c` is
  `IsGaloisConjugate σ c c`, that is `c ≅ c ∘ σ⁻¹`. This is equivalent to the
  source's `c ≅ c ∘ σ`. The statements that use it either quantify over all
  `σ` in a group or over a set of powers of `σ` that is closed under inverses.
  So the choice between `σ` and `σ⁻¹` does not affect them.

## Proved properties

These are the intrinsic well-formedness facts. All are proved in the module.

- `ArithmeticTransportEquations.refl`, `.trans` and `.symm`: the identity
  equivalence satisfies the equations along `RingEquiv.refl K`. Composites
  satisfy them along `e.trans e'`, and inverses along `e.symm`.
- `ArithmeticTransportEquations.refl_iff`: along the identity field map, the
  equations are exactly the three generator equations of a full intertwiner.
- `IsArithmeticTransport.refl`, `.trans` and `.symm`, and
  `isArithmeticTransport_refl_iff`: transport along the identity field map is
  exactly `Nonempty (S.Equivalence T)`.
- `isArithmeticTransport_congr`: the relation depends only on the full
  equivalence classes of both arguments. This makes the class-level descent
  well defined.
- `IsArithmeticTransport.target_equivalent`: for fixed `e` and `S`, any two
  transports are fully equivalent.
- On classes: `isArithmeticTransport_isoClass_iff` (evaluation at
  representatives), `isArithmeticTransport_iff` (criterion at all
  representatives with a witnessing linear equivalence),
  `isArithmeticTransport_refl_iff` (along the identity, the relation is equality
  of classes), `.refl`, `.trans`, `.symm`, and `IsArithmeticTransport.target_unique`
  (for fixed `e` and `c`, the target class is unique).
- Galois stability: `isGaloisStable_one`, `IsGaloisStable.inv` and
  `IsGaloisStable.mul`. The automorphisms that fix a class form a subgroup.

## Scope

The relation is between realizations that are given. It does not construct the
transported realization `S ∘ e⁻¹` and does not assert that one exists. The
existence of an arithmetic transport of every automorphic form, cusp form and
irreducible cuspidal realization is a separate construction. It belongs to the
global definition branch (Task 8), extending the published CM chain
`AutomorphicCMTransport` → `OperatorCMTransportClasses`. For Galois stability,
the case `d = c` used by the statements, no existence question arises. All
coefficients are complex, and the module adds no topology.

Provenance: internal composition of the published `OperatorRealization`,
`OperatorEquivalence`, `CuspidalOperatorRealization`, `AdelicGLTransport` and
`ArchimedeanLieTransport` constructions. The new compact restriction is in
`ArchimedeanCompactTransport`. The local `AddCommGroup` instances on submodule
carriers repeat the pattern of the published operator modules and add no
global instances.
