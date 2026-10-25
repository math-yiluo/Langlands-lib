# Whittaker torus expansion with last diagonal entry one

Author: Worker 394, adapting Worker 11's published
`WhittakerTypeAsymptoticStatement` telescope. This module defines the closed
proposition `Langlands.WhittakerLastEntryOneAsymptoticStatement.{uF,uV}`.
It does not prove the proposition.

The mathematical source is JPS (1979), Proposition (2.2), printed page 181,
its proof and Lemma (2.2.1), printed pages 181–183, and the finite-type
extension in Remark (2.2.5), printed page 183. The use of functions on the
full diagonal torus is a derived packaging of the source's functions on
the simple-root torus, explained below.

## Data and hypotheses

The declaration has exactly the data and hypotheses of the published
`Langlands.WhittakerTypeAsymptoticStatement`. It quantifies over a prime
`p : ℕ`, its certificate `Fact p.Prime`, a p-adic field
`F : PadicField.{uF} p`, and installs the topology from
`F.canonicalTopologicalData`. It then quantifies over every `n : ℕ`, a
carrier `V : Type uV` with `AddCommGroup V` and `Module ℂ V`, a representation
`ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V`, and an additive
character `ψ : AddChar F.Carrier ℂ`. The field and carrier universes are
independent. The rank is `n + 1`, including rank one when `n = 0`.

The hypotheses on the additive character are `Continuous ψ`, `ψ ≠ 1`,
and `∀ x, ‖ψ x‖ = 1`. The representation is admissible in the Library's
sense, `IsAdmissible ρ`, which includes smoothness, and is of finite type:

```lean
Module.Finite (MonoidAlgebra ℂ (GeneralLinear (n + 1) F.Carrier)) ρ.asModule
```

Thus finite generation is over the group algebra. Reducible representations
are included.

The local predicates are written out as in the full-torus target:

- `unipotent g` means
  `(∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1`.
- `θ g = ∏ i : Fin n, ψ (g.val i.castSucc i.succ)`.
- `equivariant ℓ` means
  `∀ g, unipotent g → ∀ v, ℓ (ρ g v) = θ g * ℓ v`,
  for `ℓ : Module.Dual ℂ V`.

The final hypothesis is the existence of a nonzero equivariant functional
`ℓ₀` such that every equivariant functional is a complex scalar multiple
of `ℓ₀`. This is the one-dimensional Whittaker-functional condition in
JPSS (1983), §2.1, printed page 385, where admissibility and finite type
together with that condition define representations of Whittaker type.
The statement does not require irreducibility, a scalar or unitary central
character, or finite dimension of the original carrier.

## Coordinates and conclusion

Write `T = Fin (n + 1) → F.Carrierˣ`, with pointwise multiplication and its
product topology. The monoid homomorphism `torus : T →* GL_{n+1}(F)` is

```lean
(Units.map (Matrix.diagonalRingHom (Fin (n + 1)) F.Carrier).toMonoidHom).comp
  MulEquiv.piUnits.symm.toMonoidHom
```

It sends `a` to the diagonal matrix with entries `a i`. Its root coordinates,
viewed in the field, are exactly

```lean
roots a i = ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier)
```

for `i : Fin n`. For a complex function `χ` on `T`, `finiteFunction χ` is
exactly

```lean
Continuous χ ∧
  FiniteDimensional ℂ (Submodule.span ℂ
    (Set.range fun b : T => fun a => χ (b * a)))
```

This is translation finiteness, as defined immediately before JPS
Proposition (2.2), rather than a requirement that `χ` be a character.

The conclusion chooses one finite set `X : Finset (T → ℂ)` such that every
member is a finite function. This choice precedes the quantifiers over the
equivariant functional `ℓ` and vector `v`. For every such `ℓ` and `v : V`
there is a family

```lean
φ : (T → ℂ) → HarmonicAnalysis.SchwartzBruhat (Fin n → F.Carrier)
```

such that, for every `a : T` satisfying `a (Fin.last n) = 1`,

```lean
ℓ (ρ (torus a) v) = ∑ χ ∈ X, φ χ (roots a) * χ a
```

The coefficients are actual complex Schwartz–Bruhat functions on the entire
additive space `F^n`: the Library definition gives locally constant functions
with compact support. They may depend on `ℓ` and `v`. The finite set `X`
may depend on the earlier data, including `ρ` and `ψ`, but is uniform in
`ℓ` and `v`. No expansion at an arbitrary last diagonal entry is asserted.

The only change to the body of `WhittakerTypeAsymptoticStatement` is the
implication `a (Fin.last n) = 1 →` in this final universal quantifier.
All current Library Lean/Markdown pairs remain unchanged.

## Correspondence with the original and derived packaging

Put `H = Fin n → F.Carrierˣ`. The source's coordinates `x ∈ H` parametrize

`diag(x₁ ⋯ xₙ, x₂ ⋯ xₙ, …, xₙ, 1)`.

The consecutive quotients of these diagonal entries recover `x`. Conversely,
every diagonal matrix with last entry one has this form. This is precisely
JPS display (2.2.2), printed page 181.

Let `α : T → H` be the unit-valued homomorphism
`α(a)(i) = a i.castSucc / a i.succ`. Its coercion into `F^n` is `roots a`.
For each finite function `λ` on `H` supplied by Proposition (2.2), take the
full-torus function `χ = λ ∘ α`. It is continuous because `α` is continuous.
Its translates satisfy

`χ(b * a) = λ(α(b) * α(a))`.

Consequently their span is contained in the image, under the linear
pullback map `f ↦ f ∘ α`, of the finite-dimensional span of the translates
of `λ`. This proves translation finiteness at the level of the mathematical
packaging. The finite set of source functions therefore yields a finite set
on `T`. If pullbacks coincide, their Schwartz–Bruhat coefficients can be
added, giving a `Finset` with the same expansion. This explanation of the
packaging is not a Lean proof in this module.

For the reducible case, fix a nonzero equivariant `ℓ₀` from the hypothesis
and consider the coefficient image `v ↦ (g ↦ ℓ₀ (ρ g v))`. Its right
translation action is a quotient of the admissible finite-type
representation. It is a finitely generated admissible space of right-smooth
functions satisfying `W(ug) = θ(u) W(g)`, to which Remark (2.2.5) applies.
The source chooses its finite set uniformly for this entire function space.
Every other equivariant `ℓ` is `c • ℓ₀`, so the same finite set works by
scaling the Schwartz–Bruhat coefficients. This is the provenance of the
quantifier order in the target. The quotient-admissibility and expansion
arguments remain proof obligations.

For `n = 0`, the source's Lemma (2.2.1) explicitly includes the trivial
zero-coordinate case. Here `H` and `Fin 0 → F.Carrier` are singleton spaces,
and the last-entry-one subtorus in `GL₁` contains only the identity.
A constant finite function and a Schwartz–Bruhat function on the singleton
give the expected form of the expansion. The declaration retains this case
without an additional rank restriction.

The source's proof applies Lemma (2.2.1) to the restrictions of Whittaker
functions to `H`. Its hypotheses require upper support bounds in each
coordinate and finite-dimensional operator spans on quotients by functions
vanishing for a sufficiently small coordinate. The proof relates the latter
quotients to Jacquet quotients for parabolics of type `(i, r-i)`. The lemma's
induction uses `|b| ≤ 1` and a small-coordinate threshold uniform in all the
other coordinates. These are substantial prerequisites for a later proof;
the present file defines only their final last-entry-one target. Extending
the result to a varying central coordinate belongs to the separate
full-torus result.

## Sources and imports

- H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms on
  GL(3) I*, Ann. of Math. (2) 109 (1979), no. 1, 169–212. Registered source
  `jps-1979-gl3-i`, SHA256
  `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
  Proposition (2.2), displays (2.2.1)–(2.2.2), its proof and Lemma (2.2.1),
  and Remark (2.2.5), printed pages 181–183 (one-based PDF pages 14–16),
  were read in the text layer and visually checked.
- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg
  Convolutions*, Amer. J. Math. 105 (1983), 367–464. Registered source
  `jpss-1983-rankin-selberg`, SHA256
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
  Section 2.1, printed page 385 (one-based PDF page 20), defining Whittaker
  type and its rank-one case, was read visually.

Both retained PDF hashes were checked. No source-specific erratum was found
in the checked project and Library notes or supplied literature index.

The module imports the published
`Langlands.Representation.Whittaker.AsymptoticStatement`, which supplies the
original telescope's definitions, notation and instances. That proposition
is a reference for the formulation; it is not assumed as a hypothesis or
used as a proof. The torus, roots and finite-function predicate are repeated
verbatim so that the new declaration is a closed proposition with the
requested telescope.
