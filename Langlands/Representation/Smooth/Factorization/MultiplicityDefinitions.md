# Multiplicity representation and tensor evaluation for a product group

This module builds the multiplicity space of a representation of a product
group `G₁ × G₂` with respect to a representation of the first factor. It
also builds the evaluation map from the external tensor product back to the
given representation. All declarations live in the namespace
`Langlands.ProductFactorization`. The module imports only Mathlib.

The module defines representations and intertwiners and proves their basic
formulas. It assumes no smoothness, admissibility, irreducibility or finite
dimension, and it does not claim that evaluation is injective, surjective or
an isomorphism.

## Setting and universes

The coefficient field is `ℂ`. Throughout:

- `G₁ : Type uG₁` and `G₂ : Type uG₂` are arbitrary groups (`Group`), in
  independent universes;
- `V : Type uV` is a complex vector space with a representation
  `ρ : Representation ℂ (G₁ × G₂) V`;
- `S : Type uS` is a complex vector space with a representation
  `σ : Representation ℂ G₁ S`, in a universe independent of `uV`.

The restriction of `ρ` to the first factor is the pullback
`ρ.comp (MonoidHom.inl G₁ G₂)`. Since Mathlib's `Representation` is an
abbreviation for a monoid homomorphism into linear endomorphisms, `ρ.comp` is
`MonoidHom.comp`. Here `MonoidHom.inl G₁ G₂ g₁ = (g₁, 1)`, so
`g₁` acts on `V` by `ρ (g₁, 1)`.

The multiplicity space is Mathlib's existing type of intertwiners

```
σ.IntertwiningMap (ρ.comp (MonoidHom.inl G₁ G₂))
```

that is, `ℂ`-linear maps `f : S → V` with `f (σ g₁ s) = ρ (g₁, 1) (f s)` for
all `g₁` and `s`. This type lives in `Type (max uS uV)`: the bundled linear
map lives there, and the intertwining condition is a proposition. In the
same-carrier case `S = ↥S₀.toSubmodule` for a subspace `S₀` of `V`, the
multiplicity space lives in `Type uV`. A development check confirmed both
universe assignments. The tensor representation below has carrier
`S ⊗[ℂ] σ.IntertwiningMap (ρ.comp (MonoidHom.inl G₁ G₂))`, again in
`Type (max uS uV)`, and `Type uV` in the same-carrier case.

## Declarations

### The second-factor operators

`TwoFactorExistence.secondOp ρ g₂` is the operator `ρ (1, g₂)` on `V`, bundled as
an intertwiner from `ρ.comp (MonoidHom.inl G₁ G₂)` to itself. It is an
intertwiner because `(1, g₂)` and `(g₁, 1)` commute in `G₁ × G₂`. Thus

```
ρ (1, g₂) (ρ (g₁, 1) v) = ρ (g₁, g₂) v = ρ (g₁, 1) (ρ (1, g₂) v).
```

The lemma `secondFactorIntertwiner_apply` records
`TwoFactorExistence.secondOp ρ g₂ v = ρ (1, g₂) v`.

### The multiplicity representation

`multiplicityRepresentation ρ σ` is a genuine
`Representation ℂ G₂ (σ.IntertwiningMap (ρ.comp (MonoidHom.inl G₁ G₂)))`,
i.e. a monoid homomorphism from `G₂` to the complex-linear endomorphisms of
the multiplicity space. Its value at `g₂` is Mathlib's linear postcomposition
map `IntertwiningMap.llcomp` with `TwoFactorExistence.secondOp ρ g₂`. So the
action is

```
(g₂ • f)(s) = ρ (1, g₂) (f s).
```

Postcomposition with an intertwiner is again an intertwiner, so `g₂ • f` stays
in the multiplicity space. Linearity of each operator in `f` is part of
`llcomp`. The two action laws are proved in the definition:

- `map_one'`: `ρ (1, 1) (f s) = f s`, since `(1, 1)` is the identity of
  `G₁ × G₂`;
- `map_mul'`: `ρ (1, g * h) (f s) = ρ (1, g) (ρ (1, h) (f s))`, since
  `(1, g * h) = (1, g) * (1, h)`.

The lemmas are:

- `multiplicityRepresentation_apply_apply` (simp):
  `multiplicityRepresentation ρ σ g₂ f s = ρ (1, g₂) (f s)`;
- `multiplicityRepresentation_apply`:
  `multiplicityRepresentation ρ σ g₂ f = (TwoFactorExistence.secondOp ρ g₂).comp f`.

### Tensor evaluation

`multiplicityEvaluation ρ σ` is an actual `Representation.IntertwiningMap`
from the external tensor product

```
Representation.tprod (σ.comp (MonoidHom.fst G₁ G₂))
  ((multiplicityRepresentation ρ σ).comp (MonoidHom.snd G₁ G₂))
```

to `ρ`. In this tensor representation, `(g₁, g₂)` acts on `s ⊗ f` by
`σ g₁ s ⊗ (g₂ • f)`. This is the external tensor convention of
`Langlands.AdmissibleProductFactorizationStatement`. The underlying linear
map is

```
TensorProduct.lift (IntertwiningMap.toLinearMapl σ (ρ.comp (MonoidHom.inl G₁ G₂))).flip.
```

Here `IntertwiningMap.toLinearMapl` is Mathlib's linear map
`f ↦ f.toLinearMap` from the multiplicity space to `S →ₗ[ℂ] V`. Its flip is the bilinear evaluation
`(s, f) ↦ f s`, and `TensorProduct.lift` makes it a linear map on
`S ⊗[ℂ] multiplicity space`. The lemma `multiplicityEvaluation_toLinearMap`
records this formula.

Equivariance is checked on pure tensors (`TensorProduct.ext'`). For `(g₁, g₂)`:

```
ρ (1, g₂) (f (σ g₁ s)) = ρ (1, g₂) (ρ (g₁, 1) (f s)) = ρ (g₁, g₂) (f s),
```

using the intertwining property of `f` and `(1, g₂) * (g₁, 1) = (g₁, g₂)`.

The pure-tensor formula `multiplicityEvaluation_tmul` (simp) is

```
multiplicityEvaluation ρ σ (s ⊗ₜ[ℂ] f) = f s.
```

### Inclusion of a subrepresentation

For any monoid `G : Type uG`, complex representation `τ` of `G` on
`W : Type uW` and `S₀ : Subrepresentation τ`, `subrepresentationInclusion S₀`
is the intertwiner from `S₀.toRepresentation` to `τ`. Its linear map is the
submodule inclusion `S₀.toSubmodule.subtype`. The intertwining identity holds
by definition, because `S₀.toRepresentation` is the restriction of `τ`. The
lemmas are `subrepresentationInclusion_apply` (simp; it sends `v` to `(v : W)`)
and `subrepresentationInclusion_injective`.

Applied to a subrepresentation `S₀` of `ρ.comp (MonoidHom.inl G₁ G₂)`, this
gives a canonical element of the multiplicity space for
`σ = S₀.toRepresentation`. The lemma
`multiplicityEvaluation_tmul_subrepresentationInclusion` states

```
multiplicityEvaluation ρ S₀.toRepresentation (v ⊗ₜ[ℂ] subrepresentationInclusion S₀) = (v : V)
```

for every `v : S₀.toSubmodule`.

## Provenance and relation to other work

This is an internal construction, not a definition quoted from a source. It
packages the standard multiplicity-space construction: the space of
`G₁`-homomorphisms from a representation of `G₁` into the restriction of a
representation of `G₁ × G₂`, the induced `G₂`-action, and evaluation.

Context: D. Flath, *Decomposition of representations into tensor products*,
Proc. Sympos. Pure Math. 33, Part 1 (1979), Theorem 1 (printed p.179;
literature ID `flath-1979-tensor-products`). Flath proves existence of the
factors on printed p.180 through Hecke-algebra modules and an inductive
limit. He then justifies uniqueness of the factor classes by noting that the
restriction of `W` to `Gᵢ` is `Wᵢ`-isotypic. Flath defines no multiplicity
space or evaluation map. This module neither reproduces nor quotes his proof.
It supplies only a concrete Hom/evaluation API, with no claim about isotypy or
bijectivity.

The published proof module
`Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof`
contains local declarations for the special case where `σ` is
`U.toRepresentation` for a subrepresentation `U` of the first-factor
restriction: `Langlands.TwoFactorExistence.Mult`, `multRep`, `eval`, `evalHom`
and `subtypeHom`. The present module allows an arbitrary `σ` on a carrier in an
independent universe `uS`. For example, a factor-uniqueness argument needs
`Hom_{G₁}(σ₁, ρ|G₁)` for a factor `σ₁` that is not a subspace of `V`. The
present module only imports Mathlib. The two APIs agree definitionally on the
common special case, but this module does not import the proof module or state
that comparison.

Mathlib names used: `Representation.IntertwiningMap`,
`Representation.IntertwiningMap.llcomp`,
`Representation.IntertwiningMap.toLinearMapl`,
`Representation.IntertwiningMap.isIntertwining`, `Representation.tprod`,
`MonoidHom.comp`, `MonoidHom.inl`, `MonoidHom.fst`, `MonoidHom.snd`,
`TensorProduct.lift`, `TensorProduct.ext'`,
`Subrepresentation.toRepresentation` and `Submodule.subtype`.

The existing `Langlands.TwoFactorExistence.first`, `second`, their action laws,
and `secondOp` are now housed in this algebraic module.
[`TwoFactorExistenceProof`](TwoFactorExistenceProof.md) imports these unchanged
declarations for its admissible factorization argument.
