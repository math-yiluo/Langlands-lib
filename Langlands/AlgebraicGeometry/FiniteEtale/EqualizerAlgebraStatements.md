# Finite étale closure of algebra equalizers

The module `Langlands.AlgebraicGeometry.FiniteEtale.EqualizerAlgebraStatements`
defines the proposition
`Langlands.AlgebraicGeometry.FiniteEtale.EqualizerAlgebraFiniteEtale`.
It states the closure property and provides no proof of it.

The complete parameter list is

```lean
(R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
[Algebra R A] [Algebra R B]
[Module.Finite R A] [Module.Finite R B]
[Algebra.Etale R A] [Algebra.Etale R B]
(f g : A →ₐ[R] B)
```

All three types lie in one arbitrary universe `u`. Thus `A` and `B` are
commutative `R`-algebras that are finite as `R`-modules and étale over `R`,
and `f` and `g` are arbitrary `R`-algebra homomorphisms from `A` to `B`.
Every displayed hypothesis is retained in the declaration's telescope.

The proposition returns `Prop` and has exactly the body

```lean
Module.Finite R (AlgHom.equalizer f g) ∧
  Algebra.Etale R (AlgHom.equalizer f g)
```

Here `AlgHom.equalizer f g` is Mathlib's actual subalgebra of `A` with
carrier `{a : A | f a = g a}`. Its inherited commutative ring and
`R`-algebra structures are used in both conjuncts. The first conjunct
asserts finiteness as an `R`-module; the second asserts étaleness over `R`.
The statement permits degenerate rings. It imposes no connectedness,
noetherianity, nontriviality, injectivity, surjectivity, or chosen split
presentation.

## Source and derived provenance

The registered external source is
`external-lean-reuse-snapshots-2026-10-21`, SHA256
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Within that retained folder, use
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/SchemeTheory/Pi1/FiniteEtale/Algebra/`
at NYLL commit `fbd320cd8b1b06487c58227e92eb135794267709`:

- `Equalizer.lean`, lines 478–516: the complete theorem
  `Algebra.Etale.equalizer`, including its hypotheses and proof.
- `Basic.lean`, lines 39–42: `Algebra.FiniteEtale` is a proposition class
  extending `Algebra.Etale R S` and `Module.Finite R S`.

The source theorem has the same commutative ring, algebra, module
finiteness, and étaleness hypotheses, with `S` and `T` renamed here to `A`
and `B`. Its conclusion is
`Algebra.FiniteEtale R (AlgHom.equalizer f g)`.
The present statement is derived by expressing the two parent properties
as a conjunction, with module finiteness first and étaleness second.
Conversely those two properties supply the source class's two parents.
This is the conjunction form of the source theorem, rather than a new
finite étale wrapper. The source's implicit ring arguments are explicit
arguments in this interface. The source proof and its helper modules are
not imported or ported by this statement module.

Attribution is documented by the registered supplement
`nyll-classfieldtheory-fbd320cd-supplement`, SHA256
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
In its `files/Nyll/EtaleFundamentalGroups/Pi1/` directory, see
`ATTRIBUTION.md`, the introduction and the entries for
`FiniteEtale/Algebra/Basic.lean` and `FiniteEtale/Algebra/Equalizer.lean`,
and the corresponding entries of `UPSTREAM.json`.
The source files credit Christian Merten and are NYLL-maintained
adaptations of pi1 code under Apache-2.0. Their pi1 comparison revision
`5c5c0171efc863ce9990171bdf46d7cb5fd582fb` is not established as the
historical NYLL import revision. The attribution records do not infer a
copyright holder where the original notice is absent.

## Formal scope

The Lean module imports Mathlib's subalgebra and étale definitions. It
introduces one proposition definition, with no theorem, axiom, or instance
asserting its conclusion. A proof of this exact proposition is a separate
obligation.
