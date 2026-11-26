# An unramified strictly Henselian extension of a DVR

`Langlands.CommutativeAlgebra.UnramifiedStrictHenselianDvrExtensionStatement.{u}`
states that a strict henselization of a discrete valuation ring exists, recording
the properties used to compare an abelian variety over the fraction field with its
base change to the fraction field of the strict henselization. The module states
the proposition and does not prove it.

## Statement

For every commutative domain `V : Type u` that is a discrete valuation ring there
exist

- a type `W : Type u` with a commutative ring structure, which is a domain and a
  discrete valuation ring;
- the structure of a Henselian local ring on `W` (`HenselianLocalRing W`) and the
  property that the residue field `ResidueField W` is separably closed
  (`IsSepClosed`), so that `W` is strictly Henselian;
- an algebra structure `V → W` that is a local homomorphism
  (`IsLocalHom (algebraMap V W)`);

such that

1. `(maximalIdeal V).map (algebraMap V W) = maximalIdeal W`, that is, the maximal
   ideal of `V` generates the maximal ideal of `W`; equivalently, the image of a
   uniformizer of `V` is a uniformizer of `W`;
2. `Algebra.IsSeparable (ResidueField V) (ResidueField W)`, for the residue field
   algebra induced by the local homomorphism (Mathlib's instance
   `Algebra (ResidueField V) (ResidueField W)`): every element of the residue field
   of `W` is algebraic over the residue field of `V` with separable minimal
   polynomial.

Since the residue field of `W` is separably closed and separable algebraic over the
residue field `κ` of `V`, it is a separable algebraic closure of `κ`.

## Source

This is the existential content of the strict henselization, from the Stacks
Project (registered source `stacks-strict-henselian-dvr-extension-2026-11-16`, files
`04GP.html` and `0AP3.html`).

- [Tag 04GP, Lemma 10.155.2](https://stacks.math.columbia.edu/tag/04GP): for a
  local ring `(R, 𝔪, κ)` and a separable algebraic closure `κ ⊂ κ^sep` there are
  local maps `R → R^h → R^sh` such that `R^sh` is strictly Henselian, `𝔪 R^sh` is the
  maximal ideal of `R^sh`, and `κ^sep = R^sh / 𝔪 R^sh` as an extension of `κ`. Taking
  `W = R^sh` with `R = V` gives the Henselian and separably closed residue field
  conditions, condition 1, and condition 2 (the residue field of `W` is `κ^sep`). The
  map `R → R^sh` is local: the preimage of the maximal ideal `𝔪 R^sh` is a proper
  ideal containing `𝔪`, hence equal to `𝔪`.
- [Tag 0AP3, Lemma 15.46.11](https://stacks.math.columbia.edu/tag/0AP3): a
  Noetherian local ring is a discrete valuation ring if and only if its strict
  henselization is. A Mathlib discrete valuation ring is Noetherian and local, so
  `W` is a discrete valuation ring; it is a domain, as every discrete valuation ring.

The statement keeps neither the universal property of the strict henselization, nor
its presentation as a filtered colimit of étale `V`-algebras, nor a chosen
identification of the residue field with a given separable closure. The common
universe `u` reflects the size of the Stacks construction, a colimit indexed by
étale algebras of finite presentation over `V`; the source does not discuss
universes.

## Relation to the Library

`Langlands.CommutativeAlgebra.StrictHenselianDvrExtensionStatement` asks for a
faithfully flat strictly Henselian discrete valuation ring over `V` and says nothing
about the maximal ideal or the residue field extension. The present statement asks
in addition for condition 1 and for the separability condition 2. Condition 1
implies faithful flatness: the local homomorphism `V → W` is then injective, because
the maximal ideal of `W` is nonzero, so `W` is a torsion-free, hence flat, module over
the discrete valuation ring `V`, and a flat local homomorphism is faithfully flat. Together, conditions 1 and 2 say that `W` has
ramification index one over `V` in the sense of Bosch, Lütkebohmert and Raynaud,
*Néron Models* (1990), §7.2, printed p. 176 (a uniformizer of `V` gives a
uniformizer of `W` and the residue extension is separable). This is the hypothesis
of §7.2, Theorem 1 (ii) there, under which the formation of Néron models is
compatible with the base change `V → W`.
