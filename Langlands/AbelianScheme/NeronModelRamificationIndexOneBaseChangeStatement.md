# Néron models and extensions of ramification index one

`Langlands.AbelianScheme.NeronModelRamificationIndexOneBaseChangeStatement`
states that the formation of Néron models of abelian varieties commutes
with base change along an extension of discrete valuation rings of
ramification index one. The module states the proposition and does not
prove it.

## Statement

The universe is `u`. The data are:

- a discrete valuation ring `V` with fraction field `K`
  (`IsFractionRing V K`);
- a discrete valuation ring `W` with fraction field `L`
  (`IsFractionRing W L`);
- an algebra structure `V → W` that is a local homomorphism
  (`IsLocalHom (algebraMap V W)`);
- the hypothesis `(maximalIdeal V).map (algebraMap V W) = maximalIdeal W`:
  the maximal ideal of `V` generates the maximal ideal of `W`, that is, a
  uniformizer of `V` maps to a uniformizer of `W`;
- the hypothesis `Algebra.IsSeparable (ResidueField V) (ResidueField W)`,
  for the residue-field algebra structure induced by the local
  homomorphism: the residue extension is separable algebraic;
- an abelian scheme `B` over `Spec K` and a Néron model
  `N : NeronModel V K B` (from `Langlands/AbelianScheme/NeronModel.lean`).

The conclusion is

`NeronModelInfra.NeronModelPropertyBundle W L
  ((CommGroupScheme.baseChange (Spec.algebraMap V W)).obj N.group).X.hom`.

Here `CommGroupScheme.baseChange (Spec.algebraMap V W)` is the actual
scheme pullback along `Spec W → Spec V`, with its induced group law, so
the group scheme in question is `N ×_V W`. The property bundle says that
its structure morphism to `Spec W` is smooth, separated, locally of finite
type and quasi-compact, and that for every smooth scheme `T` over `Spec W`
in universe `u`, restriction to generic fibres over `Spec L` is a bijection
from `W`-morphisms `T → N ×_V W` to `L`-morphisms between the generic
fibres. That is, `N ×_V W` is a Néron model of its own generic fibre
`N ×_V L`. The statement does not involve a `K`-algebra structure on `L`:
for any such structure making the square `V → W → L`, `V → K → L` commute,
this generic fibre is identified through the generic identification of `N`
with the base change of `B` to `L`.

## Relation to the sources

Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §7.2, printed
pp. 176–177 (PDF pp. 183–184):

- Before Theorem 1 (printed p. 176): for a faithfully flat extension
  `R ⊂ R'` of discrete valuation rings, `R'` has ramification index 1 over
  `R` if a uniformizing element of `R` gives rise to a uniformizing element
  of `R'` and the residue extension of `R'/R` is separable (with reference
  to §3.6, Definition 1).
- Theorem 1 (ii): if `R'/R` has ramification index 1, then `X_K` has a
  Néron model `X` over `R` if and only if `X_{K'}` has a Néron model `X'`
  over `R'`, and then the base change morphism `X ⊗_R R' → X'` is an
  isomorphism. The theorem is stated for torsors under smooth group
  schemes of finite type, and so applies to abelian varieties.
- Corollary 2 (printed p. 177): the formation of Néron models is
  compatible with extensions `R'/R` of ramification index 1.

The Lean statement is the part of Theorem 1 (ii) that applies here: given
the Néron model `N` of the abelian variety, `N ⊗_V W` is a Néron model of
the generic fibre over `L`. The Lean hypotheses are those of ramification
index 1. The hypothesis on maximal ideals also gives the faithful flatness
assumed by the source: the image of a uniformizer of `V` is a uniformizer
of `W`, hence nonzero, so the kernel of `V → W` is a prime ideal not
containing the uniformizer and is zero; then `W` is torsion-free and hence
flat over `V`, and a flat local homomorphism of local rings is faithfully
flat. A strict henselization `V → V^sh` (Grothendieck, SGA 7 I, Exposé IX,
3.4.0; BLR §7.4, printed p. 183) and the completion `V → V̂` (BLR §7.2,
Corollary 2) are such extensions. The Néron model properties are those of
BLR §1.2, Definition 1, as recorded in `NeronModelPropertyBundle`; the
source's mapping property for all smooth `R'`-schemes is asked here for
smooth schemes in the universe `u` of the rings.
