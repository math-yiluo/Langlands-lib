# Unipotence of echelon two of an open subgroup of inertia on Tate modules

`Langlands.AbelianScheme.StrictHenselianEchelonTwoInertiaStatement` is
Grothendieck's theorem that an open subgroup of the inertia group acts
unipotently, of echelon two, on the `ℓ`-adic Tate module of an abelian
variety. It is stated over the fraction field of a strictly Henselian
discrete valuation ring, with the Library's finite étale fundamental groups
and rational prime-adic Tate modules. The module states the proposition and
does not prove it.

## Statement

The universe is `u`. The data are:

- a discrete valuation ring `W` that is a `HenselianLocalRing` with
  separably closed residue field (`IsSepClosed (ResidueField W)`), that is,
  a strictly Henselian discrete valuation ring;
- a fraction field `L` of `W` (`IsFractionRing W L`);
- an abelian scheme `A` over `Spec L`, that is, an abelian variety over
  `L`;
- a natural number `ℓ` with `Fact ℓ.Prime` and `IsUnit (ℓ : W)`, so that
  `ℓ` differs from the residue characteristic of `W`;
- an algebraically closed field `Ω` in universe `u` with a geometric point
  `s : Spec Ω ⟶ Spec L`;
- a family `hu` of invertibility witnesses for the powers of `ℓ` in
  `Γ(Spec L, ⊤)`.

Write `ρ` for
`Tate.PrimeAdic.rationalMonodromyRepresentation s (geometricFiberFinite s)
torsionFiniteEtale A ℓ hu`, the action of the finite étale fundamental group
`FundamentalGroup s (geometricFiberFinite s)` on the rational `ℓ`-adic Tate
module `V_ℓ(A)` of `A` at `s`, from
`Langlands/AbelianScheme/Tate/PrimeMonodromy.lean`. The conclusion is that
there is an open subgroup `H` (an `OpenSubgroup` of the fundamental group,
for the topology of `Langlands/AlgebraicGeometry/FiniteEtale/Definitions.lean`,
induced by the actions on the finite geometric fibres of finite étale covers)
such that

`((ρ g).toLinearMap - 1) * ((ρ h).toLinearMap - 1) = 0`

for all `g` and `h` in `H`, the product being composition of
`ℚ_ℓ`-linear endomorphisms of `V_ℓ(A)`.

## Unipotence of echelon two

For a group `G` acting linearly on a module `U`, the two following
conditions are equivalent:

1. there is a submodule `U'` of `U`, stable under `G`, such that `G` acts
   trivially on `U'` and on `U / U'`;
2. `(g - 1) (h - 1) = 0` on `U` for all `g` and `h` in `G`.

If `U'` is as in 1, then `(h - 1) U ⊆ U'` and `g - 1` vanishes on `U'`,
which gives 2. Conversely, under 2 the invariants `U' = U^G` serve in 1: by
definition `G` acts trivially on them, and `(h - 1) x` lies in `U^G` for
every `x` and `h`, which says that `G` acts trivially on `U / U^G`. The
first condition is the definition of unipotence of echelon 2 in SGA 7 I,
Exposé IX, Proposition 3.5 (iv); the Lean statement uses the second.

## Relation to the sources

Grothendieck, *Modèles de Néron et monodromie*, SGA 7 I, Exposé IX
(Lecture Notes in Mathematics 288, 1972), §3, in the registered
transcription:

- Proposition 3.5 (iv) defines the condition that the inertia group `I`
  acts on `U = T_ℓ(A(K̄))` unipotently of echelon 2: there is a submodule
  `U'` of `U` stable under `I` such that `I` acts trivially on `U'` and on
  `U / U'`.
- Corollaire 3.7: for a trait `S`, there is an open subgroup `I'` of `I`
  whose action on `U` is unipotent of echelon 2. The proof uses the
  equivariant isomorphism
  `H¹(A_K̄, ℤ_ℓ) ≅ Hom(T_ℓ(A(K̄)), ℤ_ℓ)` to reduce to the action of `I` on
  `H¹`, proved with resolution of singularities of excellent schemes of
  dimension 2.

That cohomological assertion is in SGA 7 I, Exposé I (written by
P. Deligne): Théorème 3.5 (p. I-12) says that for a smooth projective
curve `C` over the fraction field of a discrete valuation ring the inertia
group acts on `H¹(C_η̄, ℚ_ℓ)` by quasi-unipotent automorphisms of echelon 2,
and, after reduction to a strictly local base, that there is an open
subgroup `I₁` of `I` with `(T - 1)² = 0` on `H¹` for `T` in `I₁`.
Remarque 3.6 (p. I-13) deduces the same for an abelian variety, a quotient
of a Jacobian, on `H¹(A, ℚ_ℓ)` and on `T_ℓ(A)`.

The translation to the Lean data is as follows.

- `S = Spec W` is a strictly Henselian trait and `K = L`. For a geometric
  point `s` of `Spec L`, the finite étale fundamental group of `Spec L` at
  `s`, with its profinite topology, is the absolute Galois group
  `Gal(L^sep/L)` with its Krull topology. Since the residue field of `W`
  is separably closed, this whole group is the inertia group `I` (Bosch,
  Lütkebohmert and Raynaud, *Néron Models*, §7.4, printed p. 183, take
  `I = Gal(K_s/K^sh)`, and here `K^sh = L`).
- The source's module is the integral Tate module `U`; the Lean statement
  uses the rational Tate module `V_ℓ(A) = U ⊗ ℚ_ℓ`. The identity
  `(g - 1) (h - 1) = 0` on `U` gives the same identity on `U ⊗ ℚ_ℓ` by
  extension of scalars, so the Lean conclusion follows from the source's.
  Remarque 3.5.1 of Exposé IX notes that the condition depends only on the
  action on `U ⊗ ℚ_ℓ`.

The source proves the theorem for every trait, with `I` the inertia group.
The Lean statement is the case of a strictly Henselian trait.

The elementwise form of the monodromy theorem,
`Langlands.AbelianScheme.AbelianInertiaQuasiUnipotentStatement`, has the
same data and asks only that each `g` have a positive power acting
unipotently. The present statement asks for one open subgroup on which the
whole action has echelon two.
