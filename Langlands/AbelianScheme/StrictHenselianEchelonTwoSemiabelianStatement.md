# The Galois criterion of semistable reduction from inertia of echelon two

`Langlands.AbelianScheme.StrictHenselianEchelonTwoSemiabelianStatement` is
the implication "inertia of echelon two implies semistable reduction" of
Grothendieck's Galois criterion of semistable reduction, SGA 7 I,
Exposé IX, Proposition 3.5, (iv) ⇒ (i), stated over a strictly Henselian
discrete valuation ring. The module states the proposition and does not
prove it.

## Statement

The universe is `u`. The data are:

- a discrete valuation ring `W` that is a `HenselianLocalRing` with
  separably closed residue field (`IsSepClosed (ResidueField W)`), that is,
  a strictly Henselian discrete valuation ring;
- a fraction field `L` of `W` (`IsFractionRing W L`);
- an abelian scheme `A` over `Spec L`, that is, an abelian variety over
  `L`;
- a Néron model `N : NeronModel W L A` (from
  `Langlands/AbelianScheme/NeronModel.lean`), with its generic
  identification;
- a natural number `ℓ` with `Fact ℓ.Prime` and `IsUnit (ℓ : W)`, so that
  `ℓ` differs from the residue characteristic of `W`.

The hypothesis is asked for every algebraically closed field `Ω` in
universe `u`, every geometric point `s : Spec Ω ⟶ Spec L`, every family
`hu` of invertibility witnesses for the powers of `ℓ` in `Γ(Spec L, ⊤)`,
and all `g` and `h` in `FundamentalGroup s (geometricFiberFinite s)`.
Writing `ρ` for
`Tate.PrimeAdic.rationalMonodromyRepresentation s (geometricFiberFinite s)
torsionFiniteEtale A ℓ hu`, the action on the rational `ℓ`-adic Tate module
`V_ℓ(A)` from `Langlands/AbelianScheme/Tate/PrimeMonodromy.lean`, it says

`((ρ g).toLinearMap - 1) * ((ρ h).toLinearMap - 1) = 0`,

the product being composition of `ℚ_ℓ`-linear endomorphisms of `V_ℓ(A)`.
That is, the finite étale fundamental group of `Spec L` acts on `V_ℓ(A)`
unipotently of echelon two.

The conclusion is `N.HasGeometricSemiabelianReduction`, the predicate of
`Langlands/AbelianScheme/PotentialSemistableReductionStatement.lean`: the
identity component of the geometric special fibre of `N`, over the
algebraic closure of the residue field of `W`, is an extension of an
abelian variety by a split torus, the torus being the scheme-theoretic
kernel of a smooth surjective homomorphism onto the abelian variety.

## Unipotence of echelon two

For a group `G` acting linearly on a module `U`, the two following
conditions are equivalent:

1. there is a submodule `U'` of `U`, stable under `G`, such that `G` acts
   trivially on `U'` and on `U / U'`;
2. `(g - 1) (h - 1) = 0` on `U` for all `g` and `h` in `G`.

If `U'` is as in 1, then `(h - 1) U ⊆ U'` and `g - 1` vanishes on `U'`,
which gives 2. Under 2 the invariants `U^G` serve as `U'`. The source states
the hypothesis in the first form; the Lean hypothesis is the second.

## Relation to the sources

Grothendieck, *Modèles de Néron et monodromie*, SGA 7 I, Exposé IX
(Lecture Notes in Mathematics 288, 1972), in the registered transcription:

- Proposition 3.5 (critère galoisien de réduction semi-stable): for a trait
  `S`, the abelian variety `A_K` has semistable reduction (i) if and only if
  (iv) the inertia group `I` acts on `U = T_ℓ(A(K̄))` unipotently of
  echelon 2, that is, there is a submodule `U'` of `U` stable under `I` with
  `I` acting trivially on `U'` and on `U / U'`. The proof of (iv) ⇒ (i)
  passes to the Henselian trait (3.4.0). With `V = U^I` the fixed part, `W`
  the toric part and `⊥` the orthogonal for the form (2.5.1) of a
  polarization (notation (2.5.3)), (iv) amounts to `(h - 1) U ⊆ V` for all
  `h` in `I`, that is, to `I` acting trivially on `U / V`; by duality `I`
  acts trivially on `V^⊥`, so `V^⊥ ⊂ V`, which is (ii). The orthogonality
  theorem 2.4, in the form (2.5.2), gives `W = V ∩ V^⊥`, so under (ii)
  `V^⊥ = W`. In the diagram of inclusions (2.5.4), `V / W` has rank `2α`
  and `V^⊥ / W` has rank `2λ`, where `α` and `λ` are the abelian and
  unipotent ranks of the identity component of the special fibre (2.1.9).
  Hence (ii) gives `λ = 0`, which is (i).
- The displayed formula (2.5.5) reads `rang V/V ∩ V^⊥ = rang V/W = 2λ`,
  and the proof of 3.5 cites it in the form "`λ = 0` is equivalent to
  `V = V ∩ V^⊥`". Both numerators lack a perpendicular: the formula that
  agrees with the diagram (2.5.4), and with the rank `2α` of `V / W` stated
  just before (2.5.5), is `rank V^⊥ / (V ∩ V^⊥) = rank V^⊥ / W = 2λ`, and
  `λ = 0` is equivalent to `V^⊥ = V ∩ V^⊥`, that is, to (ii).
- Remarque 3.5.1: condition (iv) depends only on the action of `I` on
  `U ⊗ ℚ_ℓ`.

Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §7.4, Theorem 6,
printed p. 184 (PDF p. 191), state the same equivalence: `A_K` has
semi-abelian reduction over `R` if and only if (b) there is a submodule
`T'` of `T_ℓ(A_K(K_s))`, stable under the inertia group `I`, with `I`
acting trivially on `T'` and on `T / T'`. They refer to SGA 7 IX 3.5 for
the proof. Their inertia group is `I = Gal(K_s/K^sh)` (§7.4, printed
p. 183).

The translation to the Lean data is as follows.

- When `W` is strictly Henselian it is its own strict henselization, so
  `L = K^sh`. For a geometric point of `Spec L`, the finite étale
  fundamental group of `Spec L` is the absolute Galois group `Gal(L_s/L)`,
  which is the inertia group `I` of the sources, acting on the Tate module
  of `A`.
- The source's module is the integral Tate module `U`; the Lean hypothesis
  is on `V_ℓ(A) = U ⊗ ℚ_ℓ`. Since `U` is a free `ℤ_ℓ`-module of finite
  rank, it embeds in `U ⊗ ℚ_ℓ`, so `(g - 1) (h - 1) = 0` on `U ⊗ ℚ_ℓ`
  gives the same identity on `U`, as in Remarque 3.5.1. Thus the Lean
  hypothesis implies condition (iv).
- The hypothesis is asked at every geometric point of `Spec L`. The actions
  at two geometric points are conjugate, so the condition at one point is
  equivalent to the condition at all of them.
- The conclusion is the geometric form of semistable reduction. Since the
  residue field of `W` is separably closed, a torus over it is already
  split, and the identity component of the special fibre stays an extension
  of an abelian variety by a torus over the algebraic closure.

The source proves the criterion for every trait. The Lean statement is the
case of a strictly Henselian trait, in the direction (iv) ⇒ (i).
