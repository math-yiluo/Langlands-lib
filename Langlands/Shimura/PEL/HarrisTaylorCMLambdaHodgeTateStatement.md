# The Hodge–Tate property of the λ-adic cohomology of the CM Shimura varieties

This module states, as an unproved proposition, that the Library's `λ`-adic
cohomology `H^d(S_U ×_F F̄, W)_λ` of a small CM level `U` with Harris's
coefficient system `W` has a Hodge–Tate decomposition at every finite place
of `F` above the residue characteristic `ℓ` of `λ`. The representation is
viewed as a representation of `Gal(F̄/F)` on a `ℚ_ℓ`-vector space. The module
also defines the predicate used for this, the Hodge–Tate decomposition of the
underlying `ℚ_ℓ`-representation of a representation with coefficients in a
`ℚ_ℓ`-algebra.

The module has three declarations:

* `Langlands.GaloisRepresentation.HodgeTate.HasUnderlyingHodgeTateDecomposition`
  (a predicate on local Galois representations);
* `Langlands.GaloisRepresentation.HasUnderlyingHodgeTateDecompositionAt`
  (the same predicate at a place of a number field);
* `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.CMHarrisLambdaCohomologyHodgeTateStatement`
  (the statement).

## Motivation and scope

Taylor's removal of the cohomological multiplicity (the published
`TaylorMultiplicityRemovalStatement`, module
`Langlands.Galois.TaylorMultiplicityRemovalStatement`) needs a Hodge–Tate
decomposition at a place above `ℓ`. Harris (1999), proof of Theorem 5.7,
printed pp. 313–314 (PDF pp. 15–16), notes that Taylor's argument extends from
trivial coefficients to the coefficient systems `W` because these are of
geometric origin. They "come from tensor powers of the cohomology of the
universal abelian scheme over the PEL type Shimura variety `S_K(N)`". Thus "the
Hodge–Tate decomposition, an ingredient in Taylor's argument, is available for
these cohomology groups". This module states that input for the whole
fixed-level cohomology. The proof is a separate obligation.

The statement is about the whole cohomology `H^d(S_U ×_F F̄, W)_λ` at one level
and in one degree. It is not about an isotypic part. It asserts the
decomposition with some list of twists `k 0, …, k (r − 1)`, where `r` is the
dimension over `ℚ_ℓ`. Repetitions in the list are allowed, so the multiplicity
of each Hodge–Tate weight is not fixed. The statement does not compute the
twists from `W`, and it says nothing about how the decomposition interacts
with the Hecke action.

### Why the decomposition is not `K_λ`-linear

The decomposition is that of the underlying `ℚ_ℓ`-representation. It is
linear over `C_w` and Galois-equivariant, and it is not required to commute
with the action of `K_λ`. A `K_λ`-linear decomposition into free summands
`(C_w ⊗_{ℚ_ℓ} K_λ)(k i)`, as in the published `HasHodgeTateDecompositionAt`,
would force the same multiset of Hodge–Tate weights at every embedding of
`K_λ` into `C_w`. That uniformity fails within the scope of this statement.

The following example is due to Reviewer 2555 (review of the withdrawn
candidate `53ec878e`). Take `E = ℚ`, `F` imaginary quadratic, `n = 3` and a
division algebra `A` with signature `(2, 1)`. Take `K = F` and a coefficient
prime `ℓ` inert in `F`, so that `K_λ = F_w` is quadratic over `ℚ_ℓ`. The
determinant of the regular action of `A` is an algebraic character (the cube of
the reduced norm). Its Hodge exponents at the two coefficient embeddings are
`6` and `3`, read off from the signature. At small enough level the geometric
monodromy of this rank-one coefficient system is trivial. So `H^0` on a
geometric component has weight `6` at one coefficient embedding and weight
`3` at the other, up to a common sign convention. The underlying `ℚ_ℓ`-form
has no such constraint: there the two weights simply both occur.

This is also why the statement does not supply the hypothesis of the
published `TaylorMultiplicityRemovalStatement`. That hypothesis is a
`K_λ`-linear decomposition of the form `⊕_{i < n} ((C_v ⊗_{ℚ_ℓ} L_λ)(k i))^m`.
Two things would be needed to connect this statement to Taylor's: passing to
the isotypic part, and a `K_λ`-linear refinement with `n` distinct twists each
of multiplicity `m`. Neither is formalized here, and the second does not hold
for every coefficient system, as the example shows.

## The predicate `HasUnderlyingHodgeTateDecomposition`

Let `p` be a prime and `F` a finite extension of `ℚ_p`. Let `Λ` be a field
with a topology and a `ℚ_p`-algebra structure. Let
`A : Objects F Λ` be a continuous representation of `Gal(F̄/F)` on a
finite-dimensional `Λ`-vector space `V`. Let `n : ℕ` and `k : Fin n → ℤ`.

`HodgeTate.HasUnderlyingHodgeTateDecomposition p F Λ A n k` says the
following. Make `V` a `ℚ_p`-vector space through `ℚ_p → Λ`. Then there is a
`C_F`-linear isomorphism `Φ : (Fin n → C_F) ≃ C_F ⊗_{ℚ_p} V`. It must satisfy,
for every `σ ∈ Gal(F̄/F)` and every `x`:

`Φ (i ↦ χ(σ)^{k i} · σ(x i)) = (σ ⊗ ρ(σ)) (Φ x)`.

Here `C_F` is the published `HodgeTate.Completed p F`, the completion of `F̄`,
and `σ` acts on it by `HodgeTate.galoisRingHom` (as `galoisLinear` on the
tensor product). `χ(σ)` is the published `HodgeTate.cyclotomic p σ`, the
`p`-adic cyclotomic character. So `Fin n → C_F`, with this action, is
`⊕_{i < n} C_F(k i)`. Since `Φ` is an isomorphism of `C_F`-vector spaces, `n`
equals the dimension of `V` over `ℚ_p`.

This is the standard notion of a Hodge–Tate representation applied to `V` as
a `ℚ_p`-representation, as in Faltings's theorem below. The difference from
the published `HodgeTate.HasHodgeTateDecomposition p F Λ A n m k` (module
`Langlands.Galois.Local.HodgeTate`) is twofold. The summands here are `C_F(k i)`
rather than `(C_F ⊗_{ℚ_p} Λ)(k i)`, and there is no condition that `Φ` commute
with `Λ`. The multiplicity parameter `m` is dropped, since repetitions in `k`
already express multiplicities.

`HasUnderlyingHodgeTateDecompositionAt lam A v hv n k` is the same predicate
for a `λ`-adic representation `A : LambdaAdic K L lam` of `Gal(K̄/K)`, with `K`
and `L` number fields. It applies the predicate to the restriction
`atFinitePlace v A` of `A` to a decomposition group at a finite place `v` of
`K`, with `hv : residuePrime v = residuePrime lam`. The prime is
`residuePrime lam`. `F` is the completion `K_v` and `Λ` is the completion
`L_λ`, and both are `ℚ_ℓ`-algebras through their canonical `ℓ`-adic
structures. These are exactly the conventions of the published
`HasHodgeTateDecompositionAt`.

## Inputs of the statement

The section variables are those of `HarrisTaylorCMLambdaCohomologyObjects`
(and of `HarrisTaylorCMLambdaCohomology`). They are the central simple unitary
data `D` (with `A` the central simple `F`-algebra), the charts `C`, the
conditional statements `preservation … htor`, the representability statement
`q`, a small level `U : SmallCMLevel D`, the algebraic representation `ρ` of
`D.rationalInvolution.baseChange K` on a finite-dimensional `K`-vector space
`W`, the place `p` of `ℚ` giving the coefficient prime `ℓ`, the statements
`existence` and `geometry`, the rigidity hypothesis `hRigid` at `U`, the
derived-category instances, a place `l : FinitePlacesAbove K p` (the place
`λ` of the coefficient field `K`), and a degree `degree` (the `d` above).

## The statement

`CMHarrisLambdaCohomologyHodgeTateStatement D C preservation … htor q U ρ p
existence geometry hRigid l degree : Prop` says the following. Suppose:

* `_hdiv : ∀ a : A, a ≠ 0 → IsUnit a`, that is, `A` is a division algebra;
* `hfin : CMHarrisLambdaCohomologyFiniteDimensional … l degree`, that
  `H^d(S_U ×_F F̄, W)_λ` is finite-dimensional over `K_λ`;
* `hcont : CMHarrisLambdaCohomologyContinuous … l degree`, that the Galois
  action on it has continuous orbit maps.

Then for every finite place `w : Global.FinitePlace F` with
`hw : residuePrime w = residuePrime l.1`, there are `r : ℕ` and
`k : Fin r → ℤ` such that

`HasUnderlyingHodgeTateDecompositionAt l.1 (cmHarrisLambdaCohomologyObjects … hfin hcont) w hw r k`.

In words, the restriction of `H^d(S_U ×_F F̄, W)_λ` to `Gal(F̄_w/F_w)`, as a
`ℚ_ℓ`-representation, satisfies
`C_w ⊗_{ℚ_ℓ} H^d(S_U ×_F F̄, W)_λ ≅ ⊕_{i < r} C_w(k i)`. The elaborated type of
the declaration is `Prop`.

The division-algebra hypothesis is Harris's setting. The Introduction of
Harris (1999), printed p. 299 (PDF p. 1), says that the unitary groups `GG` are
associated to division algebras with involution over CM fields. Their Shimura
varieties are then proper, which is the case covered directly by Faltings's
theorem below. The hypothesis restricts the statement, which is otherwise
stated for every `D`. That the Shimura varieties are proper is not formalized.

## Provenance

The statement is a specialization, to the Library's cohomology objects, of the
Hodge–Tate input named by Harris (1999), *Galois properties of cohomological
automorphic forms on GL(n)*, J. Math. Kyoto Univ. 39 (1999), proof of
Theorem 5.7, printed pp. 313–314 (PDF pp. 15–16). The source is
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, PDF SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`. Harris
says only that the Hodge–Tate decomposition is available. He does not say
whether it is meant linearly over the coefficient field. The `ℚ_ℓ`-form is
what the geometric argument below gives for every coefficient system, and the
example above shows that the `K_λ`-linear form with free summands can fail.

The underlying theorem is Faltings, *p-adic Hodge theory*, J. Amer. Math.
Soc. 1 (1988), Chapter III, Theorem 4.1, printed p. 298 (PDF p. 45; PDF page =
printed page − 253). The source is
`provided-1991b7d5032d5fe94ca932ccbeccf293bafd80aa29a350ed2fda545cf46b9440`,
PDF SHA-256
`2eb8b02f9e3e7662e1e79229488ee7e98240e23f221f1c9aaa7bec79cf329024`. Let `K`
be a field complete for a discrete valuation, of characteristic `0`, with
perfect residue field of characteristic `p` (Introduction, 1(b), printed
p. 255). Let `X` be smooth and proper over `K`, and let `D` be a divisor with
normal crossings. Faltings's theorem then gives `Gal(K̄/K)`-equivariant
isomorphisms
`H^n_et((X − D) ⊗ K̄, ℚ_p) ⊗ Ĉ ≅ ⊕_{a+b=n} H^a(X, Ω^b(dlog ∞)) ⊗ Ĉ(−b)`,
with `Ĉ` the completion of `K̄`. Theorem 4.1 on printed p. 298 prints the
twist as `Ĉ(−a)`, and so do the two displays for the proper case earlier on
that page. The Introduction, 1(b), printed p. 255, states the proper case of
the same theorem with `Ĉ(−b)`. This module follows the Introduction and reads
the `(−a)` on p. 298 as a misprint. For `n = 1`, the printed `(−a)` would
twist `H^1(X, O_X)` instead of the differentials `H^0(X, Ω^1)`. Since the
statement here only asserts that some list of twists exists, the discrepancy
does not affect it.

Faltings's theorem concerns constant `ℚ_p` coefficients, and it gives exactly
the `ℚ_p`-form of the decomposition used here. Two steps are needed to obtain
the statement here, and neither is formalized. The first is the reduction
Harris indicates: `H^d(S_U ×_F F̄, W)_λ` is a Galois-stable `K_λ`-direct
summand of `H ⊗_{ℚ_ℓ} K_λ`, up to Tate twist, where `H` is the `ℚ_ℓ`-cohomology
of a scheme built from the universal abelian scheme over `S_U`. The second is
that this transfers the decomposition. As a `ℚ_ℓ`-representation,
`H ⊗_{ℚ_ℓ} K_λ` is a direct sum of `[K_λ : ℚ_ℓ]` copies of `H`, hence
Hodge–Tate. A direct summand of a Hodge–Tate `ℚ_ℓ`-representation is
Hodge–Tate, and so is a Tate twist.

The coefficient prime `ℓ` is the residue characteristic of `λ`, given by `p`
in the Library's variables. The places `w` are places of the CM field `F`,
over which the Library's Shimura varieties `S_U` are defined. The twists are
integers, and the convention for `(k)` is that of the published
`HasHodgeTateDecomposition`: `σ` acts on `C_w(k)` by `χ(σ)^k σ`.
