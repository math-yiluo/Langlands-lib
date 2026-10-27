# Tempered scalar-character layers of the opposite Jacquet module

This pair states one analytic prerequisite for the opposite Jacquet quotient
criterion of Silberger 1979, Theorem 4.5.18. It isolates the temperedness of
the layers with exact scalar central character inside the actual opposite
normalized Jacquet representation of an irreducible tempered `GL_n`
representation. `Langlands.GLTemperedOppositeJacquetScalarLayerStatement` is a
proposition definition; this file proves none of the
representation-theoretic implications.

## Exact statement and actual objects

The statement quantifies over every prime `p`, every finite extension
`F : PadicField p` of `Q_p`, its actual topological data `T`, a positive rank `n`,
and a standard positive block shape `B` of `n`. Put
`M = B.Levi F.Carrier = ∏ i, GL_(B.size i)(F)` and `Q = M / Z(M)`, where `Z(M)`
is the full centre `Subgroup.center M`. The topology on `GL_n(F)` is the one
supplied by `T`; the proved instance `T.leviTopologicalGroup B` makes the
product Levi a topological group. Its topology is exactly that of the block
diagonal image, by `GeneralLinear.BlockShape.leviEquivContinuous`.

It then quantifies independently over a complex representation `π` of
`GL_n(F)` on a carrier `V : Type uV` and a complex representation `ρ` of `M` on
a carrier `W : Type uW`. The hypotheses are exactly

```text
Representation.IsIrreducible π,  T.IsTempered π,
UnitaryCentralCharacter ρ,
∃ S : Subrepresentation J,
  ∃ q : S.toRepresentation.IntertwiningMap ρ, Function.Surjective q,
```

with `J` the actual opposite normalized Jacquet representation specified
below. `T.IsTempered π` is the Library's analytic predicate: for every Haar
measure on the Borel central quotient of `GL_n(F)`, the representation is
admissible and has an actual smooth unitary scalar central character, and all
coefficient norms lie in `L^(2+ε)` for every `ε > 0`. A
`UnitaryCentralCharacter ρ` datum is an actual character
`Z(M) →* ℂˣ` with open kernel and values of norm one, through which every
central element acts on `W` by exactly that scalar. The occurrence hypothesis
supplies an actual invariant subspace `S` of `J` and an actual surjective
intertwiner from it onto `ρ`; thus `ρ` is a subquotient of `J`.

The conclusion is that, for every Borel measurable structure on `Q` and every
Haar measure `μ` on `Q`,

```text
IsTemperedModCenter ρ μ.
```

This is the Library predicate of `Tempered.lean`: `ρ` is admissible in the
all-open-subgroups convention, and there is a smooth unitary scalar central
character `c` such that `c.coefficientNorm ℓ v ∈ L^(2+ε)(Q, μ)` for every
smooth contragredient vector `ℓ`, vector `v` and real `ε > 0`. Admissibility of
`ρ` is part of the conclusion, not an assumption. The measure range is
nonempty by `T.exists_isHaarMeasure_leviCentralQuotient B` in
[TemperedInductionStatement](TemperedInductionStatement.md).

The statement does not assume that `ρ` is irreducible, of finite length,
unitarizable or semisimple, and it does not assume admissibility of `ρ`. It
requires an exact scalar central action, not a generalized central character.
The zero representation is allowed: whenever the witnesses exist for
`W = 0`, the conclusion also holds there, because every coefficient is zero
and the given character is a valid witness. The field universe `uF`, ambient
carrier universe `uV` and Levi carrier universe `uW` are independent; the
intertwiner `q` has source carrier in `uV` and target carrier in `uW`.

## Opposite Jacquet normalization

The definition of `J` is copied verbatim from
`GLTemperedDiscreteSeriesJacquetQuotientStatement` in
[DiscreteSeriesJacquetStatement](DiscreteSeriesJacquetStatement.md).
Let `P` be the standard upper block parabolic with product Levi `M`, and
let `δ = T.leviModulus B` be its positive full modulus:

```text
δ(m) = ∏_(i<j) |det m_i|^(B.size j) / |det m_j|^(B.size i),
```

with normalized absolute value `q^(-ord_F)`. The opposite parabolic `P̄`
has modulus `δ⁻¹` on `M`. The carrier of `J` is the actual opposite coinvariant
quotient `Jacquet.Coinvariants π (B.oppositeUnipotentSubgroup F.Carrier)`.
The action is the published generic construction
`Jacquet.normalizedActionOfModulus` on the embedded Levi, using the proved
normalizer inclusion
`B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup` and the full modulus
`δ⁻¹` transported to the embedded Levi. It is then pulled back to the product
Levi along `B.leviEquiv F.Carrier`. The generic construction multiplies by
the inverse square root of the supplied modulus, so on classes

```text
J(m) j(v) = δ_P̄(m)^(-1/2) j(π(m)v) = δ_P(m)^(1/2) j(π(m)v).
```

This is exactly Waldspurger's normalized Jacquet module
`π_P̄(m) j_P̄(v) = δ_P̄(m)^(-1/2) j_P̄(π(m)v)` of I.3, p.243, for the
semi-standard opposite parabolic `P̄`. Thus `J` is the opposite quotient with
the positive upper half normalization, not the upper quotient with a changed
scalar. The local `let` only specializes and transports this construction; it
introduces no new group data, axioms or representation obligations.

## Original sources

The primary source is J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques d’après Harish-Chandra* (2003), registered as
`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`. Its
one-based PDF page is the printed page minus 234. The context source is
A. J. Silberger, *Introduction to Harmonic Analysis on Reductive p-adic
Groups* (1979), registered as `silberger-1979-harmonic-analysis`, SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`, whose
one-based PDF page is the printed page plus six. No errata note for either
source was present in the current Library or the project notes.

| Source location | Use |
| --- | --- |
| W03 I.3, pp.243–244 | For an admissible representation, the direct sum decomposition into generalized eigenspaces of the split centre, indexed by its exponents; admissibility and the `δ_P^(-1/2)` normalization of the Jacquet module for a semi-standard parabolic; exactness of the Jacquet functor. |
| W03 §III.2, p.265 | An admissible representation, not necessarily irreducible, is tempered when all of its smooth coefficients satisfy the weak inequality `|f(g)| ≤ c Ξ(g)(1 + σ(g))^r`. |
| W03 Proposition III.2.2, pp.265–266 | For every admissible representation: temperedness is equivalent to `Re(χ) ∈ +ā^(G*)_P` for every semi-standard `P` and every exponent `χ` of `π_P`. |
| W03 §III.3 and Lemma III.3.1, p.267 | For an admissible tempered `π` and semi-standard `P`, `π_P = π_P^w ⊕ π_P^+`, the sums of the generalized exponent spaces with `Re(χ) = 0` and `Re(χ) ≠ 0`; the weak summand `π_P^w` is tempered. |
| W03 I.1(5), p.241; Theorem I.4.1, p.245; Lemma II.1.1, p.251 | Cartan double-coset volume, Jacquet coefficient asymptotic and `Ξ` estimate used by the analytic convention bridge below. |
| Silberger Theorem 4.5.18 and its proof, p.193 | Context only: the proof, adapted from Theorem 3.3.1, requires the auxiliary modules to be tempered and says the analogue of the Jacquet layer `V̄_χ` is tempered. The present statement isolates that analytic input for exact scalar layers; it is not the quotient criterion. |

Waldspurger works with an arbitrary connected reductive group; here the
source is specialized to `GL_n(F)` and to its standard block Levi `M`, which is
itself `GL`-type with full centre `Z(M) = A_M = ∏ F^×`, the split centre.
The opposite block parabolic contains the diagonal torus and is therefore
semi-standard.

## Derived argument beyond irreducible layers

The following is a derived mathematical route, not a verbatim source proof
and not a Lean proof. It uses no irreducibility, finite length or
semisimplicity of `ρ`.

1. *Source temperedness of `π`.* The analytic hypothesis `T.IsTempered π`
   gives the weak coefficient inequality for `π` by the reverse direction of
   the bridge recorded in
   [TemperedInductionStatement](TemperedInductionStatement.md), section
   “Analytic convention correspondence”. Thus `π` is admissible and tempered in
   the sense of W03 §III.2.
2. *The Jacquet module.* By the normalization above, `J` is `π_P̄`
   transported to the product Levi; it is admissible and smooth for the
   actual Levi topology (I.3). Since `M` has centre `A_M`, I.3 applied to the
   group `M` gives `J = ⊕_χ J_χ` over the exponents `χ` of `π_P̄`, the
   generalized `Z(M)`-eigenspaces. These summands are `M`-stable because `Z(M)`
   is central.
3. *The weak summand.* By §III.3 and Lemma III.3.1, the summand
   `J^w = ⊕_(Re χ = 0) J_χ` is an admissible tempered representation of `M`.
   Lemma III.3.1 is proved through Proposition III.2.2, which applies to every
   admissible representation; neither uses irreducibility of the summand.
4. *Scalar layers lie in the weak summand.* Let `S ⊆ J` and `q : S ↠ ρ` be the
   given witnesses and `c` the given unitary central character. As an
   admissible representation of `M`, `S` decomposes by I.3 as
   `⊕_χ (S ∩ J_χ)`. For `z ∈ Z(M)`, `(J(z) - χ(z))^d` vanishes on `S ∩ J_χ`,
   while `ρ(z)` is the scalar `c(z)`, so `(c(z) - χ(z))^d q(S ∩ J_χ) = 0`.
   Hence `q` kills `S ∩ J_χ` unless `χ = c`, and `ρ = q(S ∩ J_c)`. Since `c` is
   unitary, `Re(c) = 0`, so `S ∩ J_c` is a subrepresentation of `J^w`. Thus `ρ`
   is a quotient of a subrepresentation of the tempered module `J^w`. If `c` is
   not an exponent, `ρ = 0`.
5. *Admissible subquotients of tempered modules.* Smoothness passes to
   subrepresentations and quotients. For a compact open subgroup `K`, taking
   `K`-invariants is exact (averaging over `K`), so each `ρ^K` is a quotient of
   a subspace of the finite-dimensional `(J^w)^K`; every open subgroup contains
   a compact open one, which gives the Library's all-open-subgroups
   admissibility. For coefficients: a smooth functional on `ρ` composes with
   `q` to a smooth functional on `S ∩ J_c`. A smooth functional `ℓ` on a
   subrepresentation, fixed by a compact open `K`, extends to the smooth
   functional `ℓ' ∘ e_K` on `J^w`, where `e_K` is the `K`-average and `ℓ'` is any
   linear extension of `ℓ` from the subspace's `K`-invariants to `(J^w)^K`.
   Hence every smooth coefficient of `ρ` is a smooth coefficient of `J^w` and
   satisfies the weak inequality on `M`. So `ρ` is admissible and tempered in
   the sense of §III.2. Equivalently, by exactness of the Jacquet functor,
   the exponents of every Jacquet module of `ρ` are among those of `J^w`, and
   Proposition III.2.2(ii) applies.

## Central descent and the analytic bridge

Because `Z(M)` acts on `ρ` by the exact unitary scalar `c`, every coefficient
satisfies `|⟨ρ(mz)v, ℓ⟩| = |⟨ρ(m)v, ℓ⟩|` for `z ∈ Z(M)`. The norm therefore
descends to `Q`; this is the Library's `c.coefficientNorm`. The spherical
function `Ξ` of `M` is also `Z(M)`-invariant, so the weak inequality holds with
`σ(m)` replaced by its infimum over `mZ(M)`, a length function on `Q`. With
only a generalized central character the coefficient norms could grow
polynomially along `Z(M)` and would not descend, and the Library predicate
would have no scalar character to use. This is why the hypothesis is exact
scalar central action.

The forward direction of the bridge in
[TemperedInductionStatement](TemperedInductionStatement.md), “Analytic
convention correspondence”, then gives `L^(2+ε)(Q, μ)`. On a Cartan chamber of
`M` modulo `Z(M)` write `d(a) = δ_0(a) ≤ 1`. Double-coset volume is comparable
to `d(a)^(-1)` (I.1(5)), and `Ξ(a)` is bounded by `d(a)^(1/2)` times a
polynomial in the length (II.1.1). The `L^(2+ε)` integral is thus bounded by a
lattice sum of `d(a)^(ε/2)` times a polynomial, which converges because the
positive root sum is strictly positive in every noncentral chamber direction.
The group, modulus, centre and estimates are products over the blocks; no
tensor factorization of `ρ` is assumed. Smooth coefficients are locally
constant, hence measurable. The given character `c` is the witness for the
existential in `IsTemperedModCenter`.

Any two Borel Haar measures on the locally compact second-countable group `Q`
differ by a positive finite scalar, and such a scalar does not change membership
in `L^(2+ε)`. Hence the conclusion holds for every Borel measurable structure
and Haar measure, as stated. These are documented mathematical derivations,
not formal proofs.

## Boundaries

This is a derived lower-level statement, not a proof. It asserts no
square-integrability of a Levi representation, no quotient extraction, no
irreducibility of `ρ`, and none of the quotient or summand equivalences of
Silberger Theorem 4.5.18; those remain in
[DiscreteSeriesJacquetStatement](DiscreteSeriesJacquetStatement.md) and
[TemperedSupportStatement](TemperedSupportStatement.md). It introduces no new
coefficient classes or projector interfaces. The intended proof route uses
only the Waldspurger results above and the analytic bridge; it does not use
the regular Langlands head or exhaustion results, the square-integrable
Langlands classification, or any support, summand or exhaustion result whose
proof depends on the opposite Jacquet quotient criterion.
