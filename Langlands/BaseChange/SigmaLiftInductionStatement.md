# Sigma-lifts and irreducible normalized parabolic induction

`Langlands.BaseChange.SigmaLiftInductionStatement.{u, v, uV, uW}` is a
Prop-valued statement of compatibility of local cyclic base change with
irreducible normalized parabolic induction.

## Statement

Let `F : Type u` and `E : Type v` be nonarchimedean local fields, with their
valuative relations and topologies. Assume `CharZero F`, an `F`-algebra structure
on `E`, and `IsModuleTopology F E`. Let `σ : E ≃ₐ[F] E`, let `l n : ℕ`, and assume
`IsCyclicAlgebra σ l` and `0 < n`.

For an ordered block shape `B : GeneralLinear.BlockShape n`, write
`m = B.length` and `nᵢ = B.size i`. Its parts are positive and sum to `n`.
For each `i : Fin m`, choose complex vector spaces `V i : Type uV` and
`W i : Type uW` and admissible representations `π i` of `GeneralLinear nᵢ F`
on `V i` and `P i` of `GeneralLinear nᵢ E` on `W i`. Choose an intertwiner
`A i : SigmaIntertwiner σ nᵢ (P i)` and a scalar `c i : ℂ`.

Assume that every `π i` and `P i` is irreducible. For each `i`, assume
`IsSigmaLift σ l (π i) (hπ i) (P i) (hP i) (A i) (c i)`, where
`hπ` and `hP` are the supplied admissibility proofs. Form

```text
πB = (LocalFieldData.ofInstances F).normalizedProductInduced B π,
PB = (LocalFieldData.ofInstances E).normalizedProductInduced B P.
```

Assume that both `πB` and `PB` are irreducible. The conclusion asserts
admissibility proofs `hπ' : IsAdmissible πB` and `hP' : IsAdmissible PB` and an
intertwiner `A' : SigmaIntertwiner σ n PB` such that

```text
IsSigmaLift σ l πB hπ' PB hP' A' (∏ i, c i).
```

Here irreducibility is Mathlib's `Representation.IsIrreducible`, and the product
of scalars is Mathlib's `Finset.prod` over all indices of `Fin B.length`.
`IsAdmissible` includes smoothness. The representation spaces on each side
share one universe, `uV` for the inducing spaces over `F` and `uW` for those
over `E`. The induced spaces have the universes of the existing induction
construction.

## Conventions and scope

The products above are the Library's normalized induction from the standard
block upper triangular parabolic, acting on the smooth induced function space
of the external tensor product of the diagonal block representations.
Its modulus uses the normalized absolute value of the corresponding local
field.

`SigmaIntertwiner σ n PB` is the existing type of representation equivalences
from `PB` to its pullback by `entrywiseAut σ n`. In terms of the underlying
linear automorphism, it requires `A' ∘ PB(g) = PB(g^σ) ∘ A'`.
`IsSigmaLift` requires a nonzero scalar and equality of the twisted trace
with that scalar times the ordinary trace for all Haar measures and all
concordant test-function pairs.

Henniart–Lemaire specify the induced intertwiner
`ι_α(A₁ ⊗ ⋯ ⊗ Aₘ)`. If `T = A₁ ⊗ ⋯ ⊗ Aₘ`, their operator on induced functions
is

```text
ι_α(T)(ξ)(g) = T(ξ(g^(σ⁻¹))).
```

The Lean conclusion quantifies existentially over the intertwiner `A'`.
The product of the constants records Henniart–Lemaire's normalization for
their specific induced operator.

Each inducing lift has `c i ≠ 0`, so `q = ∏ i, c i` is nonzero. If an
intertwiner for `PB` realizes a lift with any nonzero scalar `d`, multiplying
its linear automorphism by `q / d` gives another intertwiner and multiplies
the twisted distribution by `q / d`, hence realizes scalar `q`. A nonzero
scalar multiple of a linear equivalence is again a linear equivalence. The
scaling identity is `twistedDistribution_smul` from
`Langlands.BaseChange.TwistedCharacter.Basic`, imported by
`Langlands.BaseChange.TwistedCharacter`. Thus prescribing `q` in the
existential conclusion is equivalent to asking for some intertwiner with
some nonzero lift constant.

Both products need separate irreducibility hypotheses, as in the source
lemma. The factor hypotheses permit reducible products on either side.

The admissibility proofs of the products are included in the conclusion
because `IsSigmaLift` takes them as arguments. The Library proves
preservation of admissibility under normalized parabolic induction.
See `Langlands.Parabolic.normalizedInductionAdmissibility` and its all-field
port `Langlands.AllField.Parabolic.normalizedInductionAdmissibility`.

The assumption `0 < n` matches the source's positive total rank and partitions
into positive parts. It excludes the unused case of the trivial group
`GL_0`. Henniart–Lemaire reduce to a field `E` in II.4.3, immediately before the
lemma. Both fields are assumed to be nonarchimedean local fields here so that
the Library's normalized product induction is available. `IsModuleTopology F E`
requires the extension topology to be the module topology induced from `F`.

`CharZero F` ensures agreement between the Library regularity convention
inside concordance (separable characteristic polynomial) and
Henniart–Lemaire's squarefree characteristic-polynomial convention. The two
agree over perfect fields, in particular in characteristic zero.

For each factor, and again for rank `n` in the conclusion, local `haveI`
declarations supply `T2Space`, `LocallyCompactSpace`, and
`TotallyDisconnectedSpace` for both general linear groups, using
`LocalFieldTopology.generalLinear_t2Space`,
`LocalFieldTopology.generalLinear_locallyCompactSpace`, and
`LocalFieldTopology.generalLinear_totallyDisconnectedSpace`.
These are precisely the topology certificates required by `IsSigmaLift`.

## Sources and a future proof

The primary source is Guy Henniart and Bertrand Lemaire, *Changement de base et
induction automorphe pour GL_n en caractéristique non nulle*, Mémoires de la
Société Mathématique de France 124 (2011), II.4.4, Lemme, printed p. 85
(PDF p. 93). The preceding paragraph defines the induced intertwiner; II.4.3
on the same page supplies the field reduction. The definition of a sigma-lift
is II.2.7, printed p. 67 (PDF p. 75).

- Literature ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
- Retained file `literature/Henniart-Lemaire, Changement de base et induction automorphe pour GLn en caracteristique non nulle (2011).pdf`.
- SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.

Henniart–Lemaire derive the lemma from II.4.5, printed pp. 86–88
(PDF pp. 94–96). Formula (1) descends twisted orbital integrals to the Levi
subgroup, citing their reference [57, Proposition 4.4.9]. Formula (2) is the
twisted van Dijk formula for the character distribution of an induced
representation. Formula (3) expresses its twisted character function in terms
of the Levi character function. On printed p. 88 the twisted relative
discriminant is identified with the ordinary relative discriminant at the
norm. Together with the untwisted formulas, this supplies the source route
for comparing induced character identities. A future proof needs inputs
established independently of induction compatibility.

A second source is James Arthur and Laurent Clozel, *Simple Algebras, Base
Change, and the Advanced Theory of the Trace Formula*, Annals of Mathematics
Studies 120, Princeton University Press (1989), Chapter 1, §6.2, printed
pp. 52–53 (PDF pp. 66–67). In reducing Theorem 6.2 to the discrete case, they
induce the intertwining operator and use the Atiyah–Bott formula for induced
characters, citing [11(b), Theorem 2]. That discussion treats tempered
representations; the general irreducible-product statement here is taken
from Henniart–Lemaire's lemma.

- Literature ID `arthur-clozel-1989-base-change`.
- Retained file `/home/taskhub/central-library/Arthur-Clozel--Simple algebras, base change, and the advanced theory of the trace formula (book)--1989.pdf`.
- SHA-256 `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
