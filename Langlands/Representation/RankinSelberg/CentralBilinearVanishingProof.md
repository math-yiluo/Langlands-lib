# Finite spectral support of determinant-twisted bilinear forms

`Langlands.RankinSelberg.centralBilinearVanishing` proves exactly the published
`CentralBilinearVanishingStatement.{uF,uV,uW} F T n`. The field and two carrier
universes are independent. The proof installs the supplied `T.topology` and
assumes precisely admissibility and finite group-algebra generation of each
representation. It adds no finite-length, irreducibility, Whittaker-functional,
central-character, or spectral hypothesis.

## Implemented proof

Set `m = n + 1` and let `z = centralSpectralElement T m`, the scalar matrix of
the inverse of the chosen uniformizer. The published
`centralSpectralElement_mem_center` certifies that `z` is central. Apply
`isIntegral_centralAction_of_admissible_finiteType` separately to the two
representations. This shows that both operators `ρ z` and `σ z` satisfy monic
complex polynomials, even when the carriers are infinite dimensional.

The finiteness theorem used here evaluates an intertwiner on finitely many
group-algebra generators. Smoothness supplies an open stabilizer for each
generator; admissibility makes the corresponding target fixed spaces finite
dimensional. Evaluation is injective, so the endomorphism algebra is finite
dimensional. Its elements are integral, and forgetting equivariance preserves
integrality. This argument uses no GL finite-length theorem.

Apply `exists_finite_bilinear_power_spectral_support` to these two operators
and the positive exponent `m`, with positivity supplied by `Nat.succ_pos n`.
It produces one finite set `E` before any exponent `s` or bilinear form `β`.
Internally this helper obtains a monic annihilator of the tensor operator from
the two integral operators. A bilinear form lifts to a functional on the tensor
product; scalar covariance extends to polynomial covariance. The monic
annihilator therefore forces that functional to vanish outside its finite root
set. Pulling that root set back through the positive power `m` again gives a
finite set, using the nonzero polynomials `X^m - C c`.

For any `s` outside `E`, specialize the assumed full-group covariance of `β`
to `z`. The published `determinantWeight_centralSpectralElement` identifies
its scalar as

```text
determinantWeight (normalizedAbsoluteValue T) z (-s)
  = (spectralPoint T.residueCardinality s)^(n + 1).
```

The identity uses the actual supplied normalization: an inverse uniformizer has
absolute value `q`, so the scalar matrix has determinant absolute value `q^m`.
The helper also justifies the complex-power calculation for this natural-number
base. This is exactly the covariance required by the spectral-support theorem,
which gives `β = 0`.

Rank one is covered by `n = 0`. A zero carrier is allowed on either side; the
integrality and tensor arguments remain valid in that case. No set of finitely
many exponents is asserted: `E` consists of spectral values `q^(-s)` and works
for every covariant form simultaneously.

## Provenance and scope

Worker 353 authored this proof by adapting the compiled private feasibility
example to the published target. The proof imports the statement unchanged and
uses only the published `IntertwinerFiniteness`, `BilinearSpectralSupport`, and
`CentralSpectralElement` helpers.

The mathematical role is the residual bilinear step of Jacquet,
Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions* (1983), §2.10,
printed p.398: after restriction to Schwartz functions vanishing at zero, the
remaining form is `γ(f,f′) Φ(0)` and `γ` has the displayed determinant covariance.
The registered source is `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The implemented operator-polynomial route is internal derived mathematics;
it does not claim to follow the source's twisted-contragredient argument.

This module proves the central bilinear statement only. Frobenius reciprocity,
mirabolic finite length, the irreducible pairing bounds, and the full equal-rank
trilinear uniqueness theorem remain separate obligations.
