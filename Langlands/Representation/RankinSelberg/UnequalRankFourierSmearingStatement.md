# Global and pointwise JPSS Fourier smearing

`Langlands.RankinSelberg.UnequalRankFourierSmearingStatement.{uF,uV} F T n j k`
is a proposition definition. This module supplies no proof.

Worker 462 authored the statement and its source correspondence. The shared
interface incorporates Worker 103's requirement for a global formula with
genuine integrability, Worker 12's shared-helper design, and Worker 180's
unreviewed generic same-model averaging and conditional pointwise-cutoff
interface. Worker 180's draft also motivates the finite algebraic integration
route below; none of that draft is imported or treated as a proved Library
result. The published `UnequalRankGammaPropagationStatement` describes the
same-G consumer; the adjacent-span argument is another consumer.

## Data and scope

Let `r = n + ((j+1) + k + 1)`. For every prime `p`, every
`F : PadicField.{uF} p`, every supplied `T : F.TopologicalData`, and every
`n,j,k : ℕ`, the proposition installs the topology and local-field structure
of `T` and their Borel measurable space. It quantifies over:

- every unitary additive character `ψ` and supplied scalar additive Haar
  measure `ν`;
- every independent carrier `V : Type uV` with only `AddCommGroup V` and
  `Module ℂ V`, and every smooth representation `π` of the actual
  `GeneralLinear (r+1) F.Carrier`;
- every actual `ℓ : glFunctionals ψ r π` and every coefficient
  `f : (coefficientModel π ℓ).toSubmodule`;
- every pair `κ,Φ` of actual Schwartz–Bruhat functions on
  `Fin (n+1) → F.Carrier` satisfying `IsRowFourierPair ψ ν κ Φ`.

The universes `uF` and `uV` are independent. Smoothness is the published
open-stabilizer condition. There is no topology, norm, completeness or
finite-dimensionality assumption on `V`. No irreducibility, admissibility,
Whittaker-type, nonzero-functional or nonzero-coefficient premise is imposed.
The scalar Haar measure is arbitrary; no self-dual normalization is selected.

The Fourier-pair premise means exactly

`Φ(y) = ∫ z, ψ.complex (∑ i, z i * y i) * κ(z) ∂rowMeasure ν (n+1)`.

It uses the plus sign, without conjugation. `rowMeasure ν (n+1)` is the actual
product of the supplied scalar Haar measure in all coordinates. The proposition
does not assert Fourier closure, inversion or surjectivity for arbitrary `ν`.

## One coefficient and both conclusions

There is one `f₁` in precisely the same `coefficientModel π ℓ` such that, for
every `h` in the whole group `GeneralLinear (r+1) F.Carrier`, the scalar
function

`z ↦ κ(z) * f(h * unequalRankSmearingUnipotent n j k z)`

is integrable for `rowMeasure ν (n+1)`, and its integral equals `f₁(h)`.
Integrability is an explicit part of the conclusion, so this equality is
not relying on the zero value assigned to a nonintegrable Bochner integral.
Here and below model coefficients are evaluated by the nested subtype values
`f.val.val`.

For every `g : GeneralLinear (n+1) F.Carrier` and every rectangular matrix
`X : Matrix (Fin (j+1)) (Fin (n+1)) F.Carrier`, that same witness satisfies

`f₁(unequalRankMatrix (j+1) k g X)
  = Φ(X(Fin.last j)) * f(unequalRankMatrix (j+1) k g X)`.

The block matrix is the published actual invertible matrix
`[g,0,0; X,I_(j+1),0; 0,0,I_(k+1)]`. Its last rectangular row is
`X(Fin.last j)`. The smearing matrix is the published
`unequalRankSmearingUnipotent n j k z`, with value `I+E(z)`, where
`E[a,b] = z[a]` for `a < n+1` and `b = n+j+2`, and zero elsewhere.
Both matrices have rank `r+1`. The parameters `n,j,k` may each be zero.

## Original sources and derived formulation

The originals were read directly, with the displayed matrices and formulas
inspected visually:

- Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions*,
  Amer. J. Math. 105 (1983), 367–464, registered
  `jpss-1983-rankin-selberg`, printed pp.394–395, the Fourier-smearing lemma
  inside the proof of Theorem 2.7 and its use in §2.8.
  Retained original:
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`;
  SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- The same authors, *Automorphic Forms on GL(3) I*, Ann. of Math. (2) 109
  (1979), 169–212, registered `jps-1979-gl3-i`, Proposition 4.1.4 and
  Lemma 4.1.5, printed pp.188–190, especially the conjugation argument on
  p.189 and preservation of the Whittaker model on p.190.
  Retained original:
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`;
  SHA256 `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.

No source-specific errata note was found in the supplied project notes or
literature. The source's leading rank `t` is `n+1`, its middle size is `j+1`,
its full rank is `r+1`, and its last trailing block has size `k`.
Its global definition averages `H(h U(z))` with the reflected transform
of the cutoff, and its stated conclusion integrates the last rectangular
row. The 1979 proof explicitly conjugates the same upper-column matrix and
computes its unipotent character as `ψ(zx)`.

This statement isolates the pointwise identity underlying that argument and
retains the global average required by the dual-transform consumer. It replaces
the source's reflected inverse-Fourier choice by an explicit supplied
plus-sign Fourier pair. The arbitrary-Haar, independent-universe and merely
smooth coefficient-image formulation is a derived internal extension;
neither paper states this Lean predicate verbatim.

The intended proof first takes a preimage of `f` under the surjective
coefficient map. A compactly supported locally constant scalar weight times
its smooth orbit has an algebraic finite-sum integral in `V`. Testing that
finite sum against the functional composed with `π(h)` gives the global
scalar integrability and integral formula for every `h`, without a Banach
structure on `V`. The published `AlgebraicIntegrand`, `AlgebraicIntegral`,
`Hecke.ActionIntegrand` and `Whittaker.Algebraic` APIs support this route.

For `B = unequalRankMatrix (j+1) k g X`, the required matrix calculation is
that `B U(z) B⁻¹` lies in the actual upper-unipotent subgroup and its
standard character is
`ψ.complex (∑ i, X (Fin.last j) i * z i)`.
Coefficient covariance, commutativity of field multiplication, and the
supplied Fourier pair then yield the pointwise cutoff. This calculation
and the averaging argument are proof obligations, not hypotheses or
established results of this module.

No quotient integration, second representation, spectral variable,
rational continuation, common generator, functional equation or
row-integrated corollary is asserted here. Any later integration of the
pointwise identity must prove its own convergence and interchange conditions.
