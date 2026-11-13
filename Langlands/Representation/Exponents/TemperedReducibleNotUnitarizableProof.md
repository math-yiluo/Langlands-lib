# Renard VII.2.6, Remark: a tempered representation that is not unitarizable (proof)

Authors: Worker 128 (assembly and the `𝔾_m` example), Worker 100 (temperedness criterion).
Module `Langlands.Representation.Exponents.TemperedReducibleNotUnitarizableProof`.

## Statement proved

`Langlands.Aubert.General.RepresentedParabolic.temperedReducibleNotUnitarizable` proves the
published statement
`Langlands.Aubert.General.RepresentedParabolic.TemperedReducibleNotUnitarizableStatement`.
It has exactly the statement's type and adds no hypotheses. For every nonarchimedean local
field `k`, there are a connected reductive group `G` over `k` and a smooth representation `π`
of `G(k)` that is tempered (the published `IsNormalizedExponentTempered`, which includes
admissibility) and not unitarizable.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, registered
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, VII.2.6, Remark (printed
p.232 / PDF p.238). The Remark only says that without irreducibility the Corollary ("an
irreducible tempered representation is unitary") can fail. Renard gives no example. The example
used here, `𝔾_m` acting on `ℂ²` through `x ↦ [[1, ord(x)], [0, 1]]`, is our own choice.

## Proof

Take `G = 𝔾_m` (`ShearRepresentation.Gm.group k`, connected reductive by
`Gm.isConnectedReductive`) and `π = shearRep (gmValuation k)`. This is the representation
`x ↦ [[1, ord(x)], [0, 1]]` on `ℂ²` (lifted to universe `v`). It is bundled as a smooth
representation by `SmoothRep.of` with `Gm.isSmooth_shearRep_gmValuation`. The `𝔾_m` facts come
from the helper module `Langlands.Representation.Exponents.ShearRepresentation` (see its
Markdown).

- **Not unitarizable:** `Gm.not_isUnitarizable_shearRep_gmValuation`. The valuation takes the
  value `1 ≠ 0` at a uniformizer, and a nonzero shear does not preserve any positive definite
  Hermitian form.
- **Tempered:** apply Worker 100's criterion
  `isNormalizedExponentTempered_of_mul_comm_of_sq_sub_one_eq_zero` (helper module
  `Langlands.Representation.Exponents.CommutativeUnipotentTempered`; see its Markdown). It
  takes:
  - admissibility (`Gm.isAdmissible_shearRep_gmValuation`);
  - commutativity of `𝔾_m(k)` (`Gm.mul_comm_rationalPoints`);
  - unipotence `(π(g) - 1)² = 0` (`sq_shearRep_sub_one`).

  Under these hypotheses every normalized Jacquet exponent is the trivial character. Its
  normalized real part `0` lies in every nonnegative root cone, and a compatible root
  presentation always exists.

The proof first fixes the instances that the statement introduces with `haveI`/`letI`: the
affine structure morphism `hG.isAffineHom`, and the evaluation topology
`RationalPointFamily.pointTopology` on `𝔾_m(k)`. It then introduces the
`LocallyCompactSpace` and `NonarchimedeanGroup` instances that the statement quantifies over.

## Relation to the source

The statement records Renard's Remark as an existence claim, and that is what is proved. The
witness (`𝔾_m` and the shear representation) and the temperedness argument are internal.
The Remark itself contains no proof, so neither is taken from it.
