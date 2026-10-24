# Block-character absorption for normalized upper parabolic induction

Author: Worker 346.

This module constructs explicit equivalences on the Library's actual induced
function spaces. For an actual p-adic field `F`, compatible topological data `T`,
and ordered block shape `B`, put `χ = T.leviHalfModulus B`. If `e_i(g)` has `g`
in coordinate `i` and identity matrices in every other coordinate, the block
characters are

```
χ_i(g) = χ(e_i(g)),       χ_i⁻¹(g) = χ(e_i(g))⁻¹.
```

For any family `σ_i` of complex block representations, the two constructed
`Representation.Equiv` maps have types

```
normalizedProductInduced(σ_i)
  ≃ smoothInduced_P^G(externalTensor(χ_i ⊗ σ_i)),
normalizedProductInduced(χ_i⁻¹ ⊗ σ_i)
  ≃ smoothInduced_P^G(externalTensor(σ_i)).
```

The external tensor actions on the right are inflated along the actual Levi
projection of `B.parabolic F.Carrier`. All inductions use that same standard
upper block parabolic and act by right translation. Both equivalences, and
both inverse maps, send a function `f` to the function with precisely the same
values: `(E f)(g) = f(g)` and `(E.symm f)(g) = f(g)`.

## Generic construction

Within `Langlands.Induction.SmoothCharacter`, `coordinate` restricts an
open-kernel character of a finite product of groups along
`MonoidHom.mulSingle`. The coordinate inclusion is continuous, so the
restricted kernel is open. `inverse` uses the same kernel to construct the
inverse smooth character. No commutativity of the component groups is assumed.

`factorization` proves `χ(g) = ∏ i, χ_i(g_i)`. Its proof is finite-support
induction: remove one coordinate by setting it to one, express the original
element as its coordinate inclusion times the remaining element, and use
multiplicativity. This avoids applying a commutative-group product formula to
noncommutative general linear groups.

`external_coordinate_twist` proves equality of the actual external tensor
actions:

```
external (fun i => twist χ_i σ_i) = twist χ (external σ).
```

The proof checks equality on pure tensors, pulls the individual scalars outside
the multilinear tensor map using `map_smul_univ`, and applies character
factorization. All of this works over any commutative coefficient ring and
arbitrary modules; the index, component-group and module universes are independent.

## Canonical block specialization

The remaining declarations are in `Langlands.PadicField.TopologicalData`.

- `blockHalfModulus` and `blockInverseHalfModulus` are the two explicit
  unit-valued block homomorphisms. `blockHalfCharacter` and
  `blockInverseHalfCharacter` bundle them with open-kernel proofs. Their
  `_toMonoidHom` lemmas identify the underlying homomorphisms, and the
  `isOpen_ker_blockHalfModulus` and `isOpen_ker_blockInverseHalfModulus`
  lemmas expose the certificates directly.
- `blockHalfModulus_factorization` identifies the product of the restrictions
  with `T.leviHalfModulus B`, the underlying homomorphism of the published
  `T.leviHalfCharacter B`. `blockInverseHalfModulus_factorization` gives its
  inverse version.
- `blockHalfModulus_upperUnipotent` proves triviality on the actual standard
  upper unipotent subgroup of the individual block. The proof computes its
  determinant as the product of its diagonal entries, all equal to one.
  Its coordinate inclusion therefore lies in `T.normOneLevi B`. The existing
  kernel inclusion for `leviModulus`, followed by `leviHalfModulus_eq_one`,
  gives triviality of the half character. The inverse lemma follows by inversion.
- `blockHalfTwist` and `blockInverseHalfTwist` twist each factor on its original
  carrier. `blockTensor_halfTwist` and `blockTensor_inverseHalfTwist` specialize
  the generic external tensor equality to the canonical half modulus.
- `halfAbsorptionInducing_eq` and `inverseHalfAbsorptionInducing_eq` identify
  the actual inflated parabolic covariance actions. The inverse identity uses
  `twist_twist_inv` to cancel the two scalar characters.
- `halfAbsorptionInducingEquiv` and `inverseHalfAbsorptionInducingEquiv` have
  identity underlying linear equivalences of the tensor space. The action
  identities supply their intertwining proofs.
- `normalizedProductHalfAbsorptionEquiv` and
  `normalizedProductInverseHalfAbsorptionEquiv` apply the published
  `Induction.smoothInducedEquiv` to those parabolic equivalences. Thus they are
  genuine equivalences of the existing smooth induced representations, with
  inverse maps supplied by inverse postcomposition. The four `_eval` and
  `_symm_eval` lemmas are definitional equalities proving preservation of values.
- `isAdmissible_blockHalfTwist_iff` and
  `isAdmissible_blockInverseHalfTwist_iff` apply the published
  `Langlands.isAdmissible_twist_iff` using the constructed open kernels.

The field universe `uF` and common block-carrier universe `uV` are independent;
there is no bound on either. The induced carrier has universe `max uF uV`.
All ordered positive block sizes are retained. The definitions even permit the
empty rank-zero shape, although the requested applications have positive total
rank. The equivalences require no finite-dimensionality, smoothness,
irreducibility or admissibility assumption on the block representations.
Smooth induction takes smooth vectors as in the existing Library definition.
The admissibility lemmas concern the factors individually; no assertion about
admissibility or finite length of the induced representation is made here.

## Provenance and conventions

This is an internal algebraic construction from the published modules
`Induction.BlockFactors`, `Induction.Parabolic`, `Induction.Equivalences`,
`Tensor.Finite`, `Twist.AlgebraProof`, `Twist.AdmissibilityProof`,
`Group.GL.BlockModulus` and `Group.GL.UpperUnipotent`. It introduces no alternate
induction model and assumes no desired equivalence. The character is the positive
square root of the existing explicit upper block modulus. The module does not
reprove its interpretation as a Haar scaling character.

The normalization convention is checked against W. Casselman,
*Introduction to the theory of admissible representations of p-adic reductive
groups*, draft of 1 May 1995, §2.4, printed/PDF p.26, and §3.1, printed/PDF p.32.
Section 2.4 uses left covariance `f(hg) = σ(h)f(g)` and right translation;
§3.1 defines normalized induction as induction of `σ δ_P^(1/2)`. These are
exactly the covariance and sign inherited here. Casselman's inducing data are
smooth; the present construction also works for arbitrary representation data
because it uses the Library's smooth-vector induced carrier. The coordinate
factorization and tensor absorption maps above are elementary derived
constructions, not separately quoted theorems of Casselman. The source pages
were read, and the normalization formula on p.32 was checked visually.

Registered source: `casselman-1995-admissible-representations`, SHA256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
The retained file is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
No source-specific erratum for this normalization was found in the supplied
public notes. Finite generation, finite length, Whittaker heredity and comparisons
between upper and lower parabolics are outside this construction.
