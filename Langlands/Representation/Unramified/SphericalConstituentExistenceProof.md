# Existence of spherical constituents of unramified principal series

This module proves the published proposition
`Langlands.Unramified.SphericalConstituentExistenceStatement` from
`Representation/Unramified/SphericalClassificationStatement`. The theorem is

```lean
theorem Langlands.Unramified.SphericalExistence.sphericalConstituentExistence :
    SphericalConstituentExistenceStatement.{uF}
```

Its type is exactly the target, with the target's single universe parameter
`uF`. It keeps all of the target's quantifiers: every prime `p`, every
`F : PadicField.{uF} p` with its canonical topology, every rank `r + 1`, and
every ordered tuple `z : Fin (r + 1) → ℂˣ`. The tuple may be nonunitary, and
the proof does not assume that the induced representation is irreducible. The
witness is an actual `AutomorphicObject.{uF, uF} F r.succPNat`, that is, an
irreducible admissible smooth representation whose carrier is in universe
`uF`. Its carrier is a quotient of a subrepresentation of the actual induced
space `principalSeriesOfTuple F z`. The witness satisfies both parts of
`IsSphericalConstituent`. Its fixed vectors under the published
`sphericalSubgroup F r = GL_(r+1)(O_F)` are nonzero. It is also an actual
subquotient: there is a subrepresentation `S` of the principal series and a
surjective intertwiner from `S` onto the witness. The only axioms used are
`propext`, `Classical.choice` and `Quot.sound`.

## Literature

Borel, *Automorphic L-functions*, Corvallis Part II (1979), §10.4, printed
page 45 (PDF page 54; source `borel-1979-automorphic-l-functions`). Borel
notes that `G(k) = B(k) U` for a special maximal compact subgroup `U`, so the
`U`-fixed vectors of the normalized principal series `PS(χ)` form a space of
dimension at most one. He also says that at most one irreducible constituent of
`PS(χ)` has a nonzero `U`-fixed vector. For `GL_(r+1)` and
`U = GL_(r+1)(O_F)`, the Lean proof uses the same decomposition the other way
round. It builds a nonzero `U`-fixed vector of the principal series, and then
a spherical irreducible quotient of the subrepresentation that vector
generates. The proof does not use dimension one or the uniqueness of the
constituent, and it does not use Gross's Satake bijection.

## Generic lemmas

These hold for any topological group `G` and complex representations.

- `isAdmissible_of_surjective`: suppose every open subgroup of `G` contains a
  compact open subgroup. Then a surjective intertwiner out of an admissible
  representation has an admissible target. Smoothness of the target is the
  Library's `isSmooth_of_surjective`. For a compact open `K` inside a given
  open `H`, the Library's `Compact.fixedVectorSurjectivity` says that the
  intertwiner maps the `K`-fixed vectors onto the `K`-fixed vectors. So the
  target's `K`-fixed space is finite dimensional. The Library's
  `finite_fixedVectors_of_le` then passes finiteness from `K` up to `H`.
- `exists_fixed_smoothFunction`: let `P ≤ G` be a subgroup, `K` an open
  subgroup with `G = P K`, and `σ` a representation of `P` with a vector `v₀`
  fixed by `P ∩ K`. Then some smooth induced function `f` has `f(1) = v₀` and
  is fixed by `K` under right translation. The proof chooses a decomposition
  `g = p_g k_g` for each `g` and sets `f(g) = σ(p_g) v₀`. Since `v₀` is fixed
  by `P ∩ K`, this value does not depend on the decomposition chosen. That
  gives left `P`-equivariance and right `K`-invariance. The Library
  constructor `Induction.smoothFunctionOf` turns `f` into an element of the
  smooth induced space, with `K` as its open subgroup of smoothness.

## The unramified data

Write `T = F.canonicalTopologicalData` and `B = borelShape r`. `B` has
`r + 1` blocks, all of size one, and `P = B.parabolic F.Carrier` is the upper
Borel subgroup. By definition the principal series induces from `P` the twist
by `T.parabolicHalfModulus B` of the external tensor product of the characters
`characterRepresentation (determinantQuasiCharacter F 1 (characterTuple F z i))`,
composed with the Levi projection. In the module these appear as
`blockCharacters F z` and `borelInducing F z`. The inducing space is the
tensor product `⨂_i ℂ`, and `sphericalTensor r` is the pure tensor of ones in
it. `sphericalTensor_ne_zero` evaluates it with the multilinear product map,
which sends it to `1`.

- `determinantNorm_eq_one_of_integral`: an invertible matrix with integral
  entries and an integral inverse has a determinant of normalized absolute
  value one. Both determinants are integral and their absolute values
  multiply to one.
- `leviProjection_mem_normOneLevi`: if `b ∈ P` lies in `GL_(r+1)(O_F)`, then
  each diagonal block of `b` has determinant norm one, so the Levi projection
  of `b` is in `T.normOneLevi B`. Integrality of the entries comes from
  `Conductor.mem_integralSubgroup`.
- `borelInducing_sphericalTensor`: every such `b` fixes `sphericalTensor r`.
  The half modulus is one on the norm-one Levi subgroup, by
  `T.normOneLevi_le_ker_leviModulus` and `T.leviHalfModulus_eq_one`. Each
  unramified character is one on determinant-norm-one elements, by
  `T.ker_determinantNorm_le_ker_determinantUnramifiedCharacter`. The block
  tensor of a pure tensor is the pure tensor of the block actions.
- `exists_borel_mul_spherical`: this is the Iwasawa decomposition
  `GL_(r+1)(F) = P · GL_(r+1)(O_F)`. It follows from the Library's
  `GeneralLinear.Iwasawa.exists_upperTriangular_mul` for the canonical
  valuation and `BlockShape.mem_parabolic_of_isUpperTriangular`. The compact
  subgroup is the Library's `sphericalOpenSubgroup F r`, whose underlying
  subgroup is `sphericalSubgroup F r`.
- `exists_compactOpenSubgroup_le`: every open subgroup of `GL_(r+1)(F)`
  contains a compact open subgroup. This comes from the Library's
  `BlockShape.exists_compactOpenSubgroup_hasBlockIwahoriFactorization`, whose
  block-Iwahori factorization part is discarded.
- `blockCharacters_isAdmissible` and `principalSeriesOfTuple_isAdmissible`:
  each character is smooth, since its kernel is open by
  `T.isOpen_ker_determinantUnramifiedCharacter`. Each is also finite, because
  its carrier is `ℂ`. So `FiniteTensor.isAdmissible_external` makes the tensor
  product admissible. The Library's `Parabolic.normalizedInductionAdmissibility`
  then makes the normalized induced representation `principalSeriesOfTuple F z`
  admissible.

## Main theorem

Fix `p`, `F`, `r` and `z`, and write `π = principalSeriesOfTuple F z`.

1. *A spherical vector.* `exists_fixed_smoothFunction` applies with
   `K = sphericalOpenSubgroup F r`, the Iwasawa decomposition and
   `v₀ = sphericalTensor r`. It gives `f₀` in the induced space with
   `f₀(1) = sphericalTensor r ≠ 0`, so `f₀ ≠ 0`, and `f₀` is fixed by
   `sphericalSubgroup F r`.
2. *The cyclic subrepresentation.* `S` is the complex span of the translates
   `π(g) f₀`. It is stable under `π`, so it is an actual `Subrepresentation π`.
   `W = SmoothRep.subrepresentation (SmoothRep.of π _) S` is the corresponding
   smooth representation, and `w₀ ∈ W` is `f₀`. Every subrepresentation of `W`
   that contains `w₀` contains all translates of `f₀`, so it is everything. In
   particular `W` is nontrivial.
3. *A maximal proper subrepresentation.* The Library's
   `CuspidalSupport.QuasicuspidalEmbedding.exists_isCoatom_subrepresentation`,
   applied to the generating set `{w₀}`, gives a coatom `S'` of the lattice of
   subrepresentations of `W`. Write `Q = SmoothRep.quotient W S'` and let
   `q : W → Q` be the quotient intertwiner. It is surjective, and its kernel
   is `S'`. The Library's `isIrreducible_of_isCoatom` then shows that `Q` is
   irreducible.
4. *Admissibility.* `W` is admissible by `isAdmissible_of_injective`, applied
   to its inclusion into the admissible `π`. `Q` is admissible by
   `isAdmissible_of_surjective` together with `exists_compactOpenSubgroup_le`.
   So `⟨Q, irreducible, admissible⟩` is an
   `AutomorphicObject.{uF, uF} F r.succPNat`. Its carrier is a quotient of a
   submodule of the induced space, which lives in universe `uF`.
5. *The constituent relation.* The subrepresentation is `S`, and the
   surjective intertwiner from `S` to `Q` is `q`.
6. *Nonzero spherical vectors.* `q w₀` is fixed by `sphericalSubgroup F r`
   because `q` intertwines and `w₀` is fixed. It is nonzero: otherwise
   `w₀ ∈ S'`, and then `S' = ⊤` by step 2, which contradicts `S'` being a
   coatom.

## Notes for downstream use

The helper lemmas live in the namespace
`Langlands.Unramified.SphericalExistence`. The local topology instances
repeat those of the statement module: the canonical field topology and
`F.canonicalGeneralLinearTopology`. A third local instance is the Library's
`F.canonicalGeneralLinearTopologicalGroup`. The proof edits no published
file.
