# Regular elliptic elements of `GL_n(F)` correspond to units of `D`: the proof

The module
`Langlands.JacquetLanglands.CorrespondenceInputs.RegularEllipticCorrespondenceProof`
proves one theorem, `Langlands.JacquetLanglands.regularEllipticCorrespondence`,
whose type is the published proposition
`RegularEllipticCorrespondenceStatement.{u}` of the module
`Langlands.JacquetLanglands.CorrespondenceInputs.RegularEllipticCorrespondence`.
The universe `u` is left free and no hypothesis is added.

The statement says: let `F` be a nonarchimedean local field of any
characteristic, `D` a finite-dimensional central division algebra over `F`,
and `n` a natural number with `Module.finrank F D = n ^ 2`. Then every
regular elliptic `g : GeneralLinear n F` has some `g' : Dˣ` with
`Corresponds F D g g'`. That is, `g'` is regular and the characteristic
polynomial of `g` is the reduced characteristic polynomial of `g'`.

The proof is the argument recalled on the page of the statement, after
Serre, *Local Fields*, Chapter XIII, §3, Corollaries 1 and 3 to
Proposition 7 (printed p. 194). It uses only results already in the
Library. The steps below follow the Lean proof in order.

## The polynomial `P`

Let `P` be the characteristic polynomial of the matrix `g`. It is monic
(`Matrix.charpoly_monic`) of degree `n`
(`Matrix.charpoly_natDegree_eq_dim`). It is irreducible and separable
because `g` is regular elliptic. Its constant term is nonzero: by
`Matrix.det_eq_sign_charpoly_coeff`, `det g = (-1)^n P(0)`, and
`det g ≠ 0` because `g` is invertible
(`Matrix.GeneralLinearGroup.det_ne_zero`).

## The reduced degree of `D` is `n`

The Library's `Langlands.CentralSimple.finrank_eq_reducedDegree_mul_self`
gives `Module.finrank F D = d * d`, where `d = reducedDegree F D`. With
the hypothesis `Module.finrank F D = n * n`, `Nat.mul_self_inj` gives
`d = n`.

## The field `L = F[X]/(P)`

Since `P` is irreducible, `L = AdjoinRoot P` is a field. Its power basis
`AdjoinRoot.powerBasis` has `P.natDegree = n` elements, so `L` is finite
over `F` with `Module.finrank F L = n`. The field `L` lives in the same
universe as `F`.

The Brauer-theoretic lemmas below need `L` to be a nonarchimedean local
field whose valuation extends that of `F`. The proof equips `L` with the
spectral structures of the module `Langlands.LocalField.FiniteExtension`:
the spectral norm `FiniteExtension.normedField F L` (which also gives the
topology of `L`), the valuative relation `FiniteExtension.valuativeRel F L`
of the spectral valuation, and the theorem `FiniteExtension.isLocalField F L`
that these make `L` a nonarchimedean local field. The theorems
`Langlands.ClassFieldTheory.Local.spectralFiniteExtension_valuativeExtension`
and `spectralFiniteExtension_algebraMap_continuous` say that the valuative
relation of `L` restricts to that of `F` and that `algebraMap F L` is
continuous. The Library's proof of `addOrderOf_localDivisionClass` equips
its unramified extensions in the same way.

## `L` splits `D`

Let `x` be the Brauer class `classOf (divisionAlgebraCSA F D)` of `D`. By
`Langlands.ClassFieldTheory.Local.addOrderOf_localDivisionClass`, its
additive order is `n`, so `n • x = 0`. By
`Langlands.ClassFieldTheory.Local.scalarExtension_eq_zero_iff_degree_nsmul`
(Serre's Corollary 1), a finite extension that is a nonarchimedean local
field, with continuous structure map and compatible valuation, kills
exactly the classes annihilated by its degree. As `[L : F] = n`, the
scalar extension of `x` to `L` is `0`. By
`Langlands.Brauer.classOf_eq_zero_iff`, the base change
`baseChange L (divisionAlgebraCSA F D)` is split.

## The element `g'`

Since `[L : F] = n = reducedDegree F D` and `L` splits `D`,
`Langlands.CentralDivision.embeddingOfSplitOfReducedDegree` gives an
`F`-algebra map `ι : L → D`. It is injective, as is every ring map out of a
field. Let `a = ι(root P)`, the image of the class of `X`.

By `minpoly.algHom_eq` and `AdjoinRoot.minpoly_root`, the minimal
polynomial of `a` over `F` is the minimal polynomial of `root P`, which is
`P` because `P` is monic. Hence `a ≠ 0`: the minimal polynomial of `0` is
`X` (`minpoly.zero`), whose constant term is `0`, while that of `P` is not.
So `g' = Units.mk0 a` is a unit of `D`.

## The reduced characteristic polynomial of `g'`

By `Langlands.CentralDivision.minpoly_dvd_reducedCharpoly`, the minimal
polynomial `P` of `a` divides the reduced characteristic polynomial of
`a`. Both are monic (`minpoly.monic`,
`Langlands.CentralSimple.reducedCharpoly_monic`), and the reduced
characteristic polynomial has degree `reducedDegree F D = n = P.natDegree`
(`reducedCharpoly_natDegree`). So
`Polynomial.eq_of_monic_of_dvd_of_natDegree_le` gives
`reducedCharpoly F D a = P`.

## Conclusion

`Langlands.JacquetLanglands.corresponds_iff` reduces `Corresponds F D g g'`
to three facts: `g` is regular semisimple, which is part of being regular
elliptic; `g'` is regular, since its reduced characteristic polynomial is
`P`, which is separable; and the characteristic polynomial of `g` is the
reduced characteristic polynomial of `g'`, both being `P`.

## Sources

- Jean-Pierre Serre, *Local Fields*, GTM 67, Springer, 1979. Registered as
  `serre-1979-local-fields`, SHA-256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
  Chapter XIII, §3, Corollaries 1 and 3 to Proposition 7 (printed p. 194,
  PDF page 199). The Lean proof follows the derivation of Corollary 3 from
  Corollary 1; the Brauer-theoretic results it uses are the Library
  theorems named above.
