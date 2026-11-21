# Continuing the real normalized unequal-rank equation in the larger exponents

This module carries the normalized real unequal-rank functional equation with exponential strip growth along a holomorphic family of larger inducing exponents. It is the real counterpart of the growth part of the published `ComplexUnequalCanonicalReflection` (`ComplexUnequalCanonicalGrowthReflectionStatement`). It is a derived step, internal to the project, toward continuation in the inducing exponents out of the convergence chamber, as in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §8.1.

## Block lists as parametrized lists

The `RealBlockParameters` module parametrizes real blocks by a discrete datum `Shape = Fin 2 ⊕ ℤ` and a complex exponent (`blockOfParams`, `blockList`).

- `blockShape d` is the parity of a character block and the weight of an induced block. `blockExponent d` is the exponent of the block's character data.
- `blockOfParams_shape_exponent`: `blockOfParams (blockShape d) (blockExponent d) = d`. For a character block this is `realCharacterData_ext`. For an induced block it is the published `characterOfParams_eta`.
- `eq_blockList`: every list `es` of real blocks equals `blockList sh' q` with `sh' i = blockShape es[i]` and `q i = blockExponent es[i]`, indexed by `Fin es.length`.
- `characterList_eq_blockList`: the published real character list `characterList pr z` equals `blockList (fun i => inl (pr i)) z` (`List.map_ofFn`).

## The statement

Fix `t < r` and real units `a`, `b` and `eb`. Fix quotient measure data `D` for `N_(t+1)(ℝ) \ GL(t+1, ℝ)`, a parity list `pr : Fin (r+1) → Fin 2` and a list `es` of real blocks. Fix a scale `c > 0` and a nonzero `sign`. Fix `V : GL(t+1, ℝ) → ℂ` such that every iterated right derivative of `V` lies in `regularFunctions t (−a)`, and these derivatives have polynomial growth in the real matrix height with one common exponent.

`HasRealUnequalCanonicalPairGrowth h a b eb D pr z es c hc sign V` says the following. Let `f` be any element of the published K-finite real standard module `realStandardKFinite (r+1) (characterList pr z)`, and put `W = RealGodement.canonicalJacquetMap (−a) pr z f`, which has left character `a`. Then the published `HasRealPairNormalizedGrowth` holds with these data:

- the lists `characterList pr z` and `es`, and their lists of dual blocks;
- the epsilon parameter `eb`, the scale `c` and the sign `sign`;
- the ordinary integral `realUnequalIntegral h D W V` and the dual integral `realUnequalDualIntegral h b D W V`, whose rectangular measure is self-dual for `b`.

So there are entire functions of exponential type in vertical strips that equal the pair denominators times the two integrals on a right half-plane, and they satisfy the normalized functional equation with `realPairEpsilon` for `eb` and `c`.

`RealUnequalCanonicalGrowthReflectionStatement` says the following. Let `p : ℂ → ℂ^(r+1)` be holomorphic, and suppose the predicate holds at `p z` for all `z` in some disk `|z| < δ`. Then it holds at `p 1`. `realUnequalCanonicalGrowthReflection` proves it.

The parameters `a`, `b` and `eb` are independent. The exact unequal target uses `b = a` and `eb = −a`.

## Proof

Fix `f` at `p 1`. Let `φ` be its compact restriction, which is a compact profile for `pr` (`isCompactProfile_compactRestriction`). Let `F = canonicalJacquetFamily (−a) hφ`. By definition, `canonicalJacquetMap (−a) pr (p 1) f` is `F (p 1)`.

- **Bounds.** `canonicalJacquetFamily_properties` gives regularity for `−(−a) = a` (by `neg_neg`), locally uniform derivative growth and pointwise holomorphy. The theorem `realUnequalRegularFamilyBounds` with radius 3 then gives a threshold `σ`, together with three properties of `Z(z, s) = realUnequalIntegral h D (F (p z)) V s` and `Zd(z, s) = realUnequalDualIntegral h b D (F (p z)) V s`: joint holomorphy on `ball 0 3 × {σ < Re s}`, and one bound on closed vertical strips that holds for both integrals uniformly over the disk.
- **Initial disk.** For `z` with `|z| < δ`, apply the hypothesis at `p z` to the standard section of `φ` at `p z` (`standardSection_mem`). The published `canonicalJacquetMap_standardSection` identifies its canonical value with `F (p z)`. Then `characterList_eq_blockList` and `eq_blockList` rewrite both lists as parametrized block lists. The smaller exponents form the constant family `q`.
- **Reflection.** The theorem `realPairStripReflection` applies with the shapes `inl ∘ pr` and `sh'`, the families `p` and the constant `q`, and the data `eb`, `c`, `sign` and `Z`, `Zd`. It gives the normalized pair at parameter `1`. Rewriting the lists back gives the conclusion for `f`.
