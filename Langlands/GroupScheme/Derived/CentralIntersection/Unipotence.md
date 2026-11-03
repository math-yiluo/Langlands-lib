# A unipotence criterion over an algebraically closed field

Author: Worker 1408.

This internal helper module proves a sufficient criterion for the Library
predicate `IsUnipotent` (module `Reductive.Basic`). That predicate says that
every matrix representation on a nonzero coordinate space has a nonzero fixed
vector, fixed on all test schemes. The criterion and its proof are derived
content written for the central intersection finiteness proof. The source
argument (Milne, *Algebraic Groups* (2017), Propositions 12.46(a) and 19.21(b))
works with central tori and weight blocks. This route avoids tori and proves
unipotence directly. Namespace: `Langlands.GroupScheme.CentralIntersection`.

Throughout, `K` is a field and `H` a group scheme over `Spec K`. A rational point
is a morphism `Over.mk (𝟙 (Spec K)) ⟶ H.X`. `M = σ.pointMatrix H.X (𝟙 H.X)` is
the universal matrix of a representation `σ`, with entries in `Γ(H, ⊤)`.

## Evaluation at rational points

- `evalPoint h : Γ(H, ⊤) →+* K` pulls back along the rational point `h` and then
  applies `Γ(Spec K) ≅ K`. It is the identity on scalars
  (`evalPoint_scalarMap`, `evalPoint_mapMatrix_scalarMap`). It sends the
  universal matrix of `σ` to the rational matrix of `h`
  (`evalPoint_mapMatrix_pointMatrix`, by `pointMatrix_naturality`).
- `eq_zero_of_forall_evalPoint_eq_zero`: if `K` is algebraically closed, `H` is
  reduced and locally of finite type, and `f` vanishes at every rational point,
  then `f = 0`. This is `eq_zero_of_forall_appTop_eq_zero` from
  `PointVanishing`.

## The universal matrix is unipotent

Assume `K` algebraically closed, `H` reduced, connected and locally of finite
type. Let `ρ` be a representation such that, for a fixed `m ≠ 0`, every root of
the characteristic polynomial of every rational matrix `ρ(h)` is an `m`-th root
of unity.

`isNilpotent_pointMatrix_sub_one`: the universal matrix `M` of `ρ` satisfies
`(M - 1)^e = 0` for some `e`.

Proof. Make `Γ(H, ⊤)` a `K`-algebra through `scalarMap`; then each `evalPoint h`
is a `K`-algebra map. Put `Q = (X^m - 1)^(N + 1)` with `N = card n`. At each
rational point, `Q(M)` evaluates to `Q(ρ(h))`, which is `0` by
`aeval_pow_sub_one_eq_zero` (`LinearAlgebra`). By point vanishing, every entry
of `Q(M)` is `0`. `Q` is nonzero with root `1`. So `exists_unipotent_splitting`
writes `Q = (X - 1)^e R` with a Bézout relation, and `splitting_aeval` makes
`E = (w R)(M)` idempotent with `(M - 1)^e E = 0`. Then `det E` is an idempotent
global function, so it is `0` or `1` (`eq_zero_or_eq_one_of_isIdempotentElem`,
using that `H` is connected and reduced). At the identity point, `E` evaluates
to `(w R)(1) = 1`, so `det E` evaluates to `1`. Hence `det E = 1`, `E` is
invertible, and an invertible idempotent is `1`. Therefore `(M - 1)^e = 0`.

`isNilpotent_rationalMatrix_sub_one`: evaluating at `h`, every rational matrix
`ρ(h)` is unipotent.

## Right translation

For a rational point `h`, `rightTranslation h = 𝟙 H.X * (toBase H.X ≫ h)` is
right translation by `h`, and `translationMap h` is its ring endomorphism of
`Γ(H, ⊤)`. It fixes scalars (`translationMap_scalarMap`). For every
representation `σ`, it acts on the universal matrix by
`M ↦ M · σ(h)` (`translationMap_mapMatrix_pointMatrix`). It acts on the inverse
by `M⁻¹ ↦ σ(h⁻¹) · M⁻¹` (`translationMap_mapMatrix_pointMatrix_inv`). Here
`σ(h)` denotes the image of the rational matrix in `Mat_n(Γ(H, ⊤))`. Both
identities come from multiplicativity and naturality of `pointMatrix`.

## Generation of the coordinate ring

`mem_of_isClosedImmersion`: let `H` be affine and let `ρ` have underlying
morphism a closed immersion into `GL_n`. If a subring `L` of `Γ(H, ⊤)` contains
the scalars and the entries of `M` and of `M⁻¹`, then `L` is everything.
Mathlib's `IsClosedImmersion.isAffine_surjective_of_isAffine` makes the pullback
from the coordinate ring of `GL_n` surjective. That ring is a quotient of a
polynomial ring in the entry and inverse-entry variables. Induction on
polynomials reduces to constants and variables. Constants go to scalars by
`scalarMap_generalLinear` and `scalarMap_naturality`. Variables go to entries
of `M` and `M⁻¹` by `GeneralLinear.pointsEquiv_apply_apply` and
`GeneralLinear.pointsEquiv_inv_apply`.

## The criterion

`isUnipotent_of_eigenvalues`: let `K` be algebraically closed and `H` reduced,
connected, affine and locally of finite type. Suppose that any two rational
points of `H` commute. Let `ρ : MatrixRepresentation H N` have underlying
morphism a closed immersion. If every root of the characteristic polynomial of
every `ρ(h)` is an `m`-th root of unity for a fixed `m ≠ 0`, then
`IsUnipotent H`.

Proof. First, every rational point acts unipotently in every representation `σ`.
Fix `h`. The matrices `ρ(h)` and `ρ(h⁻¹)` are unipotent, so by the translation
formulas and `mem_locallyUnipotent_of_mapMatrix_eq_mul` (and its left version)
the entries of `M_ρ` and `M_ρ⁻¹` are locally unipotent for `translationMap h`.
Scalars are fixed, so they are too. These lie in the subring
`locallyUnipotent (translationMap h)`, so by generation it is all of
`Γ(H, ⊤)`. In particular all entries of the universal matrix `M_σ` are locally
unipotent. Since `translationMap h` multiplies `M_σ` on the right by `σ(h)`,
`isNilpotent_sub_one_of_mapMatrix_eq_mul` shows that `σ(h) - 1` is nilpotent
over `Γ(H, ⊤)`. Evaluating at the identity point gives nilpotence of the
rational matrix `σ(h) - 1`.

Now let `σ` be a representation on `K^n` with `n` nonempty. The endomorphisms
`σ(h) - 1` commute pairwise, because the rational points commute, and they are
nilpotent. By `exists_ne_zero_forall_eq_zero` (`LinearAlgebra`) they have a
common nonzero kernel vector `v`, so `σ(h) v = v` for every rational point `h`.
By the published `isFixedVector_iff_universal` (module
`Reductive.UnipotentQuotient`), `v` is a fixed vector once the universal matrix
fixes it. Each coordinate of `M_σ v - v` vanishes at every rational point, so it
is `0` by point vanishing.
