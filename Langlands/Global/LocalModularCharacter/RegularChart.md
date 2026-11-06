# Regular charts at points of smooth affine schemes over complete fields

Author: Worker 1402.

This helper module is one step in the proof of
`Langlands.Global.PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement`. Let
`F` be a field, `X` a smooth affine scheme over `Spec F`, and `K` a complete nontrivially
normed field that is an `F`-algebra. The module proves that every `K`-point `p` of `X` has a
chart of the `K`-point space `AlgPoint F O K` (with `O = AffineCoordinateRing F X`) that is
regular in the following sense: it is a polynomial expression in finitely many coordinate
functions, every coordinate function is strictly differentiable along its inverse, and its
derivative detects all derivations at `p`.

## Provenance

This is internal helper content written for the proof above. The underlying mathematics is
standard: a smooth variety over a complete field is a `K`-analytic manifold near each point,
with charts given by the inverse function theorem applied to a presentation satisfying the
Jacobian criterion. In the implemented version, Mathlib supplies the inverse function theorem
(`HasStrictFDerivAt.toOpenPartialHomeomorph`) and the local structure of smooth algebras
(`Algebra.Smooth.exists_span_eq_top_isStandardSmooth`: a smooth algebra is covered by
principal opens with submersive presentations). Worker 1045 fixed the exact form of the main
statement for its use in the modular-character proof. The chart coordinates and the use of
dual numbers for derivations are choices of this implementation (see below).

## Declarations

All declarations are in namespace `Langlands.Global.LocalModularCharacter`.
Throughout, `F` is a field and `K` a nontrivially normed field with `Algebra F K`.

Polynomial evaluation (`ι` finite):

- `aeval_eq_eval_map q w`: `aeval w q = eval w (map (algebraMap F K) q)` for
  `q : MvPolynomial ι F` and `w : ι → K`.
- `hasStrictFDerivAt_aeval q w`: `y ↦ aeval y q` is strictly differentiable at `w`, with
  derivative the Library's `polynomialDerivative (map (algebraMap F K) q) w`.
- `polynomialDerivative_map_apply q w v`: this derivative sends `v` to
  `∑ i, aeval w (pderiv i q) * v i`.
- `aeval_trivSqZeroExt q w u`: evaluating `q` in the dual numbers `TrivSqZeroExt K K` at the
  point `i ↦ inl (w i) + inr (u i)` gives
  `inl (aeval w q) + inr (∑ i, aeval w (pderiv i q) * u i)`.

Presentations (`A` an `F`-algebra, `P` a presentation of `A` with variables `ι` and
relations indexed by `σ`):

- `eq_zero_of_jacobian P x u hfree hrel`: for a submersive presentation `P`, a `K`-point `x`
  of `A`, and `u : ι → K`, if `u` vanishes on the free variables (those outside
  `Set.range P.map`) and `∑ i, aeval w₀ (pderiv i (P.relation j)) * u i = 0` for every
  relation `j`, where `w₀ l = x (P.val l)`, then `u = 0`.
- `relationValues P w`: the vector `j ↦ aeval w (P.relation j)`.
- `presentationPoint P w hw`: for `w : ι → K` with `relationValues P w = 0`, the `F`-algebra
  map `A → K` sending `P.val i` to `w i`. Lemmas `presentationPoint_aeval_val`,
  `presentationPoint_apply` (its value at `a` is `aeval w (P.σ a)`) and
  `presentationPoint_val`.
- `relationValues_comp P x`: the values of the generators at a `K`-point satisfy the
  relations.
- `presentationPointHomeomorph P`: a homeomorphism between `AlgPoint F A K` and the subspace
  `{w : ι → K // relationValues P w = 0}`, given by `x ↦ (l ↦ x (P.val l))`.

Core theorem (`K` complete; `O`, `A` commutative `F`-algebras with `A` an `O`-algebra and a
scalar tower `F → O → A`):

- `derivation_map_one x D hD`: a linear map `D : O →ₗ[F] K` satisfying the Leibniz rule
  `D (a * b) = x a * D b + x b * D a` at a point `x` vanishes at `1`.
- `dualNumberHom x D hD`: such a pair as an `F`-algebra map `O → TrivSqZeroExt K K`,
  `o ↦ inl (x o) + inr (D o)`; `dualNumberHom_apply` states this formula.
- `exists_regularChart_of_away t P p hp`: if `A` is the localization of `O` away from `t`,
  `P` is a submersive presentation of `A` over `F` with finite index types, and `p` is a
  `K`-point of `O` with `p t ≠ 0`, then there are `d`, an open partial homeomorphism
  `φ : AlgPoint F O K → (Fin d → K)`, `n`, coordinate functions `c : Fin n → O`, a map
  `R : (Fin n → K) → (Fin d → K)` and a continuous linear map `R'` such that:
  1. `p ∈ φ.source` and `φ p = 0`;
  2. `R` has strict derivative `R'` at `(p (c j))_j`;
  3. `φ x = R (fun j => x (c j))` for every `x ∈ φ.source`;
  4. for every `a : O`, `s ↦ φ.symm s a` is strictly differentiable at `0`;
  5. every `D : O →ₗ[F] K` satisfying the Leibniz rule at `p` with
     `R' (fun j => D (c j)) = 0` is zero.

Scheme level (`F : Type u`):

- `smooth_affineCoordinateRing X hX`: for an affine `X : Over (Spec (CommRingCat.of F))`
  whose structure morphism is smooth, `AffineCoordinateRing F X` is a smooth `F`-algebra.
- `exists_regularChart X hX p`: for `X` as above (also assumed locally of finite type), a
  complete nontrivially normed field `K : Type u` with `Algebra F K`, and a `K`-point `p` of
  `AffineCoordinateRing F X`, the same five conclusions as in `exists_regularChart_of_away`
  with `O = AffineCoordinateRing F X`. This is the exact statement agreed with Worker 1045.
  The instance `LocallyOfFiniteType X.hom` is part of that statement but is not used in the
  proof.

## Implemented proof

**Polynomials.** Strict differentiability is the Library theorem
`Langlands.RingTheory.LocalFieldDensity.hasStrictFDerivAt_polynomial_eval` after mapping
coefficients to `K`. The dual-number formula is proved by induction on `q`
(`MvPolynomial.induction_on`); the `X i` step is the Leibniz rule for `pderiv`.

**Jacobian lemma.** The matrix `(aeval w₀ (pderiv (P.map k) (P.relation j)))_{j,k}` is the
transpose of the image of `P.jacobiMatrix` under `aeval w₀`, so its determinant is
`x P.jacobian`, a unit. The relation hypotheses say that this matrix kills
`k ↦ u (P.map k)`, since `u` vanishes off `range P.map`; hence that vector is zero
(`Matrix.eq_zero_of_mulVec_eq_zero`), and `u = 0`.

**Points of a presentation.** `presentationPoint` is `AlgHom.liftOfSurjective` along the
surjection `aeval P.val`, whose kernel is spanned by the relations. Continuity of the inverse
of `presentationPointHomeomorph` follows from `presentationPoint_apply` and continuity of
polynomial evaluation.

**Core theorem.** The open embedding `AlgPoint F A K → AlgPoint F O K` given by restriction
(`AlgPoint.isOpenEmbedding_precomp_away`) has `p` in its range, because `p t` is a unit
(`AlgPoint.range_precomp_localization`, `AlgPoint.unit_powers_iff`); let `p'` be the point of
`A` restricting to `p`, and `w₀ l = p' (P.val l)`. Index the free variables by `Fin d`
(`free k`). For each `k`, `IsLocalization.Away.surj` gives `num k : O` and `m k` with
`P.val (free k) * t ^ m k = num k` in `A`; let `b k = w₀ (free k)` and
`Q k = P.σ (t ^ m k)`. The ambient map on `ι → K` is

`Φ w = ((w (free k) - b k) * aeval w (Q k))_k, relationValues P w)`.

Its strict derivative `Φ'` at `w₀` sends `v` to `(aeval w₀ (Q k) * v (free k))_k` together
with the derivatives of the relations, because the factor `w₀ (free k) - b k` vanishes. Since
`aeval w₀ (Q k) = p t ^ m k ≠ 0`, the Jacobian lemma shows `Φ'` is injective; it is bijective
because `card ι = d + card σ`. The inverse function theorem gives a local homeomorphism `e`
from `Φ`. The Library's `zeroFibreChart` (`PointManifold.ZeroFibreChart`) restricts `e` to the
zero set of the relations, giving a chart to `Fin d → K` at `w₀`. Composing with
`presentationPointHomeomorph` and transporting along the open embedding
(`OpenPartialHomeomorph.lift_openEmbedding`) gives `φ`. It sends `p` to `0`, because
`Φ w₀ = 0`.

**Coordinates.** Take `n = d + d`, `c = Fin.append num (k ↦ t ^ m k)`, and
`R = R'` the continuous linear map `y ↦ (y (castAdd k) - b k * y (natAdd k))_k`. For a point
`y` of `A`, `y (num k) = y (P.val (free k)) * y t ^ m k` and
`aeval (y ∘ P.val) (Q k) = y t ^ m k`, so the chart value
`(y (P.val (free k)) - b k) * y t ^ m k` equals `R` applied to the coordinates. `R` is linear,
so it is its own strict derivative everywhere.

**Inverse chart.** Near `0` (on the open target of the chart), the definitions give
`φ.symm s a = aeval (e.symm (s, 0)) (P.σ (algebraMap O A a))` for `a : O`. The inverse of `e` is strictly differentiable
at `Φ w₀ = 0` (`HasStrictFDerivAt.to_localInverse`), so the composite is strictly
differentiable, and `HasStrictFDerivAt.congr_of_eventuallyEq` transfers this to
`s ↦ φ.symm s a`.

**Derivations.** A derivation `D` at `p` gives `δ = dualNumberHom p D : O → K[ε]`. Since
`δ t` has unit first component `p t`, it is a unit (`TrivSqZeroExt.isUnit_iff_isUnit_fst`),
so `δ` extends to `δ' : A → K[ε]` (`IsLocalization.liftAlgHom`); the first component of `δ'`
is `p'` (`IsLocalization.algHom_ext`). Let `u l` be the `ε`-component of `δ' (P.val l)`. By
`aeval_trivSqZeroExt`, the relations give the Jacobian conditions on `u`. Comparing
`ε`-components in `δ' (P.val (free k)) * δ (t ^ m k) = δ (num k)` gives
`D (num k) - b k * D (t ^ m k) = p t ^ m k * u (free k)`. The left side is the `k`-th
component of `R' (fun j => D (c j))`, which is zero, so `u (free k) = 0`. The Jacobian lemma
gives `u = 0`. Then for every `o : O`, writing `algebraMap O A o = aeval P.val (P.σ _)` and
using `aeval_trivSqZeroExt` with `u = 0`, the `ε`-component `D o` of `δ o` is zero.

**Scheme level.** `smooth_affineCoordinateRing` rewrites algebra smoothness as smoothness of
`affineCoordinateMap F X` (`RingHom.smooth_algebraMap`). The Library's
`General.affineCoordinateMap_eq_appTop` identifies that map with `X.hom.appTop` composed with
the isomorphism `Scheme.ΓSpecIso`, and `HasRingHomProperty.appTop` with
`RingHom.Smooth.respectsIso` gives smoothness. In `exists_regularChart`,
`Algebra.Smooth.exists_span_eq_top_isStandardSmooth` gives a set `s` spanning the unit ideal
whose localizations are standard smooth. Some `t ∈ s` has `p t ≠ 0`; otherwise the unit ideal
would lie in the kernel of `p`. A submersive presentation of `Localization.Away t` then
reduces the claim to `exists_regularChart_of_away`.

Axioms of `exists_regularChart`: `propext`, `Classical.choice`, `Quot.sound`.
