# Extending the `k^(2g)` Euler scaling from `k` invertible in the base field

Author: Worker 1222. Worker 998 fixed the names and the shape of the restricted statement,
and, after review, replaced a repeated induction by the published `isoClass_tensorPow`.

Module `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingCoprimeExtension`,
namespace `Langlands.AbelianScheme`. The module defines a restricted form of the published
target `AlgClosedFieldAmpleEulerInverseScalingStatement.{u}` and proves that the restricted
form implies the full target. It is a helper for the proof of that target. The restricted
form only needs `k` with `(k : K) ≠ 0`, and for those `k` the published
`multiplication_isIsogeny_of_ne_zero` makes multiplication by `k` an isogeny. So the proof of
the target does not need the published `FieldMultiplicationIsogenyStatement`, which asks for
the isogeny property in every characteristic.

## The restricted statement

`AlgClosedFieldAmpleEulerInverseScalingCoprimeStatement.{u} : Prop` is word for word the
published `AlgClosedFieldAmpleEulerInverseScalingStatement.{u}`, except for one added
hypothesis `(k : K) ≠ 0` right after `1 ≤ k`:

```lean
def AlgClosedFieldAmpleEulerInverseScalingCoprimeStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ),
    A.HasRelativeDimension g →
      ∀ (H N : LineBundle A.X.left), H.IsAmple →
        Nonempty (tensorObj H.obj N.obj ≅ structureSheaf A.X.left) →
          ∀ (k : ℕ), 1 ≤ k → (k : K) ≠ 0 →
            ∀ (Nk : LineBundle A.X.left),
              Nonempty (tensorObj (tensorPow H.obj k) Nk.obj ≅ structureSheaf A.X.left) →
                ∀ (hH : HasFiniteCohomology A.X.hom H.obj)
                  (hN : HasFiniteCohomology A.X.hom N.obj)
                  (hHk : HasFiniteCohomology A.X.hom (tensorPow H.obj k))
                  (hNk : HasFiniteCohomology A.X.hom Nk.obj),
                  eulerCharacteristic A.X.hom (tensorPow H.obj k) hHk *
                      eulerCharacteristic A.X.hom Nk.obj hNk =
                    (k : ℤ) ^ (2 * g) *
                      (eulerCharacteristic A.X.hom H.obj hH *
                        eulerCharacteristic A.X.hom N.obj hN)
```

`(k : K)` is the image of the natural number `k` in the field `K`. The hypothesis says that
the characteristic of `K` does not divide `k`. In characteristic zero it holds for every
`k ≥ 1`. All other names, binders and hypotheses are those of the published target; see
`AlgClosedFieldAmpleEulerInverseScalingStatement.md` for their meaning.

## Main theorem

`algClosedFieldAmpleEulerInverseScaling_of_coprime :
AlgClosedFieldAmpleEulerInverseScalingCoprimeStatement.{u} →
AlgClosedFieldAmpleEulerInverseScalingStatement.{u}`.

### Proof

Fix the data of the target: `K`, `A`, `g`, `hg`, `H`, `N`, an isomorphism
`H ⊗ N ≅ 𝒪`, `k ≥ 1`, a line bundle `Nk` with `H^{⊗k} ⊗ Nk ≅ 𝒪`, and the four
finite-cohomology witnesses.

1. *Euler polynomials.* The published `smoothProperLineBundleEulerPolynomial_degree_le`
   (`Picard/LineBundleEulerPolynomial.lean`) gives, for `H` and for `N`, finite cohomology
   of every tensor power and polynomials `P_H, P_N ∈ ℚ[X]` with
   `P_H(n) = χ(H^{⊗n})` and `P_N(n) = χ(N^{⊗n})` for every natural number `n`. Its degree
   bound is not used.
2. *Values at good integers.* Let `c = χ(H) χ(N)`. Take `n ≥ 1` with `(n : K) ≠ 0`. Apply the
   hypothesis with `Nk := N^{⊗n}`. The lemma `nonempty_tensorPow_tensorObj_tensorPow_iso`
   below supplies `H^{⊗n} ⊗ N^{⊗n} ≅ 𝒪`. The result is
   `χ(H^{⊗n}) χ(N^{⊗n}) = n^{2g} c`. Hence `P_H P_N` and `X^{2g} · c` take the same value
   at `n`.
3. *Infinitely many good integers.* `exists_nat_cast_ne_zero_gt` gives such an `n` above
   every rational number. So the set of rationals where the two polynomials agree is not
   bounded above. By Mathlib's `Set.infinite_of_forall_exists_gt` it is infinite. By
   `Polynomial.eq_of_infinite_eval_eq`, `P_H P_N = X^{2g} · c` in `ℚ[X]`.
4. *Evaluation at `k`.* By `nonempty_iso_tensorPow_of_inverse`, `Nk ≅ N^{⊗k}`. The
   published `eulerCharacteristic_eq_of_iso` (`Modules/EulerCharacteristicBasicProof.lean`)
   gives `χ(Nk) = χ(N^{⊗k})`. Evaluating the polynomial identity at `k` gives
   `χ(H^{⊗k}) χ(Nk) = k^{2g} c` in `ℚ`. The cast `ℤ → ℚ` is injective, so the identity holds
   in `ℤ`.

The proof does not use that `K` is algebraically closed or that `H` is ample, except where
it passes these hypotheses on to the restricted statement.

## Helper lemmas

Section `Classes`, for any scheme `X`. The local notation `cls` is
`LineBundle.isoClass pullbackTensorComparisonIsIso`. It takes a line bundle to its class in
the commutative group of isomorphism classes of line bundles
(`Picard/LineBundleIsoClassGroup.lean`), using the published proof
`pullbackTensorComparisonIsIso` (`Modules/PullbackTensorProof.lean`). The line bundle
structure on `tensorPow L.obj k` is the published `tensorPow_isLocallyFreeRankOne`
(`Picard/TensorRankOneProof.lean`).

- `isoClass_tensorPow_eq_pow L k`: the class of `L^{⊗k}` is `(cls L)^k`. This is a thin
  wrapper around the published `Langlands.AbelianScheme.isoClass_tensorPow` (module
  `Langlands.AbelianScheme.PolarizedFiniteLevel.CubicBundleMumfordProof`), instantiated with
  the tensor preservation `pullbackTensorComparisonIsIso`.
- `isoClass_eq_inv_of_tensorObj_iso L M e`: from `e : L ⊗ M ≅ 𝒪`,
  `cls M = (cls L)⁻¹`. The isomorphism `e` gives `cls L * cls M = 1` through
  `LineBundle.isoClass_eq_of_iso`, `LineBundle.isoClass_tensor` and
  `LineBundle.isoClass_trivial`.
- `nonempty_tensorPow_tensorObj_tensorPow_iso L M e k`: if `L ⊗ M ≅ 𝒪`, then
  `L^{⊗k} ⊗ M^{⊗k} ≅ 𝒪`. Its class is `(cls L)^k ((cls L)⁻¹)^k = 1`.
  `LineBundle.isoClass_eq_iff` turns the equal classes into an isomorphism of line bundles,
  and `LineBundle.forget` turns that into an isomorphism of modules.
- `nonempty_iso_tensorPow_of_inverse L M Mk e k ek`: if `L ⊗ M ≅ 𝒪` and
  `L^{⊗k} ⊗ Mk ≅ 𝒪`, then `Mk ≅ M^{⊗k}`. Both have class `((cls L)^k)⁻¹`.

Outside the section:

- `exists_nat_cast_ne_zero_gt K a`: for every field `K` and rational `a` there is a natural
  number `n ≥ 1` with `(n : K) ≠ 0` and `a < n`. Let `m = ⌈a⌉₊`. If `m + 1` is zero in `K`,
  then `m + 2 = (m + 1) + 1` is `1 ≠ 0` in `K`. Otherwise `m + 1` works.

## Provenance

The statement and the proof are derived and internal. The statement is the published target
restricted by one hypothesis, so that a proof of the target can avoid the isogeny property
of `[k]` when the characteristic divides `k`. The sources cited in
`AlgClosedFieldAmpleEulerInverseScalingStatement.md` need no such restriction: J. S. Milne,
*Abelian Varieties* (registered source `milne-abelian-varieties-1986-author-2022`),
Theorem 8.2, p.13, shows that `[k]` is an isogeny of degree `k^{2g}` for every `k ≥ 1`.
The interpolation argument above is not taken from a source. It combines the published Euler
polynomials (`LineBundleEulerPolynomial`), the published group of isomorphism classes of
line bundles with its tensor-power lemma `isoClass_tensorPow`, and Mathlib's
`Polynomial.eq_of_infinite_eval_eq`.

## Checks

The module compiles with no errors or warnings. `algClosedFieldAmpleEulerInverseScaling_of_coprime`
depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`. Its
import closure contains neither `AlgClosedFieldEulerInverseSymmetryStatement` nor
`AlgClosedFieldAmpleMumfordEulerSquareStatement`.
