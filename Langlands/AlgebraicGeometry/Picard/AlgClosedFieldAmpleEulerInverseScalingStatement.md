# The `k^(2g)` scaling of the Euler product of an ample line bundle and its inverse

Authors: Worker 1029 drafted the Lean proposition, which the task objective fixes
verbatim; Worker 998 wrote this file pair and the explanation.

Module `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingStatement`,
namespace `Langlands.AbelianScheme`, with `open CategoryTheory AlgebraicGeometry`,
`open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules` and
`open Langlands.AlgebraicGeometry.Modules.DerivedSections`. The file defines one
universe-polymorphic proposition,
`Langlands.AbelianScheme.AlgClosedFieldAmpleEulerInverseScalingStatement.{u}`.
It is a statement target. The file proves nothing.

## Complete proposition

```lean
def AlgClosedFieldAmpleEulerInverseScalingStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ),
    A.HasRelativeDimension g →
      ∀ (H N : LineBundle A.X.left), H.IsAmple →
        Nonempty (tensorObj H.obj N.obj ≅ structureSheaf A.X.left) →
          ∀ (k : ℕ), 1 ≤ k →
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

The imports are `Langlands.AbelianScheme.Basic`,
`Langlands.AlgebraicGeometry.Picard.Ample`, `Langlands.AlgebraicGeometry.Modules.Tensor`,
`Langlands.AlgebraicGeometry.Modules.EulerCharacteristic` and
`Mathlib.FieldTheory.IsAlgClosed.Basic`. All names are the published Library ones,
used unchanged.

## Meaning

- `K` is an algebraically closed field in universe `u`, of any characteristic.
- `A` is a published `AbelianScheme` over `Spec K` (`Langlands.AbelianScheme.Basic`):
  a commutative group scheme whose structure morphism `A.X.hom : A.X.left ⟶ Spec K`
  is smooth, proper and geometrically connected.
- `A.HasRelativeDimension g` is the published abbreviation for
  `SmoothOfRelativeDimension g A.X.hom`. So `g` is the dimension of `A.X.left`.
  Every `g`, including `g = 0`, is allowed.
- `H` and `N` are published line bundles `LineBundle A.X.left`: sheaves of
  `𝒪`-modules on `A.X.left` that are locally isomorphic to the structure sheaf.
  `H.IsAmple` is the published `LineBundle.IsAmple` from
  `Langlands.AlgebraicGeometry.Picard.Ample`, the ampleness of Stacks tag 01PS
  (EGA II, 4.5.3): `A.X.left` is quasi-compact, and every point lies in a locus
  `X_s` that is affine, for some global section `s` of some `tensorPow H.obj n`
  with `n ≥ 1`.
- The hypothesis `Nonempty (tensorObj H.obj N.obj ≅ structureSheaf A.X.left)`
  says that some isomorphism exists from the published sheafified tensor product
  `H ⊗ N` to the structure sheaf. So `N` is an inverse of `H` in the Picard group,
  `N ≅ H⁻¹`. Only the existence of an isomorphism matters, not a choice.
- `k ≥ 1` is a natural number. `tensorPow H.obj k` is the published
  right-associated tensor power: `tensorPow M 0 = structureSheaf X` and
  `tensorPow M (n + 1) = tensorObj M (tensorPow M n)`. So it is
  `H ⊗ (H ⊗ (⋯ ⊗ (H ⊗ 𝒪)))` with `k` factors `H`. It is isomorphic to the usual
  `k`-th tensor power `H^{⊗k}`, but not literally equal to it. For example,
  `tensorPow H.obj 1` is `H ⊗ 𝒪`, not `H.obj`.
- `Nk` is a line bundle with
  `Nonempty (tensorObj (tensorPow H.obj k) Nk.obj ≅ structureSheaf A.X.left)`.
  So `Nk ≅ (H^{⊗k})⁻¹ = H^{-k}`.
- `hH`, `hN`, `hHk` and `hNk` are arbitrary proofs of the published predicate
  `HasFiniteCohomology` for the four sheaves. It says that every actual derived
  cohomology `K`-vector space `(relativeCohomology A.X.hom n).obj F` is finite
  dimensional, and that these spaces vanish in all sufficiently high degrees.
  `HasFiniteCohomology` is a proposition, so the Euler characteristics do not
  depend on these proofs. The binders never restrict the statement. The proved
  theorem `Langlands.AlgebraicGeometry.Modules.smoothProperLineBundleFiniteCohomology`
  supplies such proofs for every `LineBundle` on a smooth proper scheme over a
  field. The proved theorem
  `Langlands.AlgebraicGeometry.Picard.tensorPow_isLocallyFreeRankOne` shows that
  `tensorPow H.obj k` is locally free of rank one, so that theorem applies to it
  too. Both are taken as binders here, so the statement does not import those
  proofs.
- `eulerCharacteristic A.X.hom F h` is the published integer
  `∑ᶠ n, (-1)^n * finrank K ((relativeCohomology A.X.hom n).obj F)`. Here
  `relativeCohomology A.X.hom n` is the `n`-th right derived functor of global
  sections on `𝒪`-modules, valued in `K`-modules through `A.X.hom`. No surrogate
  cohomology or Euler characteristic is used.

The conclusion is the integer identity

`χ(H^{⊗k}) · χ(Nk) = k^{2g} · (χ(H) · χ(N))`,

that is, `χ(H^k) χ(H^{-k}) = k^{2g} χ(H) χ(H^{-1})`.

## Sources and derivation

This proposition is a derived consequence. It is not a numbered result of either
source.

### Edixhoven, van der Geer and Moonen

B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties*, preliminary
version of the first chapters (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, file SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`; printed page
= PDF page − 4).

- (9.10), printed p.130 (PDF p.134), defines the Euler characteristic of a
  quasi-coherent module `F` on a proper scheme `X` of finite type over a field
  `k` as `∑_{i ≥ 0} (-1)^i dim_k Hⁱ(X, F)`. (The printed display writes `χ(L)`
  on the left; the defined quantity is `χ(F)`.) The published
  `eulerCharacteristic` is this alternating sum, with `Hⁱ` the derived functors
  of global sections.
- (9.11) Riemann–Roch Theorem, printed p.131 (PDF p.135): for a line bundle `L`
  on a `g`-dimensional abelian variety `X`, `χ(L) = c₁(L)^g / g!` and
  `χ(L)² = deg(φ_L)`. In the proof of (9.11) and (9.12) on the same page, the
  displayed formula (7) states `χ(L^m) = m^g · χ(L)` for all `m ∈ ℤ`.

Apply (7) to `L = H` with `m = k`, `m = -k` and `m = -1`:

- `χ(H^k) = k^g χ(H)`,
- `χ(H^{-k}) = (-k)^g χ(H) = (-1)^g k^g χ(H)`,
- `χ(H^{-1}) = (-1)^g χ(H)`.

Then

- left side: `χ(H^k) · χ(H^{-k}) = k^g χ(H) · (-1)^g k^g χ(H) = (-1)^g k^{2g} χ(H)²`;
- right side: `k^{2g} · χ(H) · χ(H^{-1}) = k^{2g} χ(H) · (-1)^g χ(H) = (-1)^g k^{2g} χ(H)²`.

Both sides equal `(-1)^g k^{2g} χ(H)²`, which is the identity.

The Lean sheaves are matched with the source's powers as follows. Inverses in
the Picard group are unique up to isomorphism, so `N ≅ H⁻¹` and
`Nk ≅ (H^{⊗k})⁻¹ = H^{-k}`. Any two bracketings of a tensor power are
isomorphic, so `tensorPow H.obj k ≅ H^{⊗k}`. Each `relativeCohomology A.X.hom n`
is a functor, so isomorphic sheaves have isomorphic cohomology and equal Euler
characteristics. Hence the four Lean Euler characteristics are `χ(H^k)`,
`χ(H^{-k})`, `χ(H)` and `χ(H^{-1})`. These matching facts are mathematical
explanation; this file does not prove them in Lean.

The book's abelian varieties match the Lean objects. By (0.1), printed p.1
(PDF p.5), `k` denotes an arbitrary field. By (0.4), on the same page, a variety
over `k` is a separated geometrically integral `k`-scheme of finite type. By
Definition (1.3), printed p.6 (PDF p.10), an abelian variety is a group variety
that is complete. `A.X.left` is proper and smooth over `K`, it is geometrically
connected, and it has a rational point, the unit section. A smooth connected
group scheme over a field is geometrically integral. So `A.X.left` is an abelian
variety of dimension `g` in the book's sense.

### Milne

J. S. Milne, *Abelian Varieties* (registered source
`milne-abelian-varieties-1986-author-2022`, file SHA-256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`),
Theorem 13.3, p.25, for an invertible sheaf `L` on an abelian variety `A` over a
field `k`, with `χ(L) = ∑ (-1)^i dim_k Hⁱ(A, L)`:
(a) the degree of `φ_L` is `χ(L)²`; (b) (Riemann–Roch) if `L = L(D)`, then
`χ(L) = (D^g)/g!`. By the conventions on pp.2–3, `k` is an arbitrary field and
divisors are Cartier divisors. Every invertible sheaf on the integral scheme `A`
is `L(D)` for some Cartier divisor `D`. Then `L^m = L(mD)` and
`((mD)^g) = m^g (D^g)`, so (b) gives `χ(L^m) = m^g χ(L)` for all `m ∈ ℤ`, and the
derivation above applies. This is again a derivation, not a verbatim statement.

### Restrictions compared with the source

The source consequence holds over every field and for every line bundle `L`.
The Lean statement is narrower in three ways:

- the field `K` must be algebraically closed;
- `H` must be ample (`H.IsAmple`);
- `k` is a natural number with `k ≥ 1`. Formula (7) also gives the identity for
  `k = 0` and for negative `k`, which are not stated here.

The statement asserts nothing outside these cases. Every characteristic and
every dimension `g ≥ 0` are included. No dual-scheme, symmetry, characteristic,
Mumford-map, degree or vanishing hypothesis is added.

## Role and dependencies

The intended consumer is the exact-target proof task
`c430e7e4-f317-40b4-8a98-6a3180453c97` for
`Langlands.AbelianScheme.AlgClosedFieldEulerInverseSymmetryStatement`
(`χ(M) = (-1)^g χ(N)` when `N ⊗ M ≅ 𝒪`). That task avoids Riemann–Roch and
Serre duality, which the Library lacks. In its ample case it writes
`χ(H^n)` and `χ(H^{-n})` as `P(n)` and `P(-n)` for one integer polynomial `P`. This
statement then supplies `P(k) P(-k) = C k^{2g}` for every `k ≥ 1`, with
`C = χ(H) χ(H^{-1})`.

The statement uses no dual scheme, so it needs no dual-scheme witness. Its
import closure does not contain
`Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleMumfordEulerSquareStatement`,
`Langlands.AlgebraicGeometry.Picard.AlgClosedFieldEulerInverseSymmetryStatement`
or any module importing them. These two modules define
`Langlands.AbelianScheme.AlgClosedFieldAmpleMumfordEulerSquareStatement` and
`Langlands.AbelianScheme.AlgClosedFieldEulerInverseSymmetryStatement`. So the
dependencies stay acyclic.

## Proof routes (informational)

Riemann–Roch (formula (7)) gives the identity at once, but the Library does not
have it. One route that avoids Riemann–Roch is to use the Mumford bundle of `H`
on `A ×_K A`. The shear isomorphism and the Künneth formula compute its Euler
characteristic as `χ(H) χ(H^{-1})`. A dual-side computation, such as
`Langlands.AbelianScheme.AlgClosedFieldMumfordDualEulerStatement`, gives
`(-1)^g deg φ_H`. Then `φ_{H^k} = k φ_H` has degree `k^{2g} deg φ_H`. The source
carries out both computations of `χ(Λ(L))` for non-degenerate `L` in (8)–(12),
printed p.132 (PDF p.136), as its proof of `χ(L)² = deg(φ_L)`. A proof must not
use `AlgClosedFieldAmpleMumfordEulerSquareStatement`, whose own proof consumes the
consumer target. These remarks describe possible routes only; this file proves
nothing.
