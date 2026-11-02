# The Euler characteristic of an inverse line bundle on an abelian variety

`Langlands.AbelianScheme.AlgClosedFieldEulerInverseSymmetryStatement.{u}` is a
proposition (a statement target, not a proof). Inside
`namespace Langlands.AbelianScheme`, with `open CategoryTheory AlgebraicGeometry`,
`open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules` and
`open Langlands.AlgebraicGeometry.Modules.DerivedSections`, its body is

```lean
∀ (K : Type u) [Field K] [IsAlgClosed K]
  (A : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ),
  A.HasRelativeDimension g →
    ∀ (N M : LineBundle A.X.left),
      Nonempty (tensorObj N.obj M.obj ≅ structureSheaf A.X.left) →
        ∀ (hN : HasFiniteCohomology A.X.hom N.obj)
          (hM : HasFiniteCohomology A.X.hom M.obj),
          eulerCharacteristic A.X.hom M.obj hM =
            (-1) ^ g * eulerCharacteristic A.X.hom N.obj hN
```

## Meaning

- `K` is an algebraically closed field in universe `u`, of any characteristic.
- `A` is a published `AbelianScheme` over `Spec K`: a commutative group scheme
  whose structure morphism `A.X.hom : A.X.left ⟶ Spec K` is smooth, proper and
  geometrically connected. So `A.X.left` is an abelian variety over `K`.
- `A.HasRelativeDimension g` is the published abbreviation for
  `SmoothOfRelativeDimension g A.X.hom`; `g` is the dimension of the abelian
  variety. The case `g = 0` is included.
- `N` and `M` are published line bundles on `A.X.left` (locally free sheaves of
  rank one). The hypothesis is that some isomorphism exists from the published
  sheaf tensor product `tensorObj N.obj M.obj` to the structure sheaf
  `structureSheaf A.X.left`. So `M` is an inverse of `N` in the Picard group,
  `M ≅ N⁻¹`. Only the existence of the isomorphism matters, not a choice.
- `hN` and `hM` are arbitrary proofs of the published finiteness predicate
  `HasFiniteCohomology`: every actual derived cohomology object
  `relativeCohomology A.X.hom n` of the sheaf is a finite-dimensional
  `K`-vector space, and these objects vanish in all sufficiently high degrees.
  `HasFiniteCohomology` is a proposition, so the Euler characteristics do not
  depend on these proofs. The proved Library theorem
  `Langlands.AlgebraicGeometry.Modules.smoothProperLineBundleFiniteCohomology`
  supplies such proofs for line bundles on smooth proper schemes over a field.
  They are taken as binders so that the statement does not import that proof.
- `eulerCharacteristic A.X.hom F h` is the published integer
  `∑ᶠ n, (-1)^n * dim_K Hⁿ(A, F)`. It uses the actual derived cohomology with
  the `K`-structure induced by `A.X.hom`.

The conclusion is `χ(M) = (-1)^g · χ(N)`, which is `χ(N⁻¹) = (-1)^g χ(N)`.
Exchanging `N` and `M` gives the same statement (by `tensorComm` and
`(-1)^g · (-1)^g = 1`), so the statement is symmetric in the two bundles.

## Source

B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties*, preliminary
version of the first chapters (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), Chapter IX, *The
cohomology of line bundles* (from printed p.126), (9.11) Riemann–Roch Theorem and
its proof, printed p.131 (PDF p.135; printed page = PDF page − 4). For a line
bundle `L` on a `g`-dimensional abelian variety `X` over a field, (9.11)
states `χ(L) = c₁(L)^g / g!`, and the proof derives it from the
Hirzebruch–Riemann–Roch formula, using that the tangent bundle is trivial. The
proof then notes, as its displayed formula (7), that
`χ(L^m) = m^g · χ(L)` for all `m ∈ ℤ`. Taking `m = -1` gives
`χ(L⁻¹) = (-1)^g χ(L)`, which is this statement with `L = N` and `L⁻¹ ≅ M`.
The Euler characteristic of an isomorphic sheaf is unchanged, so the
isomorphism `M ≅ N⁻¹` can replace `N⁻¹` by `M`.

The book's definition of `χ` is (9.10), printed p.130 (PDF p.134): for a
quasi-coherent module `F` on a proper scheme `X` of finite type over a field
`k`, `χ(F) = ∑_{i ≥ 0} (-1)^i dim_k Hⁱ(X, F)`. (The printed display writes
`χ(L)` on the left; the defined quantity is `χ(F)`.) The published
`eulerCharacteristic` is the same alternating sum, where `Hⁱ` is the usual
sheaf cohomology: the right derived functors of global sections on
`O_X`-modules, with the `K`-structure coming from `A.X.hom`.

The book's abelian varieties match the Lean objects. By (0.1) and (0.4) of the
book, `k` is an arbitrary field and a variety over `k` is a separated
geometrically integral scheme of finite type over `k`; by Definition 1.3 an
abelian variety is a complete group variety. The scheme `A.X.left` is proper
and smooth over `K` with geometrically connected fibre, and it has a rational
point (the unit section). A smooth connected group scheme over a field is
geometrically integral, so `A.X.left` is an abelian variety in the book's sense
of dimension `g`.

The same identity follows from J. S. Milne, *Abelian Varieties* (registered
source `milne-abelian-varieties-1986-author-2022`), Theorem 13.3 (b), p.25:
`χ(L(D)) = (D^g)/g!`. Replacing `D` by `-D` multiplies the self-intersection
number by `(-1)^g`. This second citation is a derivation, not a verbatim
statement.

### Restriction compared with the source

The source holds over every field. Here the field is required to be
algebraically closed, because the intended consumer, the Euler-square task
`fc8e4732-8e1b-497e-adb1-c27ee538f442` for
`AlgClosedFieldAmpleMumfordEulerSquareStatement`, only needs that case. The
statement asserts nothing over other fields.

## Proof routes (informational)

The statement is a Serre-duality-level fact. One standard proof uses Serre
duality on the smooth proper `g`-dimensional variety `A`. The canonical sheaf
of an abelian variety is trivial, because the tangent bundle is trivial.
Duality then gives `Hⁱ(A, N⁻¹) ≅ H^{g-i}(A, N)^∨` for every `i`, so
`χ(N⁻¹) = (-1)^g χ(N)`. Another route is the Riemann–Roch argument of the
source: show that `m ↦ χ(L^m)` equals `m ↦ m^g χ(L)` on all integers `m`, and
take `m = -1`. The current Library's proved theorem
`Langlands.AlgebraicGeometry.Picard.smoothProperLineBundleEulerPolynomial`
(of `SmoothProperLineBundleEulerPolynomialStatement`) gives polynomiality of
`χ(L^n)` only for natural `n`, so this route would also need the
negative-exponent case. Neither Serre duality nor negative-exponent
polynomiality is in the current Library.

## Role

This is one prerequisite of the final exact-target proof of
`Langlands.AbelianScheme.AlgClosedFieldAmpleMumfordEulerSquareStatement`. There,
`M ≅ L⁻¹` comes from the Mumford normalization, and the shear/Künneth
computation gives `χ(L) · χ(M)`. That product must be compared with
`(-1)^g` times the degree of the Mumford map.
