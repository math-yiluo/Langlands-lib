# Rationality of the Weil restriction of `𝔾_m` along a finite algebra over a field

This helper module proves that for every field `k` and every commutative `k`-algebra `B` that
is finite over `k`, the Weil restriction `(𝔾_m)_{B/k}` is birational over `k` to a
finite-dimensional affine space. No separability, field or étaleness hypothesis on `B` is
used. The module supports the proof of `TorusUnirationalityStatement` in
[`TorusUnirationalityProof`](TorusUnirationalityProof.md), where it gives parts 1 and 3 and
the unirational source used in part 2.

It imports [`Torus.TorusUnirationalityStatement`](TorusUnirationalityStatement.md), for
`WeilGm.groupScheme` and `HasFiniteAffineBirationalModel`, and
[`FiniteAlgebraUnits`](../FiniteAlgebraUnits.md), for the determinant-open unit group scheme.
All declarations are in the namespace `Langlands.GroupScheme.WeilGmRational`. The module adds
no statement definitions and no axioms.

## Main results

```lean
theorem hasFiniteAffineBirationalModel (k : Type u) [Field k] (B : Type u) [CommRing B]
    [Algebra k B] [Module.Finite k B] :
    HasFiniteAffineBirationalModel k (WeilGm.groupScheme (CommRingCat.of k) B).X

theorem nonempty_left (k : Type u) [Field k] (B : Type u) [CommRing B] [Algebra k B]
    [Module.Finite k B] :
    Nonempty (WeilGm.groupScheme (CommRingCat.of k) B).X.left
```

`HasFiniteAffineBirationalModel k X` (module
[`PointTopology.UnirationalTransport`](../../AlgebraicGeometry/PointTopology/UnirationalTransport.md))
says that for some finite `ι : Type u` the structure morphism `X.hom` is birational over
`Spec k` (Mathlib's `Scheme.BirationalOver`) to `𝔸(ι; Spec k) ⟶ Spec k`. The witness here is
`ι = ULift (Fin n)` with `n = finrank k B`.

`nonempty_left` says that the underlying scheme of `(𝔾_m)_{B/k}` is nonempty. It is used in
part 2 of the main proof to show that a certain image is nonempty.

## Mathematical content

This is the argument of Milne, *Algebraic Groups* (2017), Proposition 12.60, p.250, for an
arbitrary finite algebra instead of a field. Choose a `k`-basis `b` of `B` with `n` elements.
A point of `(𝔾_m)_{B/k}` with values in `R` is a unit of `B ⊗ R`, that is, an element
`∑ xᵢ bᵢ` whose multiplication matrix has invertible determinant. So `(𝔾_m)_{B/k}` is the
principal open subscheme `D(det)` of `𝔸ⁿ`, where `det` is the norm of the generic element
`∑ Xᵢ bᵢ`. The Library already builds this principal open as a group scheme
(`FiniteAlgebraUnits.groupScheme b`), so the proof only identifies the two group schemes and
uses that `D(det)` is a dense open subscheme of `𝔸ⁿ`. Density needs `D(det)` nonempty, which
holds because `det` is not nilpotent: evaluating at the coordinates of `1 ∈ B` gives
`det = 1`.

## Implemented proof

Fix the basis `b : Module.Basis (Fin n) k B`.

1. **`unitsComm T`** is the group isomorphism `(T ⊗[k] B)ˣ ≃* (B ⊗[k] T)ˣ` induced by
   `Algebra.TensorProduct.comm`. **`unitsComm_naturality`** says that it commutes with change
   of the test algebra `T`. The proof is induction on tensors.
2. **`unitsIso b : WeilGm.groupScheme (CommRingCat.of k) B ≅ FiniteAlgebraUnits.groupScheme b`**
   is built with `isoOfPointModels` (module [`Torus.Split`](Split.md)). This constructor
   needs one natural model of the point groups of both group schemes on every test scheme
   `T` over `Spec k`. The model is `(B ⊗[k] Γ(T))ˣ`, where `Γ(T)` is the `k`-algebra of global
   sections (`algΓ`). The Weil side uses `WeilGm.pointsEquiv` and its naturality. The other
   side uses `FiniteAlgebraUnits.pointsEquiv b T`, whose target is `(Γ(T) ⊗[k] B)ˣ`, followed
   by `unitsComm`. Its naturality is `FiniteAlgebraUnits.pointsEquiv_naturality` together with
   `unitsComm_naturality`.
3. **`leftIso b`** is the underlying isomorphism of schemes
   `(WeilGm.groupScheme (CommRingCat.of k) B).X.left ≅ Spec (candidateRing b)`, where
   `FiniteAlgebraUnits.candidateRing b` is the localization of `k[X_0, …, X_{n-1}]` away from
   `FiniteAlgebraUnits.determinant b`. **`leftIso_hom_over`** says that it commutes with the
   maps to `Spec k`. This is `Over.w` of the underlying morphism of `unitsIso b`.
4. **`renameRingHom k n`** is the ring isomorphism `MvPolynomial (ULift (Fin n)) k →+*
   MvPolynomial (Fin n) k` that renames variables. **`chart b`** is the composite
   `Spec (candidateRing b) ⟶ Spec k[X_i]_{i ∈ Fin n} ⟶ Spec k[X_i]_{i ∈ ULift (Fin n)} ≅
   𝔸(ULift (Fin n); Spec k)`. Its three factors are the localization map, the renaming and
   `AffineSpace.SpecIso`. It is an open immersion: the localization map is one, and the other
   two factors are isomorphisms. **`chart_over`** says that `chart b` commutes with the maps
   to `Spec k`. The proof rewrites with `AffineSpace.SpecIso_inv_over` and compares the ring
   maps on `k`.
5. **`candidateRing_nontrivial b`**: the ring `candidateRing b` is nontrivial, because it has
   a `k`-algebra map to `k`, namely `FiniteAlgebraUnits.unitCoefficientMap b 1`, the
   coefficient map of the unit `1`.
6. **`weilChart b := (leftIso b).hom ≫ chart b`** is an open immersion. It is dominant, since
   its range is open and contains the image of a prime of the nontrivial ring
   `candidateRing b`. **`weilChart_over`** combines `chart_over` and `leftIso_hom_over`.
7. **`nonempty_left`**: with `b := Module.finBasis k B`, the image under `leftIso b` of a
   prime of `candidateRing b` is a point.
8. **`hasFiniteAffineBirationalModel`**: with `b := Module.finBasis k B`, Mathlib's
   `Scheme.Hom.birationalOver` turns the dominant open immersion `weilChart b` and the
   compatibility `weilChart_over` into `Scheme.BirationalOver` between the structure map of
   `(𝔾_m)_{B/k}` and `𝔸(ULift (Fin (finrank k B)); Spec k) ⟶ Spec k`. The index type is
   finite.

## Sources

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`,
Proposition 12.60, p.250, and Definition 12.59, p.250. The proof follows Milne's argument
(Weil restriction of `𝔾_m` as the complement of the norm hypersurface in `𝔸ⁿ`). The
generalization from a finite field extension `k'` to an arbitrary finite `k`-algebra `B` is
internal. The argument does not use that `B` is a field, and the generalization gives
Proposition 12.64 for induced tori directly.
