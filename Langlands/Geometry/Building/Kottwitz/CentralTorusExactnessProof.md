# Right exactness of inertia coinvariants for a central torus quotient

This module proves the Library statement
`Langlands.Geometry.Building.Kottwitz.CentralTorusInertiaExactnessStatement` as
the theorem `Langlands.Geometry.Building.Kottwitz.centralTorusInertiaExactness`.

For a tower `k ⊆ K ⊆ E` with `E` a separable closure of `k` and `K/k` normal, a
`k`-torus `Z`, connected reductive `k`-groups `H` and `G`, a closed central
inclusion `i : Z → H` and an fppf quotient `p : H → G` by the full subgroup
functor of `i`, the theorem proves that the selected inertia map
`fundamentalInertiaMap k K E G hG H hH p : π₁(H)_I → π₁(G)_I` is surjective and
that its kernel is the range of the selected inertia map
`π₁(Z)_I → π₁(H)_I` induced by `i`. Here `I` is the relative inertia group
`relativeInertia k K E`, acting through the Galois representation of the chosen
presentation. Injectivity on the left is not claimed.

## Source

Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), source ID
`kaletha-prasad-2023-bruhat-tits-new-approach`: the proofs of Lemma 11.5.1
(printed p. 430 / PDF p. 461) and Proposition 11.5.3 (printed p. 431 /
PDF p. 462). There the exact sequence `0 → π₁(Z) → π₁(H) → π₁(G) → 0` for a
z-extension is passed to inertia coinvariants, which are right exact. The Library
statement is for an arbitrary closed central torus, a derived generalization
proved in the same way. The Lean proof below follows this route.

## Right exactness of coinvariants

`Representation.Coinvariants.rightExact_of_descent` is pure algebra. Let
`ρA, ρB, ρC` be representations of a monoid `Γ` over a commutative ring `R`, and
let `f : A → B` and `g : B → C` be linear maps with `g` equivariant, `g`
surjective and `ker g = range f`. For any linear maps `mf`, `mg` between the
coinvariant modules with `mf ∘ mk = mk ∘ f` and `mg ∘ mk = mk ∘ g` on
representatives, the theorem proves that `mg` is surjective and
`ker mg = range mf`. The proof:

- surjectivity: `mk ∘ g` is surjective and equals `mg ∘ mk`;
- `range mf ⊆ ker mg`: `mg (mf (mk z)) = mk (g (f z)) = 0`, since `f z ∈ ker g`;
- `ker mg ⊆ range mf`: if `mk (g b) = 0`, then `g b` lies in the span of the
  differences `ρC γ c - c`. Writing `c = g b'` and using equivariance, each
  difference is `g (ρB γ b' - b')`. So `g b = g b''` for some `b''` in the
  coinvariant kernel of `ρB`. Then `b - b'' = f z`, and
  `mk b = mk (b - b'') = mf (mk z)`.

Equivariance of `f` is not needed, because the hypothesis on `mf` already
records its descent.

## The main theorem

`centralTorusInertiaExactness` combines three published results:

- `Langlands.GroupScheme.AlgebraicFundamentalGroup.centralTorusFundamentalExactness`
  proves `CentralTorusFundamentalExactnessStatement` for the same data (it does not
  need `K`). It gives surjectivity of the selected map
  `fundamentalGroupMap k E H G hH hG p` and the equality of the range of the map
  induced by `i` with the kernel of the map induced by `p`. Its injectivity
  clause is not used.
- `algebraicFundamentalGroupMap` (the proof of KP Lemma 11.3.6 for
  fundamental groups), applied to the chosen presentations, gives Galois
  equivariance of `fundamentalGroupMap k E H G hH hG p`. This is in particular
  equivariance for the inertia subgroup.
- `fundamentalInertiaMapStatement` (the proof of
  `FundamentalInertiaMapStatement`) gives the representative law
  `IsFundamentalInertiaMap` for the two selected inertia maps
  `fundamentalInertiaMap`. Its `Normal k E` hypothesis holds because a separable
  closure is Galois over `k`.

`rightExact_of_descent` is then applied to the inertia representations, with
`f` and `g` the two selected fundamental-group maps and `mf`, `mg` the two
selected inertia maps.
