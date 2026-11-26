# Vanishing of degree-two Čech classes that become primitive on the square

Module `Langlands.AbelianScheme.PrimitiveCechVanishing`, namespace
`Langlands.AbelianScheme.PrimitiveCechVanishing`.

Let `K` be a field and `A` an abelian scheme over `Spec K`. Write `P = A.X ⨯ A.X` for the
square in schemes over `Spec K`, `p₁`, `p₂` for the projections and `mul A = p₁ * p₂` for the
group law (`mul`).

## The statement

`exists_coboundary` concerns ordered Čech cochains of the structure sheaf in the Library's
model `CechResolution.AllSeq` (cochains indexed by all tuples). Its data are

- a finite affine cover `W : I → A.X.left.Opens` of `A` and a `2`-cocycle `d` for it;
- a finite affine cover `W₂ : κ → P.left.Opens` of `P` and a `2`-cocycle `e` for it;
- two further finite affine covers `VP : LP → P.left.Opens` and `VQ : LQ → P.left.Opens` of
  `P`, with index maps `βP`, `βQ` into `κ` such that `VP j ≤ W₂ (βP j)` and
  `VQ j ≤ W₂ (βQ j)`;
- index maps `a₁ : LP → I`, `aₘ : LQ → I`, `a₂ : LQ → I` with `VP j` inside the inverse image
  of `W (a₁ j)` under `p₁`, and `VQ j` inside the inverse images of `W (aₘ j)` under `mul A`
  and of `W (a₂ j)` under `p₂`.

The hypotheses are two equalities of cochains:

- `hP`: the refinement of `e` to `VP` (`refineCochain` along `βP`) is the pullback of `d`
  along `p₁` (`unitCochainMap` along `a₁`);
- `hQ`: the refinement of `e` to `VQ` is the pullback of `d` along `mul A` minus the pullback
  of `d` along `p₂`.

The conclusion is that `d` is a coboundary: `d = dCochain y` for some `1`-cochain `y`.

## Proof

Let `o` be the actual cohomology class of `d` in `H²(A, 𝒪_A)` (`canonicalClass`), and write
`f^*` for the canonical pullback of structure-sheaf cohomology along `f : P ⟶ A`, as in
`FieldH2PrimitiveInjectivityStatement`. The class of `e` equals the class of each of its
refinements (`canonicalClass_refine`), and the class of a pulled-back cocycle is the pullback
of the class (`pull_canonicalClass`). By `hP` the class of `e` is `p₁^* o`; by `hQ` and
linearity it is `(mul A)^* o - p₂^* o`. Hence
`((mul A)^* - p₁^* - p₂^*) o = 0`, and the published theorem `fieldH2PrimitiveInjectivity`
gives `o = 0`. By `canonicalClass_eq_zero_iff`, `d` is a coboundary.

The proof is checked with an increased heartbeat limit (`maxHeartbeats 1600000`) for the
unfolding of the pullback maps.

## Provenance

The argument is the one in Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura
varieties*, Harvard thesis revised 14 March 2021, proof of Proposition 2.2.4.1 (printed
pp. 152–154, PDF pp. 180–182), registered as `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`. There the
obstruction of `A × A` is computed on a product cover as `pr₁^* o + pr₂^* o` and, through
the automorphism `(x, y) ↦ (x + y, y)`, as an expression involving `m^* o`; comparing
first components shows that `o` is primitive and hence zero. In this module only the first
components enter, the two computations are the hypotheses `hP` and `hQ` on two subcovers of
one cover, and the vanishing of primitive classes is the Library's
`fieldH2PrimitiveInjectivity`. The comparison of Čech classes uses the Library's
`CechResolution.AllSeq` refinement and pullback theorems.
