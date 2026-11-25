# Galois twists of the split Cayley datum

Let `L/K` be a finite Galois extension and `P ∈ GL₈(L)` a change of basis.
Suppose every Galois discrepancy `P σ(P)⁻¹` is an automorphism matrix of
the split Cayley datum over `L`. This module transports the Zorn
multiplication, identity and norm along `P` and shows that they descend
to an actual `CayleyDatum K`, called `datum hP`. It then compares the
automorphism equations of `datum hP` with those of the split datum over
every `L`-algebra, nonreduced ones included. No characteristic assumption
is made.

## Transport along an invertible matrix (any commutative ring `R`)

- `twistBilin Q` is the bilinear map `(x, y) ↦ Q⁻¹((Qx)(Qy))`, with the
  Zorn product inside. `twistUnit Q = Q⁻¹ 1` and
  `twistNorm Q x = N(Qx)`.
- `twistBilin_map`, `twistUnit_map` and `twistNorm_map`: applying a ring
  homomorphism `f` coordinatewise turns the transported structure along
  `Q` into the one along `f(Q)`. They follow from `RingHom.map_mulVec`,
  `SplitCayley.map_mulFun` and the polynomial formula for the norm.
- `twistBilin_mul_left` and `twistUnit_mul_left`: replacing `Q` by `a Q`
  changes nothing when `a` preserves the Zorn product, respectively fixes
  `1`.
- `inv_mulVec_mulVec`, `mulVec_inv_mulVec` and `mulVec_injective` are
  elementary facts about invertible matrices.

## Descent

- `lift x` is the image of `x ∈ K⁸` in `L⁸`. It is additive, semilinear and
  injective, and every automorphism fixes it (`galois_lift`).
- `descendScalar x ∈ K` is chosen by `Classical.epsilon` with image `x`
  whenever such an element exists. `algebraMap_descendScalar` shows that
  this happens for every Galois-fixed `x`: by Mathlib's
  `IsGalois.mem_range_algebraMap_iff_fixed`, these are exactly the
  elements of `K`. `descendVec` descends vectors coordinatewise, and
  `lift_descendVec` is the corresponding statement for fixed vectors.
- `IsTwist P` says that `P σ(P)⁻¹` is an automorphism matrix of the split
  datum along `algebraMap K L`, for every `σ`.
- `map_eq` rewrites `σ(P)` as `(P σ(P)⁻¹)⁻¹ P`. The inverse discrepancy is
  again an automorphism matrix (`IsAutomorphismMatrix.inv`). It therefore
  preserves the Zorn product and fixes `1` (`inv_preserves_mul`,
  `inv_preserves_unit`). By `CayleyDatum.split_norm_mulVec_eq` it
  preserves the norm.
- `twistBilin_fixed`, `twistUnit_fixed` and `twistNorm_fixed`: for vectors
  coming from `K⁸`, the transported product, identity and norm are
  Galois-fixed. Applying `σ` replaces `P` by `σ(P)`, which is `P` with an
  automorphism on its left, and the transported structure ignores such
  factors.
- `mulFun`, `unitVec` and `normFun` are the descended product, identity
  and norm. `lift_mulFun`, `lift_unitVec` and `algebraMap_normFun` record
  that their images in `L` are the transported data.
  `algebraMap_polar_normFun` identifies the image of the polar form with
  the split polar form evaluated at `P x` and `P y`.
- `multiplication` is `mulFun` as a `K`-bilinear map. `norm` is `normFun`
  as a quadratic form, built with Mathlib's `QuadraticMap.ofPolar`. Each
  required identity is checked after the injective map to `L`, where it is
  an identity for the transported Zorn structure.
- `datum hP : CayleyDatum K` assembles them:
  - `unit_mul`, `mul_unit`, `norm_unit` and `norm_mul` follow from the
    split identities after cancelling `P P⁻¹`.
  - `polar_nondegenerate`: if the descended polar form of `x` vanishes on
    `K⁸`, then the split polar form of `P x` vanishes on all `P eⱼ`. Since
    `P` is invertible, it vanishes on all of `L⁸`. The split polar form
    is nondegenerate over `L`, so `P x = 0` and `x = 0`.

## Comparison over `L`-algebras

Fix a ring homomorphism `f : L →+* R` and write `Q` for the image of `P`
and `φ = f ∘ algebraMap K L`.

- `algebraMap_structureConstant`: the structure constants of `datum hP`
  map to the transported products of standard basis vectors.
- `multiplicationOver_eq` and `unitOver_eq`: the Library's extended
  multiplication and identity of `datum hP` along `φ` are the Zorn product
  and identity over `R` transported along `Q`. Both sides are bilinear,
  and they agree on standard basis vectors (`bilinear_apply_eq_sum`).
- `isAutomorphismMatrix_iff`: `h ∈ GL₈(R)` is an automorphism matrix of
  `datum hP` along `φ` exactly when `Q h Q⁻¹` is an automorphism matrix of
  the split datum along `φ`. Substitute `x = Q⁻¹ a` and `y = Q⁻¹ b`.
- `conjEquiv` is the resulting group isomorphism `h ↦ Q h Q⁻¹` between the
  two automorphism subgroups of `GL₈(R)`, with value lemmas
  `conjEquiv_apply` and `conjEquiv_symm_apply`.

## Source

Knus, Merkurjev, Rost and Tignol, *The Book of Involutions* (1998),
registered as `knus-merkurjev-rost-tignol-1998-book-of-involutions`. The
proof of Theorem 26.19, printed p.373 / PDF p.396, describes Cayley
algebras over `F` through the multiplication tensor in
`Hom(C ⊗ C, C)`, with descent along `F_sep/F`. Proposition 29.1, printed
p.392 / PDF p.415, gives the twisting rule. When `H¹(F, G) = 1`, a cocycle
`a_σ = g⁻¹ σ(g)` with values in the stabilizer of the tensor `w`
corresponds to the twisted tensor `g · w`. This module carries out that
construction at a finite Galois level, in coordinates. `P⁻¹` plays the
role of `g`, since `P σ(P)⁻¹ = (P⁻¹)⁻¹ σ(P⁻¹)`. The descended `datum hP`
is the twisted multiplication `(x, y) ↦ P⁻¹((Px)(Py))`. The
norm is descended as well. The argument through Galois-fixed scalars is a
derived formalization, not the source's wording.
