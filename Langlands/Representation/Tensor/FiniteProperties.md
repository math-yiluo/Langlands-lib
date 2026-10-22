# Irreducibility, admissibility and Jacquet vanishing of finite external tensors

Author: Worker 218.

This module proves three general properties of the Library's actual finite
external tensor product `Langlands.FiniteTensor.external` (from
`Langlands.Representation.Tensor.Finite`). Here `ρ i` is a representation of a
group `H i` on a vector space `V i` over a field `k`, for `i` in a finite
index type `ι`. It acts on `⨂[k] i, V i`, and `g` acts on a pure tensor by
`⊗ v i ↦ ⊗ ρ i (g i) (v i)`. No factor is assumed finite-dimensional.

- `isIrreducible_external`: if every factor is irreducible and every
  self-intertwiner of every factor is a scalar multiple of the identity, the
  external tensor product is irreducible.
- `isAdmissible_external`: if the groups carry topologies and every factor is
  admissible, the external tensor product is admissible for the product
  topology.
- `coinvariants_external_subsingleton`: if one factor `j` has zero
  coinvariants `Jacquet.Coinvariants (ρ j) (N j)`, the external tensor product
  has zero coinvariants for the product subgroup `Subgroup.pi Set.univ N`.

These are standard facts about tensor products of representations. The proofs
below are self-contained and use only Mathlib and the Library modules
imported here. The scalar-endomorphism hypothesis of the first item is stated
explicitly. For admissible irreducible complex representations, the Library's
Schur lemma `Langlands.admissibleSchur_scalarEndomorphism` supplies it.

## Internal notation: one-slot maps

`slot j T` is the family of linear maps that is `T` in slot `j` and the
identity in every other slot. It is an `abbrev` for `Function.update`, used
only as notation inside these proofs; it is not a mathematical definition
from the literature. The supporting lemmas are as follows.

- `slot_apply_update` and `map_slot_tprod_update` show that
  `PiTensorProduct.map (slot j T)` changes only the `j`-th entry of a pure
  tensor.
- `map_induction`: a property preserved by every one-slot map
  `PiTensorProduct.map (slot j (f j))` is preserved by `PiTensorProduct.map f`.
  The proof is by induction on finite sets `S`, using the families that are
  `f i` for `i ∈ S` and the identity outside `S`. Adding an index factors the
  family as a composite with a one-slot map (`PiTensorProduct.map_comp`).
- `split_map_slot`: under Mathlib's equivalence
  `PiTensorProduct.equivPiTensorComplSingletonTensor`, which writes the tensor
  product as `(⨂ over i ≠ j) ⊗ V j`, a one-slot map becomes
  `LinearMap.lTensor _ T`. The two linear maps agree on pure tensors.

## Fixed vectors of maps in one slot

`lTensor_eq_of_forall_fixed` concerns a family of maps `T a` on a vector
space `W` and a map `π` on `W` that fixes every common fixed vector of the
family. If `y ∈ X ⊗ W` is fixed by every `lTensor X (T a)`, then `y` is fixed
by `lTensor X π`. The proof chooses bases `b` of `X` and `c` of `W`. For each
basis index `κ` of `X`, it uses the contraction
`Φ κ = lid ∘ rTensor (b.coord κ) : X ⊗ W → W`. Then `Φ κ` commutes with every
`lTensor X S`, and the coordinate of `z` at `(κ, μ)` in the tensor basis
`b.tensorProduct c` is the `μ`-coordinate of `Φ κ z`. Each `Φ κ y` is fixed by
all `T a`, hence by `π`. So `lTensor X π y - y` has all coordinates zero.

`map_slot_eq_of_forall_fixed` transfers this to one slot of the indexed
tensor product through `split_map_slot`. `map_eq_of_forall_fixed` then uses
`map_induction` to treat all slots at once: if `x` is fixed slotwise by the
families `T i`, and each `π i` fixes the common fixed vectors of `T i`, then
`PiTensorProduct.map π x = x`.

## Action of coordinate elements and group-algebra stability

`external_mulSingle` shows that `external ρ (Pi.mulSingle j h)` equals
`PiTensorProduct.map (slot j (ρ j h))`, because `ρ i 1` is the identity in
every other slot.

`map_slot_asAlgebraHom_mem` shows that a subrepresentation `U` of
`external ρ` is stable under `PiTensorProduct.map (slot j a)` for every image
`a = (ρ j).asAlgebraHom r` of a group-algebra element `r`. The proof is
induction on `r` (`MonoidAlgebra.induction_linear`). The zero and sum cases
use multilinearity of `PiTensorProduct.map` in slot `j`. A single
`c • g` acts as `c` times the coordinate element `Pi.mulSingle j g`, which
preserves `U`. `map_asAlgebraHom_mem` combines these slots through
`map_induction`. Thus `U` is stable under
`PiTensorProduct.map (fun i => (ρ i).asAlgebraHom (r i))` for any family `r`.

## Irreducibility

`exists_asAlgebraHom_eq_on` is a form of the Jacobson density theorem. Let `σ`
be irreducible, so its group-algebra module `σ.asModule` is simple. Suppose
every self-intertwiner of `σ` is scalar. Then for every `k`-linear map `f` on
the carrier and every finite set `s` of vectors, some group-algebra element
acts as `f` on `s`. Self-intertwiners are exactly the group-algebra-linear
endomorphisms (`Representation.IntertwiningMap.equivLinearMapAsModule`). The
hypothesis therefore makes `f`, transported to `σ.asModule` by
`σ.asModuleEquiv`, commute with every such endomorphism. Mathlib's
`jacobson_density` then provides the group-algebra element.

`isIrreducible_external` chooses bases `b i` of the factors
(`Basis.ofVectorSpace`) and the product basis `Bt = Basis.piTensorProduct b`.
Each factor is nontrivial because it is simple as a group-algebra module, so
each basis index type is nonempty. The basis vector of a chosen multi-index
is then a nonzero tensor, and the lattice of subrepresentations has `⊥ ≠ ⊤`.

Now let `U` be a subrepresentation containing `x ≠ 0`, and fix a multi-index
`p` with `Bt.repr x p ≠ 0`. For any vectors `u i`, let `f i` be the rank-one
map `w ↦ (b i).coord (p i) w • u i`. Then `PiTensorProduct.map f` is the
rank-one map `y ↦ Bt.repr y p • tprod u`, as checked on pure tensors with
`Basis.piTensorProduct_repr_tprod_apply`. Density in each factor gives
group-algebra elements `r i` that act as `f i` on the finitely many basis
vectors `b i (q i)` with `q` in the support of `Bt.repr x`. Expanding `x` in
the basis `Bt` shows that
`PiTensorProduct.map (fun i => (ρ i).asAlgebraHom (r i)) x` equals
`PiTensorProduct.map f x`. The left side lies in `U` by group-algebra
stability, and the right side is `Bt.repr x p • tprod u`. Dividing by the
nonzero coordinate puts every pure tensor in `U`. Since pure tensors span
(`PiTensorProduct.span_tprod_eq_top`), `U = ⊤`. A subrepresentation with no
nonzero vector is `⊥`.

## Admissibility

`fixedVectors_external_le` concerns subgroups `K i ≤ H i`. It shows that the
vectors fixed by `Subgroup.pi Set.univ K` lie in the range of
`PiTensorProduct.map` applied to the inclusions of the factor fixed spaces
`fixedVectors (ρ i) (K i)`. In each factor, choose a complement of the fixed
space (`Submodule.exists_isCompl`), let `p i` be the projection onto the fixed
space along it (`Submodule.projectionOnto`), and let `π i` be `p i` followed
by the inclusion. Each `π i` fixes every `K i`-fixed vector. A vector `x`
fixed by the product subgroup is fixed by every coordinate element
`Pi.mulSingle j a` with `a ∈ K j`, that is, by every one-slot map
`slot j (ρ j a)` (`external_mulSingle`). By `map_eq_of_forall_fixed`,
`PiTensorProduct.map π x = x`. This map factors as the inclusion map after
`PiTensorProduct.map p`, so `x` lies in the range.

`isAdmissible_external` gets smoothness from the Library's
`isSmooth_external`. Given an open subgroup `K` of the product group, let `K' i`
be its preimage under the continuous coordinate inclusion
`MonoidHom.mulSingle H i` (`OpenSubgroup.comap`, `continuous_mulSingle`).
Every element of `Subgroup.pi Set.univ K'` lies in `K`
(`Subgroup.pi_mem_of_mulSingle_mem`, using finiteness of `ι`). So the
`K`-fixed vectors lie inside the fixed vectors of the product subgroup. By
the previous lemma these lie in the range of a linear map from
`⨂ i, fixedVectors (ρ i) (K' i)`. That tensor product is finite-dimensional
because each factor is, by admissibility (Mathlib's instance
`PiTensorProduct.finite`). `Submodule.finiteDimensional_of_le`
concludes.

## Coinvariant vanishing

`subsingleton_coinvariants_iff` uses `Jacquet.mk_eq_zero` and
`Jacquet.mk_surjective`. It shows that `Jacquet.Coinvariants σ N` is a
subsingleton exactly when every vector lies in `Jacquet.relations σ N`.

`coinvariants_external_subsingleton` assumes the coinvariants of factor `j`
for `N j` vanish. Fix a pure tensor `tprod v`. Let `e` be the linear map
`w ↦ tprod (update v j w)` from `V j`. By `Jacquet.relations_eq_span`, the
relations of `ρ j` are spanned by the vectors `ρ j n w - w` with `n ∈ N j`.
The map `e` sends each of these to
`external ρ (Pi.mulSingle j n) (e w) - e w`, a relation for the product
subgroup, since `Pi.mulSingle j n ∈ Subgroup.pi Set.univ N`. So `e` maps all
relations of `ρ j` into the product relations. By hypothesis `v j` is a
relation, so `tprod v = e (v j)` is a product relation. Pure tensors span, so
every vector is a relation, and the coinvariants vanish.
