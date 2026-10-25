# Directed local algebra and module approximation systems

This module defines the data and properties of the systems appearing in the
Stacks Project, Lemma 10.127.13 (tag **00QX**), together with its ring-only
predecessor Lemma 10.127.11 (tag **00QV**). It defines no existence or flatness
statement. In particular, Lemma 10.128.3 (tag **00R6**) is a later consumer, not
a conclusion stored in these data.

## Source and provenance

The original is the registered source
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`:

- `00QL.html`, Lemma 10.127.13, all six displayed conditions and its proof;
- `00QV.html`, Lemma 10.127.11, its four conditions and proof;
- `00R3.html`, Lemma 10.128.3, its statement and proof, for the intended use.

The online originals are [00QX](https://stacks.math.columbia.edu/tag/00QX),
[00QV](https://stacks.math.columbia.edu/tag/00QV), and
[00R6](https://stacks.math.columbia.edu/tag/00R6).
The source hypothesis of 00QX is a local map of local rings `R → S`, with `S`
essentially finitely presented over `R` and `M` finitely presented over `S`.
Those finite-presentation hypotheses belong in the later existence statement;
they are not needed to define a diagram or its six approximation properties.
The source proof constructs local polynomial quotients and cokernels of finite
matrices. This module does not carry out that construction.

The data structures, use of a directed preorder, chosen cocone maps, direct-limit
comparison maps, tensor order, and universe parameters are an internal API
presentation of the source systems. Mathlib supplies the algebraic constructions:
`DirectedSystem`, `Ring.DirectLimit`, `AddCommGroup.DirectLimit`,
`Algebra.EssFiniteType`, `Module.Finite`, tensor products, and
`IsLocalization.AtPrime`. The short equation lemmas follow by unfolding the
canonical tensor lifts or by applying Mathlib's direct-limit computation rules
and semilinearity. No existence, descent, or flatness lemma is used in them.

## Local algebra data

All names are in `Langlands.Algebra`. The structure
`LocalAlgebraSystem.{uI,uA,uB,uR,uS} ι R S` has explicit ambient assumptions
`[Preorder ι] [Nonempty ι] [IsDirectedOrder ι]`, commutative local rings `R,S`,
and a local algebra map `algebraMap R S`. A directed preorder is sufficient:
antisymmetry is not used in the diagram, and an ordinary directed partially
ordered set is a special case.

For a system `D`, the exposed fields are:

| Fields | Meaning |
| --- | --- |
| `base i`, `alg i` | The actual rings `Rᵢ`, `Sᵢ`, with commutative-ring and local-ring instances. |
| `componentAlgebra`, `structure_local` | The actual local structure map `fᵢ : Rᵢ → Sᵢ`, expressed as `algebraMap`. |
| `baseMap i j h`, `algMap i j h` | Ring homomorphisms `rᵢⱼ : Rᵢ → Rⱼ`, `sᵢⱼ : Sᵢ → Sⱼ` for `h : i ≤ j`. |
| `base_directed`, `alg_directed` | Mathlib `DirectedSystem` identity and composition laws. |
| `baseMap_local`, `algMap_local` | Locality of both transition homomorphisms. |
| `map_comm` | `sᵢⱼ(fᵢ(r)) = fⱼ(rᵢⱼ(r))`. |
| `baseι i`, `algι i` | Actual ring homomorphisms `Rᵢ → R` and `Sᵢ → S`. |
| `baseι_local`, `algι_local` | Locality of the cocone homomorphisms. |
| `baseι_compat`, `algι_compat` | Each cocone map commutes with every transition. |
| `ι_comm` | `algι i (fᵢ(r)) = algebraMap R S (baseι i r)`. |

The `DirectedSystem` laws say that the self-map is the identity and that
`map j k hjk (map i j hij x) = map i k (hij.trans hjk) x`. All maps are bound to
the same exposed ring structures; the commuting-square equations do not use
separately chosen algebra structures.

## Varying-ring modules and colimits

For `M : Type uM`, `[AddCommGroup M] [Module S M]`,
`LocalModuleSystem.{uI,uA,uB,uN,uR,uS,uM} D M` supplies:

- actual `obj i = Mᵢ : Type uN`, with additive-group and `Sᵢ`-module instances;
- `map i j h : Mᵢ →ₛₗ[D.algMap i j h] Mⱼ`;
- `directed`, with identity and composition laws on those maps;
- `ιM i : Mᵢ →ₛₗ[D.algι i] M`, and `ιM_compat` for its cocone law.

Thus `map i j h (s • m) = D.algMap i j h s • map i j h m`, and
`ιM i (s • m) = D.algι i s • ιM i m`. These are actual semilinear maps, not
arbitrary functions labelled as module maps. Restricting scalars along
`algebraMap (D.base i) (D.alg i)` gives the component base-ring module action
when a consumer needs it.

`LocalAlgebraSystem.baseColimitMap` and `algebraColimitMap` use
`Ring.DirectLimit.lift` on the specified ring cocones. The corresponding `_of`
lemmas identify their values on each canonical inclusion.
`LocalAlgebraSystem.IsColimit` is bijectivity of both of these ring maps.
The definition therefore identifies genuine Mathlib colimits with `R` and `S`;
Mathlib's lift and uniqueness properties are available. The two commuting-square
laws ensure that these identifications respect the given arrow `R → S`.

`LocalModuleSystem.moduleColimitMap` is `AddCommGroup.DirectLimit.lift` on the
underlying additive maps, using classical decidable equality on the index.
`moduleColimitMap_of` identifies it with `ιM i` on every component.
`moduleColimitMap_smul_of` explicitly proves its compatibility with the
`Sᵢ`-actions through `D.algι i`. The predicate `LocalModuleSystem.IsColimit`
requires `D.IsColimit` and bijectivity of this additive comparison map.
This specifies the underlying module colimit together with the compatible
already-given `S`-action on `M`; it does not assume an unrelated module
identification. An explicit action of the ring direct limit on the additive
direct limit is not constructed here. Its comparison with other colimit APIs
can be developed from these canonical maps later.

## The actual base-change maps

`D.RingBaseChange h` is the actual tensor product `Sᵢ ⊗[Rᵢ] Rⱼ`, with the
`Rᵢ`-algebra structure on `Rⱼ` induced by `D.baseMap i j h`. The ring homomorphism
`D.ringBaseChangeMap h` is constructed using `Algebra.TensorProduct.lift` and
`D.map_comm`. Its computation lemma `ringBaseChangeMap_tmul` reads

```
s ⊗ r ↦ D.algMap i j h s * algebraMap (D.base j) (D.alg j) r.
```

`D.IsPrimeLocalization h` first installs the algebra structure induced by this
exact ring homomorphism. It then requires an actual ideal
`p : Ideal (D.RingBaseChange h)`, a proof `hp : p.IsPrime`, and
`IsLocalization.AtPrime (D.alg j) p` for that installed structure.
The prime is an existential witness that a proof may extract. This is a
localization condition on the canonical map; it does not require that map to
be bijective.

`E.moduleBaseChangeMap h` is the canonical `Sⱼ`-linear map

```
Sⱼ ⊗[Sᵢ] Mᵢ →ₗ[Sⱼ] Mⱼ,      s ⊗ m ↦ s • E.map i j h m.
```

The `Sᵢ`-algebra structure on `Sⱼ` is induced by `D.algMap i j h`.
The construction restricts the action on `Mⱼ` along this same homomorphism,
turns the semilinear transition into an `Sᵢ`-linear map, and applies
`LinearMap.liftBaseChange`. `moduleBaseChangeMap_tmul` proves the displayed
formula. The source writes `Mᵢ ⊗[Sᵢ] Sⱼ`; the implementation uses scalar-first
order. Mathlib's `TensorProduct.comm` exchanges the two factors; the associated
source-order map sends `m ⊗ s` to `s • E.map i j h m`. Thus bijectivity is the
same condition in either order. The stored map itself is `Sⱼ`-linear, so a
bijectivity witness also supplies a linear equivalence via
`LinearEquiv.ofBijective`.

## Approximation predicates

`LocalModuleSystem.IsApproximation E : Prop` has exactly the six source clauses:

1. `E.IsColimit`, including both ring comparison maps and the additive module comparison map;
2. every `D.base i` is `Algebra.EssFiniteType ℤ`;
3. every `D.alg i` is `Algebra.EssFiniteType (D.base i)`;
4. every `E.obj i` is `Module.Finite (D.alg i)`;
5. every `D.ringBaseChangeMap h` satisfies `D.IsPrimeLocalization h`;
6. every `E.moduleBaseChangeMap h` is bijective.

`LocalAlgebraSystem.IsApproximation D : Prop` is the four-clause ring-only
version from 00QV: ring colimits, the two essential-finite-type conditions,
and the canonical prime-localization condition. Neither predicate asserts
existence of witnesses. There is no flatness, injectivity-lifting, eventual
flatness, or fibrewise criterion conclusion among the data or clauses.

## Universe choices and later operations

The independent parameters are `uI` for `ι`, `uA` for all `Rᵢ`, `uB` for all
`Sᵢ`, `uN` for all `Mᵢ`, and `uR,uS,uM` for the three target carriers.
The structure universe is larger because it stores these types; this does not
identify or constrain the target universes. The ring direct limits live in
`Type (max uI uA)` and `Type (max uI uB)` and the additive direct limit in
`Type (max uI uN)`. Their homomorphisms can have targets in different universes.

An existence theorem must choose index and component universes large enough
for its construction. For example, it may use a common maximum of the ambient
input universes for those four parameters, while keeping `R,S,M` in their
original independent universes. The API therefore permits arbitrary parent
input universes; it makes no assertion that one fixed small index universe
works for all inputs. Any use of `ULift` in a later construction must prove the
required transport compatibility. No such transport or existence result is
assumed here.

The index is an external parameter and all component types, actions, maps,
prime-localization witnesses, and equations are exposed. This permits later
restriction to directed tails, synchronization of systems for a ring tower,
and residue-fibre constructions. Those operations and their colimit and
approximation-preservation proofs are outside this definition unit.
