# The absolute global Weil group as a projective limit along Weil maps

Worker 8 authored this definition unit for task
`6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`. All declarations lie in the namespace
`Langlands.ClassField.Global`. The module builds Artin and Tate's absolute Weil group
`U = W_F` of a number field `F`. It is the subgroup of coherent families in the product
of the relative Weil groups `W_{K/F}` of the finite Galois layers `K` of an extension
`Ω / F`. Coherence is measured along a *supplied* transitive system of Weil maps
`W_{L/F} → W_{K/F}` in the sense of `Langlands.ClassField.Global.RelativeWeilMap`. The
module also gives the projections `W_F → W_{K/F}`, their universal property, the map
`g : W_F → Gal(Ω/F)` and the subgroups `U_E = g⁻¹(G_E)`. It does not prove that a
transitive system exists, and it does not prove that the projections are surjective.
Both remain explicit obligations (see the last section).

## Setting

Fix a class family `c : FundamentalClass.ClassFamily.{u}`, a number field `F : Type u`,
a field `Ω : Type u` with `[Algebra F Ω]`, and `h : FundamentalClass.Restriction c`.
The finite Galois layers of `Ω / F` are Mathlib's `FiniteGaloisIntermediateField F Ω`,
ordered by inclusion. Everything lives in the single universe `u` of the published
relative Weil groups `RelativeWeilGroup c F K`. `W_{K/F}` is a relative Weil group in the
sense of the sources only when `c F K` is the arithmetic fundamental class. All
constructions below work for every class family.

## Declarations

### Finite Galois layers (`FiniteGaloisLayer`)

- `FiniteGaloisLayer.numberField` (instance): a finite Galois layer `K` of `Ω / F` is a
  number field, by `NumberField.of_module_finite`.
- `FiniteGaloisLayer.galoisTopology K` is the discrete topology on `Gal(K/F)`. It is the
  published `relativeGaloisTopology F K`, which the relative Weil groups use. The module
  installs it as a local instance for layers only, so that `Ω ≃ₐ[F] Ω` keeps Mathlib's
  Krull topology. Downstream files may use `relativeGaloisTopology` instead. The two
  instances are definitionally equal.
- `FiniteGaloisLayer.algebra hKL`, for `K ≤ L`, is the algebra structure `K → L` given by
  the inclusion. `FiniteGaloisLayer.isScalarTower hKL` gives `IsScalarTower F K L`. These
  are the structures under which `RelativeWeilGroup.IsWeilMap c F K L h` is stated for
  layers.

### Transitive systems of Weil maps

`WeilMapSystem c F Ω h` is the structure with fields

1. `map hKL : W_{L/F} →ₜ* W_{K/F}` for all layers `K ≤ L`;
2. `isWeilMap hKL`: `map hKL` is a Weil map, `RelativeWeilGroup.IsWeilMap c F K L h`;
3. `map_map hKL hLM t`: `map hKL (map hLM t) = map (hKL.trans hLM) t` (transitivity).

For a system `S`:

- `S.surjective_map hKL`: each `map hKL` is surjective (field 1 of `IsWeilMap`).
- `S.map_self K t`: `S.map le_rfl t = t`. This follows from surjectivity and
  transitivity; it is not an extra axiom.
- `S.projection_map hKL t`: the image of `map hKL t` in `Gal(K/F)` is the restriction to
  `K` of the image of `t` in `Gal(L/F)`.

### The projective limit

- `S.weilSubgroup` is the subgroup of the product `∀ K, W_{K/F}` consisting of the
  families `x` with `S.map hKL (x L) = x K` for all `K ≤ L`
  (`mem_weilSubgroup_iff`).
- `S.WeilGroup` is that subgroup as a type. The instances `instTopologicalSpace` and
  `isTopologicalGroup` give it the topology induced from the product topology, and say
  that it is a topological group. They are declared explicitly so that downstream files
  find them without any local Galois-topology instance.
- `S.toLevel K : S.WeilGroup →ₜ* W_{K/F}` is evaluation at `K` (`toLevel_apply`). It
  satisfies `S.map hKL (S.toLevel L x) = S.toLevel K x` (`map_toLevel`), and elements are
  determined by their projections (`ext`).
- `S.lift f hf`: a family of continuous homomorphisms `f K : G →ₜ* W_{K/F}` from a
  topological group `G`, with `S.map hKL (f L g) = f K g`, factors through a continuous
  homomorphism `G →ₜ* S.WeilGroup` (`toLevel_lift`). It is the unique such homomorphism
  (`lift_unique`).

### The Galois map

- `S.toGaloisLimit` sends `x` to the family of images of `S.toLevel K x` in `Gal(K/F)`, as
  an element of Mathlib's `ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor
  F Ω)`. Its compatibility uses `S.projection_map`. It is continuous
  (`continuous_toGaloisLimit`).
- With `[IsGalois F Ω]`, `S.toGalois : S.WeilGroup →ₜ* (Ω ≃ₐ[F] Ω)` composes this with
  the inverse of Mathlib's continuous isomorphism `InfiniteGalois.continuousMulEquivToLimit
  F Ω`. Here `Ω ≃ₐ[F] Ω` has the Krull topology. `restrictNormalHom_toGalois` gives the
  characterization `g(u)|_K = g_K(u_K)`: the restriction of `S.toGalois x` to `K` is the
  image of `S.toLevel K x` in `Gal(K/F)`.

### The subgroups `U_E`

Assume `[IsGalois F Ω]`.

- `S.fieldSubgroup E`, for an intermediate field `E` of `Ω / F`, is the inverse image
  under `S.toGalois` of `E.fixingSubgroup`, the subgroup of `Gal(Ω/F)` fixing `E`
  (`mem_fieldSubgroup_iff`). The field `E` need not be normal over `F`.
- If `E / F` is finite-dimensional, `S.fieldSubgroup E` is open (`isOpen_fieldSubgroup`,
  from Mathlib's `IntermediateField.fixingSubgroup_isOpen`) and closed
  (`isClosed_fieldSubgroup`).
- `mem_fieldSubgroup_iff_projection_toLevel`: if `E ≤ K` for a finite Galois layer `K`,
  then `x ∈ U_E` exactly when the image of `S.toLevel K x` in `Gal(K/F)` fixes every
  element of `E`. The proof uses `restrictNormalHom_toGalois` and Mathlib's
  `AlgEquiv.restrictNormal_commutes`.
- For a finite Galois layer `K`, `U_K` is the kernel of
  `W_F → W_{K/F} → Gal(K/F)` (`mem_fieldSubgroup_layer_iff`,
  `fieldSubgroup_layer_eq_ker`), so it is normal (`fieldSubgroup_layer_normal`). The proof
  uses Mathlib's `IntermediateField.restrictNormalHom_ker`.

## Source correspondence

E. Artin and J. Tate, *Class Field Theory*, AMS Chelsea 2009, literature ID
`artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`. The PDF page is
the printed page plus nine. The following passages of Chapter XV were read from the
original.

- Printed p.177 (PDF p.186): Weil maps `ϕ_{L/K} : U^L → U^K` between the Weil groups of
  the finite normal layers.
- Printed pp.178–179 (PDF pp.187–188): a *transitive collection* of Weil maps, i.e.
  `ϕ_{M/K} = ϕ_{L/K} ϕ_{M/L}` for every triple `M ⊃ L ⊃ K`. The lemma there proves
  that one exists when every `A_K / A_k` is compact.
- Theorem 7 and its proof, printed pp.179–181 (PDF pp.188–190). One chooses a transitive
  collection. `U` is the subgroup of `∏_K U^K` of the elements `u = (u_K)` with
  `u_K = ϕ_{L/K} u_L` for all `L ⊃ K`, with the topology induced by the product
  topology. `ϕ_L(u) = u_L`. `g : U → G` is characterized by `ψ_K g = g_K ϕ_K`, using the
  completeness of `G`. Finally `U_E = g⁻¹(G_E)` for every field `E`, not necessarily
  normal.
- Lemma on printed p.181 (PDF p.190), first statement: `U_E = ϕ_K⁻¹(U^K_E)` for
  `K ⊃ E ⊃ k` with `K/k` normal. `mem_fieldSubgroup_iff_projection_toLevel` is this
  statement, with `U^K_E` written as the inverse image of the subgroup of `Gal(K/F)`
  fixing `E`.

J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979),
literature ID `tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`, §1.1–1.2, printed
pp.3–5 (PDF pp.12–14), was also read. Definition 1.1 gives `W_F` with
`φ : W_F → G_F` and the subgroups `W_E = φ⁻¹(G_E)`. Its axiom (W4) says that
`W_F → proj lim W_{E/F}` is an isomorphism of topological groups. §1.2 says that a Weil
group can be constructed as the projective limit of the group extensions `W_{E/F}`, and
that this construction is carried out in Artin–Tate.

### Derived formulation

1. **Supplied system.** Artin–Tate first *choose* a transitive collection. Here the
   collection is the explicit datum `S : WeilMapSystem c F Ω h`, and every construction
   depends on it. The source's uniqueness up to isomorphism is not formalized.
2. **Index set.** The layers are the finite Galois subextensions `K` of a fixed `Ω / F`,
   the normal layers of Artin–Tate's class formation for `G = Gal(Ω/F)`. The limit
   itself needs no hypothesis on `Ω`. The map `g` and the subgroups `U_E` need
   `IsGalois F Ω`. For Tate's `W_F`, take `Ω` to be an algebraic closure of `F`.
3. **The Galois map.** Artin–Tate obtain `g` from the completeness of `G`. In Lean this is
   Mathlib's isomorphism of `Gal(Ω/F)` with the limit of its finite quotients,
   `InfiniteGalois.continuousMulEquivToLimit`.
4. **Galois-group topology.** The relative Weil groups carry the published discrete
   topology on `Gal(K/F)`. This agrees with the source, since these groups are finite.

## Scope and remaining obligations

These results are neither proved nor assumed here:

- existence of a `WeilMapSystem` for the arithmetic fundamental-class family (the lemma
  on printed pp.178–179 together with the existence of Weil maps, see
  `RelativeWeilMap.md`);
- surjectivity of `S.toLevel K`, which Artin–Tate derive from the compactness of the
  kernels of Weil maps (printed pp.179–180);
- density of the image of `g`, the second statement of the lemma on printed p.181
  (`U_E^c = ϕ_K⁻¹((U^K_E)^c)`), the isomorphisms `f_E : A_E ≅ U_E/U_E^c`, and the Weil
  group axioms W1–W4 for `(U, g, {f_E})`;
- uniqueness of `W_F` up to isomorphism.

They are theorem obligations about these objects. Local–global maps `W_{F_v} → W_F`
and representations of `W_F` are built in separate modules.
