# Restriction of an irreducible representation to a normal subgroup of finite index

This internal module proves Clifford's theorem in the form of Bernstein–Zelevinsky
1976, Lemma 2.9(b). Let `ρ` be an irreducible representation of a group `G` on a
vector space `V` over a field `k`, and let `N` be a normal subgroup of finite index.
Then the restriction `ρ.comp N.subtype` is semisimple and is the sum of finitely
many irreducible subrepresentations. A second form allows a subgroup `H` that has
finite index only after the centre is adjoined, provided the centre acts by scalars.
All declarations are in namespace `Langlands.FiniteIndexRestriction`.

No topology, smoothness or finiteness of `V` is assumed. The group `G`, the field
`k` and the carrier `V` live in independent universes.

## Generic facts

- `exists_ne_zero ρ hirr`: an irreducible representation has a nonzero vector.
  Otherwise `⊥ = ⊤` in its subrepresentation lattice.
- `span_orbit_eq_top ρ hirr hv`: the `k`-span of the orbit `{ρ g v}` of a nonzero
  vector `v` is all of `V`. The span is a nonzero subrepresentation.
- `isIrreducible_toRepresentation_of_isAtom S hS`: an atom `S` of the lattice of
  subrepresentations is irreducible as a representation on its own carrier. The
  proof passes through Mathlib's order isomorphism
  `Subrepresentation.subrepresentationSubmoduleOrderIso` with submodules of
  `ρ.asModule`. The carrier of `S` is linearly isomorphic to the corresponding
  atom, which is a simple `k[G]`-module.

## Normal subgroups of finite index

Section `Normal` fixes a normal subgroup `N`.

- `exists_mem_mul_out N g`: every `g` is `n * r.out` with `n ∈ N`, where `r.out`
  is the chosen representative of the coset `r` of `g` in `G ⧸ N`.
- `translate ρ N g S` is the definition selected for this unit. For a
  subrepresentation `S` of the restriction, it is the subspace `{x | ρ g x ∈ S}`,
  that is, the translate `ρ(g)⁻¹ S`. It is again invariant under `N` because `N` is
  normal. `mem_translate` unfolds membership.
- `translateOrderIso ρ N g` packages translation by `g` as an order automorphism of
  the subrepresentation lattice of the restriction, with inverse translation by
  `g⁻¹`.

From here on `N` also has finite index (`[N.FiniteIndex]`); `eq_zero_of_forall_out_mem`
does not use finite index.

- `finite_asModule ρ N hirr`: the restriction is a finitely generated `k[N]`-module.
  Its generators are the vectors `ρ r.out v` for a fixed nonzero `v`, one for each
  of the finitely many cosets `r`. Every `ρ g v = ρ n (ρ r.out v)` lies in their
  `k[N]`-span, and the orbit of `v` spans `V`.
- `exists_isCoatom ρ N hirr`: the restriction has a maximal proper
  subrepresentation `M`. The submodule lattice of a finitely generated module is
  coatomic, and `⊥ ≠ ⊤` because `V ≠ 0`.
- `eq_zero_of_forall_out_mem ρ N hirr M hM hx`: let `M` be a maximal proper
  subrepresentation of the restriction. A vector `x` with `ρ r.out x ∈ M` for every
  coset `r` is zero. The vectors whose whole `G`-orbit lies in `M` form a
  `G`-subrepresentation `I`. It is not `⊤`, since then `V ≤ M`. So it is `⊥` by
  irreducibility. The hypothesis on `x` gives `x ∈ I`, because
  `ρ g x = ρ n (ρ r.out x)` and `M` is `N`-invariant.
- `isSemisimpleModule_asModule ρ N hirr`: the restriction is a semisimple
  `k[N]`-module. The translates `M_r = translate ρ N r.out M` are maximal proper,
  so each quotient by `M_r` is simple. The map
  `x ↦ (x mod M_r)_r` into the finite product of these quotients is injective by
  the previous lemma. A submodule of a semisimple module is semisimple
  (`IsSemisimpleModule.of_injective`).
- `isSemisimpleRepresentation_comp ρ N hirr`: the same as
  `Representation.IsSemisimpleRepresentation (ρ.comp N.subtype)`, through Mathlib's
  `isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`.
- `exists_finite_atoms ρ N hirr`: there are `m : ℕ` and
  `W : Fin m → Subrepresentation (ρ.comp N.subtype)` with every `W i` an atom and
  `⨆ i, (W i).toSubmodule = ⊤`. In a semisimple module the simple submodules have
  supremum `⊤` (`IsSemisimpleModule.sSup_simples_eq_top`). Since the module is
  finitely generated, `⊤` is a compact element (`Submodule.fg_iff_compact`). So
  finitely many simple submodules already have supremum `⊤`. The published
  `Langlands.Subrepresentation.toSubmodule_iSup` turns the supremum of
  subrepresentations into the supremum of their submodules.

## Adjoining a centre that acts by scalars

Section `Center` fixes a subgroup `H` and a hypothesis
`hscalar : ∀ z : Subgroup.center G, ∃ c : k, ∀ v, ρ z v = c • v`.

- `supCenterOrderIso ρ H hscalar` is an order isomorphism between the
  subrepresentation lattices of `ρ.comp (H ⊔ Subgroup.center G).subtype` and of
  `ρ.comp H.subtype`. Both sides consist of the same subspaces. A subspace
  invariant under `H` is invariant under `H ⊔ center G`, because every element of
  the join is `h * z` (`Subgroup.mem_sup_of_normal_right`, the centre is normal)
  and `z` acts by a scalar.
- `finite_irreducible_restriction ρ H hirr hscalar` is the main theorem. It assumes
  `[H.Normal]` and `[(H ⊔ Subgroup.center G).FiniteIndex]`. Then
  `Representation.IsSemisimpleRepresentation (ρ.comp H.subtype)` holds. Moreover
  there are `m : ℕ` and `W : Fin m → Subrepresentation (ρ.comp H.subtype)` with
  every `(W i).toRepresentation` irreducible and `⨆ i, (W i).toSubmodule = ⊤`. The
  join `H ⊔ center G` is normal because `H` and the centre are. Semisimplicity, a
  property of the lattice (`ComplementedLattice`), and the atoms transfer through
  `supCenterOrderIso`.

The conclusion is the reduced spanning form: finitely many irreducible
subrepresentations whose sum is everything. It is not stated as an internal direct
sum. With semisimplicity a direct subfamily can be extracted, but that is not
formalized here.

## Provenance

The proofs follow Bernstein–Zelevinsky 1976 (`bernstein-zelevinsky-1976-representations-gln`),
Lemma 2.9(b), p. 17. There the restriction is generated by translates of a nonzero
vector, a maximal proper submodule `E'` is chosen (their 2.6), and
`E → ⊕ E/π(g_i)E'` is shown to be an embedding. Their bound `k ≤ |G/H|` on the
number of summands is not formalized. The passage from `H ⊔ Z` to `H` when the
centre acts by scalars is the last step of their Lemma 3.26, p. 36. The
`supCenterOrderIso` packaging and the use of compactness of `⊤` for the finite
family are internal to this formalization. The module supplies the generic step of
the determinant-unit specialization in
`Langlands.Representation.CuspidalSupport.DeterminantUnitFiniteRestriction`.
