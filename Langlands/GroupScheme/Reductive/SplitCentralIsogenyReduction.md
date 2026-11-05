# Reduction of the central Isogeny Theorem to the Isomorphism Theorem

Author: Worker 277.

This internal assembly proves one conditional result,
`Langlands.GroupScheme.splitCentralIsogenyExistence_of_commonTorusIsomorphism`.
It is a proof-producing `def` whose type is the implication below, with the
`linter.defProp` linter disabled for it, so that the module can be published
as a definition artifact before the hypotheses are proved; it is used exactly
like a theorem. It shows that the published `SplitCentralIsogenyExistenceStatement` (Milne,
Theorem 23.9, central case; see
[`SplitClassificationStatement`](SplitClassificationStatement.md)) follows from
four statements, taken as hypotheses:

- `RootDatumExistenceStatement` ([`RootDatumStatement`](RootDatumStatement.md)):
  every split maximal torus of a connected reductive group has a root datum;
- `CentralIsogenyRootDatumHomStatement`
  ([`CentralIsogeny.SplitRootDatumStatement`](../CentralIsogeny/SplitRootDatumStatement.md)):
  a central isogeny with a compatible torus map `t` defines a morphism of root
  data with weight map `χ ↦ t ≫ χ` and coweight map `ν ↦ ν ≫ t`;
- `SplitCentralTorusQuotientStatement`
  ([`CentralTorusQuotientStatement`](CentralTorusQuotientStatement.md)): the
  quotient of a split reductive group by the kernel of a torus isogeny whose
  character map hits every root;
- `SplitCommonTorusIsomorphismStatement`
  ([`SplitIsomorphismStatement`](SplitIsomorphismStatement.md)): the
  Isomorphism Theorem for two groups sharing a split maximal torus.

The module proves none of these four statements. The conclusion is the
unchanged target statement, with every binder and the full conclusion. The
argument is the standard derivation of the Isogeny Theorem from the
Isomorphism Theorem by passing through a central quotient (compare Milne,
Remark 23.26). The route is internal; it adds no claim from the literature.

## The proof

Let the data of the target be given: groups `G`, `G'`, split maximal tori
`i : T ⟶ G` and `i' : T' ⟶ G'`, root data `P` of `i` and `P'` of `i'`, and a
morphism of root pairings `f : P' ⟶ P` with injective weight map
`X(T') → X(T)` and injective coweight map `Y(T) → Y(T')`.

1. **The torus map.** `IsSplitTorus.exists_hom_of_characterMap`
   ([`Torus.CharacterMapHom`](../Torus/CharacterMapHom.md)) gives
   `t : T ⟶ T'` with `t ≫ χ = f.weightMap χ` for every character `χ` of `T'`.
   Both root data use the actual lattice pairing (first component of
   `IsRootDatumOf`), so `RootDatumHom.coweightMap_apply_of_weightMap`
   ([`RootDatumHomLattices`](RootDatumHomLattices.md)) gives
   `f.coweightMap ν = ν ≫ t` for every cocharacter `ν` of `T`.
2. **The central quotient.** The maps `χ ↦ t ≫ χ` and `ν ↦ ν ≫ t` are
   injective, because they are the weight and coweight maps of `f`. Every root
   `α` of `i` is `P.root j` for some index `j` (second component of
   `IsRootDatumOf`). By `root_weightMap` of `f`, it equals
   `f.weightMap (P'.root (f.indexEquiv.symm j)) = t ≫ P'.root (f.indexEquiv.symm j)`.
   So `SplitCentralTorusQuotientStatement` applies. It gives a connected
   reductive group `Q`, a central isogeny `q : G ⟶ Q` and a maximal torus
   `i'' : T' ⟶ Q` with `i ≫ q = t ≫ i''`.
3. **Root data of the quotient.** `RootDatumExistenceStatement` gives a root
   datum `P''` of `i''`, indexed by some `J''`. Then
   `CentralIsogenyRootDatumHomStatement`, applied to `q` and `t`, gives a
   morphism `f'' : P'' ⟶ P` with weight map `χ ↦ t ≫ χ` and coweight map
   `ν ↦ ν ≫ t`.
4. **Matching the root data on `T'`.** Let
   `e := f''.indexEquiv.trans f.indexEquiv.symm : J'' ≃ J'`. The weight maps of
   `f` and `f''` are both `χ ↦ t ≫ χ`. So `f.weightMap` sends both
   `P'.root (e j)` and `P''.root j` to `P.root (f''.indexEquiv j)`, by
   `root_weightMap` of `f` and of `f''`. Since `f.weightMap` is injective,
   `P'.root ∘ e = P''.root`. The coweight maps of `f` and `f''` are both
   `ν ↦ ν ≫ t`. So by `coroot_coweightMap` of `f` and of `f''`, both
   `P'.coroot (e j)` and `P''.coroot j` equal
   `P.coroot (f''.indexEquiv j) ≫ t`. Hence `P'.coroot ∘ e = P''.coroot`.
5. **The Isomorphism Theorem.** `SplitCommonTorusIsomorphismStatement`,
   applied to `i'' : T' ⟶ Q`, `i' : T' ⟶ G'`, `P''`, `P'` and `e`, gives an
   isomorphism `ψ : Q ≅ G'` with `i'' ≫ ψ.hom = i'`.
6. **Conclusion.** Put `φ := q ≫ ψ.hom`. Then
   `i ≫ φ = t ≫ i'' ≫ ψ.hom = t ≫ i'`, and `f.weightMap χ = t ≫ χ` by step 1.
   `IsCentralIsogeny.comp_iso`
   ([`CentralIsogeny.Transport`](../CentralIsogeny/Transport.md)) shows that
   `φ` is a central isogeny.

The definition has universe parameter `u` and uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.
