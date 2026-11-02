# Affine open charts through field points of a commutative group space

Internal step in the proof of `SeparatedAddCommGroupSheafSchemeRepresentabilityStatement`.

Setting: `G` is a presheaf of commutative groups on schemes over `Spec k`, where `k` is a
field. Write `F := G ⋙ forget`. Assume `F` is an fppf sheaf with closed-immersion diagonal.
It has an etale map `a : Y(U) ⟶ F` from a scheme `U` locally of finite type over `k`.

This module uses the dense affine open proposition `SeparatedDenseAffineOpenLFTProp` (the
published dense affine open statement together with local finite type of the affine open;
proved in `SeparatedDenseAffineOpenReduction`) as a hypothesis `hS1`. It uses the affine
quotient statement (Stacks 03BM) through `GaloisAffineDescent`. All affine opens are tracked as
`IsLFTAffineOpen`, so the final chart is locally of finite type.

The mathematical idea follows Stacks Project, Groups in Spaces, Lemma 79.10.2 (Tag 0B8D).
The proof there passes through an algebraic closure and identity components. Here the route
is derived and stays over `k`:
- the extension is a finite normal extension;
- a translation trick replaces identity components;
- Galois descent of invariant affine opens (Stacks 03BM) replaces descent from `k̄`.

## Step 1: `exists_affine_containing_translates`

Data: an affine nonempty `U₀` locally of finite type over `k`, an etale chart
`a₀ : Y(U₀) ⟶ F × Spec L`, a section `gL ∈ G(Spec L)` and finitely many endomorphisms
`ψ τ` of `Spec L`.

1. The coproduct `V = ∐_τ U₀` carries one section `b ∈ (F × Spec L)(V)`. On the `τ`-th
   component, `b` is the translate of `a₀` by `c_τ := (ψ τ)^* gL`. The section is written
   down directly as `codiag^* x₀ + φ^* gL` with `φ = desc(α₀ ≫ ψ τ)`, so no sheaf gluing is
   needed.
2. `b` is etale by `CoproductChart.isEtale_of_forall_ι`.
3. The sheafified image `Q` of `b` is a separated algebraic space with the affine etale
   surjective atlas `V`. This uses Worker 1150's `OpenSubfunctorImages`.
4. `hS1` gives an affine open `A ⊆ Q`, represented by a scheme locally of finite type, whose
   preimage in `V` is dense.
5. The preimages in `U₀` of the `τ`-th components are dense opens. Their finite intersection
   contains a closed point `w` (`FieldSchemePoints`).
6. Take `L'` normal and finite over `k`, containing the finite residue field `κ(w)`. The
   resulting `L'`-point `ρ` of `U₀` has every translate `translate (c_τ) (a₀ ρ)` in `A`.

## Step 2: `exists_galois_stable_affine`

Data: `L` normal over `k`, an affine open `A ⊆ F × Spec L`, and `L'` finite normal with
`j : L ⟶ L'`. Assume `(q' + j^* c_τ, j) ∈ A` for every `τ ∈ Aut(L/k)`.

Define `W ⊆ F × Spec L'` as the intersection over `σ ∈ Aut(L'/k)` of the preimages of
`A.preimage (mapRight (specOverMap j))` under `(x, β) ↦ (x + (β ≫ σ)^* q', β ≫ σ)`. Then:
- `W` is an affine open represented by a scheme locally of finite type (`IsLFTAffineOpen`), by
  `IsLFTAffineOpen.preimage_mapRight` and `IsLFTAffineOpen.iInf_preimage_iso`, since the
  diagonal is closed;
- `W` is stable under the Galois action, by reindexing `σ`;
- `W` contains `(j^* gL, id)`. For each `σ`, apply the hypothesis with
  `τ := (σ⁻¹)|_L` (`exists_restrict`).

## Step 3: `exists_open_chart_of_field_point`

For a finite extension `K/k` and a `K`-point `t` of `U`:
1. Choose `L` finite normal containing `K`, and an affine open `U₁ ∋ t` of `U`.
2. Apply Step 1 to `U₀ = U₁ × Spec L`, with the translates indexed by `Aut(L/k)` acting
   on `gL = t^* a`.
3. Apply Step 2.
4. `fst_invariant_of_galois_stable` turns Galois stability into invariance. Then
   `isLFTAffineOpen_universalImage_fst` descends `W` to an affine open `W₀ ⊆ F`, again
   represented by a scheme locally of finite type.
5. `W₀` contains `t^* a`, by `mem_of_surjective` along the surjection
   `Spec L' ⟶ Spec K`.
6. The representing isomorphism of `W₀` gives the required open immersion `b` from an affine
   scheme `V` with `V ⟶ Spec k` locally of finite type.
