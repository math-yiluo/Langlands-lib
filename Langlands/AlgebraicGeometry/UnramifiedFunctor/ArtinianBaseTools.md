# Step 1 of Murre's induction: basic tools over an affine base

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseTools`. It is the first of the
supporting modules of the proof `Langlands.AlgebraicGeometry.UnramifiedFunctor.murreArtinianBase`
(module `MurreArtinianBase`) of `MurreArtinianBaseStatement`.

All declarations are in the namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase`. Throughout, `R : CommRingCat.{u}`
and `F : (Over (Spec R))ᵒᵖ ⥤ Type v`. For an `R`-algebra `T`, `ovR R T` is the object
`Spec T ⟶ Spec R`, and `homR φ` is the morphism `Spec T' ⟶ Spec T` of an `R`-algebra map
`φ : T → T'`. Both come from the Library module `MurreChartsAffine`. The conditions (F1a)
`ZariskiSheaf`, (F1b) `FaithfullyFlatSheaf`, (F4′) `ArtinianLifting` and strong (F5)
`NilpotentInjective` are the Library definitions of module `MurreCriterionStatement`. No
statement of this module is a hypothesis of the target. They are internal lemmas, derived
for the proof below.

## Restriction

* `res φ x := F.map (homR φ).op x`: restriction of `x ∈ F(Spec T)` along `φ : T →ₐ[R] T'`.
* `res_res`: functoriality, `res ψ (res φ x) = res (ψ ∘ φ) x`.
* `homR_id`, `res_id`: identity.
* `map_iso_injective`: `F` of an isomorphism is injective.
* `algebraOverBase_eq`, `algHomOver_eq`, `map_algHomOver_tower`: these compare the Library's
  `algebraOver`/`algHomOver` objects over `ovR R M` with `ovR R B` for an `M`-algebra `B`.
  They are used to read (F4′) in terms of `res`.

## Separation

* `nilInj`: strong (F5) for a local artinian `R`-algebra `A` and a nilpotent ideal `I`:
  restriction along `A → A/I` is injective.
* `fieldInj`: with (F1b), restriction along a map of fields `K → L` is injective. This is the
  Library lemma `Charts.map_injective_of_field`.
* `FieldAgree w₁ w₂`: `w₁` and `w₂` have the same restriction along every `R`-algebra map to a
  field. `FieldAgree.restrict`: stability under restriction.
* `eq_of_residue_local` and `eq_of_fieldAgree_local`: for `T` local artinian, agreement at the
  residue field gives equality (strong (F5) for the maximal ideal, which is nilpotent).
* `exists_sep`, `isLocalRing_away`: in an artinian ring, each maximal ideal `𝔫` has an element
  `s ∉ 𝔫` lying in all other maximal ideals, and `T[1/s]` is local.
* `eq_of_fieldAgree`: (F1a) together with strong (F5). If `T` is artinian, elements of
  `F(Spec T)` that agree at all points with values in fields are equal. The basic opens
  `D(s_𝔫)` cover `Spec T`, and on each the ring is local artinian.

## Descent and products

* `flatDescent`: (F1b) for a faithfully flat `C → P`. If `w ∈ F(Spec P)` has equal pullbacks
  along the two maps `P → P ⊗_C P`, then `w` comes from `F(Spec C)`. The proof applies
  `FaithfullyFlatSheaf` to `Spec P ⟶ Spec C`, with the pullback identified with
  `Spec (P ⊗_C P)`.
* `subsingleton_of_isEmpty`: (F1a) on the empty cover. Over an empty scheme, `F` has at most one
  element.
* `specIso`, `homMk_eq`, `comap_fst_ne_comap_snd`: auxiliary identifications.
* `exists_prod`: (F1a) for the cover of `Spec (A × B)` by `Spec A` and `Spec B`. Elements
  `a ∈ F(Spec A)` and `b ∈ F(Spec B)` glue to `w ∈ F(Spec (A × B))`.

## Elements over a field point

* `IsOver ι π η w`, for `ι : C → X`, `π : C → ℓ` and `η ∈ F(Spec ℓ)`, `w ∈ F(Spec X)`: for every
  field `K` and maps `ψ : X → K`, `ψ₀ : ℓ → K` with `ψ₀ ∘ π = ψ ∘ ι`, one has
  `res ψ w = res ψ₀ η`. This expresses "`w` lies over `η`" pointwise.
* `IsOver.restrict`: stability under restriction.
* `isOver_of_res`: an element restricting to `η` lies over it.
* `IsOver.res_eq`: an element lying over `η` along the identity restricts to `η`, with
  `ψ = π` and `ψ₀ = id`.
* `isNilpotent_of_mem_maximalIdeal`, `map_maximalIdeal_eq_zero`: in a local artinian ring the
  maximal ideal is nil, so maps to fields kill it.

## (F4′) in terms of `IsOver`

`artLift` restates (F4′). Let:

* `π : C → ℓ` be a surjection from a local ring onto a field, and `η ∈ F(Spec ℓ)`;
* `N` be a local artinian ring, with `j : C → N` inducing a surjection onto the residue field
  of `N`;
* `N ⊆ A'` be finite with `length_N(A'/N) = 1`.

Then an element of `F(Spec A')` over `η` gives an element of `F(Spec N)` over `η`.

The proof works through the residue field `k_N` of `N`.

* `π` and `j` induce a map `θ : ℓ → k_N`, and `ξ₀ := res θ η`.
* `ArtinianLifting` is applied to `ξ₀` and `w'`, after transport along the Library's tower
  isomorphisms.
* Its compatibility hypothesis is the equality of the restrictions of `w'` and `ξ₀` to
  `A' ⊗_N k_N`. That ring is artinian, so the equality follows from `eq_of_fieldAgree` and
  the hypothesis that `w'` lies over `η`.
* (F4′) returns `ξ ∈ F(Spec N)` whose restriction to `k_N` is `ξ₀`. Every map from `N` to a
  field factors through `k_N`, so `ξ` lies over `η`.
