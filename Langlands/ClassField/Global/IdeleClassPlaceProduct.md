# Single-place idele classes under `C_K → C_L` and the Galois action

Let `L / K` be a finite extension of number fields and `p` a finite place of
`K`. For `a ∈ K_pˣ`, write `[a]_p` for the idele (or idele class) of `K` whose
coordinate at `p` is `a` and whose other coordinates are `1`. This is Mathlib's
`IdeleGroup.ofAdicCompletion` (respectively `IdeleClassGroup.ofAdicCompletion`).
For a finite place `q` of `L` above `p`, the published
`FiniteExtension.completionMap p q : K_p → L_q` is the completed embedding.
The module proves the standard fact

  `ι([a]_p) = ∏_{q | p} [a]_q`,

where `ι` is the inclusion of ideles (or idele classes) `K → L` and `a` is read
in `L_qˣ` through `completionMap p q`. It then rewrites the right-hand side as a
product of Galois conjugates of a single factor `[a]_w`.

All statements concern finite places only. They are internal bookkeeping for
the transfer argument relating local and global reciprocity (John Tate,
*Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979),
Proposition (1.6.1), p.8; see also item 4 of "Relation to the source" in the
Markdown of the published `LocalRelativeWeilTransferStatement`). There, for
`a ∈ F_zˣ`, the conjugates of the idele class `[a]_w` of `E` by a set of
representatives of `Gal(E/F) / D_w` multiply to the image of `[a]_z` under
`C_F → C_E`. The module proves only this idele-class identity. It makes no
claim about Weil groups or reciprocity maps.

## Places form

Namespace `Langlands.Global.AdelicFunctoriality`. The fields are
`K : Type u` and `L : Type v`, with `[Algebra K L]`. `FinitePlacesAbove L p` is
the published subtype of finite places of `L` over `p`, finite by its
published `Fintype` instance.

- `finiteAdeleInclusion_ofAdicCompletion p x`: for `x ∈ K_p`, the published
  `finiteAdeleInclusion` sends the finite adele with the single coordinate `x`
  at `p` (Mathlib's `FiniteAdeleRing.ofAdicCompletion`) to
  `∏ q : FinitePlacesAbove L p, FiniteAdeleRing.ofAdicCompletion L q (completionMap p q x)`.
- `ideleInclusion_ofAdicCompletion p a`: for `a ∈ K_pˣ`, the published
  `ideleInclusion` sends `IdeleGroup.ofAdicCompletion (𝓞 K) K p a` to
  `∏ q : FinitePlacesAbove L p, IdeleGroup.ofAdicCompletion (𝓞 L) L q (Units.map (completionMap p q) a)`.
- `prod_ofAdicCompletion_eq_ideleClassInclusion p a`: the corresponding
  identity of idele classes, written with the product on the left:
  `∏ q : FinitePlacesAbove L p, IdeleClassGroup.ofAdicCompletion (𝓞 L) L q (Units.map (completionMap p q) a)`
  equals the published `ideleClassInclusion` of
  `IdeleClassGroup.ofAdicCompletion (𝓞 K) K p a`.

## Galois conjugates of one factor

Namespace `Langlands.ClassField.Global`, section `Conjugates`. Here
`F : Type u`, `E : Type v`, `z` is a finite place of `F`, `w` a finite place of
`E` with `w` over `z`, and `a ∈ F_zˣ`. The published
`relativeIdeleClassAut F E σ` is the action of `σ ∈ Aut(E/F)` on `C_E`. The
published `finitePlaceEquiv σ` sends a place `q` of `E` to the place `σ⁻¹(q)`
whose ideal is the preimage of `q` under `σ`. So
`finitePlaceEquiv σ q = w` means `q = σ(w)`.

- `relativeIdeleClassAut_ofAdicCompletion_completionMap σ q h a`: if `q` lies
  over `z` and `h : finitePlaceEquiv σ q = w`, then `σ` sends `[a]_w` to
  `[a]_q` in `C_E`.
- `prod_relativeIdeleClassAut_ofAdicCompletion σ hσ a`: let `σ : ι → Aut(E/F)`
  be a family indexed by a finite type `ι`. The hypothesis `hσ` says that for
  every place `q` of `E` over `z` there is exactly one `i` with
  `finitePlaceEquiv (σ i) q = w`. Then
  `∏ i, relativeIdeleClassAut F E (σ i) [a]_w = ideleClassInclusion [a]_z`.

## Coset representatives of the decomposition group

Section `Cosets`. Here `F E : Type u`, `E / F` is Galois, and the published
`FundamentalClass.decompositionHom z w : Gal(E_w/F_z) →* Gal(E/F)` restricts
local automorphisms to `E`. Its range is the decomposition group `D_w`.

- `existsUnique_finitePlaceEquiv_eq_of_coset σ hσ q hq`: let
  `σ : ι → Gal(E/F)` be a family of left coset representatives of `D_w`. This
  means that every `τ` satisfies `(σ i)⁻¹ * τ ∈ D_w` for exactly one `i`. Then
  every place `q` over `z` satisfies `finitePlaceEquiv (σ i) q = w` for exactly
  one `i`. So the family meets the hypothesis of the previous theorem.
- `prod_relativeIdeleClassAut_ofAdicCompletion_of_coset σ hσ a`: for such
  representatives with finite index type,
  `∏ i, relativeIdeleClassAut F E (σ i) [a]_w = ideleClassInclusion [a]_z`.

## Proofs

- `finiteAdeleInclusion_ofAdicCompletion` compares coordinates at every place
  `q` of `L`. Mathlib's `FiniteAdeleRing` has its own coercion to functions.
  So the `q`-coordinate of the finite product is computed through the
  evaluation-at-`q` monoid homomorphism and `map_prod`. Both sides are then
  `Pi.mulSingle` values. By the published `finiteAdeleInclusion_apply`, the
  left side is `completionMap` applied to the coordinate of the single-place
  adele at `q ∩ 𝓞 K`. If `q` lies over `p`, then
  `q ∩ 𝓞 K = p` (the published `finitePlacesAbove_under`), and only the factor
  indexed by `q` contributes (`Finset.prod_eq_single`). Otherwise
  `q ∩ 𝓞 K ≠ p`, so the left side is `completionMap 1 = 1`, and every factor
  is `1` at `q`.
- `ideleInclusion_ofAdicCompletion` compares underlying adeles, using the
  published `ideleInclusion_val` and `Units.coe_prod`. The two components of
  the product of adeles are again computed through ad hoc projection monoid
  homomorphisms. The infinite component is the image of `1`, hence `1`. The
  finite component is the previous lemma.
- `prod_ofAdicCompletion_eq_ideleClassInclusion` unfolds both sides to images
  under the quotient map by principal ideles. It then applies `map_prod` and
  the idele identity.
- `relativeIdeleClassAut_ofAdicCompletion_completionMap` substitutes
  `w = finitePlaceEquiv σ q`. It then applies the published
  `ideleClassEquiv_ofAdicCompletion`, which moves a single-place idele class
  along `σ`, and the published
  `IdeleGaloisDescentProof.finiteCompletionEquiv_completionMap`, which says
  that the completed transport along `σ` fixes the image of `F_z`.
- `prod_relativeIdeleClassAut_ofAdicCompletion` first shows that each place
  `(finitePlaceEquiv (σ i)).symm w` lies over `z`, by the published
  `IdeleGaloisDescentProof.finitePlaceEquiv_under`. The map
  `i ↦ (finitePlaceEquiv (σ i)).symm w` into `FinitePlacesAbove E z` is
  bijective by `hσ`. The proof rewrites the right side with the places form
  and reindexes the product along this bijection (`Fintype.prod_bijective`).
  The factors then agree by the single-conjugate lemma.
- `existsUnique_finitePlaceEquiv_eq_of_coset` chooses `g` with
  `finitePlaceEquiv g q = w` (the published `exists_finitePlaceEquiv_eq`,
  transitivity on places over `z`). By the published
  `finitePlaceEquiv_trans`,
  `finitePlaceEquiv (x * y) w = finitePlaceEquiv y (finitePlaceEquiv x w)`.
  With the published `mem_range_decompositionHom_iff` (the range of
  `decompositionHom z w` is the stabilizer of `w`), this gives
  `finitePlaceEquiv (σ i) q = w ↔ (σ i)⁻¹ * g⁻¹ ∈ D_w`. The coset hypothesis
  at `τ = g⁻¹` then gives existence and uniqueness of `i`.
- `prod_relativeIdeleClassAut_ofAdicCompletion_of_coset` combines the two
  previous theorems.
