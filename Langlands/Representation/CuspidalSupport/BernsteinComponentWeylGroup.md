# The finite group `W` acting on the unramified twists of a cuspidal datum

Module `Langlands.Representation.CuspidalSupport.BernsteinComponentWeylGroup`,
namespace `Langlands.CuspidalSupport.ComponentWeyl`.

## Provenance

This is an internal construction for the proof of Renard VI.7.1 (Theorem; Renard 2026, French
version dated 9 July 2026, printed pp.180–181, PDF pp.186–187).

Renard's group `W` is built from the normalizer of the Levi `M` and the stabilizer of the
inertial class of `ρ`. It acts on `X(M)` by `ω ↦ χ·(ω ∘ c)`, where `c` runs over conjugations
normalizing `M` and `χ` over characters with `ρ ⊗ χ ≅ ρ^c`. The construction below defines this
group directly as a group of permutations of `X(M)` and proves the properties the Theorem
needs. Renard derives its finiteness from finiteness of `N_G(M)/M` and of the unramified
stabilizer of `ρ` (Renard V.2.7). Here both finiteness facts enter as hypotheses, and the
final proof discharges them from Library results.

## Setting

- `F` is a non-archimedean local field.
- `H` and `G` are group schemes over `F`, with `H` affine and locally of finite type.
- `j : H ⟶ G` is a group-scheme homomorphism, and `ρ` is a smooth complex representation of
  `H(F)`.
- `UChar H` abbreviates the unramified characters
  `unramifiedCharacters (fun χ => (rationalNormCharacters H χ).toMul)` of `H(F)`.
- `H(F)` carries the canonical topology `rationalPointTopology F H.X`, installed as a local
  instance.

A *self-conjugacy* of `j` is a `RationalLeviConjugacy j j`. It consists of a point `c.point`
of `G(F)` and an isomorphism `c.iso : H ≅ H` with `j ≫ inner(c.point) = c.iso.hom ≫ j`.

## Declarations

### Twists and pullbacks (section `Isos`)

These are `Nonempty`-isomorphism versions of the Library's twist API.

- `twist_congr`, `twist_twist` (`(A ⊗ ψ) ⊗ χ ≅ A ⊗ χψ`), `twist_one`, `twist_eq`.
- `twist_inv_twist`: `(A ⊗ χ) ⊗ χ⁻¹ ≅ A`.
- `twist_iso_iff`: `A ⊗ χ ≅ B` iff `A ≅ B ⊗ χ⁻¹`.
- `pullback_congr`.
- `pullback_twist`: `(A ⊗ χ)^e ≅ A^e ⊗ (χ ∘ e)`.
- `twist_iso_twist_iff`: `A ⊗ χ ≅ B ⊗ ψ` iff `A ⊗ χψ⁻¹ ≅ B`.

### Affine permutations (section `Affine`)

- `restrict_inv_hom`, `restrict_hom_inv`: restriction of characters along `e.hom` and
  `e.inv` are mutually inverse.
- `affinePerm e χ` is the permutation `ω ↦ χ * (ω ∘ e)` of `UChar H`, for `e : H ≅ H`. Its
  inverse is `ω ↦ (χ⁻¹ ω) ∘ e⁻¹`. `affinePerm_apply` is its defining equation.
- `comp_affine_mem_regular`: let `f : K ⟶ H`, `χ ∈ X(K)` and `g ∈ ℂ[X(K)]`. Then
  `ω ↦ g(χ * (ω ∘ f))` lies in `ℂ[X(H)]`. Here `ℂ[X(·)]` is `unramifiedRegularFunctions`.

### Inner automorphisms (section `Conjugation`)

- `restrict_innerIso`: an unramified character is invariant under the inner automorphism
  `H.innerIso m`.
- `pullback_iso_of_conj`: suppose `e, e' : H ≅ K` satisfy
  `e(x) = n e'(x) n⁻¹` on points, for some `n ∈ K(F)`. Then `A^{e'} ≅ A^e`.
- `iso_hom_eq_of_point_eq`: let `j` be a monomorphism, and let `c, c'` be self-conjugacies with
  `c.point = c'.point · j(m)`. Then `c.iso.hom = inner(m) ≫ c'.iso.hom`.

### The group (section `Weyl`)

- `twistSet ρ e` is the set `{χ | ρ ⊗ χ ≅ ρ^e}`.
- `iso_pullback_twist_iff`: `ρ ⊗ ω ≅ (ρ ⊗ ω')^e` iff `ω · (ω' ∘ e)⁻¹ ∈ twistSet ρ e`.
- `weylGroup j ρ : Subgroup (Equiv.Perm (UChar H))` has carrier
  `{affinePerm c.iso χ | c : RationalLeviConjugacy j j, χ ∈ twistSet ρ c.iso}`.
- `assoc_iff_exists_weylGroup`: `(∃ c, ρ ⊗ ω ≅ (ρ ⊗ ω')^c) ↔ ∃ w ∈ weylGroup j ρ, w ω' = ω`.
- `weylGroup_comp_mem_regular`: each `w ∈ weylGroup j ρ` preserves `ℂ[X(H)]` under
  composition.
- `twistSet_finite`: if the unramified stabilizer `{χ | ρ ⊗ χ ≅ ρ}` is finite, every twist set
  is finite.
- `twistSet_affinePerm_eq_of_point_eq`: for a monomorphism `j`, suppose
  `c.point = c'.point · j(m)`. Then `c` and `c'` have the same twist set and the same affine
  permutations.
- `weylGroup_finite` assumes three things:
  - `j.hom.hom` is a monomorphism;
  - there are finitely many points `g_t ∈ G(F)` such that every `w` normalizing `j` is
    `g_t · j(m)` for some `t` and some `m ∈ H(F)`;
  - the unramified stabilizer of `ρ` is finite.

  Under these hypotheses `weylGroup j ρ` is finite.

## Proofs

- **Subgroup.**
  - *Identity:* the refl conjugacy with `χ = 1`.
  - *Product:* for `(c, χ)` and `(d, ψ)`, take `c.trans d` with `χ · (ψ ∘ c)`. The twist
    condition follows by chaining `ρ ⊗ χ(ψ∘c) ≅ (ρ ⊗ χ) ⊗ (ψ∘c) ≅ ρ^c ⊗ (ψ∘c)`, then
    `≅ (ρ ⊗ ψ)^c ≅ (ρ^d)^c ≅ ρ^{c.trans d}`.
  - *Inverse:* for `(c, χ)`, take `c.symm` with `(χ ∘ c⁻¹)⁻¹`, using
    `rationalIsoPullbackCancelIso`.

  The permutation identities are `rationalUnramifiedCharacterRestrict_comp` and
  multiplicativity of restriction.
- **Orbits.** Use `iso_pullback_twist_iff`, with `χ = ω · (ω' ∘ c)⁻¹`. Then
  `affinePerm c.iso χ ω' = ω`.
- **Regular functions.** By `Algebra.adjoin_induction`. A generator `e_m : ω ↦ ω(m)` is sent to
  `ω ↦ χ(m) · ω(f(m))`, a scalar multiple of the generator `e_{f(m)}`.
- **Inner automorphisms.**
  - `restrict_innerIso` uses `rationalPoints_map_innerIso` and commutativity of `ℂˣ`.
  - `pullback_iso_of_conj` uses the intertwiner `A(n)`.
  - `iso_hom_eq_of_point_eq` cancels the monomorphism `j` in
    `c.iso.hom ≫ j = j ≫ inner(c'.point · j(m))`, rewriting with `innerIso_mul_hom` and
    `innerIso_hom_comp`.
- **Finiteness.**
  - Each element of `W` comes from some `c`, and `c.point = g_t · j(m)` for some `t`, so `W`
    is covered by finitely many sets `S_t`.
  - Fix `c₀` in `S_t`. Every other `c` in `S_t` has `c.point = c₀.point · j(m₀⁻¹ m)`, so by
    `twistSet_affinePerm_eq_of_point_eq` it has the same twist set and permutations as `c₀`.
    Hence `S_t` lies in the image of the finite set `twistSet ρ c₀.iso` under
    `affinePerm c₀.iso`.
  - That twist set is a translate of the finite stabilizer.
