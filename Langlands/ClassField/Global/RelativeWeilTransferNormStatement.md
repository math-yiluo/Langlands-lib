# Transfer and the intermediate-field inclusion of relative Weil groups

Author: Worker 84. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1 (H2, Galois-side global inputs).
Worker 1795 (task `cc3ec74b`, Galois-side functional equation) asked for it. It is
missing from the Library and from every task found.

The module has two proposition definitions and nothing else. Nothing is proved
and nothing is assumed.

The target is
`Langlands.ClassField.Global.RelativeWeilGroup.TransferNormCompatibilityStatement`.
Let `F ⊆ K ⊆ E` be number fields with `E / F` Galois. The target says that the
transfer `W_{E/F} → C_F`, restricted along the inclusion `W_{E/K} → W_{E/F}`, is the
transfer `W_{E/K} → C_K` followed by the idele-class norm `N_{K/F} : C_K → C_F`:

`transfer_F (incl t) = N_{K/F} (transfer_K t)` for every `t ∈ W_{E/K}`.

## Declarations

Notation. `c : FundamentalClass.ClassFamily.{u}` is a class family. `W_{E/F}` is
the published `RelativeWeilGroup c F E`, an extension of `Gal(E/F)` by `C_E`.
`C_F = NumberField.IdeleClassGroup (𝓞 F) F`.

- `transfer c F E : W_{E/F} →* C_F` is the published transfer. It is the group
  transfer to the normal subgroup of finite index `C_E` (published
  `ideleTransfer`). Its values lie in the image of `C_F`, and it is read in `C_F`
  (published `ideleClassInclusion_transfer`). On `C_E` it is the idele-class norm
  (published `transfer_inclusion`).
- `restrictionInclusion c F E K h : W_{E/K} → W_{E/F}` is the published
  intermediate-field inclusion. It needs `h : FundamentalClass.Restriction c`. It is
  injective, it is compatible with the inclusions of `C_E` and with the projections
  to the Galois groups, and its image is the inverse image of `Gal(E/K)` (published
  `restrictionInclusion_injective`, `restrictionInclusion_inclusion`,
  `range_restrictionInclusion`).
- `ideleClassNorm (K := F) (L := K) : C_K →ₜ* C_F` is the published idele-class
  norm.
- `TransferNormCompatibility c F K E h` (proposition definition), for number fields
  with `[Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
  [IsGalois F E]` and `h : FundamentalClass.Restriction c`. It asserts
  `transfer c F E (restrictionInclusion c F E K h t) =
    ideleClassNorm (K := F) (L := K) (transfer c K E t)` for every
  `t : RelativeWeilGroup c K E`. The instance `IsGalois K E` is
  `IsGalois.tower_top_of_isGalois F K E`, as in `restrictionInclusion`.
- `TransferNormCompatibilityStatement` (the target, universe parameter `u`)
  quantifies `TransferNormCompatibility c F K E h` over every class family `c`,
  all such number fields `F K E : Type u` and every `h`.

The module uses the published discrete topology `relativeGaloisTopology` on
`Gal(E/F)` as a local instance, because `restrictionInclusion` is a continuous
homomorphism for it. The statement is about group homomorphisms only, so the
topology does not affect its meaning.

## Relation to the source

Tate (1979), (1.2.2), p.4, states for Weil groups and `F ⊆ E' ⊆ E` that the
reciprocity isomorphisms `r_E : C_E → W_E^{ab}` and `r_{E'}` turn the norm
`C_E → C_{E'}` into the map `W_E^{ab} → W_{E'}^{ab}` induced by inclusion. Tate
derives it from the group fact that, for a normal subgroup `H` of finite index in
`G`, the composite `H^{ab} → G^{ab} → H^{ab}` (inclusion, then transfer) is the
product of the conjugates by representatives of `G/H`. The target is the same
compatibility for relative Weil groups and the published transfer in place of
`r^{-1}`, with `F ⊆ K ⊆ E`. The provenance is derived.

1. *Any class family.* No arithmetic hypothesis is needed. The identity is a
   statement about the group extension `W_{E/F}` and holds for every class family
   with `Restriction c` (see below). `Restriction c` is needed only to define the
   inclusion.
2. *`K / F` need not be Galois.* Tate's remark treats a normal subgroup. Here
   `W_{E/K}` is normal in `W_{E/F}` only when `K / F` is Galois. The proof sketch
   below covers the general case.
3. *Intended use.* Worker 1795 needs it in the Galois-side functional equation
   (task `cc3ec74b`). Restricted to `W_{E/K}`, the character
   `reciprocityCharacter c F E χ = (χ ∘ transfer_F)⁻¹` must equal
   `reciprocityCharacter c K E (χ ∘ N_{K/F})`. Then each Brauer term is a Hecke
   character of `K`. On `C_E` both sides already agree by transitivity of norms,
   but without the target they could differ by a character of `Gal(E/K)`.

## Why the target is true

This is a sketch of the expected proof. Nothing here is proved in the module.

Write `G = W_{E/F}`, `H` for the image of `W_{E/K}` and `A` for the image of `C_E`.
`A` is abelian and normal of finite index in `G`, and `A ⊆ H`.

1. *Transfer to `A` restricted to `H`.* Use the orbit formula for the transfer
   with left cosets: `Ver_{G→A}(g) = ∏_i x_i⁻¹ g^{n_i} x_i`. The product runs over
   representatives `x_i A` of the orbits of `⟨g⟩` acting on `G/A` by left
   multiplication, and `n_i` is the orbit length. Let `h ∈ H`, and write
   `G = ⊔_k H z_k`. Since `A` is normal, `H z_k = ⊔_j y_j z_k A` with
   `H = ⊔_j y_j A`. Left multiplication by `h` preserves each `H z_k`, and
   `y A ↦ y z_k A` identifies the action on `H/A` with the action on `H z_k / A`.
   Hence `Ver_{G→A}(h) = ∏_k z_k⁻¹ Ver_{H→A}(h) z_k`. The `z_k⁻¹` run over
   representatives of `G/H`.
2. *Conjugation is the Galois action.* Conjugation by `s ∈ G` on `A = C_E` is the
   action of the image of `s` in `Gal(E/F)`. So `ideleTransfer c F E (incl t)` is
   the product of the `σ`-conjugates of `ideleTransfer c K E t`, with `σ` running
   over `Gal(E/F)/Gal(E/K)`. This uses the compatibility of `restrictionInclusion`
   with the inclusion of `C_E` and with the projections.
3. *Norm.* `ideleTransfer c K E t` is the image of `transfer c K E t ∈ C_K` in
   `C_E`. For `x ∈ C_K`, the product of the conjugates `σ(x)` over
   `σ ∈ Gal(E/F)/Gal(E/K)` (the `F`-embeddings of `K` into `E`) is the image of
   `N_{K/F} x` in `C_E`. The published `ideleClassNormGaloisProduct` is the case
   `K = E`. The inclusion `C_F → C_E` is injective (published idele-class Galois
   descent), so the two sides of the target agree in `C_F`.

## Sources

- Tate (1979), *Number theoretic background*, Corvallis Proc. Symp. Pure Math. 33,
  part 2: §1 opening, p.3 (transfer); (1.2.2) and the remark after it, p.4.
