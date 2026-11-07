# Transfer of local relative Weil maps and local reciprocity

Author: Worker 84. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1. It supplies the abelian local
step of the Galois-side global functional equation (published target
`Langlands.Global.FunctionalEquationComparison.RelativeWeilTwistFunctionalEquationStatement`).
Along a local map `ι : W_{F_z} → W_{E/F}`, the twisting character
`reciprocityCharacter c F E χ` restricts to the `z`-component of `χ` composed with
local reciprocity.

The module has two proposition definitions and nothing else. Nothing is proved
and nothing is assumed.

The target is
`Langlands.ClassField.Global.RelativeWeilGroup.LocalTransferReciprocityStatement`.
Let `E/F` be a Galois extension of number fields, `z` a finite place of `F`, and
`ι : W_{F_z} → W_{E/F}` a local map at a place `w` of `E` above `z`. The target
says that the composite of `ι` with the transfer `W_{E/F} → C_F` is the inverse of
geometric local reciprocity of `F_z` followed by `F_zˣ → C_F`:

`transfer (ι g) = i_z(rec_z(g))⁻¹` for every `g ∈ W_{F_z}`.

## Declarations

Notation: `c : FundamentalClass.ClassFamily.{u}` is a class family, and
`RelativeWeilGroup c F E`, written `W_{E/F}`, is the published extension
`1 → C_E → W_{E/F} → Gal(E/F) → 1` of the class `c F E`. It is Tate's relative Weil
group only when `c` is the arithmetic fundamental class family (see "Relation to the
source", item 1). `W_{F_z}` is the published
`Weil.Local.localWeilGroup (padicField z)`. `C_F` is
`NumberField.IdeleClassGroup (𝓞 F) F`, and
`i_z = IdeleClassGroup.ofAdicCompletion (𝓞 F) F z : F_zˣ →* C_F` sends `a` to the
class of the idele with `z`-component `a` and all other components `1` (Tate's `η`
in (1.6.1)). `transfer c F E : W_{E/F} →* C_F` is the published transfer: the group
transfer to the normal finite-index subgroup `C_E`, whose values lie in the image of
`C_F` and which is then read in `C_F` (published `ideleTransfer`,
`ideleClassInclusion_transfer`). On `C_E` it is the idele-class norm (published
`transfer_inclusion`).

- `HasLocalTransferReciprocity z ι` (proposition definition), with implicit
  `{c} {F E}` and `[IsGalois F E]`, for a finite place `z` of `F` and
  `ι : W_{F_z} →ₜ* W_{E/F}`. It asserts: for every reciprocity candidate
  `ez : LocalFactor.RankOne.ReciprocityCandidate (padicField z)` satisfying the
  published geometric normalization
  `LocalClassField.GeometricWeilReciprocityRelation (padicField z)
  (padicField z).canonicalTopologicalData ez`, and every `g : W_{F_z}`,

  `transfer c F E (ι g) = (i_z (reciprocityUnits (padicField z) ez g))⁻¹`.

  Here `LocalFactor.RankOne.reciprocityUnits _ ez : W_{F_z} → F_zˣ` is the
  abelianization map followed by `ez`. By the published proved
  `Langlands.LocalClassField.geometricWeilReciprocityUniqueness`, any two geometric
  candidates are equal, so the quantifier over `ez` costs nothing.
- `LocalTransferReciprocityStatement` (the target) quantifies over every class
  family `c`, all number fields `F E : Type u` with `[Algebra F E]` and
  `[IsGalois F E]`, every finite place `z` of `F`, every finite place `w` of `E`
  with `[w.asIdeal.LiesOver z.asIdeal]`, every reciprocity candidate `e` of
  `E_w = towerPadicField z w`, and every `ι : W_{F_z} →ₜ* W_{E/F}`. It states that
  the published `IsLocalRelativeWeilMap z w e ι` implies
  `HasLocalTransferReciprocity z ι`. Its only universe parameter is `u`.

The published `IsLocalRelativeWeilMap z w e ι` says three things. First, `e`
satisfies the geometric normalization. Second, through `E → E_w → \bar{F_z}`, the
image of `ι g` in `Gal(E/F)` acts as the Galois image of `g`. Third, on
`W_{E_w}`, `ι ∘ completionWeilMap z w` is the inverse of `e`-reciprocity followed by
`E_wˣ → C_E → W_{E/F}`. Nothing is assumed about the existence of such a map. If
none exists, the target says nothing about that `ι`.

Both definitions use Mathlib's default Krull topology on `Gal(E/F)`, as
`IsLocalRelativeWeilMap` does. The transfer is a plain group homomorphism, so no
other topology enters. No `FundamentalClass.Restriction` hypothesis is needed,
because no subgroup `W_{E/K}` occurs.

## Consequence for twisting characters

The published `reciprocityCharacter c F E χ` is `w ↦ (χ (transfer c F E w))⁻¹`
(published `reciprocityCharacter_apply`), for a continuous character `χ` of `C_F`.
If the target holds and `IsLocalRelativeWeilMap z w e ι`, then for every geometric
`ez` and every `g : W_{F_z}`,

`reciprocityCharacter c F E χ (ι g) = χ_z (reciprocityUnits (padicField z) ez g)`,

where `χ_z = χ ∘ i_z` is the `z`-component of `χ`. This one-line consequence is
explained here and is not part of the Lean module.

## Relation to the source

Tate (1979), Proposition (1.6.1), p.8, gives, for a place `v` of a global field `F`,
a continuous `θ_v : W_{F_v} → W_F` such that, for every finite extension `E` of `F`,
the square formed by `r_{E_v} : E_vˣ → W_{E_v}^{ab}`, `r_E : C_E → W_E^{ab}`, the
map `θ_v^{ab}` and the map `η` that sends `a ∈ E_vˣ` to the class of the idele with
`v`-component `a` and all other components `1`, commutes. The target is the case
`E = F` of that square, in a derived relative form. It differs from the source as
follows.

1. **Groups.** Tate's `W_F` is replaced by `W_{E/F}`, and only finite places `z`
   occur. Tate's `W_F^{ab}` with `r_F : C_F ≅ W_F^{ab}` is replaced by the transfer
   `W_{E/F} → C_F`. In Tate's setting this is the right replacement. By (W3), p.4,
   the transfer `W_F^{ab} → W_E^{ab}` corresponds under `r_F`, `r_E` to the
   inclusion `C_F ⊆ C_E`. So the transfer of `W_{E/F} = W_F/W_E^c` to its subgroup
   `C_E = W_E^{ab}` is `r_F^{-1}` on `W_F^{ab}`, landing in `C_F`. The target is
   stated for every class family `c`, and for a general `c` it is a statement about
   the class extension `W_{E/F}`, not about Weil groups. The groups are Tate's
   relative Weil groups only in the arithmetic specialization, the published
   hypothesis `IsArithmeticClassFamily c` (assumed by the published
   `RelativeWeilTwistFunctionalEquationStatement`). The target does not say that
   the transfer is the abelianization map. That is the published
   `RelativeWeilTransferReciprocityStatement`, which needs the arithmetic
   hypotheses and has no proof in the Library. The target does not need it.
2. **Sign.** Tate's (1.4.1), p.6, normalizes `r_{E}` geometrically, and the
   Library's geometric candidate `ez` is the inverse of Tate's `r_{F_z}`. Tate's
   square gives `transfer(θ_z(g)) = η(ez[g])` in Tate's coordinates. The published
   `IsLocalRelativeWeilMap` explains that the Library's coefficient embedding is
   Tate's composed with inversion on `C_E`. Its third part carries the matching
   inverse. In the Library's coordinates the transfer therefore takes the value
   `η(ez[g])⁻¹`, which is the inverse in `HasLocalTransferReciprocity`. On the
   subgroup `W_{E_w}` the target follows from the third part of
   `IsLocalRelativeWeilMap`, `transfer_inclusion` (the transfer of `inclusion a`
   is `N_{E/F} a`), and local class field theory, which turns the norm
   `E_wˣ → F_zˣ` into the inclusion `W_{E_w} ⊆ W_{F_z}`.
3. **Relation to the restriction statement.** The published
   `Langlands.ClassField.Global.RelativeWeilGroup.LocalInducedRestrictionStatement`
   has a transfer condition of the same form for maps `ιu : W_{K_u} → W_{E/K}`, at
   places `u` of an intermediate field `K` above `z`. The target is not the case
   `K = F` of that statement. There the maps `ιu` are existential, and their
   domain is `localWeilGroup (towerPadicField z z)`, a different Lean term from
   `localWeilGroup (padicField z)`. The target is a property of the given `ι`
   itself.
4. **Why the target is true.** The argument works for every class family `c`. Let
   `D ⊆ Gal(E/F)` be the decomposition group of `w`, `A = C_E` (embedded by
   `inclusion`) and `H = projection⁻¹(D)`.
   - By the second part of `IsLocalRelativeWeilMap`, `projection ∘ ι` is the
     restriction of `σ_g` to `E` read in `D`. The Weil group is dense in the Galois
     group, so `W_{F_z}` maps onto `Gal(E_w/F_z) ≅ D`. The kernel of this map is
     `W_{E_w}`, the range of `completionWeilMap z w`, because `E` is dense in
     `E_w`. So `ι(W_{F_z}) ⊆ H`, `ι(W_{E_w}) ⊆ A` by the third part, and `ι`
     induces a bijection `W_{F_z}/W_{E_w} → H/A`.
   - Split the cosets of `A` in `W_{E/F}` into `H`-orbits, which are indexed by
     `D \ Gal(E/F)`. With coset representatives `t_d s_r`, the transfer of
     `h ∈ H` to `A` is `∏_{r ∈ D\Gal(E/F)} s_r⁻¹ V_H(h) s_r`, where `V_H` is the
     transfer of `H` to `A`. Conjugation in the class extension acts on `C_E`
     through the Galois action.
   - Transfer is natural along a homomorphism that maps the subgroup into the
     subgroup and induces a bijection of cosets. Applied to `ι`, with coset
     representatives taken from `ι(W_{F_z})`, `V_H(ι g)` is the image under the
     third part of `IsLocalRelativeWeilMap` of the local transfer
     `W_{F_z} → W_{E_w}^{ab}`. By local class field theory, `e` turns that local
     transfer into `ez` followed by the inclusion `F_zˣ ⊆ E_wˣ` (Serre 1979,
     XI §3, diagram (2)). Hence `V_H(ι g) = i_w(ez[g])⁻¹` in `C_E`.
   - The conjugates `r⁻¹ · i_w(ez[g])` for `r ∈ D\Gal(E/F)` are the classes of
     the ideles with component `ez[g] ∈ F_zˣ` at the places `r⁻¹w`. These are the
     places of `E` above `z`, each once. Their product is the image of
     `i_z(ez[g])` under `C_F → C_E`, so `transfer(ι g) = i_z(ez[g])⁻¹`.

   This argument uses the three parts of `IsLocalRelativeWeilMap`, the density of
   the Weil group, and local class field theory for the geometric reciprocity maps
   of `F_z` and `E_w`. It does not use that `c` is the fundamental class, it does
   not use `Restriction c`, and it does not use transfer reciprocity for `W_{E/F}`.
   In the Library, the local transfer square is part of the published
   `CommonClosure.CoherentFamilyRelation`; the existence of the normalized system
   is the published `CommonClosureReciprocityExistence`, which has no proof in the
   Library. This is only a sketch of why the statement is true; the proof is a
   separate obligation.

## Intended use

In the reduction of the published `RelativeWeilTwistFunctionalEquationStatement`
to the Hecke functional equation (Tate 1979, §3.5; Henniart 2000, §2.3), the
representations at a finite place `z` are restricted along `ι`. The twist by
`reciprocityCharacter c F E χ` restricts, by the consequence above, to the
local character `χ_z ∘ reciprocityUnits ez`. Together with
`LocalInducedRestrictionStatement` and the published Brauer induction statement
`InducedCharacterGenerationStatement`, this identifies local factors of
`S ⊗ reciprocityCharacter χ` at `z` with local factors of twisted Hecke
characters. The reduction and the proof of the target are separate obligations.

## Sources

- John Tate, *Number theoretic background*, in *Automorphic Forms,
  Representations and L-Functions*, Proc. Sympos. Pure Math. 33, Part II (1979),
  3–26. §1 opening, p.3 (transfer `G^{ab} → H^{ab}` by a section of `H\G`);
  (1.1) with (W1) and (W3), pp.3–4 (Weil groups; transfer corresponds to
  inclusion); (1.2.2) and the remark after it, p.4 (on a normal subgroup the
  transfer is the product of conjugates); (1.4.1), p.6 (geometric normalization of
  local reciprocity); Proposition (1.6.1), p.8 (the local map `θ_v` and the square
  with `η`). Printed page `p` is PDF page `p + 9`. Registered source
  `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`, verified on
  6 November 2026.
- Jean-Pierre Serre, *Local Fields*, GTM 67, Springer, 1979. Chapter XI §3,
  "Functorial properties of the reciprocity map", diagram (2), printed p.170, and
  its limit form (2)*, printed p.171 (transfer `Ver` corresponds to inclusion
  `A_E → A_{E'}`). Printed page `p` is PDF page `p + 6`. Registered source
  `serre-1979-local-fields`, SHA256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`, verified on
  6 November 2026.

The relative form with the transfer `W_{E/F} → C_F`, the sign, and the argument in
item 4 are derived by Worker 84 for this program. They are not quoted from the
sources.

## Dependencies

The module imports the published `Langlands.ClassField.Global.LocalRelativeWeilMap`
(`IsLocalRelativeWeilMap`, and through its imports `padicField`, `towerPadicField`,
`LocalFactor.RankOne.ReciprocityCandidate`, `reciprocityUnits` and
`LocalClassField.GeometricWeilReciprocityRelation`) and
`Langlands.ClassField.Global.RelativeWeilTransfer` (`transfer`).
