# Proof of the star-sheaf cokernel injection and undersized obstructions

Worker 1038. This pair proves the existing closed proposition
`Langlands.Sheaf.Renard.StarDiagram.CokernelScopeStatements.{u,v}` as the
theorem `Langlands.Sheaf.Renard.StarDiagram.cokernelScopeStatements`.
The target and its three conjuncts are imported unchanged from
[StarCokernelScopeStatements](StarCokernelScopeStatements.md). The objects
`F`, `G`, `Ti i`, `f`, `gi i`, the topology and the cover `starCover` are the
published ones from [StarDiagram](StarDiagram.md). The category is the
original `BasisSheaf.{u,v} (allOpenBasis (Option I))`. Its zero morphisms are
the canonical pointwise ones named in the statement module. The cokernel
interfaces are Mathlib's `CokernelCofork`, `IsColimit`, `HasCokernel` and
`Abelian`. The theorem has universe parameters `u` and `v`. It uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The source interfaces come from David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
II.2.1, printed pp.33–34 / one-based PDF39–40, defines presheaves on a chosen
basis, their morphisms and the unique-gluing sheaf condition (F). A.VI.1,
printed p.261 / PDF267, lists sheaves of abelian groups among the motivating
abelian categories and states the axioms, among them AB2* (every morphism has
a cokernel). These pages were reread for this proof and the fingerprint of
the retained original was verified.

The star diagram, the injection and both universe-size obstructions are
internal derived mathematics. Renard does not print them, and this proof
claims no error in the printed text. The only source principle used is the
unique gluing of II.2.1, through the published `BasisSheaf.unique_gluing`.

## Helper lemmas

All helpers are in `Langlands.Sheaf.Renard.StarDiagram`, with
`{I : Type u}` and the published `topology I` installed as a local instance.

- `live_starCover a`: every member of `starCover` contains `none`. Both
  cases are the published `live_E` and `live_U i`.
- `cofork_app_f`: for any `c : CokernelCofork f`, the component of `c.π` on
  `V` sends the image of every `F`-section under `f` to zero. This is
  `CokernelCofork.condition c` applied to that component, using the canonical
  zero components.
- `cofork_app_eq_zero_of_not_leaf`: on an open `V` with `¬ Leaf V`, `f` is the
  identity, because `weight V = 1`. So the component of `c.π` on `V` is zero
  on every `G`-section.
- `restrict_cofork_eq_zero_of_not_leaf`: the same vanishing after a section of
  `c.π`'s image is restricted to an open without leaves. The proof uses
  naturality of `c.π` with respect to restriction
  (`restriction_naturality_apply`).
- `leafValue i a`: the integer `1` if `a = some i` and `0` otherwise, with
  `leafValue_self` and `leafValue_ne`.
- `leafFamily c i a`: the image under `c.π` of the integer section
  `intSection (starCover a) _ (leafValue i a)`.
- `starCover_eq_of_mem`: if a member `starCover a` contains a leaf point
  `some k`, then `a = some k`. This holds because `E` contains no leaf and
  `U j` contains only the leaf `some j`.
- `leafFamily_compatible`: the family `leafFamily c i` is compatible in the
  literal sense of `Compatible`. Let `W` lie in both `starCover a` and
  `starCover b`. If `W` contains a leaf `some k`, then `starCover_eq_of_mem`
  gives `a = some k = b`, and the two restrictions coincide. Otherwise both
  restrictions vanish by `restrict_cofork_eq_zero_of_not_leaf`.
- `leafSection c i`: the global section obtained by applying
  `BasisSheaf.unique_gluing` to the vertex `c.pt`, the cover
  `starCover_covers` of `whole I` and this compatible family. The existence
  part is chosen. `leafSection_restrict` records that its restriction to
  each `starCover a` is `leafFamily c i a`.
- `factor_apply`: if `φ : c.pt ⟶ T` satisfies `c.π ≫ φ = g`, then `φ` applied
  to the `c.π`-image of a `G`-section equals `g` applied to that section.
- `mem_starCover_some i`: `some i` lies in `starCover (some i) = U i`.
- `leafSection_detect c hc i j`: fix the colimit structure `hc`. Let
  `φᵢ = (CokernelCofork.IsColimit.desc' hc (gi i) (f_comp_gi_eq_zero i)).1`
  be the factorization of `gi i` through `c`. The component of `φᵢ` on `U i`
  sends the restriction of `leafSection c j` to the mod-two section with
  value `leafValue j (some i)` reduced modulo two. The proof combines
  `leafSection_restrict`, `factor_apply` and the published
  `gi_apply_section`.
- `leafSection_injective c hc`: suppose `leafSection c i = leafSection c j`
  with `j ≠ i`. Then `leafSection_detect` gives the same mod-two value for
  `i` and for `j` on `U i`. That value is `1` for `i` and `0` for `j`, so
  `0 = 1` in `ZMod 2`, which is false.

Empty `I` needs no separate case: the injection is then the empty function.

## The three conjuncts

`cokernelSectionInjection : CokernelSectionInjectionStatement.{u,v}`. Given
`I : Type u`, any actual `c : CokernelCofork (f.{u,v} (I := I))` and any
`hc : IsColimit c`, the embedding is `⟨leafSection c, leafSection_injective c hc⟩`
into the carrier of `Sections c.pt.obj.obj (whole I)`. The proof uses no
other cokernel, abelian structure, size bound or relation between `u` and
`v`. Gluing and detection are proved from the published objects, not
assumed.

`undersizedNoCokernel : UndersizedNoCokernelStatement.{v}`. Assume
`HasCokernel (f.{v+1,v} (I := Type v))`. Then Mathlib's
`cokernelIsCokernel` is a colimit structure on the chosen cokernel cofork.
The injection at universes `v+1` and `v` embeds `Type v` into a global
section carrier lying in `Type v`. By `small_of_injective`, `Type v` would be
`Small.{v}`. This contradicts Mathlib's `not_small_type.{v,v}`.

`undersizedNotAbelian : UndersizedNotAbelianStatement.{v}`. Let `A` be an
`Abelian` structure on `BasisSheaf.{v+1,v} (allOpenBasis (Option (Type v)))`.
Its `has_cokernels` field supplies a cokernel of `f`. That field is stated
for the zero morphisms coming from `A`, while `UndersizedNoCokernelStatement`
uses the canonical zeros. The helper `hasCokernel_of_hasZeroMorphisms_eq`
moves `HasCokernel` between any two `HasZeroMorphisms` structures on the same
category. Such structures are equal by Mathlib's `Subsingleton` instance for
`HasZeroMorphisms`. The transported cokernel contradicts
`undersizedNoCokernel`.

`cokernelScopeStatements` is the conjunction of these three theorems.

## Scope

The two negative results concern only this star specialization: space
universe `v+1`, index type `Type v` and section carriers in `Type v`. They
make no claim about other spaces and do not assert that a sufficient section
universe is necessary in general. The separate positive target
`Langlands.Sheaf.Renard.BasisSheafAbelianStatement` uses section universe
`max u v`. For this space that universe is at least `v+1`, so it is a
different category and there is no conflict. This pair changes neither that
target, nor the normalized-presheaf result, nor any imported statement or
construction pair.
