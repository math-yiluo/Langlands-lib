# Renard II.2.5: the original-sheaf comparison `F ⟶ P(Γc F)` is an isomorphism

Worker 42 implemented this proof. The entry theorem is
`Langlands.Sheaf.Renard.CompactSectionEquivalence.sheafComparisonIsIso :
SheafComparisonIsIso`. It proves the published proposition
`CompactSectionEquivalence.SheafComparisonIsIso` from
`CompactSectionEquivalenceStatement.lean` exactly as stated. That proposition
covers every `X : Type` with a topology satisfying
`Langlands.Topology.IsLocallyProfinite X` and every complex vector sheaf `F`.
The proof adds no further premise.

## Source

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, II.2.5. The Theorem
is on printed p.39 / PDF p.45. The relevant step is the last paragraph of
its proof, on printed p.40 / PDF p.46. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF pp.45–46 were read for this proof.

Renard starts from a sheaf `M`, sets `M = M_c(X)`, and observes that
`χ_U · M = M(U)` for every compact open `U`. He concludes that the sheaf
rebuilt from `M` is the original sheaf. The published comparison
`SheafProjectorComparison.sheafComparison F hX` formalizes this
identification over every open `V`, not only compact ones. It sends a
section `s ∈ F(V)` to the family indexed by the compact opens `U ⊆ V`.
The component at `U` is the restriction `s|_U` extended by zero, which is a
compact section of `F` fixed by `χ_U`. Its target is the published projector
sheaf `ProjectorVectorSheaf.functor.{0, 0} hX` applied to
`compactSectionFunctor hX` at `F`. Over `V`, that sheaf's sections are the
compatible families of the module of compact sections, indexed by the
compact opens inside `V`. The proof below shows that every component of
this map is bijective. Renard's single sentence is thus checked over every
open set.

## The implemented proof

The proof works with germs throughout. All component and restriction
formulas come from the published `SheafProjectorComparison`,
`ProjectorPresheaf`, `CompactSectionTestModule` and `VectorSheafScalars`
modules.

Helper lemmas:

- `exists_inside_mem`: every point `x` of an open `V` lies in some compact
  open `U ⊆ V`. This uses
  `IsLocallyProfinite.hasCompactOpenNeighborhoodBasis`.
- `Γgerm_action`: at every point `x`, the germ of `χ_U · s` is the value of
  the indicator of `U` at `x` times the germ of `s`. This rewrites the
  projector `action` as multiplication by the test function `test hX U` and
  applies the published `Γgerm_testSmul`.
  - `Γgerm_action_of_mem` specializes this to points of `U`, where `χ_U`
    does not change germs.
  - `Γgerm_value_of_not_mem` specializes it to points outside `U`. A compact
    section fixed by `χ_U` (`value_fixed`) has zero germ there.
- `Γgerm_family_eq`: take two members `U`, `W` of a compatible family `t`
  and a point `x ∈ U ∩ W`. Set `I = interOpen hX U W`. Compatibility
  together with `restriction_val` says that `χ_I · t_U = t_I = χ_I · t_W`.
  The germs of both sides are unchanged at `x ∈ I`. Hence `t_U` and `t_W`
  have equal germs at `x`.

**Injectivity (`family_injective`).** Suppose `family F hX s = family F hX t`
for sections `s, t ∈ F(V)`. Take `x ∈ V` and choose a compact open
`U ⊆ V` containing `x` by `exists_inside_mem`. The `U` components
`extension F hX U _ s` and `extension F hX U _ t` are then equal, so their
germs at `x` agree. By the published `Γgerm_extension_of_mem`, these germs
are the germs of `s` and `t` at `x`. The published sheaf extensionality
`ext_germ` gives `s = t`.

**Surjectivity (`family_surjective`).** Let `t` be a compatible family over
`V`. The cover is indexed by `Inside (compactOpenBasis hX) V`, the compact
opens contained in `V`. For each such `U`, let `sf U ∈ F(U)` be the
restriction to `U` of the global compact section `t_U`. By
`germ_res_apply`, the germ of `sf U` at `x ∈ U` is the global germ of
`t_U`.

1. The cover reaches all of `V`, by `exists_inside_mem`.
2. The local sections are compatible. On `U ∩ W`, both restrictions have
   the germ of `t_U`, respectively `t_W`, and these agree by
   `Γgerm_family_eq`. Hence they are equal by `ext_germ`.
3. `F.existsUnique_gluing'`, Mathlib's gluing for sheaves applied to the
   cover `Ucov U = U` of `V`, gives `s ∈ F(V)` restricting to every
   `sf U`.

It remains to show that the `U` component of `family F hX s` equals `t_U`.
Both are compact sections, so `ext_compact` reduces this to equal germs at
every `x ∈ X`.

- If `x ∈ U`, the extension has the germ of `s` at `x`
  (`Γgerm_extension_of_mem`). That germ is the germ of `s|_U = sf U`, which
  is the germ of `t_U`.
- If `x ∉ U`, the extension has germ zero (`Γgerm_extension_of_not_mem`).
  The germ of `t_U` is also zero by `Γgerm_value_of_not_mem`, because `t_U`
  is fixed by `χ_U`.

`BasisAllOpen.families_ext` then identifies the two families.

**Assembly.** `family_bijective` combines both directions. In
`sheafComparison_isIso`, `ConcreteCategory.isIso_iff_bijective` turns each
bijective component of the underlying presheaf morphism
`(sheafComparison F hX).hom.app V` into an isomorphism in
`ModuleCat ℂ`. `NatIso.isIso_of_isIso_app` makes the presheaf morphism an
isomorphism. Morphisms of sheaves form a full subcategory, so
`ObjectProperty.isIso_hom_iff` lifts this to `IsIso (sheafComparison F hX)`.
The entry theorem `sheafComparisonIsIso` introduces `X`, its topology,
`hX` and `F` and applies `sheafComparison_isIso`.

## Scope

The hypothesis `hX : IsLocallyProfinite X` is Hausdorffness together with a
compact-open neighbourhood basis. The published constructions take `hX` as an
argument. Beyond them, this proof uses `hX` directly only through its
compact-open neighbourhood basis. It assumes no compactness, countability or
nonemptiness of `X`. It uses no inverse functor, comparison certificate or
equivalence. Empty opens and
empty spaces are covered: extensionality by germs is vacuous there, and
gluing over an empty cover is part of the sheaf condition. The companion
statements `CompactSectionFunctorIsEquivalence` and
`ProjectorFunctorIsEquivalence` in the same statement file are not proved
here.
