# Compact sections of a short exact sequence with c-soft kernel

Author: Worker 310.

The theorem `Langlands.Cohomology.cSoftShortExact.{u}` proves exactly the
published closed proposition
`Langlands.Cohomology.CSoftShortExactStatement.{u}`. For every locally compact
Hausdorff `X : TopCat.{u}`, commutative ring `R : Type u`, and short complex `S`
of sheaves of `ModuleCat.{u} R` on `X`, it assumes that `S` is short exact and
that `S.X₁` is c-soft. It proves both

- short exactness after applying the compactly supported global sections
  functor `Langlands.Sheaf.CompactSupport.functor`, and
- `IsCSoft S.X₂ → IsCSoft S.X₃`.

There are no additional hypotheses. C-softness and germs along compact sets use
the existing colimit definitions in `Langlands.Sheaf.CompactSoft`.

## Imported compact-germ lifting

The proof imports `Langlands.Sheaf.CompactSoft.GermLiftingProof` and applies
`Langlands.Sheaf.CompactSoft.compactGermLifting X R S hS hF`. For every compact
subset `K`, this theorem makes
`(setSectionsFunctor R K).map S.g.hom` surjective. Its proof constructs lifts
near compact sets by local surjectivity, correction by kernel sections, and
finite gluing. The present module uses that theorem as published, and supplies
the compact-support cutoff and final exactness argument.

The imported `exists_kernel_section` also gives the left exactness of sections
on any open set: a middle section with zero quotient image comes from a kernel
section on the same open set. The imported `exists_glue_pair` glues compatible
sections on two opens. The private `exists_glue_binary` adapts it to an open
`U` covered by two specified subopens, by identifying `U` with their union.

## Compact-support cutoff

`compactSections_surjective_of_compactGerm_lifting` is a reusable conditional
helper. It assumes local compactness and Hausdorffness, short exactness of `S`,
c-softness of `S.X₁`, and surjectivity on germs along every compact subset.
It proves surjectivity of the quotient map on compactly supported global
sections. The last hypothesis is discharged in the final theorem by the
imported compact-germ lifting theorem.

Let `s` be a quotient global section with compact support `K`. Choose an open
neighbourhood `V` of `K` with compact closure `L`. Lift the germ of `s` along
`L`, represent the lift by a middle section `t` on an open neighbourhood `U` of
`L`, and shrink `U` until `g(t) = s|U`. This uses `exists_setGerm_eq`,
`setGerm_naturality`, and `setGerm_eq` from the published germ API.

On `O = U ∩ Kᶜ`, the image of `t` is zero. The private
`restrict_zero_off_support` proves this by vanishing of every stalk germ and
sheaf section extensionality. The imported `exists_kernel_section` then gives
a kernel section `a` on `O` with `f(a) = t|O`.

The compact boundary `B = L \ V` lies in `O`. By `isCSoft_iff`, the germ of
`a` along `B` extends to a compactly supported global kernel section `a'`.
Equality of these germs gives an open neighbourhood `N` of `B`, contained in
`O`, where `t - f(a'|U)` vanishes. Only the global extension property of `a'`
is needed after this step; its compact-support witness is discarded.

The set `C = L \ N` is compact, contains `K`, and is contained in `V`. The
corrected middle section on `V` agrees with zero on `V ∩ Cᶜ`, since this
overlap lies in `N`. Binary gluing produces a global section `b`, equal to the
corrected section on `V` and to zero on `Cᶜ`. Its support is closed and
contained in `C`, hence compact. On `V`, the zero composite `g ∘ f = 0` shows
`g(b) = s`; on `Cᶜ`, both are zero because `K ⊆ C`. Sheaf uniqueness for this
two-open cover proves the global equality. Thus `b` is a compactly supported
lift of `s`.

## Quotient softness and final assembly

`isCSoft_quotient_of_compactGerm_lifting` assumes only surjectivity on compact
set germs and c-softness of the middle sheaf. It needs neither separation nor
local compactness nor short exactness as separate hypotheses. Lift a quotient
germ, realize the middle germ by a compactly supported global section using
c-softness, then map that section to the quotient. `compactGerm_naturality`
identifies its germ with the original one. The published compact-support
presheaf functor ensures that its image still has compact support.

`shortExact_of_compactGerm_lifting` has the assumptions of the cutoff helper.
The compact-support functor is additive and preserves finite limits. Its
exactness-and-monomorphism characterization gives exactness at the middle
term and monicity of the first map. The cutoff helper makes the last map
surjective, hence an epimorphism in `ModuleCat`. The constructor
`ShortComplex.ShortExact.mk'` assembles short exactness. Pair it with the
quotient-softness helper. Finally, `cSoftShortExact` discharges the germ-lifting
hypothesis using the published `compactGermLifting` theorem, proving the exact
closed target for every universe `u`.

## Provenance

This is the colimit-germ implementation of Kashiwara–Schapira, *Sheaves on
Manifolds* (1990), §2.5, Proposition 2.5.8 and Corollary 2.5.9, printed p.105.
Proposition 2.5.1(ii), printed pp.102–103, explains the compact colimit-germ
interpretation; Definition 2.5.5 and Proposition 2.5.6, printed pp.104–105,
explain the c-soft extension convention already used by the published
`IsCSoft`. The conditional helper statements are internal formalization
choices that separate the cutoff and quotient arguments from compact-germ
lifting. No new comparison with another definition of c-softness is claimed.

Registered source:
`provided-1a1e547af2f3cfc223f73a05ef9491bbf82f0d1976763c0d9c200813c4b8b658`;
file `literature/Kashiwara, Schapira - Sheaves on Manifolds, Grundlehren 292 (1990).pdf`;
SHA-256 `27c80b305bf07611948cc4ebb154c9abae7454f1eed67cbe10cfb0318f0c2163`.
