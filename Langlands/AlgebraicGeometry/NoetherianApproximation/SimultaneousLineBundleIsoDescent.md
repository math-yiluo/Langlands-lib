# Simultaneous descent of two line-bundle isomorphisms

This internal corollary of the published `lineBundleIsoSubalgebraDescent` theorem
places two actual module-sheaf isomorphisms over one finitely generated algebra
stage. It is intended for the two axis comparisons in generic line-bundle
descent; it does not itself construct a bundle model or identify any axes.

For two `A₀`-subalgebras `T₁ ≤ T₂` of `A`,
`subalgebraInclusionSpecMap` is the actual morphism `Spec T₂ → Spec T₁`
induced by `Subalgebra.inclusion`. Its companion theorem
`subalgebraInclusionSpecMap_comp` proves that this morphism followed by
`Spec T₁ → Spec A₀` equals `Spec T₂ → Spec A₀`. The proof uses
contravariance of `Spec.map` and the defining algebra maps.

`exists_fg_pair_lineBundle_iso` works in an arbitrary universe `u`. Let `A` be an
algebra over a commutative ring `A₀`, and let `f₀ : X₀ → Spec A₀` be
quasi-compact and quasi-separated. Four modules `M₁`, `N₁`, `M₂`, `N₂` on `X₀`
are each locally free of rank one in the Library's sense. On any given pullback
square `X → X₀` over `Spec A → Spec A₀`, assume that the pullbacks of `M₁` and
`N₁` are isomorphic and likewise those of `M₂` and `N₂`. For every finite subset
`s` of `A`, the theorem gives a finitely generated `A₀`-subalgebra `T` of `A`
containing `s`. Along every pullback square over `Spec T → Spec A₀`, it supplies
both actual module-sheaf isomorphisms, each expressed by `Nonempty` of the
corresponding isomorphism type. No field, normality or noetherian hypothesis is
used.

Apply the imported single-isomorphism descent theorem first to `M₁`, `N₁` and
`s`, obtaining `T₁`. Choose finite algebra generators `s₁` of `T₁`. Apply the
same theorem to `M₂`, `N₂`, prescribing `s₁ ∪ s`; this gives `T₂`. The
universal property of algebra adjoin proves `T₁ ≤ T₂`. The second comparison
already holds along every indicated pullback over `T₂`. For the first one, the
named map `subalgebraInclusionSpecMap` gives the spectrum map, and its companion
theorem gives the required equality over `Spec A₀`. A pullback lift maps any
given stage square over `T₂` to the
chosen base change over `T₁`. Pull back the first comparison along this lift,
using `nonempty_iso_pullback_of_fac` and its first projection equation.

The implementation composes existing Library descent and pullback lemmas. This
is derived internal content and makes no new literature translation claim. In
particular, an isomorphism of bundles is retained as an actual sheaf
isomorphism, rather than replaced by equality of quotient classes. The
arbitrary-valuation extension theorem remains a separate obligation.
