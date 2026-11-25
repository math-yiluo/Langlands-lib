# Étale morphisms of analytic spaces are open

`Langlands.Analytic.SaturatedAtlasPresentation.etaleOpenMap` proves the exact
Library proposition `EtaleOpenMapStatement.{u,v} K` for every complete
ultrametric normed field `K`. It concerns the actual point map supplied by
`localizedSpaceFunctor` on the existing localized analytic category.

The implemented proof first proves openness for a strong representative that
is étale over all recognized affinoid pieces. Pointwise flatness includes a
finite local neighborhood. Shrinking this neighborhood inside any given
source neighborhood preserves flatness, because the new pieces are clopen
pieces of the original ones and their restriction maps are flat. On each of
finitely many recognized target pieces, the finite Banach image contains a
neighborhood of the image point. The finite intersection of these relative
neighborhoods, combined with the neighborhood formed by the union of the
pieces, proves openness on the ambient spaces. These steps are implemented
in `StrongOpen`.

The finite local image argument, implemented in `FiniteFlatImage`, uses
injectivity of the faithfully flat localized ring map. Noetherianity gives a
single element outside the image point's kernel that annihilates the entire
kernel of the original map. The spectral image contains the open nonvanishing
locus of that element by finite Banach lying over. `FiniteBanachLyingOver`
provides this lying-over result with the norm control required for arbitrary
base valuations, including the trivial valuation. Its paired Markdown details
the residue-field extension and boundedness argument.

Finally, the definition of `etale` supplies an isomorphism of arrows between
the localization of this strong representative and the given morphism. The
underlying space functor sends the two isomorphism components to
homeomorphisms. The commutative square expresses the given point map as the
composition of the strong point map with these homeomorphisms; openness is
preserved by this composition.

The geometric provenance is Vladimir G. Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), registered source
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Proposition 3.2.7, printed p.59 / PDF p.56, proves openness for flat quasifinite
maps; Definition 3.3.4, printed p.63 / PDF p.60, gives the étale specialization.
The helper lemmas and the categorical transport are derived implementations
in the Library model. No extra base-change, compactness, Hausdorffness, local
model, or nontrivial-valuation premise is added to the target, and its Lean
and Markdown declarations and all their imports are unchanged.
