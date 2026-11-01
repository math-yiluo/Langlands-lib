# Coherent filtrations by integral closed ideal sheaves

`CoherentIntegralIdealFiltrationStatement` states the finite filtration of a
coherent sheaf on a Noetherian scheme in Stacks Project, Lemma 30.12.3,
tag [01YF](https://stacks.math.columbia.edu/tag/01YF).
The retained original is `coherent.tex`, lines 3050–3141,
label `lemma-coherent-filter`, in the registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`, at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`. The source folder fingerprint is
`af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a`;
the file fingerprint is
`702ca51850d0f9a615888dc0ced8100e104c98961e05a48b32c3ddf6eda61604`.

The hypotheses are an actual Noetherian scheme `X` and a module sheaf `M`
which is quasi-coherent and has finitely generated sections on every affine
open. These are the finite type quasi-coherent, hence coherent, sheaves of
the source under its Noetherian hypothesis. The statement has no chosen
filtration, numerical polynomial, positivity assumption, or generic
nonvanishing certificate as an input.

The conclusion supplies a natural length `n` and module sheaves `F j` for
`j : Fin (n + 1)`. Every term is quasi-coherent with finite affine
sections. The initial term is a zero object, and the last term is isomorphic
to `M`. Each consecutive pair has an actual short exact sequence

`0 → F j.castSucc → F j.succ → i_* I → 0`.

Here `i : Z → X` is an actual closed immersion, `Z` is integral, and `I`
is a nonzero quasi-coherent module with finite affine sections on `Z`.
A monomorphism `I → structureModule Z` expresses that it is an ideal
sheaf. This is a sheaf subobject formulation of a coherent ideal; it does
not assert that the ideal is invertible. Its pushforward is the existing
functor `Scheme.Modules.pushforward i`, and short exactness uses
`CategoryTheory.ShortComplex.ShortExact`.

The monomorphisms in these short exact sequences, followed by the terminal
isomorphism, exhibit the `F j` as nested subobjects of `M`. Thus the short
exact sequence formulation expresses the source's subsheaf filtration and
successive quotient isomorphisms. It allows length zero precisely for a
zero sheaf. Repeated supports are allowed, as in the source.

The current tag page and all four comments were also read and retained as
`stacks-coherent-devissage-01yf-comments-2026-11-01`, fingerprint
`67ccba1e843ee09586d4e9d906aa13a4d8227075d1cfb5b11945a0af5cfb36c2`.
Comment 6958 explains the explicit coherence and nonzero requirements; both
are included in the retained TeX and the Lean statement. Comment 950's
ideal-power notation correction is already incorporated in the retained
proof. The support equalities and support containment discussed in comments
2176, 6815 and 6958 are consequences and are not additional clauses here.

This is a structural prerequisite for coherent-sheaf devissage. Its
statement supplies neither a proof of the filtration nor an Euler
polynomial or a positive leading coefficient.
