# Schwartz spaces on the Levi scheme and the actual Levi subgroup

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviSchwartz`.
Namespace: `Langlands.HarishChandraSchwartz`.

This is an internal compatibility construction from `RationalLeviScheme` and the
generic `GroupTransport` equivalence. It compares the existing Schwartz spaces; it
does not introduce a different function-space construction.

The source conventions are Waldspurger (2003), I.1, printed p.240 (PDF p.6), for the
inherited compact subgroup `M ∩ K`; II.1, printed p.252 (PDF p.18), for applying the
Xi construction to a Levi; and III.6, printed pp.271–272 (PDF pp.37–38), for the
Schwartz-space topology and the use of `C(M)`. The equivalence here is a derived
identification, not a separately numbered source theorem.

Let `F` be an arbitrary nonarchimedean local field and `G` an affine group scheme
locally of finite type over `F`. The parameters expose connected reductivity of `G`,
a maximal split torus `i`, a generic cocharacter `ν`, and a subset `J` of the simple
relative roots. Set `L = Standard.leviScheme i ν J`, with embedding `j`, and let
`M_J(F) = standardLeviPoints i ν J`. Take an open compact subgroup `K` of `G(F)`,
a matrix representation `ρ` with a nonempty finite index type, and the explicit
Levi Iwasawa hypothesis

`M_J(F) = (P₀(F) ∩ M_J(F)) (K ∩ M_J(F))`.

No splitness, quasisplitness or characteristic-zero assumption is made. Closedness
or faithfulness of `ρ` is not needed for this exact comparison.

`rationalLeviSchwartzEquiv` is a continuous complex-linear equivalence from

`Space (rationalLeviXi hKc hM) (σ_ρ restricted to M_J(F))`

to `RationalSchwartzSpace` on `L(F)`, using the compact subgroup `j⁻¹(K)`, its
published Iwasawa decomposition, and the restricted representation `ρ ∘ j`.
These spaces carry their existing locally convex inductive-limit topologies.
The first is the space used as the codomain of `rationalConstantTerm`.

The forward map is `f ↦ f ∘ leviSchemePointsEquiv i ν J`. The inverse precomposes
with the inverse point equivalence; the two application lemmas state these formulas.
`nu_rationalLeviSchwartzEquiv` proves exact equality of every defining extended-real
seminorm `ν_r`, for all real `r`.

The implementation applies `Space.comapEquiv` to the canonical topological group
isomorphism `leviSchemePointsEquiv`. Its two weight premises are the published
identities `rationalXi_leviScheme` and `rationalHeight_restrict_leviHom`. The generic
construction proves continuity on compact-open levels by equality of their
seminorms and then uses the inductive-limit universal property, in both directions.

The Levi Iwasawa decomposition is retained as an explicit hypothesis. This
comparison does not prove its existence, any new coefficient or integral estimate,
or Plancherel inversion. In particular it does not assert compatibility of Haar
measures or convolution, which would require corresponding measure data.
