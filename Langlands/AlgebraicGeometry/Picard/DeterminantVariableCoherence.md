# Identity and composition coherence for variable-rank determinant pullback

This derived construction proves coherence of the actual variable-rank
determinant pullback comparison. The input is a supplied covering system of
actual finite frames for a module sheaf on a scheme. Ranks may vary with the
chart; the scheme and chart index type share one universe.

The actual local frame-generator maps are compatible with the canonical module
pullback comparisons for identity and composite scheme morphisms. These
identities follow from the imported local-hom pullback coherence and the
canonical structure-sheaf pullback isomorphisms. An isomorphism preserving two
matching finite local frames has mixed determinant coefficient one, because
the transported actual section basis equals the target basis.

Maps out of the glued determinant are determined on local generators: every
local section is a scalar multiple of the determinant generator, and the
cover detects equality. The pullback adjunction gives corresponding criteria
for maps from one or two successive pullbacks of the determinant.

`pullbackIdentityIso` is the determinant map induced by the module pullback
identity comparison. It preserves local generators. `pullbackIso_identity`
therefore identifies its composite with the determinant pullback comparison
as the canonical module-sheaf identity pullback isomorphism.

`pullbackCompositionIso` is the determinant map induced by the module-sheaf
comparison from successive to composite pullback. It preserves the actual
determinant generators. The imported identity for successive pullback of
sections identifies the generators on both routes. Thus
`pullbackIso_composition` identifies successive determinant comparisons with
the single composite comparison preceded by the canonical pullback-composition
isomorphism of the determinant sheaf.

Both equalities lift to actual line bundles through their full subcategory.
The proof adapts the existing fixed-rank coherence argument using mixed
finite-basis determinants. The generic local-hom and section pullback lemmas
are reused directly. No constant-rank, affine or quasi-compact assumption is
introduced. These results do not construct frames, prove naturality under
arbitrary module-sheaf isomorphisms, or construct an ample parabolic
polarization.
