# Naturality of variable-rank determinant pullback

Let `X` and `Y` be schemes in universe `u`, let `M` and `N` be actual module
sheaves on `X`, and let `φ : M ≅ N`. The supplied covering frame families `e`
and `d` may have different chart index types and independent finite ranks
`n i` and `m j`. The actual free frames are indexed by `ULift (Fin (n i))`
and `ULift (Fin (m j))`, respectively. The morphism `q : Y ⟶ X` is arbitrary.

`frameGenerator_iso_expansion` expands the image of a source frame vector in
the actual target basis, summing over `Fin (m j)`. Pulling back this equality
of local morphisms from the structure module and evaluating on one proves
`isoBasis_repr_pullback`: each coordinate is carried through the actual
structure-sheaf map `q.app V`. The two finite index types need not coincide.
The imported mixed finite-basis determinant map lemma then gives
`isoUnit_pullback`. For unequal ranks on an overlap, the coefficient ring is
trivial, as proved in the imported finite-basis construction.

`pullback_hom_ext_genSec_overlap` determines maps out of the pulled-back
determinant using generators on intersections of the two covering families.
Its proof applies the actual pullback adjunction, sheaf separation on the
intersection cover, and local scalar generation of the determinant. The
square criterion `pullback_iso_square_eq_of_genSec_overlap` then reduces an
actual isomorphism equality to these generator images. Together with the
imported rank-independent section-image lemma, the determinant generator
formulas and `isoUnit_pullback` prove `pullbackIso_naturality`:

`q^*(det φ) ≪≫ pullbackIso d q = pullbackIso e q ≪≫ det(q^*φ)`.

The determinant on the right uses the actual constructed pulled-back frames
and the image of `φ` under `Scheme.Modules.pullback q`.
`lineBundlePullbackNaturalityIso` lifts that determinant map to actual line
bundles. `lineBundlePullbackIso_naturality` gives the same commuting square
in the full subcategory of locally free rank-one module sheaves, by equality
of the underlying sheaf maps.

This is an internal derived adaptation of the Library's fixed-rank
`DeterminantNaturality` to its actual variable-rank frame, isomorphism and
pullback constructions. Frames and coverage remain explicit inputs. The
construction supplies neither frame existence nor the parabolic Lie
polarization, its ampleness, or the parent representability theorem.
