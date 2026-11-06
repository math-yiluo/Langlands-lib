# Actual Ext and derived-sections pushforward under a homeomorphism

Let `e : X ≅ Y` be an isomorphism of actual topological spaces in arbitrary
universe `u`. Pushforward of actual abelian sheaves along `e.hom` is the
published equivalence `sheafPushforwardEquivalence e`; its inverse is
pushforward along `e.inv`. These exact equivalences preserve injectives.

`pushforwardSectionsIso e` identifies actual global sections after
pushforward with actual global sections on `X`, with identity components.
`pushforwardDerivedComparison e F n` is the existing canonical
`compComparison` for that section isomorphism. It is a morphism

`R^n Γ(X, F) → R^n Γ(Y, e_* F)`.

The definition uses vanishing of the positive derived functors of the
homology-preserving pushforward. It does not substitute a new map into
the Ext or right-derived constructions.

`cohomologyPushforwardEquiv_symm_HAddEquiv` proves, for every actual abelian
sheaf `F`, every nonnegative degree and every actual Ext-defined cohomology
class `a` on `X`,

`HAddEquiv Y (e_* F) n ((cohomologyPushforwardEquiv e F n).symm a)`

`= pushforwardDerivedComparison e F n (HAddEquiv X F n a)`.

Here both `HAddEquiv` and `cohomologyPushforwardEquiv` are the unchanged
published additive equivalences. `cohomologyPushforwardEquiv_HAddEquiv`
gives the equivalent forward square: apply the canonical derived-sections
comparison to the `HAddEquiv` image of the actual Ext pushforward; the
result is the `HAddEquiv` image of the original pushed-sheaf class.
Neither theorem requires the caller to supply an injective resolution.

The proof first establishes `cohomologyPushforwardEquiv_symm_apply`.
The inverse of the existing Ext-defined equivalence is the forward exact
adjunction applied after precomposition with the forward component of
`constantInversePushforwardIso`. This follows by applying the existing
forward equivalence, cancelling the adjunction equivalence, and composing
the actual constant-sheaf isomorphism with its inverse in Ext degree zero.

The private `homGlobalSectionsIso_mk₀` identifies evaluation of the actual
Hom-to-sections isomorphism with the published degree-zero sheaf-cohomology
normalization on `Ext.mk₀`. The private `adjunct_sections` combines this
with the already published `cohomologyPushforwardEquiv_equiv₀` to show that
the actual adjunction and constant-sheaf comparison preserve sections.
Thus the section normalization used in all degrees is established from
the existing actual equivalence.

For a supplied injective resolution `I` on `X`,
`pushforwardResolutionHomMap e I` is the actual map from Hom out of the
constant integer sheaf into `I.cocomplex` to Hom out of the constant integer
sheaf on `Y` into the mapped injective resolution. Its coefficient map is
precomposition with the actual constant-sheaf isomorphism, then the actual
Hom adjunction. Additivity and coefficient naturality make it a cochain map.
The private sections-square lemma proves componentwise that this map
corresponds to the identity comparison of sections, using `adjunct_sections`.

Lift a Hom-resolution homology class along `homologyπ` from cycles. The
existing `extAddEquivHomology_symm_homologyπ` expresses its Ext class by
`extMk`. The inverse pushforward formula, `mk₀_comp_extMk`, and the included
`ExtAdjunctionResolution.extEquiv_extMk` show that its image has exactly
the mapped coefficient. Naturality of `homologyπ` and `cyclesMap_i` prove
the Ext/Hom-homology compatibility. The only larger heartbeat allowance
is finite and scoped to this private compatibility lemma.

`resolutionGlobalSectionsHomologyEquiv_pushforward` applies the actual
Hom-to-sections homology isomorphisms on both resolutions. The sections
square gives equality of the induced homology maps. This identifies the
existing inverse Ext-defined pushforward with the identity section-complex
comparison before passing to canonical right-derived cohomology.

For the final square choose the existing injective resolution of `F` and
its actual pushforward. `HAddEquiv_eq_of_resolution` computes both unchanged
sheaf-cohomology comparisons on these resolutions.
`resolutionComparison_compComparison` computes the canonical pushforward
comparison on the same source resolution. The private
`comparisonOfInjectiveResolution` identifies its resolution comparisons
with the inverses of `isoRightDerivedObj`. Evaluating this morphism equality
and applying the resolution-level compatibility proves the inverse square.
Applying it to the forward Ext pushforward gives the forward square.

The provenance is internal, from actual Ext adjunctions, the published
constant-sheaf and degree-zero normalizations, and canonical injective-resolution
comparisons. The result holds for all actual topological spaces related by
`e`, including the underlying homeomorphisms of nilpotent closed immersions.
Combining this comparison with the relative module comparisons to identify
actual Picard obstruction maps, and proving the exact field Picard-stack
atlas, remain further obligations.
