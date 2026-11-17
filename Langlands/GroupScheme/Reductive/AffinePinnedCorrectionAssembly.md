# Assembly of actual local pinned corrections

For affine pinned models `M`, `N`, a common scheme `T` with base maps `f`,
`g`, and an actual comparison `e`, `FppfPinnedCorrection e` records a single
flat, surjective, locally finitely presented morphism `p : U ⟶ T` and an
actual section `c` of the target pullback group such that
`pullComparison e p ≪≫ innerIso c` is concretely locally pinned.
`FppfPinnedCorrection.ofCover` constructs this object from any small fppf
covering family on which `HasPinnedCorrection` holds. The predicate
`HasPinnedCorrection` means existence of an actual target section giving a
concretely locally pinned correction on the current common scheme.

The construction imposes no finiteness, connectedness, affineness or
nonemptiness condition on the common scheme or the covering schemes. It uses
their scheme coproduct, so it also handles the empty covering family of an
empty scheme. Root relabellings may vary between the covering pieces.

This is an internal assembly from the existing disjoint-component point
construction, normalized pullback identities and
`AffinePinnedDisjointPinning`:

1. On a disjoint decomposition `q i : Z i ⟶ T`, `Disjoint.basePoint` first
   converts a section of the direct target pullback on each `Z i` to the
   iterated pullback through `baseChangeCompIso`. The equivalence
   `baseChangeBasePointsEquiv` projects it to a relative point of the
   group over `T`, and the existing disjoint relative-point construction
   assembles these into an actual base section.
   `pullBasePoint_basePoint` proves exact recovery under normalized
   component pullback. Its proof uses the component factorization law,
   the first-projection formula for a pulled-back base section, and
   pullback extensionality.
2. `Disjoint.corrected_isLocallyPinned` pulls the corrected comparison to
   each component. The identities `pullComparison_trans`,
   `pullComparison_inner` and the section-recovery theorem identify its
   restriction with the supplied pinned correction. The
   disjoint-component pinning-detection theorem then proves the global
   assertion.
3. `pinnedCorrection_pullComparison_comp_iff` retains the actual
   direct-versus-iterated normalized pullback identifications through
   `pullComparisonAlong` tower coherence.
4. `FppfPinnedCorrection.ofCover` takes the coproduct of the covering
   schemes. Its projection is flat and locally finitely presented by
   the collapsed-cover property, and is surjective by the original
   covering condition. The preceding coherence lemma and the coproduct
   component equations convert each local witness to the exact
   normalized component endpoints. Step 2 then gives the required
   global corrected comparison and actual target section on the
   coproduct.

`FppfPinnedCorrection.comparison` is this concretely pinned comparison.
`sourcePoint` transports the inverse target section through the inverse
original pulled-back comparison. The theorem `innerIso_sourcePoint` proves
that its inner automorphism is exactly
`pullComparison e p ≪≫ comparison.symm`. The proof applies the naturality
of inner conjugation under a group homomorphism, identifies the transported
section after composing with the original comparison, and cancels that
isomorphism. It uses the inner-automorphism formula for an inverse section.

Finally, `fppfLocalPinnedNormalization_of_pinnedCorrections` proves the exact
`FppfLocalPinnedNormalizationExistenceStatement` from the hypothesis that a
`FppfPinnedCorrection` exists for every comparison. It unpacks the actual
cover, pinned comparison and source point just constructed. This is a
conditional reduction: this module does not prove existence of the initial
local correction witnesses for arbitrary comparisons, nor the parent
comparison-existence statement.
