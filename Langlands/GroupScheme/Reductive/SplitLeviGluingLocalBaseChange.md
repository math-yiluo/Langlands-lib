# Local Levi comparisons and simple directions after field extension

This internal support module pulls back the actual local Levi comparisons and the actual generic chamber with its indexed rank-one kernel directions. The simple-root indices are transported through the split-torus character lattice equivalence. It provides the local and direction data needed to assemble a field extension of a `SimpleComparisonGraph`; it does not yet assemble that graph or prove a projection isomorphism.

Throughout, `k : Type u` and `K : Type u` are fields with a specified `Algebra k K`. The field extension is arbitrary: no separability, finiteness, perfectness, algebraic closedness or characteristic restriction is imposed. The actual group-scheme and commutative-group-scheme pullback functors use `algebraBaseMap k K`.

## Actual local comparisons

`baseChange_groupHom_comp K ν i` identifies the dynamic pullback of the ambient cocharacter `groupHom ν ≫ i` with the pulled-back torus cocharacter followed by the pulled-back inclusion. It uses the existing identification of cocharacter lattice pullback with dynamic pullback and functoriality of composition.

`LocalComparison.baseChange K L` takes an actual `LocalComparison i₁ i₂ ν` over the original common commutative group scheme `T`. It returns an actual comparison for the two pulled-back inclusions and `cocharacterLattice.baseChange ν`. Its two source groups, closed inclusions and torus factorizations are their actual pullbacks. Its comparison is the actual pullback of `L.iso`.

Both full centralizer representations survive base change by the published `Dynamic.isRepresentedBy_centralizer_baseChange`; the cocharacter identity above identifies their targets with the required torus-cocharacter composites. Functoriality preserves the two torus factorization squares and the comparison's common-torus square. Thus the result includes an actual isomorphism with its required compatibility, rather than only equalities of rational points. This local comparison transport requires only the supplied record and the field extension; it does not add splitness, reductivity, root data or a new local isomorphism as an assumption.

## Actual simple roots and directions

The remaining results take an affine ambient group `G₁` locally of finite type, an actual inclusion `i : T.toGrp ⟶ G₁`, and splitness `hT : IsSplitTorus T.toGrp`. No maximality or reductivity assumption on the ambient group is required.

`mem_positiveRelativeRoots_baseChange_iff K hT i ν α` proves that the pullback of `α` is positive for the pulled-back `ν` exactly when `α` is positive for `ν`. The published actual root-support comparison preserves and reflects root membership, and the published lattice-pairing comparison preserves the integer pairing.

`mem_simpleRelativeRoots_baseChange_iff` strengthens this to the intrinsic simple roots, defined as positive roots which are not a sum of two positive roots. The character lattice pullback is an additive equivalence. It sends a decomposition into positive roots to such a decomposition and, conversely, pulls every proposed decomposition back through its surjectivity and injectivity. Hence this result does not require a reduced root system or a supplied root datum.

`simpleRootsBaseChangeEquiv K hT i ν` is the resulting actual equivalence of simple-root index types. Its value is character lattice pullback on the underlying root.

The support result `LeviGluing.IsGenericCocharacter.baseChange` preserves genericity: every extended actual root comes from an original root through the character lattice equivalence, and its nonzero pairing remains the same integer. `IsRankOneDirection.baseChange` preserves the exact rank-one direction condition used in the local gluing premise. Two extended roots pairing to zero pull back to original roots with zero pairings. Independence of their extended pair would imply independence of the original pair under the induced integral linear map, contradicting the original rank-one condition. No additional condition on coroots, characteristic or reducedness is used.

The primary entry `SimpleRootDirections.baseChange K hT i S` constructs a full `SimpleRootDirections` record for the actual pulled-back inclusion. Its chamber is the actual cocharacter pullback. Its direction at an extended simple root is the pullback of the direction at its preimage under `simpleRootsBaseChangeEquiv`. Genericity is the preceding transport theorem. The unchanged pairing proves annihilation of the indexed root, and the preceding rank-one transport proves the required direction condition. This constructs directions from the original record and splitness; it assumes neither a chosen extended chamber nor new extended local comparison maps.

## Provenance and limits

This is an internal derivation from the published split character/cocharacter lattice equivalences and pairing comparison, actual adjoint root-support base change, dynamic centralizer representation base change, and the definitions of the earlier local comparison and direction records. All subgroup-functor representations are on every scheme test.

The actual generated envelope still has to be reindexed by the transported simple-root equivalence to assemble the full extended `SimpleComparisonGraph`. Graph projection invertibility, exact Levi gluing and the exact arbitrary-field common-torus isomorphism theorem remain separate obligations. The module does not derive the original rank-one local comparisons from equality of root data.
