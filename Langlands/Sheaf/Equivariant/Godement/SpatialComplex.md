# Spatial maps of full equivariant Godement complexes

This is an internal specialization of
`Langlands.Cohomology.CokernelComplex.Lax` to the existing full equivariant
Godement construction. Its inputs are actual continuous equivariant maps and
the previously constructed neighborhood-colimit stalk maps. No higher
comparison map is supplied as an assumption.

The current module uses the existing Godement complex and abelian-category
instances: ring, group, spaces and module carriers have a common universe `u`.
Coefficients are arbitrary commutative-ring modules. The point actions have
continuous constant translations. No group topology or smoothness is imposed.

For an equivariant continuous map `f : X → Y` and a full equivariant module
sheaf `F` on `X`, `Spatial.complexMap` is a genuine chain map
`Godement_Y(f_*F) → f_*Godement_X(F)`. The direct image is the complete
label-preserving direct image on ordinary open sets, and its action on complexes
is degreewise. The source and target are the existing `Godement.complex`
objects, without a new choice of complex.

The construction specializes `Lax.complexMap` with `Spatial.zeroNatTrans` and
the proved `Spatial.coaugmentation_zeroMap` square. Direct image preserves zero
morphisms because it is additive. At every residual stage the generic map
descends through the source cokernel after precomposition, so the construction
does not require direct image to preserve cokernels. The resulting degree maps
commute with the actual differentials.

`complexNatTrans` packages naturality in every original transport-natural sheaf
morphism, and `complexMap_naturality` states its square explicitly.
`complexMap_f_zero` identifies degree zero with the original spatial
stalk-family map. `augmentation_complexMap` identifies the image of the actual
family-of-germs augmentation with direct image of the source augmentation.
`complexMap_id` and `complexMap_comp` follow from the generic cokernel
uniqueness laws and the proved spatial degree-zero identity and composition
laws. The composite is the comparison for `g` followed by `g_*` applied to the
comparison for `f`, as dictated by the stalk maps.

No properness assumption is needed for this sheaf-level chain comparison.
This module establishes neither an isomorphism nor a quasi-isomorphism.
Acyclicity, a derived-functor identification, smoothness, etale or analytic
realization, arithmetic coefficients and towers, and the actual Harris
specialization remain separate obligations.
