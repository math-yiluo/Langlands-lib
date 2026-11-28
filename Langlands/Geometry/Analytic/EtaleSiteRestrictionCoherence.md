# Coherence of restriction on small analytic étale sites

For an étale map of localized analytic spaces over a complete nonarchimedean normed field, `EtaleSite.restriction` restricts a sheaf by precomposition with the functor that composes étale test objects with the map. `EtaleSite.restrictionId` and `EtaleSite.restrictionComp` use the isomorphisms of the test functors for an arrow equal to an identity or a composite. The equality formulation applies to images of identity and composite arrows under a level tower functor.

For a functor preserving the sheaf condition on the relevant sites, `EtaleSite.restrictionSheafComposeIso` exchanges this restriction with postcomposition of sheaves. Its components are identities on the underlying presheaves. `restrictionSheafComposeIso_id` and `restrictionSheafComposeIso_comp` identify the components of the two pastings using the same maps of étale tests.

The analytic small étale site and the associated site morphism are those of Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993), §4.1, p. 82. The comparisons are derived from postcomposition on étale tests.
