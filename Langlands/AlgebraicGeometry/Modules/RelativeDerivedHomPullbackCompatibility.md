# Compatibility of relative sections with pullback and counit

This internal supporting unit compares the actual relative sections map with inverse image and the abelian-sheaf adjunction counit for any morphism `f : Y ⟶ X` over `Spec R`. It derives from the imported `homGlobalSectionsIso_pullback_counit` and the definitions of `relativeSectionsHomIso` and `relativePushforwardSectionsIso`; no external statement is transcribed.

`relativeSectionsHomIso_pullback` identifies the following two maps on a section of the underlying abelian group of `Γ_X(f_* M)`: first identify it with a Hom from the constant integer sheaf, apply inverse image, precompose with `constantPullbackIso.inv`, and postcompose with the counit; or first apply the actual relative pushforward/sections isomorphism and then the Hom/sections isomorphism on `Y`.

The proof applies the inverse Hom/sections comparison, uses the imported adjunction identity and cancels the comparison isomorphisms. It evaluates the module pushforward composition and equality comparisons on top sections, where their maps are identities.

`relativeHomComplexPullback` names the chain map obtained by applying inverse image to each Hom, precomposing with `constantPullbackIso.inv`, and postcomposing with the actual counit.

`relativeSectionsComplexIso_pullback` proves the resulting equality of chain maps on every bounded below module complex. Its left side uses `sectionsComplexIso`, the exact inverse-image Hom-complex map and `relativePullbackCounit`; its right side forgets scalars on `pullbackSectionsComplexIso` and then uses `sectionsComplexIso` on `Y`. Equality follows degree by degree from the ordinary sections identity. Neither theorem assumes that module inverse image is exact or that module direct image preserves injectives. This unit does not yet assert compatibility of the derived cohomology comparisons.
