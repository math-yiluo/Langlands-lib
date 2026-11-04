# Comparison of fixed-family and arbitrary integral Harris class images

This internal unit compares the normalized class image of a fixed polarized
Harris family with the existing image allowing arbitrary integral-action
representatives. It uses the same universe-zero arithmetic data, fixed abelian
scheme, supplied dual witness and polarization, prescribed dimension and named
prerequisites as the fixed-family image presheaf. The test category is its full
admissible subcategory over the fixed family base.

`harrisIntegralCMLevelFamilyCondition_integral` proves that a compatible class
family satisfying the fixed-family image condition satisfies the existing
`IntegralCMFamilyCondition`. At each actual geometric point, it takes the raw
orbit supplied by the condition and the existing
`harrisIntegralCMFullActionLevelRepresentative` on the very same direct
pullback of the fixed family. The family-evaluation formula identifies this
representative's normalized class with the given family value. The argument
uses no new integralization or existence assertion and retains the existing
rational-isogeny equivalence relation.

`harrisIntegralCMLevelFamilyImageToIntegral` packages that implication into a
natural transformation of presheaves. It retains the normalized class family
and supplies the proved integral-image witness. Naturality in every test map
and original Harris level arrow is reflexive because both image presheaves
restrict the same actual normalized pullback and transporter maps. The final
inclusion equality proves that this factorization has exactly the existing
fixed-family inclusion as its underlying map to the original normalized
presheaf.

The provenance is internal: actual integral representatives, the proved family
evaluation law and subtype inclusions supply all comparisons. This unit
asserts no converse or surjectivity, and no representing geometry, smoothness,
projectivity or output admissibility. Those remain obligations of the host
representability task.
