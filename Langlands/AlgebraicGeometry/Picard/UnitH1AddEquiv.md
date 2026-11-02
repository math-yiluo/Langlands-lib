# Additivity of the actual unit H¹ classification

This internal construction continues the published actual unit-sheaf H¹
classification. It uses the original scheme Picard group and actual Ext-defined
`Sheaf.H` of the structure-sheaf units.

`UnitCechLineBundle.pairUnits_add` identifies addition of ordered unit cochains
with multiplication of overlap units. Its proof applies additivity of unit
restriction. On any full open cover, `tensorIso` applies the published
`CocycleGluing.tensorIso` through that equality. Thus `lineBundle_classOf_add`
computes the existing Picard class of the gluing of a sum: `localizedTensorIso`
identifies the explicit sheaf tensor with the categorical tensor, and
`Picard.classOf_tensor` computes its class.

For finite full covers, `UnitCechH1Comparison.classOfCocycle_add` follows from
additivity of the published actual cohomology comparison map. These constructions
are internal consequences of the cited published Lean dependencies; they
introduce no new literature translation.

For every compact scheme `X : Scheme.{u}`, `Group.unitCohomologyClass_add`
proves additivity of the published classifier. Choose finite presentations of
line-bundle representatives of two given Picard classes. Restrict both closed
cochains to their finite common intersection cover. The published refinement and
presentation recovery isomorphisms show that the two resulting glued bundles
still represent the given classes. The sum gluing represents their sum by
`lineBundle_classOf_add`; the published classification computes its actual H¹
class, and `classOfCocycle_add` identifies it with the sum of the two values.
The common cover need not have affine intersections.

`Group.unitCohomologyAddEquiv X` equips exactly the published underlying-type
equivalence `Group.unitCohomologyEquiv X` with this additive compatibility:

```text
Group X ≃+ Sheaf.H (UnitCechH1Comparison.unitSheaf X) 1.
```

Its value is the existing `Group.unitCohomologyClass`; on the class of an actual
line bundle it computes that bundle's published presentation-independent H¹
class. The zero and negative computations follow from the additive equivalence.

The universe `u` is arbitrary. Only the final classification and its group
compatibility require compactness. The tensor step uses the published actual
sheaf tensor and its comparison with the categorical tensor, and requires no
extra tensor-preservation assumption. No smoothness, properness, separatedness
or ground-field hypothesis is imposed. Naturality in scheme morphisms,
deformation theory and fppf Picard-sheaf representability are further
obligations; this module does not assert them.
