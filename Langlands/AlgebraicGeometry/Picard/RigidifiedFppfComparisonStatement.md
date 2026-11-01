# The canonical rigidified comparison with the fppf Picard sheaf

`Langlands.AlgebraicGeometry.Picard.RigidifiedFppfComparisonStatement.{u}`
is a closed proposition about actual schemes in every universe `u`. For
`f : X → S`, it assumes that `f` is quasi-compact and quasi-separated,
that `ε : S → X` is a section with the stated section law, and that the
canonical structure-sheaf map of every base change is an isomorphism on
every open:

```
∀ (T : Over S) (U : T.left.Opens),
  IsIso (((relativeProjection f).app T).app U).
```

Its conclusion says that the specified natural transformation
`RigidifiedLineBundle.toPicardSheaf f ε section_eq` is an isomorphism.
The source is the published presheaf of actual rigidified line-bundle
isomorphism classes on `T ×_S X`, with the proved
`RigidifiedModule.pullbackCoherence`. The target is the underlying
set-valued presheaf of the published abelian-group-valued relative Picard
sheaf. That sheaf is the actual sheafification of the ordinary relative
Picard presheaf on `Scheme.fppfTopology.over S`.

All `S`-schemes occur as test schemes, including nonreduced and
non-quasi-compact schemes. The hypotheses put no restrictions on those
test schemes. The statement assumes neither representability nor a
universal bundle, a chosen dual, smoothness, properness, projectivity or a
field base. The universal structure-sheaf condition is an explicit
hypothesis of this supporting comparison statement; this file does not
remove it from any representability theorem.

The supporting construction fixes the map, rather than choosing an
unspecified isomorphism. `RigidifiedLineBundle.forgetClasses` sends a
rigidified class to the ordinary class of its underlying line bundle.
Its well-definedness follows by applying the actual forgetful functor to
a rigidified isomorphism and using the published ordinary class equality
criterion. `forgetClasses_classOf` proves its formula on representatives.
`forgetClassNatTrans` proves naturality by quotient induction, the
ordinary geometric pullback formula, and `pullbackForgetIso`. Thus it
uses the actual pullback of each rigidified family.

`toPicardSheaf` composes that transformation with the actual
abelian-group sheafification unit, after forgetting group structure.
`toPicardSheaf_app_classOf` proves that on every actual family `(L, α)`
its value is the unit applied to the ordinary class of `L`.
`map_toPicardSheaf_classOf` proves compatibility of this formula with
every morphism of test schemes, using the constructed natural
transformation.

`toClassPicardSheaf` instead composes with the actual set-valued
sheafification unit. Its component formula is
`toClassPicardSheaf_app_classOf`, whose right-hand side is the published
`RelativePicard.sheafClassOf` of the underlying line bundle.
`toPicardSheaf_forgetSheafIso_hom` proves that the published canonical
group/set comparison `RelativePicard.forgetSheafIso` identifies these
two maps. It follows directly from that comparison's proved unit
compatibility. Both presheaves have class universe `u+1`, so no universe
reduction or change of isomorphism classes is used.

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft, Chapter VI §1, Definition (6.1) and paragraph (6.2),
printed pp.87–89 (PDF pp.91–93), registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Worker 149 read and hash-verified these pages and viewed the displayed
formulas on PDF pp.92–93. A bounded source-specific errata search found
no relevant erratum.

Definition (6.1) supplies the ordinary presheaf and its fppf
sheafification. Paragraph (6.2) assumes precisely the qcqs, universal
canonical structure-sheaf and section hypotheses, defines rigidified
bundles and arbitrary geometric pullback, and identifies their class
functor with the Picard sheaf. Its normalization sends a line bundle to
`L ⊗ p_T* (ε_T* L)⁻¹`. A line bundle pulled back from the base has
trivial class after fppf sheafification, which explains why the
comparison in the reverse direction is precisely forgetting
rigidification and taking the ordinary sheafification image. This is
the canonical-map interpretation of the source, using the published
parameter-first fibre-product convention and its canonical symmetry.

The quotient map, naturality, component formulas and compatibility with
group/set sheafification are internal consequences of the published
definitions, proved in this file as described above. The substantive
isomorphism assertion under the geometric hypotheses is a Prop-valued
statement only. Its proof, including the required descent and
normalization arguments, is a separate obligation.
