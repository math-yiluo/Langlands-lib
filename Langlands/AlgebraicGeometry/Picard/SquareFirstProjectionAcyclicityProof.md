# Total acyclicity from acyclicity on first-projection fibres

Authors: Worker 1013 and Worker 975.

The theorem `Langlands.AbelianScheme.algClosedFieldSquareFirstProjectionAcyclicity.{u}`
proves the published
`AlgClosedFieldSquareFirstProjectionAcyclicityStatement.{u}` exactly. For an
abelian scheme `A` over an algebraically closed field `K` and a line bundle
`Q` on `A ×_K A`, acyclicity of the restrictions to every rational fibre
`{x} × A` implies acyclicity of `Q` on the square, in every natural degree.
The field, characteristic and universe are arbitrary; dimension zero and
degree zero are included.

The proof is an internal deduction from the published universal-perfect-sections,
rational-fibre, fibre-identification and pushforward-vanishing theorems. It
adds no geometric construction or hypothesis to the statement. Its source
context is the first Leray calculation in Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, Proposition (7.21), printed p.106 / PDF p.110, as detailed
in the paired statement Markdown. The registered original is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

## Implemented proof

Let `p₁ := pullback.fst A.X.hom A.X.hom` and let `U` be the whole open of
`A.X.left`. The map `p₁` is smooth and proper by base change from the abelian
scheme structure morphism, and `A.X.hom` is locally of finite type by
smoothness. These facts are supplied by the existing instances.

Apply
`DerivedSections.isZero_pullback_higherDirectImage_of_rationalFibres` to
`p₁`, `Q` and `U`. Its universal-perfect-sections premise is discharged by
the published theorem `universalPerfectSections`, whose complete type is
`UniversalPerfectSectionsStatement.{u}`. Thus no perfectness or base-change
assertion is assumed. The rational-fibre theorem works over affine opens,
uses the Nullstellensatz to turn maximal-ideal quotient points into rational
points, and combines universal perfect representatives with the algebraic
residue-field acyclicity criterion and affine-open detection of higher direct
images. This replaces the jump-locus argument described as an intended route
in the statement Markdown.

For a rational point `x : Spec K ⟶ U` with its structure-map equation,
`Over.homMk (x ≫ U.ι)` defines the corresponding rational point `x'` of `A`.
The hypothesis gives vanishing for the restriction of `Q` along the section
inclusion with components `(A.X.hom ≫ x'.left, 𝟙 A.X.left)`. The published
`squareFirstFibreCohomologyIso` identifies that cohomology with the actual
pullback fibre cohomology of `p₁`. Transporting `IsZero` across this
isomorphism supplies the rational-fibre premise in every natural degree.
Line-bundle pullback has ordinary module pullback as its underlying object.

We obtain that every `higherDirectImage p₁ q` of `Q.obj` becomes zero after
pullback along `U.ι`. Pull it back once more along
`A.X.left.topIso.inv`. The ordinary module pullback composition, congruence
and identity isomorphisms identify the result with the higher direct image
itself. Hence all higher direct images vanish, including degree zero.

Finally,
`DerivedSections.isZero_relativeCohomology_of_higherDirectImage` gives
vanishing of every relative cohomology group along
`p₁ ≫ A.X.hom`, the square's structure morphism in the target. That published
lemma uses the proved pushforward comparison, pushforward injective
acyclicity, and vanishing of the degree-zero pushforward. This supplies the
cohomological composition step in the source's first Leray calculation.

The proof uses only the fibrewise hypothesis in the target and the named
published results. It does not use the downstream translation-difference
lifting theorem or any dual or Picard scheme.
