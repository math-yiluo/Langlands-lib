# Rational points of dominant pointed products

Internal helpers for the proof of the field step of KP Lemma A.4.26. Over an
algebraically closed field, a rational point in the topological image of a
finite-type morphism lifts to a rational point: its nonempty closed fibre has
a closed point, which is rational by the Nullstellensatz. A dominant affine
finite-type parametrization of a smooth connected affine group has image
containing a nonempty open set by Chevalley. That open and its translate
intersect in a rational point. Thus any abstract subgroup containing the
parametrized points contains the whole group of rational points.

The declarations are:

- `exists_point_lift`: both schemes are locally of finite type over the
  algebraically closed field. The fibre over the rational point is closed,
  and the Jacobson property gives a closed point in it. The closed-point
  correspondence then gives the lifting section.
- `points_mem_of_dominant`: the parameter scheme is affine and locally of
  finite type; the target group is smooth, affine and connected. For an
  arbitrary point `x`, choose a rational point `a` in the intersection of the
  open set and its inverse image under right multiplication by `x`. Both
  `a` and `a*x` lift through the parameter morphism, so their images belong
  to the given subgroup. Its closure under inverse and multiplication puts
  the image of `x` in it as well.
- `generatedImage_range_le`: apply the preceding lemma to the dominant finite
  power supplied by `GeneratedImage.HasSmoothConnectedGeneration`. Each
  parametrized point is an ordered product of source images, so belongs to
  any subgroup containing those images. The source here is affine,
  geometrically integral and locally of finite type.

These are derived internal lemmas using the Mathlib algebraically closed point
correspondence and the Library's constructibility, pointed generation and
smooth connected geometry results. The open-set argument is the one in Borel,
*Linear Algebraic Groups*, second enlarged edition (1991), Proposition 1.3(a),
printed p. 47 / PDF p. 58, also used in the proof of Proposition 2.2,
printed pp. 57–58 / PDF pp. 68–69. The source ID is
`borel-1991-linear-algebraic-groups-second`, SHA-256
`7c62e6b8fdb26c0490a3cce4afbd8c9d0c02fb90a1f03e21699bd21ecdfca16e`.
