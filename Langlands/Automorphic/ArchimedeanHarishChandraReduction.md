# Harish-Chandra finiteness on archimedean slices

Borel–Jacquet, *Automorphic forms and automorphic representations* (1979), §4.3
(1)–(2) and (i), printed p. 195 (PDF p. 190 of `borel-jacquet-1979-automorphic`),
restrict automorphic forms to finitely many slices at infinity and apply the
real-group finiteness theorem of §1.7, printed p. 191 (PDF p. 186). The theorem
there cites Harish-Chandra, *Automorphic forms on semisimple Lie groups* (1968),
Chapter I, §2, Theorem 1, printed p. 8. Borel–Jacquet explain the role of the
center for reductive groups in §1.6(1) and §1.7.

For a finite component `b` and level `L`, `archimedeanSliceStabilizer` is the
infinite image of the rational elements whose finite component lies in
`b L b⁻¹`. The space `archimedeanAnnihilatedForms` consists of smooth functions
on the infinite general linear group, left invariant under the specified
subgroup, of polynomial growth for `matrixHeight`, and annihilated by the
specified center ideal. The compact multiplicity space consists of equivariant
linear maps into this space. Every vector in such an image has a
finite-dimensional orbit span because its source is finite-dimensional.

`ArchimedeanHarishChandraFinitenessStatement` states finite dimensionality of
these multiplicity spaces for the slice stabilizers of compact open levels and
cofinite center ideals. It packages the archimedean input needed for §4.3(i),
using the same complex enveloping center, standard compact subgroup and
arbitrary finite-dimensional source representation as the adelic statement. The
formulation in terms of equivariant maps is derived from the fixed-type spaces
of §4.3. It lets the reduction work directly with the source representation in
the Lean target.

Restriction of an actual adelic form at `b` has the required left invariance by
rational covariance and right level invariance. Growth is the corresponding
slice condition in the definition of a form. The actual enveloping and compact
right actions restrict to their archimedean counterparts. Restriction on
multiplicity maps is linear and injective since the selected slice evaluations
are faithful on the level-fixed families. The compact equivariance identities
apply to every source representation in the adelic statement.

The theorem `harishChandraFiniteness_of_archimedean` takes
`ArchimedeanHarishChandraFinitenessStatement` as its hypothesis. For the given open
subgroup it chooses a compact open subgroup contained in it by
`OperatorRealization.exists_compact_openSubgroup_le`. Fixity by the original
subgroup implies fixity by the smaller one, giving a linear inclusion with the
same center ideal and compact equivariance. The slice restriction at the
smaller level embeds its multiplicity space into the product indexed by
`FiniteLevelDoubleCosets`. This index is finite by
`finite_finiteLevelDoubleCosets`, and the archimedean hypothesis gives finite
dimensionality of every factor. The composite injection from the original
multiplicity space into this finite-dimensional product proves the adelic
conclusion.
