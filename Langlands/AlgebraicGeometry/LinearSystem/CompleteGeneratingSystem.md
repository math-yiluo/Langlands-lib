# Complete generating bases and equality of projective images

`CompleteGeneratingSystem p L` consists of a basis of all global sections of
an actual line bundle `L` on a scheme `X` over a field `K`. The index set is
`Fin (n + 1)` and the scalars are those from `p : X ⟶ Spec K`. At every scheme
point there is a basis section with nonzero residue. `map` is the actual
`linearSystemMap` of the basis; it is over `Spec K`. It is finite when `p` is
proper and `L` is ample, by `isFinite_linearSystemMap_of_isAmple`.

The two image-comparison lemmas work over any field. At a rational point `x`
choose a basis section `s_j` generating the fibre. The pencil tests
`s_i - α_i s_j` with `α_i = (s_i/s_j)(x)` vanish at `x`. If every section
vanishing at `x` also vanishes at a rational point `y`, these tests vanish at
`y`. The generating hypothesis implies `s_j` is nonzero at `y`: otherwise
every `s_i` would vanish by the pencil tests. The coordinate ratios at `x` and
`y` then agree, so the projective images agree as maps from the field spectrum.
For a dual-number point `t` over `x`, the same chart contains both `t` and the
constant lift of `x`. If every section vanishing at `x` pulls back to zero on
the entire dual-number spectrum along `t`, the pencil tests give the same
coordinate ratios there as for the constant lift. This gives equality of
maps from the dual-number spectrum, not just equality at its underlying
point. These are the pencil arguments in `LinearSystemMorphismProof`,
applied directly to the specified map and to the vanishing hypotheses on
all sections.

Over an algebraically closed field, with `p` locally of finite type, rational
generation suffices to show a basis generates everywhere. If the union of the
basis generation opens omitted a point, its closed complement would contain
a closed point by the Jacobson property. This point has a rational lift `y`.
By hypothesis there is a section `s` nonvanishing at `y`. Each basis section
has zero ratio to `s` there. The basis expansion of `s` and linearity of the
ratio then force `s` to vanish there, a contradiction. For a nonempty scheme
with finite-dimensional section space, a rational point exists, and rational
generation makes the section dimension positive. `Module.finBasisOfFinrankEq`
provides the required indexing of a full basis and the preceding argument
proves its generation condition.

This is internal infrastructure combining the Library's actual linear-system
map, ratio lemmas and Jacobson closed-point dictionary. No point or tangent
separation theorem is asserted.
