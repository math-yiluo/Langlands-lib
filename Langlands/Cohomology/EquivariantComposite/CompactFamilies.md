# Compact indexed families and smooth cofree representations

Author: Worker 141.

Internal support for the compact composite proof. The ordinary family presheaf
assigns arbitrary coefficient entries to the points of an open set. Its compact
sections use the existing actual germ-support submodule. Each row of an indexed
compact section has support contained in an inverse group translate of the
indexed support, hence is compact. Reading rows intertwines the indexed action
with left inverse translation on group functions of compact ordinary rows.

For a compact group under the existing stable-neighbourhood assumptions, the
saturation of a closed set is closed: the derived joint continuity permits the
standard compact-times-closed pointwise-action theorem. No Hausdorff hypothesis
is needed.

The row map is bijective after taking smooth vectors when the group is compact.
For the inverse, a uniformly smooth group function has finite range. The finite
union of the actual supports of its compact rows is a closed compact set K.
Its group saturation is closed and compact by the preceding argument and
CompactAction. Outside that saturation, every indexed coordinate vanishes,
since a zero germ of an ordinary arbitrary family forces the corresponding
entry to vanish. The open complement therefore witnesses a zero germ of the
indexed family. Its support is a closed subset of the compact saturation, hence
compact. This proves that assembling the rows supplies the inverse.

`compactFamiliesCofreeIso` bundles the resulting equivariant linear equivalence
between smooth compact sections of the actual indexed-family sheaf and the
smooth cofree representation on the module of compact ordinary families. It is
an objectwise isomorphism for every coefficient family, with arbitrary
commutative coefficients and the host task's assumptions. No naturality in the
coefficient family or derived composite identification is asserted here.
