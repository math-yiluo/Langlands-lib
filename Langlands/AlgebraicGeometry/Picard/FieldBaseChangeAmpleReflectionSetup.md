# Topological prerequisites for field base change ampleness reflection

This private supporting development proves only compactness and
quasi-separatedness of the original scheme when the specified line bundle
becomes ample after an arbitrary field extension. It does not prove reflection
of ampleness or supply sections over the original scheme.

The first lemma is an internal deduction from Mathlib's definitions: pull back
two affine opens along a quasi-compact surjection, intersect their compact open
preimages in the quasi-separated source, and take the continuous image. By
surjectivity this image is the original intersection. No separatedness or
flatness is needed for this topological argument.

A morphism between spectra of fields is surjective because its source is
nonempty and its target has one point. Surjectivity and affineness survive
base change. The published ampleness API gives compactness and
quasi-separatedness of the base changed scheme. Compactness descends along
the continuous surjection; the preceding lemma gives quasi-separatedness.

All fields, schemes and line bundles remain in the arbitrary universe `u`.
The original reflection statement and its import closure are unchanged.
