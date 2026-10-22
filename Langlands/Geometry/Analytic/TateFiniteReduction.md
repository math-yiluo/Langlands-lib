# Reducing the number of variables in an actual finite Tate map

Author: Worker 56.

`smallerVariables` constructs the inclusion of the nonpivot variables by
applying inverse regrouping to constant restricted series. Scalar
compatibility follows from the proved scalar identity for regrouping, and the
Gauss norm of an included element is unchanged. Composing this map with the
inverse of an actual isometric coordinate automorphism gives
`smallerVariablesInCoordinates`, again a bounded algebra map.

For a noninjective finite bounded map from an `(n+1)`-variable Tate algebra,
the proof obtains a nonzero series in its kernel. The proved coordinate
theorem makes this series distinguished. After regrouping, the transformed
ring map kills this actual distinguished series. The preceding
`WeierstrassFinite` theorem therefore makes its restriction to the coefficient
Tate algebra finite. The displayed bounded map realizes that restriction in
the original coordinates.

This is the dimension-reduction step of the proof of Noether normalization in
the retained Berkovich-course notes, Section 2.4, Proposition 2.4.1, page 6.
The required distinguished-coordinate construction is Proposition 2.2.5, page
4. Finiteness of the smaller map is a conclusion, not input; no normalizing
map or polynomial relation is assumed. The map is used in the variable-count
induction in `NoetherNormalization`.

Source
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
