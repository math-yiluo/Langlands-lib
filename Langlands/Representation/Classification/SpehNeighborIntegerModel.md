# Integer models of rank-lower neighboring rectangle labels

This derived interface reconstructs an actual multisegment as the realization of
a finite multiset of integer intervals. It supports the neighboring Speh argument
of Badulescu (2014), Theorem 1(b)(ii), and uses the imported concrete realization
and containment-count rank order. It is an internal adapter, not a new
classification or duality assertion.

For an actual segment of positive length `n` beginning at the integer coordinate
`z`, the interval `[z,z+n-1]` has the same base and length. Segment extensionality
identifies its realization with the given segment. Multiset induction applies
this construction to each occurrence, retaining repeated segments and the empty
input. `integerModel` chooses one such multisegment; `realize_integerModel`
proves exact equality with the original actual multisegment.

For any actual label rank-lower than the union `a(l,k+1)+a(l,k-1)`, the inherited
beginning multiset gives beginnings at coordinates `y+j`, where
`y=(-k-l+1)/2` and `0 ≤ j ≤ l`. At the MW ending offset
`x=(k-l-1)/2`, these are `x+(j+1-k)`, an integral translate.
`neighborIntegerModel` therefore applies the generic construction without any
additional hypothesis about the actual label. Its realization is exactly that
label.

The last two lemmas apply the imported first-round endpoint argument to this
integer model. They bound both the integer dual's interval lengths and its
realization's actual segment lengths by `l`. They retain the explicit
`EndingBound` premise, which controls recursive outputs after the first round.
The statements do not establish that premise or identify the computed dual with
the actual Aubert image. They do not prove the neighboring Speh irreducibility
target.
