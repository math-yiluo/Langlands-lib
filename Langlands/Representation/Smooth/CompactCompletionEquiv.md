# Completion of an intertwining equivalence

This internal supporting construction extends `CompactCompletion.map` to an
actual `Representation.Equiv`. The topological group and the two complex module
carriers have independent universes; both representations are smooth.

`CompactCompletion.equiv` applies the given intertwining equivalence `E` to
each component of a compatible family. The existing completion map proves
compatibility using commutation with genuine compact averaging. Applying the
inverse intertwiner componentwise gives the inverse, since the two identities
for `E` hold at each compact index. The component formulas are definitional.

This is the functorial transport of the compatible-family completion used
in the parent Levi completion construction. It asserts no parabolic
structure or Jacquet comparison.
