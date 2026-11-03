# Positive integral multiples in a possibly nonreduced relative root system

This is an internal arithmetic deduction from the Library's existing
`HasRelativeRootSystem` predicate. It does not prove that predicate for any
reductive group. In particular it has no dependency on the vector structure of
relative root subgroups, so it is available as an acyclic input to that proof.

For a crystallographic root pairing over the rationals, suppose that the root
beta is n times the root alpha, where n is a natural number. Pairing both sides
with the coroot of beta gives 2 = n m, where m is the integral root-coroot
pairing. Thus n divides 2 and is either 1 or 2. No finiteness, reducedness or
spanning condition is used in this arithmetic argument. The value n = 0 is
also excluded by the same equation.

`relativeRootMultipliers i a` records the natural-number coefficients n for
which n alpha is an actual relative root. The conditional subset theorem places
this set inside {1, 2}.

The actual-relative-root adapter uses the image equality inside
`HasRelativeRootSystem` to lift alpha and n alpha to indices of the supplied
root pairing. Equality after rationalization and the injectivity of the
submodule inclusion give the required equality of root vectors. The generic
arithmetic lemma then excludes every multiple n at least 3. If 2 alpha is
absent, it excludes every natural multiple except alpha itself.

The field and scheme universe is arbitrary. All actual-relative-root results
retain `HasRelativeRootSystem i` explicitly; they do not claim the still
separate structural existence theorem `RelativeRootSystemStatement`.
