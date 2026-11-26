# A global Hecke twist meeting lower and upper conductor bounds

`GlobalHeckeNormTwistDepthStatement` fixes a cyclic Galois extension of
number fields, a distinguished lower finite place, and a finite set of
other lower finite places. The restrictions of a finite family of lower
Hecke characters must exhaust the norm-trivial characters at every upper
completion above that set. Fix conductor bounds on the lower places and
on each of the upper places.

There is a finite-order Hecke character trivial at the distinguished lower
place, with norm pullback trivial at every place above it. At each finite
place in the auxiliary set, multiplying its component by any member of
the lower character family gives a quasicharacter of conductor at least the
lower bound. Its idelic norm pullback has local conductor at least the
upper bound at every corresponding upper place.

For each upper completion, the local norm conductor formula gives a
sufficient bound on the original lower twist using
`deepNormTwistConductors`. Use the sum of the bounds over the places above
each lower place and invoke the Library's finite-order Hecke character
prescription `ramifiedTwistIsolation`. Nontriviality on the prescribed
principal units implies the strict lower conductor bound. The local
component of the idelic norm pullback is the completed norm pullback,
which gives its upper bound and its triviality above the distinguished place.
