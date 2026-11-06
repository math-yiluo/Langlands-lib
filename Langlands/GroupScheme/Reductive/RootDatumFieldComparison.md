# Comparing full root data over arbitrary fields

This derived internal unit uses the Library's actual split-torus lattice
transport and its geometric root-data comparison. It supports the
generic-fibre comparison in the strict-Henselian isomorphism problem.

`SplitRootDatum.baseChangeEquiv` identifies a root datum with its transported
datum along any map between spectra of integral domains. The character map
is actual character pullback, the contravariant cocharacter map is the
inverse of actual cocharacter pullback, and the root index map is the
identity. The proof checks the full pairing and both roots and coroots from
the definition of `SplitRootDatum.baseChange`. Its two formula theorems
record the character map and the cancellation of cocharacter pullback.
The lattice equivalences cover the entire lattices, including central
directions. No root-span generation condition is assumed.

`nonempty_rootDatumEquiv_of_iso` compares supplied actual root data for
isomorphic connected reductive groups over an arbitrary field, on arbitrary
chosen split maximal tori. The proof extends both groups, both tori, their
inclusions and their supplied root data to an algebraic closure. The
published field-extension, maximal-torus base-change and root-datum
base-change theorems give the required geometric hypotheses. The geometric
comparison theorem gives an equivalence there. Composing with the two
canonical lattice transport equivalences gives an equivalence of the
original full root data.

The base rings have arbitrary universe `u`; the transport construction
allows root indices in a separate universe `v`. The comparison theorem has
root indices in `u`, matching the published geometric inputs. This unit
neither constructs an integral split root datum nor proves integral
classification. It also makes no extension claim for a chosen generic
isomorphism.
