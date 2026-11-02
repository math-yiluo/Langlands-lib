# Actual segment constituents and graded exact-K0 classes

The variable `Δ` is the published actual segment model
`T.Segment.{max uF uV,uF}`, with length `k=Δ.length` and total rank
`n=Δ.degree`. The coefficient field is complex, and `F,T` are the current
`PadicField` models. All representation carriers lie in `Type (max uF uV)`;
the field and carrier universes remain independent.

`segmentSocleObject` chooses an actual smooth representation from the
published `Classification.segmentZelevinskyConstituentExistence`;
`segmentSpecialObject` chooses one from
`Classification.segmentSpecialConstituentExistence`. Their specifications
are the actual strong relations `T.IsSegmentSocle` and `T.IsSegmentHead`
for the increasing normalized segment induction. In Zelevinsky's notation
they are respectively `⟨Δ⟩` and `⟨Δ⟩ᵗ`, the special quotient. These choices
use existing existence theorems and are not new existence axioms or labels.
Irreducibility gives their finite group-algebra length.

`segmentSocleObject_iso` and `segmentSpecialObject_iso` prove actual
categorical isomorphisms with any supplied strong constituents of the same
segment. The proof transports to a common actual representative of the
initial supercuspidal class, then uses the canonical socle or head
equivalences. This step is performed before passing to K0.
The class transport theorems then apply the published isomorphism
invariance of the actual exact Grothendieck group.

`segmentSocleClass` and `segmentSpecialClass` are homogeneous exact K0
classes. `gradedSegmentSocle` and `gradedSegmentSpecial` include them in
the actual graded direct sum. The final theorem reuses the existing
`Langlands.Aubert.segmentSocleHead` on these actual objects and retains
the unadjusted sign `(-1)^(n-k)`. That theorem is equality of virtual
classes, not an asserted isomorphism from a virtual Aubert sum to a module.
No support-sign adjustment or whole-ring comparison is proved here.

Original sources are Zelevinsky 1980, §§3.1 and 9.1, printed pp.180–181
and 197, and Aubert 1995, Remark 2.2 and Theorem 2.3, printed pp.2184–2185.
The existing upper-parabolic, positive half-modulus, right-translation
models and residue-normalized `ν=|det|` are retained.

The actual mathematical dependencies include the published two segment
constituent-existence proofs and their helper chains: common-image
multiplicity one, segment and cuspidal Jacquet multiplicity, segment
Jacquet and tensor reversal, segment induction admissibility, cuspidal
Jacquet exactness, upper subrepresentation and opposite quotient
detection, cuspidal-support association, spherical quotient admissibility
and compact-open subgroups. The signed class identity additionally uses
the published Aubert segment-exchange chain, including its irreducible
image, signed effectivity and Jacquet-detection inputs. The module does
not claim classification independence; these are GL representation
results, not part of an allowed external Chapter V structural boundary.
