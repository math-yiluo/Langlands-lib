# The cocharacter image of a simply connected central cover

Let `φ : G → G'` be a central isogeny over any field `k`, with `G` algebraically simply
connected and `G'` connected reductive. Let `i : T → G` and `i' : T' → G'` be split maximal
tori and let `t : T → T'` satisfy `i ≫ φ = t ≫ i'`. For any supplied root datum `P'` of
`i'`, the image of actual integral cocharacter pushforward along `t` is exactly
`P'.corootSpan ℤ`.

`IsCentralIsogeny.cocharacterCorootSpanEquiv` is the resulting integer linear equivalence
from the full cocharacter lattice of `T` to that coroot span. Its underlying map sends an
actual cocharacter `ν` to `ν ≫ t`, as recorded by the application theorem. The root datum
of the source is constructed in the proof, rather than supplied as an extra hypothesis.
The index types and the field are allowed at an arbitrary common universe.

This is an internal consequence of published Library results. `rootDatumExistence`
constructs a finite reduced root datum `P` of `i`, and
`centralIsogenyRootDatumHom` gives a root pairing morphism from `P'` to `P` whose coweight
map is actual cocharacter pushforward. Its bijection of root indices identifies the image
of the source coroot span with the target coroot span, by mapping the span of its coroots.
`splitSimplyConnectedCorootSpan` says the source span is the full lattice, proving the
image equality. Finally `cocharacterMapInt_injective_of_square` proves injectivity of this
pushforward from finiteness of the central isogeny, and `LinearEquiv.ofInjective` followed
by transport along the image equality constructs the displayed equivalence.

No characteristic restriction or reducedness assumption on the kernel is used. This
unit does not identify a particular quaternionic spin kernel or its Levi diagonal map;
those comparisons remain separate from this general lattice computation.
