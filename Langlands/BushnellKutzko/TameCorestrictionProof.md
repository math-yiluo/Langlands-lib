# Tame corestriction

`Langlands.BushnellKutzko.tameCorestriction` proves
`Langlands.BushnellKutzko.TameCorestrictionStatement`, the existence,
unit comparison, and filtration images of tame corestrictions.
The proof implements the duality argument of Bushnell–Kutzko 1993,
(1.3.2)–(1.3.4), printed pp. 28–29
(`bushnell-kutzko-1993-admissible-dual-gln`), using linear trace pairings.

For a nonzero vector space, evaluation of the extension scalars at a
nonzero vector embeds the extension field into the original
finite-dimensional vector space. The extension is therefore finite.
Separation of \(1\) from the extension maximal ideal gives a base-linear
form \(\ell\) on the extension field. For \(z\) in the extension field,
\(\ell(z\mathfrak o_E)\subseteq\mathfrak p_F\) holds exactly when
\(z\in\mathfrak p_E\). Outside the maximal ideal, \(z\mathfrak o_E\)
contains \(1\), which the separating form detects.

The trace pairing on the base endomorphism algebra and the trace
pairing on the extension endomorphism algebra composed with \(\ell\)
are nondegenerate by rank-one tests. The adjoint of restriction of
scalars for these pairings is a bimodule map by cyclicity of trace.
Both pairings exchange filtration indices \(n\) and \(1-n\) when
tested against the base maximal ideal. On the extension this uses
closure of each step under extension integers and the conductor
property of \(\ell\). Trace adjunction gives the image inclusion.
For the reverse inclusion, a linear form separating an omitted point
from the finite image module is represented by a trace test in the
complementary step. The complementary-step pairing contradicts
the separation. The equality at depth zero supplies the order-image
property in `TameCorestriction`.

For another tame corestriction, the base trace represents its
composition with \(\ell\) and the extension trace by an endomorphism.
Bimodule compatibility makes that endomorphism commute with all
extension-linear maps. Testing this commutation on rank-one maps
shows it acts by an extension scalar. It follows from trace
adjunction that the second corestriction is the scalar multiple of
the constructed one. On the normalized chain made from an extension
basis, the common order-image property puts the scalar and its
inverse in \(\mathfrak o_E\). Such a unit preserves every relative
filtration step, so all tame corestrictions have the same images.

For the zero vector space the zero map gives existence and the unit
\(1\) gives the comparison. The strict inclusions in a lattice chain
rule out a chain on that space. The field and vector-space universes
are independent, and the proof applies to inseparable finite
extensions as well.
