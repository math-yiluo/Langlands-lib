# Compatible pinnings retaining a specified centralizer torus

For a supplied torus representing the centralizer of a split torus, construct
Galois-compatible pinning data over a finite field extension splitting that
centralizer torus. The connected reductive group, the split torus, and the
root-datum existence statement are explicit inputs.

The descended torus and its inclusion are definitionally the supplied
`C.torus` and `C.inclusion`. The projection lemmas are reflexivity proofs.
This retains the specific torus needed to apply the rational-coordinate
reconstruction to the original centralizer inclusion.

The proof chooses an actual reduced root datum for the split maximal torus
after base change. It then applies the existing constructor from the
ground-field regular cocharacter of the supplied centralizer. The chosen
root datum does not change the descended torus or its inclusion.

The provenance is internal: this is the construction used in the published
`nonempty_galoisCompatiblePinningData` existence proof, retained as a
data-valued definition with its exact torus and inclusion. Its hypotheses
are unchanged. It makes no relative-root-generation claim.
