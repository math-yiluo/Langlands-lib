# Basic open charts of conormal generators

For a finite type augmented commutative algebra over `R`, the residue-field
conormal dimension pulls back along any ring map `R → B`. Tensor cancellation
identifies the residue conormal on the test with the extension of the residue
conormal at the image point, along the canonical map of residue fields.

At a test point of residue conormal dimension `r`, `sectionJetConormalChart`
finds a basic neighborhood of its image in `Spec R`. The conormal on this
neighborhood is spanned by `r` classes of elements from the original
augmentation ideal. The proof lifts a basis of the residue conormal to the
localized module and applies Nakayama's lemma. A linear map with these
localized generators lifts from the original ring up to a denominator. Its
localization remains surjective after shrinking to one basic open.

This is the spanning-chart step in the construction of the fixed-rank
smooth-section locus of SGA 3, Exposé XV, Lemma 5.4.
