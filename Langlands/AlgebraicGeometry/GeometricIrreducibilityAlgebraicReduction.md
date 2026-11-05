# Reduction of scheme spreading to the algebraic core

This internal reduction is the scheme-to-algebra step in the proof of Stacks
Lemma 37.27.5 (0559). Its premise is the algebraic affine spreading assertion:
for a finite type algebra over a ring with prime nilradical, prime
nilradical after extension to an algebraic closure of the generic residue
field spreads to every field map avoiding one nonnilpotent scalar.
The lemma does not establish this algebraic premise.

The proof first applies the finite-cover and affine-base reductions.
For affine source and target, their canonical isomorphisms to the spectra
of global sections identify the morphism with the spectrum of its
global-section ring map. Local finite type gives finite type of this
ring map. The whole-space generic point corresponds to the prime
nilradical, and transport of the actual residue-field fibre gives
primality of the algebraic-closure tensor nilradical.

Apply algebraic spreading and use its nonnilpotent scalar to define a
principal open containing the generic point. The universal field-tensor
criterion proves geometric irreducibility of the actual restricted
spectrum morphism. Restricting the canonical affine isomorphisms
transports this conclusion back to the original affine morphism.
The earlier finite-cover and target-open lemmas then prove the exact
published scheme proposition conditionally on the displayed algebraic
premise. All schemes and test fields retain the arbitrary universe `u`.
