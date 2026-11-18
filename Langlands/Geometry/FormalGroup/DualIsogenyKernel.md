# Finite locally free kernels of scalar-power duals

This internal unit constructs the finite projective actual kernel
model for an integral scalar-power dual map.

Let f map scalar-divisible M to scalar-divisible N, with f an
actual isogeny. Let g be a reverse formal-module map with both
composites equal to the respective scalar-power endomorphisms
pi^j. Use the existing finite projective model C of N[pi^j].
Since f composed with g is that scalar endomorphism, ker g is
contained in N[pi^j]. The quotient construction gives an actual
representing algebra D for ker g that is finite and finitely
presented over the base.

The universal point of ker f lifts through the scalar power on M
after a faithfully flat, finitely presented extension of ker f's
coordinate algebra K. Applying f to that lift gives a point of
N[pi^j] mapping under g to the universal ker f point. Translation
by it identifies the corresponding fibre with ker g. The algebra
of this fibre is D tensor B over the base and is flat over C by
base change along the faithfully flat cover K to B. C is finite
projective, so that tensor algebra is flat over the original base.

The zero kernel point gives an augmentation K to the base.
Every base prime lifts along K by pulling it back through that
augmentation. Flatness and surjectivity on prime spectra make K,
hence B, faithfully flat over the base. To descend flatness of D,
tensor an injective linear map with D and then with B. Associativity
identifies the latter with tensoring by the flat module B tensor D,
so it is injective. Faithful flatness of B reflects this injectivity.
Together with finite presentation, the descended flatness gives
projectivity. The quotient corepresentation completes the required
actual finite kernel model.

This is the finite-kernel portion of the integral dual-isogeny
construction needed by `LocalQuasiIsogenyInverseStatement`. It
does not construct g. All coefficient rings and finite coordinate
types retain their existing generality.
