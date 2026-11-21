# Fixed adelic coefficients of a cyclic generator

`adeleCoefficientAut` regards arithmetic transport on the upper-field
adeles as an algebra automorphism over the ground field. Its entrywise
action on matrices is `AdelicGLTransport.adelicEquiv`.

For a cyclic extension of number fields, the powers of the given generator
exhaust its Galois group. A coefficient fixed by the generator is therefore
fixed by the full group. Applying the Library's adele descent theorem
identifies it with a ground-field adele. Conversely, arithmetic transport
fixes each ground-field adele. The same inclusion contains the positive
real ideles used to correct determinant norms, so their scalar matrices are
fixed by the twist.

This derived comparison connects the published arithmetic transport and
Galois descent to the cyclic matrix norm and to the fixed-scalar condition
of the twisted centralizer calculation.
