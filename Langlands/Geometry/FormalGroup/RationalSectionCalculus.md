# Bilinear composition and category laws on rational Hom sheaf sections

This internal construction proves laws for the composition constructed in
RationalSectionComposition. The coefficient ring O is commutative, R is an
O-algebra, and F is an O-algebra field. R and F share a universe; O may have
a different universe. All coordinate types are finite and may differ.

Each finite tuple of actual sheaf sections lifts locally through a product
of genuine sheafification units. The image sieve of that product map is
covering. The actual target sheaf is separated, so comparing two sections on
this sieve proves their equality. The private `eq_of_local_lifts` lemma
implements this reduction directly with the covering image sieve and the
separatedness part of the sheaf condition. No global representative is assumed.

The four bilinear laws use this reduction for two or three inputs. Naturality
and linearity of restriction identify their restricted expressions with the
corresponding local tensor representatives. The representative agreement law
then reduces them to the proved additivity and F-scalar laws for tensor
composition. `compLinear` packages this same section operation as an F-bilinear
map; its linear-map laws imply the two zero-composition identities.

`id M U` is the image of the tensor identity of M after actual base extension
to the structure ring on U. Restricting this section gives the tensor identity
on the smaller open because the actual coefficient restriction preserves
identity maps. The two identity laws for arbitrary sections follow by lifting
one section locally and applying the tensor identity laws there.

Associativity lifts three sections simultaneously. Repeated naturality and
representative agreement identify both restricted composites with the two
parenthesizations of their tensor composition. Tensor associativity proves
the comparison, and separatedness gives equality of the original sections.

These constructions and proofs are internal consequences of genuine
sheafification and the previously implemented tensor formal Hom calculus.
No composition law is supplied as input. No finite-kernel composition,
quasi-isogeny rigidity, representability or universal object is asserted.
