# The vector-kernel step in characteristic-zero Levi decomposition

`Langlands.GroupScheme.CharacteristicZeroReductiveVectorExtensionStatement`
is a proposition, not a proof. It asks for a homomorphic section of every
faithfully flat homomorphism `q : E ⟶ H` of group schemes over an arbitrary
characteristic-zero field, where `E` is affine, `H` is connected reductive,
and the actual scheme-theoretic kernel of `q` is a vector group of a specified
finite dimension. Dimension zero is included. The section is defined over the
original field and its composite with the original quotient is the identity.
The vector-group premise supplies natural additive coordinates on every
scheme test; it concerns the full kernel rather than only rational points.

This is a derived intermediate statement for the characteristic-zero Levi
proof. Its mathematical provenance is the vector-kernel special case of the
characteristic-zero Levi theorem recorded in Milne, *Algebraic Groups* (2017),
25.48–25.49, printed p.559 (PDF p.575). A vector kernel is smooth, connected
and unipotent. Such an extension of a connected reductive group is smooth
and connected, its unipotent radical is the full vector kernel, and a Levi
subgroup maps isomorphically to the quotient. This explains the formulation;
the module does not formalize those deductions or invoke the Levi theorem.
The official errata retained with the registered source contain no correction
to these items.

For use in the Levi proof this statement must instead be proved independently,
for example by vanishing of rational algebraic degree-two cohomology for
reductive groups in characteristic zero. A scheme section alone does not
meet its conclusion, and complete reducibility alone is not supplied here.
The intended consumer performs dimension induction on a larger smooth
connected unipotent kernel, choosing an ambient-stable central vector
subgroup at each step. Thus this statement isolates the one vector-extension
step and does not assume a Levi subgroup or a section for a general
unipotent extension.

Source: registered `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`,
25.48–25.49.
