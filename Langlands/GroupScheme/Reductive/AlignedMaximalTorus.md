# Descended maximal tori aligned with split coordinates

`HasAlignedMaximalTorus s j ψ` records a ground-field maximal torus containing
the supplied closed split torus `s`. Over the separable closure, an ambient
isomorphism identifies that maximal torus with the supplied split maximal
torus `j`, and the induced map from the scalar extension of the original
split torus is exactly `ψ`.

`hasAlignedMaximalTorus` constructs these data for connected reductive groups,
given an initial ambient isomorphism and its factorization through `j`.
First a ground-field maximal torus containing `s` is chosen. Its scalar
extension is split and maximal. In the target group, it and `j` contain
the same split subtorus. The published centralizer conjugacy theorem gives
a conjugation between them which fixes that subtorus. Composing the ambient
isomorphism with this conjugation supplies the alignment. Cancelling the
closed inclusion `j` proves that the subtorus map remains precisely `ψ`.

This is an internal construction from the Library's maximal-torus
containment, scalar-extension, splitting and centralizer-conjugacy theorems.
It does not assert a type C root calculation or prove the antihermitian
distinguished-vertex statement.
