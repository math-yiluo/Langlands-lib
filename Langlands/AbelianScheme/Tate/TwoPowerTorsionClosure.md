# Invariance of the actual two-power torsion closure

This internal geometric step uses the actual section-defined `twoPowerTorsionLocus` and the existing multiplication morphism. Multiplication by two preserves the locus by exponent arithmetic. Over an algebraically closed characteristic-zero field, actual section divisibility also shows that its image is the whole locus.

The inverse image of the locus lies in its Zariski closure. For each actual torsion section, its underlying point is closed. The inverse-image fibre is therefore a closed subset of the actual abelian scheme. This scheme is Jacobson because it is locally of finite type over a field. The closed points in that fibre are dense in the fibre and correspond to actual field-valued sections. The square of each such section equals the given torsion section, since the two sections have the same underlying closed point over an algebraically closed field. Every such section is killed by the next power of two. The whole fibre consequently lies in the torsion closure.

Multiplication by two is étale and hence open. Inverse image therefore commutes with closure, and the previous fibre argument proves equality of the full inverse image of the closure with the closure itself. Multiplication is also finite and hence closed. Its image likewise commutes with closure, giving equality of the image of the closure with the closure itself.

These are derived invariance results, motivated by the torsion-closure argument in Edixhoven, van der Geer and Moonen, *Abelian Varieties*, Chapter V, §3, Theorem (5.30), printed page 84 / PDF page 88, registered as `edixhoven-vandergeer-moonen-abelian-varieties-draft`. They do not assert density, a numerical torsion formula, or a closed subgroup scheme structure on the closure.
