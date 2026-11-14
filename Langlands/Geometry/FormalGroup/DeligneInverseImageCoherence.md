# Coherent ordinary inverse image of Deligne coefficient sheaves

This module constructs the canonical identity and composition isomorphisms for
ordinary inverse image of module sheaves. It proves associativity, both unit
equations, and compatibility with the existing coefficient restriction,
coefficient extension, rationalization and constant-sheaf comparisons.

This is derived infrastructure for Deligne's data in Drinfeld, *Coverings of
p-adic Symmetric Regions* (1976), Section 2 A, printed p.109 (PDF p.3), final
paragraph defining the lattice, tangent sheaf, map and rational frame,
continuing on printed p.110 (PDF p.4). The registered original is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The source's lattice and full rational degree-zero frame require ordinary
inverse image and its scalar comparisons to agree under changes of base.
The coherence proved here is a consequence of adjunction uniqueness; it is
not a separate theorem attributed to Drinfeld.

The parameters are arbitrary commutative rings `O` and `R`, a ring homomorphism
`ρ : O →+* R`, and continuous maps between topological spaces, all in the
same universe `u`. The rationalization specializations additionally use an
`O`-algebra field `F`. Neither a local-field hypothesis nor nilpotence is
needed for this infrastructure.

Write `P_O(f)` for ordinary inverse image with coefficients in `O`. For
`f : X → Y` and `g : W → X`, `inverseImageIdIso` and `inverseImageCompIso`
are natural isomorphisms

```
I_O(X) : P_O(id_X) ≅ Id
C_O(f,g) : P_O(f) ⋙ P_O(g) ≅ P_O(g ≫ f).
```

They are constructed by `Adjunction.leftAdjointUniq` from the actual
inverse-image/direct-image adjunctions. Ordinary direct image along an identity
is definitionally the identity functor, and iterated direct image is
definitionally direct image along the composite. Thus the comparisons use the
actual functors and require no supplied coherence isomorphisms.

`inverseImage_assoc` identifies the two comparisons from triple inverse image
to inverse image along the composite: first compare `f,g` and then `g ≫ f,h`,
or first compare `g,h` and then `f,h ≫ g`. Its equation uses the definitionally
equal bracketings of functor composition. `inverseImage_id_comp` says
`C_O(id_Y,f)` is `I_O(Y)` whiskered on the right by `P_O(f)`.
`inverseImage_comp_id` says `C_O(f,id_X)` is `I_O(X)` whiskered on the left
by `P_O(f)`. Naturality in a sheaf map is part of each natural isomorphism.

For scalar restriction `Q_X = coefficientRestriction ρ X`, let
`A_f : Q_Y ⋙ P_O(f) ≅ P_R(f) ⋙ Q_X` be the existing comparison.
`inverseImageRestrictionIso_id` states that `A_id` followed by `I_R`
and scalar restriction agrees with scalar restriction followed by `I_O`.
`inverseImageRestrictionIso_comp` compares the following two paths:

```
Q_Y ⋙ P_O(f) ⋙ P_O(g)  →  P_R(g ≫ f) ⋙ Q_W.
```

One path uses `C_O(f,g)` and `A_(g≫f)`. The other uses `A_f`,
then `A_g`, then `C_R(f,g)`, with the displayed surrounding functors
whiskered in each step. These are equations for the existing canonical
comparisons, rather than replacements chosen to satisfy the equations.

`inverseImageExtensionIso_id` and `inverseImageExtensionIso_comp` prove the
same two equations for actual coefficient extension followed by sheafification,
with the coefficient roles reversed. The scalar extension/restriction
adjunction supplies the uniqueness argument. `inverseImageRationalIso_id`
and `inverseImageRationalIso_comp` specialize these equations to
`ρ = algebraMap O F`; the existing rationalization is definitionally this
extension functor.

For constant module sheaves, `inverseImageConstantIso_id` identifies the
identity-base comparison with `I_O` after the constant-sheaf functor.
`inverseImageConstantIso_comp` says that constant sheaves compared successively
along `f` and `g` give the same isomorphism as comparison along `g ≫ f`
after `C_O(f,g)`. The right adjoint here is evaluation at the terminal top
open. This evaluation agrees definitionally with evaluation after ordinary
direct image, so the same uniqueness argument applies.

The implemented proofs first establish equality of the units of associated
composite adjunctions, including the identity cases. Two private lemmas show,
using injectivity of the mates equivalence, that whiskering a canonical
left-adjoint uniqueness isomorphism gives the uniqueness isomorphism for
the composite adjunctions. Transitivity of these isomorphisms reduces every
coherence path to the same uniqueness isomorphism. The coefficient proofs
instantiate the actual adjunctions explicitly, so their definitionally
commuting direct-image and scalar functors are the ones being compared.

This module does not yet lift these comparisons to graded lattices or framed
lattices, prove compatibility of the ordinary-to-structural map with base-map
composition, or establish full four-data coherence. Admissibility transport,
the admissible `Nilp` functor, the integral determinant comparison, normalized
`PGL` action, identification with data attached to special formal modules,
Drinfeld's Proposition 2.4 (Section 2 B, printed p.110), and representability
remain separate obligations.
