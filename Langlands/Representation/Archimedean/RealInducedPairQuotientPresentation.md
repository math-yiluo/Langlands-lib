# Ascending-character quotient presentation for two real induction blocks

This is a derived construction from the Library's actual real standard modules, compact-finite function spaces and block Frobenius maps. It supplies a presentation and a descent interface for the GL4 filtration problem. It proves no exchange of induction blocks, identifies no heavier replacement image, and does not prove `RealInducedInducedFiltrationStatement`.

Let `d,e` be complex character data with positive absolute weights `L=|d.weight|` and `M=|e.weight|`, and arbitrary complex exponents `a,b`. Choose `sd,se : Fin 2` independently. There is no order or genericity condition on the exponents.

For `d`, `lo d sd` has parity `sd` and exponent `a-L/2`. The character `hi d sd` has parity `sd+L+1` modulo two and exponent `a+L/2`. The pair parity is `L-1` modulo two, and the exponent difference is `L`. Thus their pair induction `positiveData d sd` has positive weight `L` and exponent `a`. The same construction applies to `e`.

The concrete source `X` is the list `[lo d,hi d,lo e,hi e]` of four character blocks. Collapsing its left pair gives `DX=[induced (positiveData d sd),lo e,hi e]`; collapsing its right pair gives `EX=[lo d,hi d,induced (positiveData e se)]`. Collapsing both gives `Z=[induced (positiveData d sd),induced (positiveData e se)]`. All four lists have rank four. Parity arguments are suppressed in these displayed list names only.

The maps `Dd : KF 4 X → KF 4 DX` and `De : KF 4 DX → KF 4 Z` are the actual tail Frobenius maps at positions zero and two. Their inverse-tail maps `Sd` and `Se` satisfy `Dd(Sd f)=f` and `De(Se f)=f`. These are linear sections; no exact intertwining is claimed for them. The tails themselves are exact intertwiners for compact right translation and every real matrix derivative: their recurrence parameters are `1-L` and `1-M`, the actual adjacent exponent differences plus one.

The map `qd : KF 4 Xd → KF 4 X` is the binomial Frobenius map from `Xd=[hi d,lo d,lo e,hi e]`, and `qe : KF 4 Xe → KF 4 X` is its right-pair counterpart from `Xe=[lo d,hi d,hi e,lo e]`. Both maps are exact intertwiners. On each pair, Fourier coefficients prove that the tail kernel equals the binomial image. The zero composite follows because their multiplier supports are disjoint on the source parity class. The reverse containment uses the inverse binomial multiplier and the published `ker_le_range`. The parity condition excludes the boundary `|j|=L` or `|j|=M`. All equalities concern actual compact-finite standard-module vectors, including the induction constraint on the other pair whenever present.

Set `T=De ∘ Dd` and `S=Sd ∘ Se`. Then `TS=id`, so `T` is surjective, and it is an exact intertwiner. Its kernel is

`ker T = range qd ⊔ range qe`.

For the nontrivial containment, if `Tf=0`, write `Dd f=qeD b` using the right tail kernel. The residual `f-Sd(Dd f)` lies in the left tail kernel, so equals `qd a`. Disjoint Frobenius commutation gives `Sd(qeD b)=qe(SdXe b)`. Hence `f` is a sum from the two displayed ranges. For the reverse containment, `Dd qd=0`; the alternative order of the two disjoint tails shows `T qe=0`. Both commuting squares are applications of `blockFrobMap_disjoint_comm`, with no extra commutation premise.

The standard module of `Z` equals that of the original list `[induced d,induced e]`. This is proved directly. The position characters depend on the absolute weights and exponents, which agree, and the two induction conditions at positions zero and two have exactly the same absolute Fourier cutoffs. This comparison does not require literal equality of the complex character data, and covers negative original weights. Applying `kFiniteFunctions` gives `KF_Z`; the identity on underlying functions is the published exact map `ofEqMap`.

Consequently `quotientMap=ofEqMap ∘ T` is an explicit surjective exact intertwiner from `KF 4 X` onto `KF 4 [induced d,induced e]`. Its section is `quotientSection=S ∘ ofEqMap⁻¹`, and its kernel is still the sum of the two explicit binomial images.

The descent theorem has a concrete vanishing criterion. For any list `F`, submodule `M ≤ KF 4 F`, and linear map `P : KF 4 X → KF 4 F` intertwining modulo `M`, assume the two exact linear-map equalities `P ∘ qd=0` and `P ∘ qe=0`. Then `Q=P ∘ quotientSection` intertwines modulo `M`, satisfies `Q ∘ quotientMap=P`, and has the same range as `P`. The proof kills the computed kernel, subtracts the section of each image to obtain the factorization, and applies the published `modulo_of_comp_surjective`.

`RealInducedPairQuotientPresentationStatement` packages these section, surjectivity, exact intertwining, kernel, and descent assertions for every `d,e,sd,se` with positive absolute weights. `realInducedPairQuotientPresentation` proves that proposition from the preceding results. The zero-weight cases and the maps needed to produce a linked filtration are outside this module.

The provenance is internal. The one-pair tail-section, inverse-binomial and recurrence arguments follow the published two-character reducible filtration. The ascending-character choice and elementary descent argument also parallel the GL3 pushforward development in `RealCharacterInducedPushforward`. This module constructs its own rank-four maps from the published data and uses only the disjoint commutation theorem beyond its published imports; no GL3 classification assertion or unproved landing hypothesis is used.

The section identities reuse the existing
`RealCharacterInducedPushforward.tail_inv` with the same parameters and
conclusion; this module adds no separate copy of that general lemma.
