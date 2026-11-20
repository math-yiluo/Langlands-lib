# Whole quasi-isogeny in Drinfeld's framing formula

Drinfeld, *Coverings of p-adic symmetric regions* (1976), §2 A, printed p. 109 (PDF p. 3), gives
\[
(g_1,g_2)\cdot(\psi,Y,\rho)
  = (\psi\circ\mathrm{Fr}^{-n},{}^{g_2}Y,\rho\,g_1^{-1}g_2^{-1}\mathrm{Frob}^{n}),
\qquad
n=v(\det g_1)+v(\operatorname{Nrd}g_2).
\]

`actionResidueMap` and `actionTarget` construct the first two components using the residue-cardinal Frobenius and the special target's inverse-conjugated order action. The underlying target cover is preserved. `actionSourceFrobenius` restricts the actual signed relative Frobenius to that reduced cover. The construction takes the fixed frame's matrix coordinates and the exact nonnegative relative Frobenius inverse proposition as inputs.

`actionFramingOnCover` follows signed Frobenius by the inverse matrix, the original framing, and the reduced target twist quasi-isogeny. The latter has forward tensor given by \(g_2^{-1}\) acting on the old reduced target. An order-equivariant rational morphism commutes with the division action after scalar extension. The proof reduces to integral order elements by tensor induction and uses finite-cover detection to pass their chartwise commutation to the whole tensor. Applying this to the framing and the inverse matrix gives the printed order \( \rho\,g_1^{-1}g_2^{-1}\mathrm{Frob}^{n} \). Evaluation on each test of the original cover respects the actual quasi-isogeny composition.

`actionFraming` transports this quasi-isogeny to the fixed frame extended by the shifted residue map on the transformed target's actual reduced cover, and to the actual reduction of that target. The endpoint equalities preserve the forward tensor and its constant chart-height condition. The height-zero calculation and the action laws on comparison classes remain separate obligations.
