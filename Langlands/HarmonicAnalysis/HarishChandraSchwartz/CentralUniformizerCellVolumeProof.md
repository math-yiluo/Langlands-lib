# Double-coset mass on the central uniformizer quotient

`centralUniformizerCellVolume` proves that the projection onto the central
uniformizer quotient is injective on each compact-open double coset and
preserves its mass under the specified Weil compatibility with counting
measure. [Statement](CentralUniformizerCellVolumeStatement.md)

Let \(H_G\) be the rational-character valuation homomorphism on \(G(F)\)
with its canonical topology. The equality `rationalCharacterValuation_ker`
and `compactSubgroup_le_rationalCommonNormKernel` show that \(H_G\) is
trivial on the compact open subgroup \(K\). For \(x=k_1 g k_2\) in
\(D=KgK\), multiplicativity gives \(H_G(x)=H_G(g)\).
`RenardCartan.bijOn_C0_splitValuationImage` gives injectivity of \(H_G\)
on the actual uniformizer subgroup \(C\), using the finite-index range
of character restriction to the split component. If \(x,y\in D\) have
the same image under the left quotient map \(q\), then \(yx^{-1}\in C\)
and \(H_G(yx^{-1})=H_G(1)\). Injectivity on \(C\) gives \(x=y\).

The double coset \(D\) is compact and open in the Hausdorff rational-point
group, so its complex-valued indicator is continuous and compactly
supported. In the Weil formula `IsCompatible.integral_formula`, the
orbital average at \(q(x)\) counts the elements \(c\in C\) with \(cx\in D\).
The set of such elements is empty off \(q(D)\) and a singleton on \(q(D)\)
by the injectivity just proved. Counting measure therefore makes the
orbital average the indicator of \(q(D)\).

The continuous open quotient map makes \(q(D)\) compact and open. The
indicator integrals agree by the Weil formula. The ambient Haar measure
and the regular quotient measure are finite on these compact sets, so
taking real parts yields equality of the original masses
\(\mu_Q(q(D))=\mu_G(D)\).

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026. The ambient Haar weights occur in VII.1.2
before (VII.1.2.2), printed pp. 221–222 (PDF pp. 227–228). The subgroup
averaging underlying the normalization is in II.3.9, printed pp. 48–50
(PDF pp. 54–56). The proof uses the norm kernel and lattice comparisons
from V.2.3 and V.2.5–6, printed pp. 105–108 (PDF pp. 111–114).
Registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
