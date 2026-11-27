# The Lie algebras of a parabolic, its Levi subgroup and its unipotent radical as weight spaces: statement

Module `Langlands.GroupScheme.Rational.LeviCocharacterLieWeightsStatement`, namespace
`Langlands.GroupScheme`. It contains one `Prop`-valued definition,
`LeviCocharacterLieWeightsStatement`, and proves nothing; the proof is
`leviCocharacterLieWeights` in the module `Langlands.GroupScheme.Rational.LeviCocharacterLieWeights`.

## Statement

The statement quantifies over a field `k : Type u`, group schemes `G`, `Q`, `M'`, `V` over
`Spec k` with affine structure morphisms, and morphisms `q : Q ⟶ G`, `iV : V ⟶ Q`,
`l' : M' ⟶ Q`. It assumes that `G` is connected reductive (`IsConnectedReductive G`), that `q`
is a parabolic subgroup (`IsParabolicSubgroup q`), that `iV` is a geometric unipotent radical of
`Q` (`LeviSubgroup.IsGeometricUnipotentRadical iV`) and that `l'` is a rational Levi subgroup of
`Q` (`IsRationalLeviSubgroup l'`). The conclusion is that there is a cocharacter
`ψ : 𝔾_m ⟶ M'` with:

1. `ψ` central in `M'` (`IsCentral ψ`);
2. `q` represents the dynamic parabolic `P_G(ψ ≫ l' ≫ q)`;
3. `weightSpace (ψ ≫ l' ≫ q) (t ↦ t⁰)`, the fixed space of `𝔾_m` acting on the actual Lie
   algebra `lieKernel G k` through `ψ ≫ l' ≫ q` and the adjoint representation, is the image of
   `lieKernel M' k` under the map `Lie.targetMapLinear (l' ≫ q) k` induced by `l' ≫ q`;
4. the sum over `n ≥ 1` of the weight spaces of the characters `t ↦ tⁿ` is the image of
   `lieKernel V k` under `Lie.targetMapLinear (iV ≫ q) k`;
5. the sum over `n ≥ 0` of the same weight spaces is the image of `lieKernel Q k` under
   `Lie.targetMapLinear q k`.

The Lie algebras are the actual dual-number identity kernels `lieKernel _ k`, and the weight
spaces are the Library's `weightSpace`, defined by the adjoint action of all points of `𝔾_m`
over all test algebras.

## Sources and provenance

The statement is derived. Item 2 for some cocharacter of `G` is the theorem that parabolic
subgroups are dynamic parabolics: J. S. Milne, *Algebraic Groups* (2017)
(`milne-2017-algebraic-groups`), Theorem 25.1. The cocharacter can be moved into the centre of
the given Levi subgroup, which is then the centralizer of the cocharacter, and the unipotent radical
is the dynamic unipotent subgroup `U_G(ψ)`. Items 3–5 are the description of the Lie algebras of
the dynamic subgroups `Z_G(ψ)`, `U_G(ψ)` and `P_G(ψ)` by the weights of `𝔾_m`: B. Conrad,
O. Gabber and G. Prasad, *Pseudo-reductive groups*, second edition (2015)
(`conrad-gabber-prasad-2015-pseudo-reductive`), Proposition 2.1.8 (1), printed p. 53
(PDF p. 79).
