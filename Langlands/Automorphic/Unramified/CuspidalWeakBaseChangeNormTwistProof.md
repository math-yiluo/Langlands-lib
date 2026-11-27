# Norm-trivial determinant twists preserve attached weak base change: proof

`Langlands.Automorphic.Unramified.cuspidalWeakBaseChangeNormTwist` proves
[`CuspidalWeakBaseChangeNormTwistStatement`](CuspidalWeakBaseChangeTwistStatement.md)
at the independent universes `uF`, `uE` of the two number fields and `uV`, `uW` of
the spectral carriers. The extension `E/F` is an arbitrary finite extension of
number fields; no Galois or cyclicity hypothesis is used. Let `χ` be a Hecke character
of `F` trivial on the idele-class norms from `E`, let `c'` be the finite-order
determinant twist of `c` by `χ`, and let `d` be an attached weak base change of `c`.
The proof shows that `d` is an attached weak base change of `c'`.

## The local norm calculation

`Langlands.Global.HeckeCharacter.IsTrivialOnNorm.finiteUniformizerValue_pow_inertiaDeg`
states: if `χ` is trivial on norms from `E`, `v` is a finite place of `F` and `w` is a
place of `E` above `v` with ramification index `e_w = 1`, then
`χ.finiteUniformizerValue v ^ f_w = 1`, where `f_w` is the residue degree
(`w.1.asIdeal.inertiaDeg (𝓞 F)`) and `χ.finiteUniformizerValue v` is the value of the
local component `χ_v` at the canonical uniformizer `ϖ_v` of the completion `F_v`.

1. Let `x` be the image of `ϖ_v` under the completion map `F_v → E_w`
   (`FiniteExtension.completionMap`). Since `e_w = 1`, `x` is a uniformizer of `E_w`.
2. Its local norm is `N_{E_w/F_v}(x) = ϖ_v ^ [E_w : F_v]`
   (`FiniteExtension.localNorm_algebraMap`), and the local degree is
   `[E_w : F_v] = e_w f_w = f_w` (`Langlands.Global.AdelicFunctoriality.localDegree_eq`).
   So the norm of this upstairs uniformizer is exactly `ϖ_v ^ f_w`, with no unit factor.
3. The idele-class norm of the class of the idele supported at `w` with component `x`
   is the class of the idele supported at `v` with component `N_{E_w/F_v}(x)`
   (`Langlands.Global.AdelicFunctoriality.ideleClassNorm_ofAdicCompletion`, stated for
   fields in independent universes).
4. Triviality of `χ` on norms gives `χ_v(ϖ_v ^ f_w) = 1`, that is
   `χ_v(ϖ_v) ^ f_w = 1`.

## The main proof

1. Since `χ` is trivial on norms it has finite order (`IsTrivialOnNorm.hasFiniteOrder`),
   and `IsoClass.isFiniteOrderDeterminantTwist_iff_eq` identifies `c'` with the actual
   class `IsoClass.determinantTwist c χ`.
2. The weak base change `d` of `c` supplies spectral systems `s` attached to `c`, `t`
   attached to `d`, and the arithmetic weak base-change relation
   `t.IsArithmeticWeakBaseChangeOf s`: for all but finitely many `v`, `v` is not
   exceptional for `s`, no place `w` above `v` is exceptional for `t`, every such `w`
   has `e_w = 1`, and the unordered spectrum of `t` at `w` is the `f_w`-th power of the
   spectrum of `s` at `v`.
3. `IsoClass.HasSpectralSystem.determinantTwist` attaches to the twisted class the
   spectral system `s` scaled at each `v` by `χ.finiteUniformizerValue v`
   (`SpectralSystem.scale`), restricted to the complement of
   `U = s.exceptional ∪ χ.finiteDeterminantTail (r + 1)`. The set
   `χ.finiteDeterminantTail` is a finite set of places outside which `χ_v ∘ det` is
   trivial on the integral points; that is, `χ` is unramified there. The upper system
   `t` stays attached to `d`.
4. All but finitely many places lie outside the finite set `U`
   (`Finset.eventually_cofinite_notMem`), so for all but finitely many `v` the conditions
   of step 2 hold and `v ∉ U`. At such `v` and
   any `w` above it, `Eigenvalues.power_scale` gives
   `(χ_v(ϖ_v) · s_v) ^ f_w = χ_v(ϖ_v) ^ f_w · s_v ^ f_w`, the local norm calculation
   makes the scalar `1` (`e_w = 1` by step 2), and `Eigenvalues.scale_one` removes it.
   Hence the spectrum of `t` at `w` is the `f_w`-th power of the twisted spectrum at `v`.

So the scaled system attached to the twisted class and the original upper system `t`
witness `IsWeakBaseChangeOf d c'`.

## Source

Weak base change is Arthur–Clozel (1989), `arthur-clozel-1989-base-change`,
Chapter 3, Definition 1.1 with relation (1.1), printed p. 199: at almost all finite
places `v` and `w | v`, the Hecke eigenvalues of the lift at `w` are the `f_v`-th
powers of those of `π_v`. Lemma III.6.3, printed p. 217, concerns a cyclic extension
`E/F` of degree `ℓ` and a cuspidal `π_E` with `π_E ≃ π_E^σ` for a generator `σ` of
`Gal(E/F)`. Under these hypotheses it states that exactly `ℓ` representations of
`GL(n, A_F)` are lifted by `π_E`, namely the twists `π_F ⊗ η_{E/F}^i`
(`0 ≤ i < ℓ`) of any one of them, `π_F`, where `η_{E/F}` generates the characters
of `F^× N(A_E^×) \ A_F^×`. The statement proved here is narrower: it starts from a
given weak lift `d` of `c` and shows that `d` is also a weak lift of the twist of `c`
by a character trivial on norms. It assumes neither cyclicity nor Galois invariance of
`d`. The proof above is the eigenvalue calculation behind this direction and holds
for an arbitrary finite extension.
