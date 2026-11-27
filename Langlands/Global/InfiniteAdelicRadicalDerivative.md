# The derivative of the normalizing factor of a parabolic as a trace on its unipotent radical

Module `Langlands.Global.InfiniteAdelicRadicalDerivative`, namespace
`Langlands.Global.InfiniteAdelicGroupPoints`. The setting is that of
`InfiniteAdelicAdjointDerivative`: `F` is a number field, `H` an affine group scheme over `F`
with `hsmoothH : SmoothOfRelativeDimension e H.X.hom`, and `tangentKernel F hsmoothH X` is the
dual-number kernel point of an identity tangent vector `X` of `H(F_∞)`.

## Declarations

- `targetMapLinear_comp_apply`: `Lie (f ≫ g) = Lie g ∘ Lie f` on dual-number Lie kernels, for
  morphisms of affine group schemes over a field.
- `mfderiv_halfModulus_one_eq_radicalTrace`: let `G` be connected reductive over `F`, `q : Q ⟶ G`
  a parabolic subgroup with geometric unipotent radical `iV : V ⟶ Q` (a monomorphism) and
  rational Levi subgroup `l : M ⟶ Q`, all affine of locally finite type, and let `c : H ⟶ M`.
  Then the derivative at the identity along `X` of the normalizing factor
  `m ↦ (c ≫ l)(m)^{-ρ_Q}` (`parameterPower F Q (-halfModulusParameter F Q)`, that is
  `δ_Q(c(m))^{-1/2}`) is

  ```text
  -1/2 · Σ_v mult(v) · Re (tr_{F_∞} normalAdjoint (Lie l (Lie c (B X))) | Lie V ⊗ F_∞)_v,
  ```

  with `B X = tangentKernel F hsmoothH X` and `normalAdjoint` the adjoint action on the Lie
  algebra of the normal subgroup `V` (module `LeviRadicalTrace`). Proof: by
  `mfderiv_halfModulus_one_eq_trace_ad` the derivative is
  `-1/2 · Σ_v mult(v) · Re (tr ad (Lie (c ≫ l) (B X)) | Lie Q ⊗ F_∞)_v`. Write
  `Lie (c ≫ l) = Lie l ∘ Lie c`; `Lie.trace_toEnd_levi` splits the trace into the trace on
  `Lie V ⊗ F_∞` and the trace on `Lie M ⊗ F_∞`. The second vanishes by
  `Lie.trace_toEnd_eq_zero_of_isConnectedReductive`, since `M` is connected reductive.

## Provenance

Internal. On the Levi subgroup, `δ_Q = |det(Ad | Lie Q)|` equals `|det(Ad | Lie V)|` because
`det Ad` is trivial on the reductive `M`. This is the infinitesimal form of that identity at the
identity of `H(F_∞)`. The normalizing factor is the one of Mœglin–Waldspurger I.2.17 used in
`LeviRestrictionCenterTransferStatement`.
