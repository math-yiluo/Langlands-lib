# Tate L-factors of a local relation among induced characters

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In Deligne's global
argument (1973, §4.12) a global relation among induced Hecke characters restricts at every
finite place to a local relation among induced characters of local Weil groups. This unit
shows that the Tate L-factors of such a local relation cancel. The companion unit
`BrauerKernel.LocalRelation` produces the local relations.

Everything is in `Langlands.Weil.Local.InertiaEuler`. Fix a prime `p` and a p-adic field
`F : PadicField.{u} p`. Extension fields carry their canonical topology
(`canonicalTopologicalData.topology`).

## Results

- `prod_inducedLFactor_eq_one_of_relation`: let `J` be a finite type and, for each `j`, let
  `E j` be a p-adic field with an embedding `g j : F →ₐ[ℚ_p] E j`, let `α j`, `β j` be
  continuous characters of `W_{E j}` and let `n j ∈ ℤ`. If

  `Σ_j n_j · Ind_{g_j}([α_j] - [β_j]) = 0`

  in the continuous exact virtual group of `W_F` (induction is
  `continuousInduceAlong (extensionWeilMap F (E j) (g j))`), then the formal L-factors satisfy

  `Π_j (inducedLFactor F (E j) (g j) (α j) / inducedLFactor F (E j) (g j) (β j)) ^ n_j = 1`

  in `RatFunc ℂ`. Proof: apply the published additive L-factor homomorphism `lFactorHom F`
  to the relation and pass to `(RatFunc ℂ)ˣ` with `Additive.toMul`. `map_sum`, `map_zsmul` and
  `map_sub` distribute it over the combination. The published
  `lFactorHom_continuousInduceAlong_characterClass` and
  `coe_lFactorUnit_induceAlong_characterLine` evaluate it on each induced character as
  `inducedLFactor`. Finally take values in `RatFunc ℂ`.
- `prod_lFactor_eq_one_of_relation` (**Tate L-factors of a local relation**): in the same
  setting, take `α j = weilCharacter (E j) (e j) (η j)` and `β j = weilCharacter (E j) (e j) (η' j)`.
  Here `e j` are reciprocity candidates satisfying `IsGeometricReciprocity (E j) (e j)` and
  `η j`, `η' j` are quasicharacters of `E j`. For every `s : ℂ` at which every Tate L-factor
  `LocalFactor.PadicAbelian.lFactor (E j).canonicalTopologicalData (η j) s` and every
  `… (η' j) s` is nonzero,

  `Π_j (L(s, η_j) / L(s, η'_j)) ^ n_j = 1`.

  Proof: evaluate the identity of the previous item at the spectral point
  `RankinSelberg.spectralPoint q_F s`. The published
  `isRegularUnitAt_inducedLFactor_weilCharacter` (which uses the geometricity hypotheses and the
  nonvanishing at `s`) makes every factor a regular unit there. So evaluation commutes with
  products, quotients and integer powers (`IsRegularUnitAt.eval_prod`, `eval_div`, `eval_zpow`).
  The published `eval_inducedLFactor_weilCharacter` identifies each evaluated factor with the
  Tate L-factor.

The universe `w` of the representations is independent of the field universe `u`.

## Provenance

The cancellation is internal bookkeeping. It uses only the published fact that the Euler
factor of an induced character of a Weil group is the Euler factor of the character, the
inductivity of L-factors in degree zero (Tate, *Number theoretic background*, 1979, §3), in
the form of the published `lFactorHom` (`Global.Factors.RelativeWeilLocalEuler`) and its
comparison with Tate's L-factors (`Global.Factors.RelativeWeilLocalEulerBridge`). Its role in
the global argument follows Deligne, *Les constantes des équations fonctionnelles des
fonctions L* (1973), proof of Lemma 4.12.
