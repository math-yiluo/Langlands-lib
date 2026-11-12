# Relative roots and the minimal parabolic of `U(1,1)`: proof

Author: Worker 3483 (shared draft revision 13 of Task 3483). Submitted by
Worker 218 for Task 5580, with the list of published inputs completed.

This module proves `RelativeRootsStatement` (module
`Langlands.GroupScheme.Examples.QuasiSplitUnitaryRelativeRootsStatement`) as
the theorem `relativeRootsStatement`, in the namespace
`Langlands.GroupScheme.QuasiSplitUnitary`. Write `λ = cocharacter b c`, the
cocharacter `t ↦ diag(t, t⁻¹)` of `U(1,1) = groupScheme b c` over
`S = Spec F`. The proof uses no assumption on the characteristic. It uses the
general Library statements only through their published proofs. For the
centralizer equality of part 4 it uses a direct rank-one argument instead of
the published general theorem `genericCentralizer`
(module `Langlands.GroupScheme.Rational.GenericCentralizerProof`), which
would also give it.

## Part 1: maximality

`isMaximalSplitTorus_cocharacter` proves `IsMaximalSplitTorus λ`. The Library
theorem `rankStatement` (module
`Langlands.GroupScheme.Examples.QuasiSplitUnitaryRankProof`) gives two facts:
`λ` is a closed subgroup, and every closed subgroup `𝔾ₘ^J ⟶ U(1,1)` has
`Nat.card J ≤ 1`. Together with `isSplitTorus_gm`, the first fact makes `λ` a
split subtorus. For maximality, take a split subtorus `i' : T' ⟶ U(1,1)`, an
isomorphism `eK : T' ≅ 𝔾ₘ^J`, and `f` with `f ≫ i' = λ`:

- `eK⁻¹ ≫ i'` is a closed subgroup (`IsClosedSubgroup.of_iso`,
  `IsClosedSubgroup.comp`), so `Nat.card J ≤ 1` by the rank bound;
- `λ` is a monomorphism (`IsClosedSubgroup.mono_overHom`), so `f` is one
  (`mono_of_mono_fac`);
- `splitTorus.isIso_of_mono_of_iso` (module
  `Langlands.GroupScheme.Torus.SplitMono`) shows that a monomorphism from a
  group scheme isomorphic to `𝔾ₘ^{PUnit}` (`splitTorus.gmIso`) to one
  isomorphic to `𝔾ₘ^J` with `Nat.card J ≤ 1` is an isomorphism. So `f` is an
  isomorphism.

## Part 2: the relative roots

The roots are computed after base change to `E`, where `U(1,1)` becomes `GL₂`.

1. `mem_roots_diagonalCocharacter_iff` computes the roots of the diagonal
   cocharacter `t ↦ diag(t, t⁻¹)` of `GL₂` over `E`
   (`GeneralLinear.diagonalCocharacter (Fin 2) (CommRingCat.of E) (weights 1)`):
   they are the characters `ψ` of `𝔾ₘ` with exponent `gmEndEquiv E ψ = ±2`.
   The cocharacter is the composite of `hyperbolicCocharacter E`, the
   cocharacter `(1, -1)` of the diagonal torus, with the diagonal torus
   (`GeneralLinear.cocharacterLatticeEquiv_symm_comp_diagonalTorus`). By
   `mem_roots_comp_iff` (module `Langlands.GroupScheme.Torus.WeightRestriction`),
   its roots are the nonzero restrictions of the roots of the diagonal torus.
   These are `eₐ − e_b` with `a ≠ b` (`GeneralLinear.roots_diagonalTorus`).
   Their restrictions have exponent `weights 1 a − weights 1 b = ±2`
   (`pairing_root_hyperbolic`, via `splitTorus.latticePairing_symm_symm`).
   `GL₂` is smooth (`GeneralLinear.smoothStatement`), which supplies the
   finite-type instance used there.
2. `mem_relativeRoots_cocharacter_iff` shows that `χ` is a relative root of
   `λ` exactly when `gmEndEquiv F χ = ±2`. It chains three equivalences:
   - `mem_roots_baseChange_iff` (module
     `Langlands.GroupScheme.Torus.RootSupportBaseChange`; finite type comes from
     the smoothness in `isConnectedReductive`, extracted with
     `IsConnectedReductive.smooth`): `χ` is a root of `λ` iff its base change
     is a root of `λ_E`;
   - `roots_mem_of_transport_iff` (module
     `Langlands.GroupScheme.Rational.CrossTorusLieTransport`), applied to the
     identification `Gm.commBaseChangeIso` of the base change of `𝔾ₘ` and to
     `splittingIso b c hc : U(1,1)_E ≅ GL₂`. The required compatibility `htr`
     is the published `baseChangeCocharacter_cocharacter_splittingIso`, which
     says that the splitting carries `λ_E` to `t ↦ diag(t, t⁻¹)`;
   - step 1, together with `gmEndEquiv_congr_baseChange` (from
     `gmEndEquiv_baseChange`): base change and the identification keep the
     exponent of a character of `𝔾ₘ`.
3. `relativeRoots_cocharacter` rewrites the exponent condition as
   `χ = Gm.powerHom S 2` or `χ = Gm.powerHom S (-2)`, using
   `eq_gmEndEquiv_zsmul` and `gmEndEquiv_zsmul_id`.

## Parts 3 and 4: generic cocharacters

In `relativeRootsStatement`, part 2 and `gmEndEquiv_comp` give
`IsGenericCocharacter λ ν ↔ gmEndEquiv F ν ≠ 0`: the pairing of `±2` with
`ν` is `±2 · gmEndEquiv F ν`. In particular the identity cocharacter is
generic (part 3): its exponent is `1` by `gmEndEquiv_id`.

- *Minimality.* The published theorem `genericMinimalParabolic`
  (module `Langlands.GroupScheme.Rational.GenericMinimalParabolicProof`) applies
  to `U(1,1)`, which is connected reductive by `isConnectedReductive`, and to
  `λ`, which is a maximal split torus by part 1.
- *Dynamic Levi subgroup.* Write `ν = n • 𝟙` with
  `n = gmEndEquiv F ν ≠ 0`. `zsmul_comp_cocharacter` shows
  `ν ≫ λ = weightCocharacter b c n`, the cocharacter `t ↦ diag(tⁿ, t⁻ⁿ)`.
  It checks this on points with `Gm.comp_zsmul_id` and
  `pointsEquiv_weightCocharacter`. `centralizer_weightCocharacter` shows that
  for `n ≠ 0` its dynamic Levi subgroup is `diagonal b c`, comparing the two
  subgroup functors on every test scheme (`SubgroupFunctor.ext`). The criterion
  `mem_centralizer_weightCocharacter_iff`
  (module `Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamicProof`)
  describes it by the block Levi condition for the weights `(n, −n)`. That
  condition is the one for `(1, −1)` because `n ≠ 0`. Finally
  `torusCentralizer λ = Dynamic.centralizer λ`
  (`torusCentralizer_gm_eq_dynamicCentralizer`), and
  `Dynamic.centralizer λ = diagonal b c` (`centralizer_cocharacter`).

## Auxiliary declarations

`hyperbolicCocharacter`, `pairing_root_hyperbolic`,
`mem_roots_diagonalCocharacter_iff`, `isMaximalSplitTorus_cocharacter`,
`gmEndEquiv_congr_baseChange`, `mem_relativeRoots_cocharacter_iff`,
`relativeRoots_cocharacter`, `zsmul_comp_cocharacter` and
`centralizer_weightCocharacter` are public lemmas of this module. The local
instance `baseChangeAffine` records that the base change to `E` of an affine
group scheme is affine. The module sets
`backward.isDefEq.respectTransparency false`.

## Published inputs

This is every published Library theorem that the compiled proof uses, with its
module. It lists the theorems named in the Lean source and also those inserted
by tactics: lemmas applied by `simp` and instances found by type-class
resolution. The list was obtained by collecting the constants that occur in the
compiled terms of all declarations of this module and keeping those from
`Langlands` modules. A `simp?` run on every `simp` call checked the lemmas that
`simp` uses. Names are in the namespace `Langlands.GroupScheme` unless written
in full. All other lemmas the proof uses are from Mathlib or Lean core, for
example `mono_of_mono_fac`, `Grp.comp_hom_hom` and `map_zpow`.

Theorems named in the proof or used by `simp`:

- `Langlands.GroupScheme.Examples.QuasiSplitUnitaryRankProof`:
  `QuasiSplitUnitary.rankStatement`.
- `Langlands.GroupScheme.Examples.QuasiSplitUnitaryReductiveProof`:
  `QuasiSplitUnitary.isConnectedReductive`.
- `Langlands.GroupScheme.Examples.QuasiSplitUnitarySplittingCocharacter`:
  `QuasiSplitUnitary.baseChangeCocharacter_cocharacter_splittingIso` (with the
  definition `QuasiSplitUnitary.baseChangeCocharacter`).
- `Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamicProof`:
  `QuasiSplitUnitary.mem_centralizer_weightCocharacter_iff` and
  `QuasiSplitUnitary.centralizer_cocharacter`.
- `Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamic`:
  `QuasiSplitUnitary.pointsEquiv_weightCocharacter` and
  `QuasiSplitUnitary.diagonalUnitary_val` (with the definitions `weights`,
  `weightCocharacter`, `matrixCoordinates` and `diagonal`).
- `Langlands.GroupScheme.Examples.QuasiSplitUnitarySplitting`: the definition
  `QuasiSplitUnitary.splittingIso` (no theorem).
- `Langlands.GroupScheme.Rational.GenericMinimalParabolicProof`:
  `genericMinimalParabolic`.
- `Langlands.GroupScheme.Rational.TorusCentralizer`:
  `torusCentralizer_gm_eq_dynamicCentralizer`.
- `Langlands.GroupScheme.Rational.CrossTorusLieTransport`:
  `roots_mem_of_transport_iff`.
- `Langlands.GroupScheme.Rational.RelativeRoots`: `relativeRoots_eq_roots` and
  `isGenericCocharacter_iff`.
- `Langlands.GroupScheme.Rational.SplitRankTransport`:
  `IsClosedSubgroup.comp`.
- `Langlands.GroupScheme.Rational.SplitTorus`: `IsClosedSubgroup.of_iso`.
- `Langlands.GroupScheme.ClosedSubgroupMonomorphism`:
  `IsClosedSubgroup.mono_overHom`.
- `Langlands.GroupScheme.SubgroupFunctor`: `SubgroupFunctor.ext`.
- `Langlands.GroupScheme.Reductive.Basic`: `IsConnectedReductive.smooth`.
- `Langlands.GroupScheme.Torus.SplitMono`: `splitTorus.isIso_of_mono_of_iso`.
- `Langlands.GroupScheme.Torus.Split`: `isSplitTorus_gm`,
  `isSplitTorus_splitTorus` (with the definition `splitTorus.gmIso`).
- `Langlands.GroupScheme.Torus.RootSupportBaseChange`:
  `mem_roots_baseChange_iff`.
- `Langlands.GroupScheme.Torus.WeightRestriction`: `mem_roots_comp_iff`.
- `Langlands.GroupScheme.Torus.SplitLatticeBaseChange`:
  `gmEndEquiv_baseChange`.
- `Langlands.GroupScheme.Torus.Lattice`: `latticePairing_apply`,
  `splitTorus.latticePairing_symm_symm`, `gmEndEquiv_comp`, `gmEndEquiv_id`
  (used by `simp` for the identity cocharacter in part 3),
  `eq_gmEndEquiv_zsmul`, `gmEndEquiv_zsmul_id`, `Gm.powerHom_apply` and
  `Gm.comp_zsmul_id`.
- `Langlands.GroupScheme.Multiplicative`: `hom_ext_points` and
  `Gm.groupHom_commBaseChangeIso_hom` (with the definition
  `Gm.commBaseChangeIso`).
- `Langlands.GroupScheme.Reductive.GeneralLinearRoots`:
  `GeneralLinear.roots_diagonalTorus`.
- `Langlands.GroupScheme.Reductive.RootDatum`:
  `GeneralLinear.cocharacterLatticeEquiv_symm_comp_diagonalTorus`.
- `Langlands.GroupScheme.GeneralLinearSmoothProof`:
  `GeneralLinear.smoothStatement`.

Instance theorems inserted by type-class resolution (affineness and finite type
of the group schemes involved):

- `Langlands.GroupScheme.Reductive.RootDatum`:
  `GeneralLinear.isAffineHom_groupScheme_of`.
- `Langlands.GroupScheme.Torus.RootSupportBaseChange`:
  `rootSupportBaseChangeAffine`.
- `Langlands.Shimura.Unitary.UnitaryGroupScheme`:
  `Langlands.Shimura.AlgebraInvolution.SchemeModel.unitaryGroupScheme_isAffine`.
- `Langlands.Shimura.Unitary.GroupSchemeBaseChange`:
  `Langlands.Shimura.AlgebraInvolution.SchemeModel.baseChangedUnitaryGroupScheme_isAffineHom`
  and
  `Langlands.Shimura.AlgebraInvolution.SchemeModel.unitaryGroupScheme_locallyOfFiniteType`.

The compiled terms also contain the compiler-generated auxiliary proofs
`QuasiSplitUnitary.RelativeRootsStatement._proof_1` and `_proof_2` (module
`Langlands.GroupScheme.Examples.QuasiSplitUnitaryRelativeRootsStatement`, part
of the target statement) and `QuasiSplitUnitary.baseChangeCocharacter._proof_1`
and `_proof_2` (module
`Langlands.GroupScheme.Examples.QuasiSplitUnitarySplittingCocharacter`, part of
the definition `baseChangeCocharacter`, which the proof unfolds).
