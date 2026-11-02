# Generic finiteness of quasi-finite morphisms at minimal primes

`Langlands.AlgebraicGeometry.Morphisms.GenericFiniteness`. A quasi-finite algebra of finite
type is finite after inverting one element outside a given minimal prime of the base. The
analogous statement holds for a separated, quasi-compact, locally quasi-finite morphism locally
of finite type to an affine scheme. Etale morphisms are locally quasi-finite.

## Source and licence

Adapted from three files of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`, project literature folder "Anthropic - Fermat's
Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"):

| FLT file | SHA-256 |
| --- | --- |
| `P2M/Sol/S_Algebra_QuasiFinite_exists_not_mem_finite_awayMap_of_mem_minimalPrimes.lean` | `b43f020fc5926a044e67d68a61c4740378a177483271715e5448c799850d03c1` |
| `P2M/Sol/S_AlgebraicGeometry_LocallyQuasiFinite_exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes.lean` | `b57702c06c56f5fb8779aba9bd3436b3e680705ab1811911ad643a9a73c79b82` |
| `P2M/Sol/S_AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType.lean` | `c7940b058b0198280dde9beadd2e3b3cffd09c71ce7d27e56b73465b711f4130` |

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT
`LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT
`ATTRIBUTION.md` does not list these files as containing third-party material.

## Changes against the FLT files

- The three files are merged into one module. All declarations are in the namespace
  `Langlands.AlgebraicGeometry.GenericFiniteness`; the FLT wrapper namespaces `P2MW.<file>`,
  `GFRingGC7`, `AlgebraicGeometry` and `GFLocal` are dropped.
- The two `solution` theorems and `GFLocal.main` are renamed as listed below. The FLT
  scheme-level `solution` is a one-line wrapper of `GFLocal.main` and is omitted.
- The P2M commands `p2m_open`, `p2m_open_scoped` and `p2m_export` are replaced by ordinary
  `open` commands, and `P2M.Util` is not imported. Because the name `IsFinite` is then
  ambiguous in the scheme section, `@IsFinite` is written `@_root_.AlgebraicGeometry.IsFinite`.
- `haveI`/`letI` in proofs are written `have`/`let` (Mathlib linter).
- In `exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes`, the FLT step
  `rw [← Scheme.Hom.comp_apply, morphismRestrict_ι]; simpa using hy'` is replaced by an explicit
  `Scheme.Hom.comp_apply` rewrite, for the project Mathlib.
- The scheme section sets `backward.isDefEq.respectTransparency.types false` (an FLT lakefile
  option), which the `IsFinite` instance arguments need.
- The etale specialization reuses the published
  `Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale` from `TorsionFiniteEtale`.

## Declarations

Ring part (FLT file 1):
- `isIntegral_of_isLocalRing_of_forall_isNilpotent`: over a local ring whose maximal ideal is
  nil, a quasi-finite algebra is integral.
- `exists_not_mem_isIntegral_smul`: for a minimal prime `p` and `a : A`, some `t ∉ p` makes
  `t • a` integral.
- `finite_awayMap_of_forall_isIntegral_smul`: if each generator becomes integral after
  multiplication by `t a`, then `R_r → A_r` is finite for `r` the product of these `t a`.
- `exists_not_mem_finite_awayMap_of_mem_minimalPrimes` (FLT `solution`): for
  `Algebra.FiniteType R A`, `Algebra.QuasiFinite R A` and a minimal prime `p` of `R`, there is
  `r ∉ p` with `Localization.awayMap (algebraMap R A) r` finite.

Scheme part (FLT file 2):
- `isFinite_ι_of_isClosed`: the inclusion of a clopen open subscheme is finite.
- `IsFinite.of_forall_isClosed_of_iSup_eq_top`: a morphism is finite if its source is covered
  by finitely many clopen opens on each of which it is finite.
- `exists_isFinite_restrict_chart`: for `Spec A → Spec R` of finite type and quasi-finite,
  some `r ∉ p` makes the restriction over `D(r s)` finite for every `s`.
- `exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes` (FLT `GFLocal.main`):
  for `f : X ⟶ Spec R` locally of finite type, locally quasi-finite, separated and
  quasi-compact, and a minimal prime `p`, there is `r ∉ p` with `f ∣_ D(r)` finite. The images
  of the finitely many affine charts over `D(r)` are closed (each chart is finite there, hence
  proper) and open; the clopen criterion then gives finiteness.

Unramified part (FLT file 3):
- `locallyQuasiFinite_of_formallyUnramified` (FLT `solution`): a formally unramified morphism
  locally of finite type is locally quasi-finite (ring-level `Algebra.QuasiFinite` instance on
  affine opens).
- The existing `Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale` is imported for
  the etale specialization.
