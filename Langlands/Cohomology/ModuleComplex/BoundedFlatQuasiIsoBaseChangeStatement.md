# Base change of quasi-isomorphisms between bounded flat complexes

`Langlands.Cohomology.ModuleComplex.BoundedFlatQuasiIsoBaseChangeStatement.{u}`
is a Prop-valued algebraic statement, in an arbitrary carrier universe u.

Let R be a commutative ring. Let K and C be natural-number-indexed complexes
of flat R-modules, both zero in degrees strictly greater than a common n,
with differentials δ and d. Let φ be a chain map from K to C. Assume it
induces an isomorphism on degree-zero cycles and on all positive cohomology
modules. For every commutative R-algebra A, the conclusion asserts the same
four cycle and boundary conditions for the degreewise base change of φ from
A tensor K to A tensor C.

The degree-zero hypotheses say that a δ-cycle killed by φ is zero, and every
d-cycle is the image of a δ-cycle. In each positive degree the hypotheses say
that a δ-cycle whose image is a d-boundary is a δ-boundary, and every d-cycle
is the image of a δ-cycle modulo d-boundaries. The conclusion repeats these
conditions with each linear map replaced by `LinearMap.baseChange A`.
Thus “quasi-isomorphism” in this statement is expressed entirely through
cycles and boundaries; it does not use a chosen derived-category isomorphism.
The differential-square-zero and chain-map identities are explicit hypotheses.

No flatness of A over R and no noetherianity or finiteness assumption are
made. Flatness of every term of both bounded complexes is required. The
statement alone supplies no geometric base-change map or naturality result.

## Provenance

The theorem type is taken from the registered original
`anthropic-flt-complete-lean-source-6e837e75`, folder SHA-256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`,
Anthropic FLT commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:

- `Theorems/Thm_Module_quasiIso_baseChange_of_quasiIso_of_flat.lean`,
  complete theorem `Module.quasiIso_baseChange_of_quasiIso_of_flat`;
- `P2M/Sol/S_Module_quasiIso_baseChange_of_quasiIso_of_flat.lean`,
  theorem `solution` and the `QisoBC` cone construction.

The Lean file preserves the quantified theorem type and packages it as a
Prop-valued definition in the Langlands namespace. It imports Mathlib alone;
it does not import the original proof or P2M wrapper. No proof is claimed here.
Copyright and license are retained in the Lean header and in
`licenses/Anthropic-FLT/LICENSE` and `licenses/Anthropic-FLT/NOTICE`.
