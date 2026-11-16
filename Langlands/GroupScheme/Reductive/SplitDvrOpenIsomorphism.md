# Generically equal reductive open subgroups over a DVR

This is an internal derived construction used in the reductive monomorphism
argument. It combines the closed-field isomorphism in
`Reductive.SplitOpenGenericIsomorphism` with field-extension descent and the
two-fibre criterion in `AlgebraicGeometry.DiscreteValuationFibreIsomorphism`.
It makes no claim to translate a separate external theorem.

Let `R` be a local integral domain, let `K` be a fraction field, and let
`f : M ⟶ G` be a homomorphism of group schemes over `Spec R`. The hypotheses are:

- `M` is reductive and `G` is smooth and affine over `R`;
- the underlying scheme morphism of `f` is a monomorphism and an open immersion;
- the base change of `f` to `Spec K` is an isomorphism;
- for a finite type `I`, there is a closed subgroup inclusion
  `i : splitTorus (Spec R) I ⟶ M` that is fibrewise maximal.

The generic isomorphism and the supplied coordinate split torus are explicit
hypotheses. All rings, schemes and torus indices are in the declared universe.

`closedResidueField_isIso` proves that `f` becomes an isomorphism over the
canonical residue field `k` of `R`. The proof applies `closedFieldIso` to the
algebraic closure of `k`. The structural map from `R` to this closure is local:
it is the composite of the canonical residue homomorphism with a homomorphism
between fields. Its unique point therefore lies over the closed point of `R`,
as required by `closedFieldIso`. The scalar-tower base-map identity and
`TorusIsomorphismLocus.isIso_comp_baseChange_iff` identify this pullback with the
iterated pullback through `k`. Finally,
`TorusExistence.isIso_of_isIso_baseChange` reflects the isomorphism along the
field extension from `k` to its algebraic closure. This lemma only needs the
local-domain hypotheses, not the DVR assumption.

For `isIso_of_dvr`, assume additionally that `R` is a discrete valuation ring.
The reductivity of `M` supplies flatness and local finite presentation of its
structural morphism, while smoothness of `G` supplies local finite type. The
supplied generic isomorphism and the derived residue-field isomorphism satisfy
`Langlands.AlgebraicGeometry.isIso_of_generic_special` for the underlying
morphism in `Over (Spec R)`. That criterion proves the underlying scheme map
is an isomorphism; `TorusIsomorphismLocus.isIso_of_underlying` then reflects it
to the group-scheme category.

`dvrIso` is the resulting actual isomorphism `M ≅ G`, constructed as `asIso f`.
The simplification lemma `dvrIso_hom` states that its forward homomorphism is
exactly `f`. This unit retains the split-torus hypothesis and does not assert
the unrestricted reductive monomorphism closed-immersion theorem.
