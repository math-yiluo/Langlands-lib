# Galois stability of the uniformizer-power normal-basis lattice

The theorem
`Langlands.NYLL.LocalClassFieldTheory.galoisGroup_apply_mem_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice`
proves the exact published target with suffix `Statement`. It retains the full
source telescope: fields `K L : Type u`, their algebra, finite-dimensional and
Galois instances, a valuative relation, topology and nonarchimedean local-field
structure on `K`, the level `n`, automorphism `sigma`, element `x` and membership
premise `hx`.

A private helper `latticeStableForDilate` proves stability of the integer lattice
by induction over its defining span. On an orbit generator, applying `sigma`
gives the generator indexed by `sigma * tau`. Zero and addition are preserved;
for integer scalars, the automorphism fixes their images from `K`, so it commutes
with scalar multiplication. This implements the argument of source M144.007
without depending on its unpublished proof or publishing its reserved name.
The generator step uses the orbit definition directly instead of M144.004.

The main proof unfolds membership in the scalar-image submodule. Given the
witness `y` for `x`, it uses `sigma y` as witness for `sigma x`. The helper gives
lattice membership, and multiplicativity plus `sigma.commutes` show that the
base-uniformizer scalar is fixed. This uses the definitional equivalence of
source M144.015 directly. The only import is the published
`NormalBasisGaloisAction.LatticeStabilityStatement` module and its published
transitive definitions and Mathlib imports; there are no unpublished imports.

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean`,
lines 98–118, M145.004. The private span proof adapts
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 91–117,
M144.007; scalar-image membership is at lines 178–184, M144.015.
Registered source `nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Worker 517 extracted the proof, prefixed the namespace, reduced imports, stated
the theorem through its published proposition, and made the helper adaptations
above. The original author/copyright header is retained; Apache-2.0 LICENSE and
NOTICE remain in `licenses/NYLL/`. This is a supporting lattice theorem and
claims no host class-formation or reciprocity result.
