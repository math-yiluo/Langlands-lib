# Existence of the actual algebraic Siegel setup

Worker 715

`Langlands.Global.AdelicSiegelFactors.siegelAlgebraicSetupExistence` proves
`SiegelAlgebraicSetupExistenceStatement.{u}` for an arbitrary universe `u`. For
every number field `F : Type u` and every affine, locally finite type, connected
reductive group scheme `G` over `F`, it supplies `T`, `i`, `ν`, `T₀` and `j`
satisfying `IsSiegelAlgebraicSetup F G T i ν T₀ j`.

The Lean proof applies `siegelAlgebraicSetupExistence_of_structural` to three
published theorems.

- `genericMinimalParabolic` gives minimality of the dynamic parabolic attached
  to the generic cocharacter `ν`. The assembly transfers this to the canonical
  standard parabolic `Standard.parabolicHom i ν ∅` via equality of subgroup
  functors.
- `derivedMaximalSplitTorus` gives a maximal split torus `T₀` of the derived
  subgroup that maps compatibly into the ambient maximal split torus `T`.
  The resulting map `T₀ ⟶ T` is the witness `j`.
- `derivedCentralSplitTorusProduct` gives a central isogeny from the product of
  `T₀` and the central split component `Z₀` to `T`. After identifying the two
  multiplication maps, its surjectivity supplies the scheme-surjectivity clause
  of `IsSiegelAlgebraicSetup`.

The assembly chooses `T` using the trivial cocharacter and then chooses a
generic `ν` on `T`. It obtains the derived subgroup and split component from
their representability and existence theorems. It uses the published standard
subgroup comparisons for the rational Levi, the geometric unipotent radical,
the equality of the standard Levi subgroup functor with the torus centralizer,
and the identification of the nonzero weights on `Lie P` with the positive
relative roots.

The algebraic data are those used by Getz and Hahn, *An Introduction to
Automorphic Representations* (2024), §2.7, printed p. 71 (PDF p. 88), in the
paragraph preceding (2.25). The registered source is
`getz-hahn-2024-automorphic-representations` (SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`).
The proof follows the published Lean assembly, which starts with a maximal
split torus and obtains the minimal parabolic from a generic cocharacter.
[Published statement and structural assembly](AdelicSiegelSetupExistence.md)
