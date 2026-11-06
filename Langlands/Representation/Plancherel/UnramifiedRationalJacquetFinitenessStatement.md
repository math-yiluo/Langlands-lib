# Native Jacquet fixed modules of the actual universal induced family

Workers 1775 and 1780. The source is David Renard,
*Représentations des groupes réductifs p-adiques*, 2026 version, VI.9.2,
printed pp.198–199 / PDF pp.204–205, especially the paragraph on printed
p.199 applying VI.5.3 to the universal supercuspidal family. Registered
source: `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The supercuspidality definition is VI.2.1, printed p.137 / PDF p.143.

`Langlands.Plancherel.RationalSupercuspidalJacquetFamilyFiniteStatement`
states finite generation over the complete rational-norm algebra of every
compact-open fixed module of every output normalized Jacquet action of the
actual universal induced supercuspidal family. It is a `Prop`-valued
definition; the coefficient-geometric-lemma argument is a remaining proof
obligation.

The field and group schemes range over universe `u`, and the inducing
carrier `E` ranges independently over `uV`. The field is an arbitrary
nonarchimedean local field, and `G` is an arbitrary connected reductive
group scheme over it. There is no splitness, matrix-group, characteristic,
or finite-dimensionality restriction.

The geometric and topological scope is explicit:

- Connected reductivity supplies the affine and smooth structures of `G`.
  Smoothness gives local finite type. The ambient point topology is exactly
  `rationalPointTopology F G.X`. The statement constructs Hausdorffness of
  the field using `BruhatTits.localField_t2Space`, Hausdorffness and local
  compactness of the point group using `rationalPoint_t2Space` and
  `rationalPoint_locallyCompactSpace`, and its nonarchimedean group
  structure using
  `Aubert.General.RationalPointFamily.affineRationalPoint_nonarchimedeanGroup`.
  These are derived structures, not additional freely supplied topologies
  or local compactness hypotheses.
- The inducing maps are actual group-scheme maps `p : P ⟶ G`,
  `l : M ⟶ P`, and `a : A.toGrp ⟶ M`, together with a verified
  `ParabolicRootPresentation p l a`. Its compatibility includes the actual
  parabolic and rational Levi predicates, maximal split torus, split
  component, and all-test-scheme comparisons with the standard and dynamic
  subgroups. In particular its realization field identifies the given
  parabolic and Levi images with a dynamic parabolic and centralizer for
  an actual cocharacter. No existence of such a presentation for arbitrary
  supplied maps is asserted. Connected reductivity of `M`, supplied by
  the rational Levi predicate, derives the affine structure used by the
  existing point and norm comparisons.
- The map `n : U ⟶ P` satisfies
  `LeviSubgroup.IsGeometricUnipotentRadical n`, so it represents the
  unipotent radical both over the field and over its algebraic closure.
  The point subgroups are literally the ranges of `p`, `l ≫ p`, and
  `n ≫ p` at the identity test scheme. The supplied `h` is an
  `IsSemidirectDecomposition` of precisely those point subgroups.
  Closedness `hU` of that literal radical in the canonical ambient
  topology and continuity `hr` of the actual projection `h.projection`
  remain explicit premises. The latter is the projection used by the
  inducing representation, rather than a projection of an unrelated
  model.
- Closedness of the inducing Levi is already proved by
  `isClosed_parabolicLeviPointSubgroup r`; its topology agrees with that
  of the Levi scheme through `parabolicLeviPointHomeomorph r`.
  The inducing parabolic is closed by its verified closed group-scheme
  embedding and the published rational-point closed-embedding theorem.
  These closedness facts are not extra premises.
- `CompactSpace (Induction.LeftQuotient (RationalNormalized.ParabolicPoints p))`
  is retained as an explicit premise for the literal inducing quotient
  `P(F) \ G(F)`, with its quotient topology. This is the compact-quotient
  input to the source induction/admissibility route. The declaration does
  not prove compactness from parabolicity. It does not impose compactness
  of a vector carrier or of the inducing group.

The inducing action `σ` acts on the literal subgroup
`parabolicLeviPointSubgroup p l`. Its smoothness, admissibility,
`Representation.IsIrreducible σ`, and
`RationalNormalized.IsSupercuspidal r σ` are separate antecedents.
The existing `IsAdmissible` convention includes smoothness and finite
generation of the complex fixed submodules for every open subgroup.
Smoothness is also written separately to retain the source-facing scope.
No implication from the new supercuspidality predicate to admissibility
is used. The companion `RationalParabolicCuspidality` module constructs
the pullback through the canonical Levi point homeomorphism and tests
vanishing of the actual character-one Jacquet quotient for every proper
rational parabolic of that Levi scheme, with every supplied actual
geometric radical. Properness is properness of the subgroup functor on
all test schemes. Thus supercuspidality supplies vanishing, not a
coefficient-finiteness hypothesis.

The scalar ring is exactly `RationalNormalized.RegularAlgebra r`, the
evaluation-generated algebra associated to every member of
`parabolicLeviRationalNormCharacters r`, indexed by all rational
characters of the inducing Levi. No finite norm subfamily or unrelated
algebra is supplied. The universal inducing carrier is the existing
tensor `RegularAlgebra r ⊗[ℂ] E` with its actual universal action. The
family is the published
`RationalNormalized.inducedRepresentation r h hU σ`, on
`RationalNormalized.Induced r h hU σ`. These are the full covariant smooth
functions with a uniform open right stabilizer and pointwise scalar
action. The inflation uses `h.projection` and the positive half-modulus
of the full inducing parabolic.

For an arbitrary output cocharacter `χ` of `G`, `outputLeviPoints χ` is
exactly the literal dynamic centralizer subgroup at the identity test
scheme. The radical is exactly
`BruhatTits.DynamicUnipotentContainment.unipotentPoints χ`. Its
closedness is supplied by the published `isClosed_unipotentPoints χ`,
and the normalizer containment is the Levi normalizer field of the
published `dynamic_isSemidirectDecomposition χ`. Its projection is the
actual dynamic limit projection, proved continuous in
`continuous_dynamic_projection`; the dynamic parabolic is proved closed
in `isClosed_dynamic_parabolic`. The closed-Levi theorem
`IsSemidirectDecomposition.isClosed_levi_of_continuous_projection` then
also gives closedness of this literal output centralizer. These output
facts require no additional supplied subgroup comparisons or topologies.
The inducing and output parabolics are independent.

`outputJacquetRepresentation r h hU σ χ` applies the existing
`UnramifiedNormalized.jacquetRepresentation` directly to that full
induced representation, the literal output radical, and the literal
output centralizer. Its carrier is precisely
`Jacquet.Localization.Coinvariants (inducedRepresentation r h hU σ) N 1`,
the quotient by the native scalar-linear span of the radical's
character-one relations. Its action twists quotient descent by the
actual inverse half-modulus character extended constantly to
`RegularAlgebra r`. There is no passage to complex scalars or substitute
finite-support induced space.

`UniversalInducedJacquetFiniteness r h hU σ` is the conclusion predicate:
for every output cocharacter and every open subgroup `J` of its literal
Levi, compactness of `J` implies
`Module.Finite (RegularAlgebra r)
  (fixedVectors (outputJacquetRepresentation r h hU σ χ) J.toSubgroup)`.
The global statement has exactly this conclusion after the geometric
and representation hypotheses above. Finite generation of these native
Jacquet fixed modules occurs only in the conclusion. No scalar
Noetherianity instance is a premise or an ingredient of the definition.

Renard's route starts with coefficient admissibility of the universal
tensor and its full normalized induction, using VI.8.1–2. In VI.9.2,
he applies VI.5.3 to the universal supercuspidal family. The output
Jacquet module has a finite filtration whose nonzero pieces are induced
conjugate coefficient families when the inducing Levi is conjugate to
a Levi subgroup of the output Levi; the other pieces vanish. This
deduces coefficient admissibility of the Jacquet module. In the present
formalization, the coefficient version of that geometric lemma,
the actual filtration and its identifications, and the resulting
compact-open fixed-module finite generation remain to be proved.
None is supplied as a premise or a model field. VI.8.3 alone is not a
general coefficient-Jacquet admissibility theorem.

This statement isolates that representation-theoretic input to the
uniform-compression argument. It neither assumes nor proves uniform
compression, eventual stability, a specialization isomorphism, or a
geometric-lemma comparison isomorphism. The only new transport needed
to state it is the concrete inducing-Levi pullback in the companion
module. Its smoothness theorem applies continuous pullback along the
published homeomorphism.
