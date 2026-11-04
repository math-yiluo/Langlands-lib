# Complete dynamic threshold regions under split-torus restriction

Author: Worker 200.

This internal adapter combines the exact dynamic root-restriction image
formula in `SubtorusIntertwiningRoots` with the compatible-form comparison
in `IntertwiningCone`. It then specializes to the single ambient Weyl form
constructed in `AmbientCharacterFormNaturality` and the actual continuous
characters used in `AmbientCharacterIntertwiningCone`.

For an arbitrary field and arbitrary morphism `f : A → T` of actual split
tori, let `i : T.toGrp → G` be an arbitrary morphism to a smooth affine
group scheme. Suppose the explicit forms `B_A`, `B_T` and real linear lift
`L` satisfy `CompatibleCharacterForms f B_A B_T L`. The generic theorem
`CompatibleCharacterForms.mem_intertwiningRegion_dynamic_iff` says that
the following two conditions are equivalent for every real parameter `x`,
integral cocharacters `nu`, `eta` of `A`, and real threshold `R`:

- `L x` satisfies every ambient root inequality for `i`, using the dynamic
  subgroup of `cocharacterMapInt f nu` and the dynamic subgroup of the
  negative of `cocharacterMapInt f eta`.
- `x` satisfies every local root inequality for `groupHom f ≫ i`, using the
  dynamic subgroup of `nu` and the dynamic subgroup of `-eta`.

The proof unfolds the regions, substitutes the exact image formula for
the local root intersection, and applies
`CompatibleCharacterForms.mem_rootThresholdRegion_iff`. That image formula
retains every root in both dynamic supports: strict positivity excludes
zero restricted weights, and either sign depends only on the restricted
character. Different ambient roots may restrict to the same local root.
Neither injectivity of character restriction nor an equality between
arbitrary images of subgroup intersections is needed.

`weylInducedCharacterForm_mem_intertwiningRegion_dynamic_iff` applies this
theorem to the constructed orthogonal lift and the form induced from the
single ambient relative Weyl form. This specialization requires the
underlying maps of `f` and `i` to be monomorphisms and an explicit finite
ambient relative Weyl quotient. Its local form is the induced form;
no equality with an independently chosen local Weyl form is claimed.

For a nonarchimedean local field `F`, an affine locally finite type group
scheme `M` and a specified morphism `j : A.toGrp → M`,
`weylAmbientUnramifiedIntertwiningRegion` is a subset of the existing
continuous unramified-character group of `M`. The topology on actual
rational points is `rationalPointTopology F M.X`. For each character,
restrict its underlying point character along `j`, take its normalized
real part in the full real character space of `A`, and apply the
constructed orthogonal lift. The definition tests that lifted parameter
against every root in the ambient dynamic intersection, with the
constructed ambient Weyl form and the postcomposed cocharacters above.
The normalized real part uses the existing negative logarithm divided
by the logarithm of the residue cardinality.

When `G` is also smooth,
`weylAmbientUnramifiedIntertwiningRegion_eq` proves equality with
`weylUnramifiedIntertwiningRegion` for the corresponding local dynamic
subgroups. The proof applies the preceding real-region comparison to the
normalized real part of each canonical continuous character. Reductivity
of `M` and split-component hypotheses are unnecessary for this equality.

With `IsConnectedReductive M` and the actual predicate `IsSplitComponent j`,
`exists_positiveImageCharacter_mem_weylAmbientUnramifiedIntertwiningRegion`
retains a real additive functional on the actual valuation image of `M`
whose positive image character, transported by the canonical continuous
equivalence, belongs to this region. It rewrites by the proved set equality
and applies the existing positive-witness theorem. The same character
therefore satisfies all local inequalities as well.
`weylAmbientUnramifiedIntertwiningRegion_nonempty` retains that witness
and proves nonemptiness for every `nu`, `eta`, and `R`.

All fields retain arbitrary universe and characteristic. The complete
actual root sets include multipliable roots; empty intersections, rank
zero and central directions are allowed. The provenance is composition
of the proved exact root-image formula, compatible-form identity,
ambient-form construction and positive actual-image character witness.
The adapter identifies no common Levi or opposite parabolic radical,
and imposes no finite-length representation hypothesis. Convergence,
rational continuation and the Plancherel theorem remain separate
obligations.
