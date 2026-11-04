# Open actual norm kernel and discrete valuation quotient

Author: Worker 200.

This derived consumer removes the extra rational-point topology premises from
the open-kernel and discrete-image part of `RationalCharacterTopology`. The
field `F : Type u` is any `IsNonarchimedeanLocalField`, with its supplied
valuation and topology. The actual group scheme `G` is affine and its
structure morphism is locally of finite type. No reductivity, smoothness,
splitness, characteristic-zero assumption or restriction on `u` is needed.

Every source group in this module is `GroupScheme.rationalPoints G`, carrying
its existing categorical Hom group law and exactly
`rationalPointTopology F G.X`. The local topological-group certificate is the
published `PointTopology.rationalPoint_isTopologicalGroup`. No global
rational-point topology instance is added.

The proof of `isOpen_rationalCommonNormKernel` takes the compact open subgroup
already constructed by
`Langlands.BruhatTits.rationalPoint_exists_compactOpenSubgroup`. The published
`compactSubgroup_le_rationalCommonNormKernel` places it inside the common
kernel of the actual normalized rational-character norms. A subgroup
containing an open subgroup is open. `rationalCommonNormOpenSubgroup`
packages this very kernel as an open subgroup; its subgroup identity is
definitional. In particular, this argument does not require finite generation
of the character group or assume openness of an infinite intersection.

`rationalNormKernelQuotientDiscrete` proves that the actual quotient topology
is discrete. `rationalNormKernelQuotientContinuousEquiv` equips the published
algebraic quotient-to-valuation-image equivalence with continuity in both
directions, using discreteness. Its formula on quotient representatives is
the published algebraic identity. Composing with the continuous quotient map
proves continuity of `rationalValuationImageProjection`; the discrete target
then proves joint local constancy. Thus all actual valuation coordinates,
including an infinite family of characters, are locally constant together.
`rationalCanonicalValuationImageProjection` bundles the same actual map.

`rationalCanonicalImageUnramifiedEquiv` applies the published character
descent/pullback construction with this proved continuity. Its forward map is
evaluation after the actual image projection, and its inverse satisfies the
displayed formula on that projection. This is a multiplicative equivalence
of the existing character groups. Continuity of this equivalence with
respect to their compact-open topologies is a separate assertion and is not
claimed here.

Provenance: this is an internal deduction from the published actual
rational-point compact-open subgroup, rational norm-character continuity
and compact-subgroup containment, the algebraic quotient-to-image
identification, and the existing character descent construction. The
compact-open theorem itself uses the shared affine point-topology proofs
and the proved Van Dantzig theorem. Their proofs are reused; no second
local-profiniteness construction is introduced.

The intended source setting is Waldspurger I.1, printed pp.239–240 /
PDF pp.5–6 (`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`),
and Renard V.2.3, printed pp.105–106 / PDF pp.111–112, 9 July 2026 edition
(`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
These passages motivate the actual norm kernel and integer valuations;
the topological consumer proof above is derived from the Library.

This closes the extra nonarchimedean-group and weak local-compactness
premises for these consumers on actual finite-type affine group points.
It does not prove second countability, closed-immersion comparisons,
finite rank or full rank of the valuation image, split-center finite-index
comparisons, finite-dimensional character tori, stabilizer finiteness,
measure normalizations or a Plancherel theorem.

Local instances use explicit module-specific names to prevent generated-name
collisions under joint imports. Their types, bodies and local scope are
unchanged.
