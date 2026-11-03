# Local-point prerequisites for smooth real characters

Authors: Workers 118 and 6.

This module states three local-point obligations used by the proof route for
Renard V.3.19. Every declaration is a proposition definition. No compactness,
cocompactness, or derived-point annihilation theorem is proved here.

Fix a nonarchimedean local field `F`, in either characteristic, and an actual
group scheme `M` with `hM : IsConnectedReductive M`. Write `K` for the existing
`Langlands.Plancherel.rationalCommonNormKernel M`, `Z` for the existing
`schemeCenterPoints M`, and `D` for
`(derivedSubgroup M).carrier (Over.mk (𝟙 _))`. These abbreviations in the
explanation refer to subgroups of the same `rationalPoints M`; this module
introduces no replacement group, torus, or valuation lattice.

The three parameterized targets assert:

1. `CentralNormKernelCompactness M hM`: the subset `Z ∩ K` is compact.
2. `CentralDerivedNormKernelCocompactness M hM`: the point-group quotient
   `K / (((Z ∩ K) ⊔ D).subgroupOf K)` is compact.
3. `DerivedSmoothRealAnnihilation M hM`: every homomorphism
   `f : M(F) →* Multiplicative ℝ` with open kernel satisfies `D ≤ f.ker`.
   Its target is the additive group of real numbers written multiplicatively,
   so membership in the kernel means additive value zero.

Each target derives affineness from `hM` and explicitly installs
`rationalPointTopology F M.X`. The subgroup and quotient topologies in the
second target are inherited from that topology. The slash is a quotient of
actual point groups, not the rational points of a scheme quotient. The
`subgroupOf K` expression takes the intersection with `K` explicitly and does
not assume derived-point membership in `K` in order to form the quotient.
Its identification with `(Z ∩ K)D` uses that separate inclusion and normality.
The three closed declarations ending in `Statement` quantify every such
field and group in universe `u`; `SmoothRealStructureStatement.{u}` is their
conjunction. There are no splitting, characteristic, tameness, or
residue-characteristic restrictions and no structural conclusions supplied
as hypotheses.

## Original source and derived formulation

The registered source is Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026,
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original passages read for this unit are V.2.1, printed p.104 / PDF p.110;
V.2.2–V.2.3, printed pp.105–106 / PDF pp.111–112; V.2.5–V.2.6, printed
pp.107–108 / PDF pp.113–114; and V.3.19, printed p.115 / PDF p.121.
The supplementary registered source
`renard-2010-corrections-complements`, SHA-256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is the author's errata for the 2010 edition, not a separate correction of the
2026 edition. Its PDF pp.8–9 were also read: p.8 explicitly replaces
finite-index claims at 2010 printed pp.125 and 134 by cocompactness in
positive characteristic. The governing 2026 passages already use
cocompactness. This module retains that distinction.

V.2.1 distinguishes the algebraic derived subgroup from the center and its
connected radical. V.2.3 defines the common norm kernel and states that the
algebraic derived points lie in it. V.2.6 states compactness of the norm-kernel
intersection with the center. V.3.19 uses cocompactness of the product of the
radical points and derived points, then of its intersection with the norm
kernel, to prove that every smooth additive real map kills that kernel.

The first target preserves V.2.6 using the full all-test scheme center. This
retains the possible disconnected or nonsmooth schematic center rather than
silently replacing it by its radical. The second is an intermediate
local-point consequence needed by V.3.19: replacing the radical by the larger
center preserves the intended compact quotient. This is a derived target,
not a claim that a displayed formula in Renard defines this Lean quotient.
In particular, the proof must establish the subgroup and topology comparisons.

The third target isolates a missing justification in the abbreviated source
argument. Renard invokes triviality on commutators after discussing the
algebraic derived subgroup. A group homomorphism to an abelian group kills
the abstract commutator subgroup automatically; it does not follow by
definition that it kills all rational points of the algebraic derived
subgroup. The Lean target retains that actual derived functor. It asserts
annihilation by ambient smooth real homomorphisms, without asserting equality
with abstract commutators. Its provenance is this explicitly identified
proof prerequisite.

## Ownership and proof boundary

The algebraic derived subgroup and scheme center are imported from the shared
algebraic-group program. Their representability, central-product, and
commutative-target annihilation interfaces remain with that program.
Scheme epimorphy supplies neither surjectivity on local points nor
cocompactness or finite index there. In equal characteristic an inseparable
isogeny can have infinite-index image on rational points; this unit makes
no finite-index claim.

`CenterSplitComponentCompactnessStatement` is a related existing target for
`Z(F)/A(F)` with an actual maximal central split torus. It is not repeated
here: compactness of `Z ∩ K` concerns a different subset and needs a comparison
with the valuation kernel. Likewise, the final
`Langlands.Plancherel.RationalSmoothRealDescentStatement` is separately owned;
this module does not introduce a competing norm-kernel annihilation or
unique-factorization target.

After these prerequisites are proved, one must still prove their application
to norm-kernel annihilation: compact groups have trivial smooth real image;
the derived clause kills `D`; the remaining compact quotient has finite
smooth image, which is trivial in the torsion-free real group. Those
topological and quotient steps, and the unique factorization through the
existing valuation-image projection, are further proof obligations. They
are not supplied by this statement pair or assumed as new Renard external
structural hypotheses.
