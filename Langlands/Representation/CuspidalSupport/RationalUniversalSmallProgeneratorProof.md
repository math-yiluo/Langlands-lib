# Renard VI.4.1 for the full-restriction Π₁: proof

`Langlands.CuspidalSupport.rationalUniversalSmallProgenerator` proves exactly the
published proposition
`Langlands.CuspidalSupport.RationalUniversalSmallProgeneratorStatement.{uF, uV}`
(module `Langlands.Representation.CuspidalSupport.RationalUniversalSmallProgeneratorStatement`),
at two independent arbitrary universes: `uF` for the field and group, `uV` for
the carrier of the representation π. [Statement](RationalUniversalSmallProgeneratorStatement.md)

The theorem proves the stated proposition at both universes with the structural
and cuspidality hypotheses specified below; it adds no hypothesis of its own. Its
axioms are `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

Fix a nonarchimedean local field `F : Type uF` of either characteristic, a
connected reductive group scheme `G` over `Spec F`, a maximal split torus
inclusion `i`, the canonical topology `rationalPointTopology F G.X` on `G(F)`
together with the target's three topological premises (locally compact,
nonarchimedean group, Hausdorff), a generic cocharacter `ν`, and the target's
structural premises `StandardCocharacterStatement.{uF}`, `HasRelativeRootSystem i`
and closedness of every standard unipotent subgroup. Let
`π : SmoothRep.{0, uF, uV} ℂ G(F)` be irreducible and cuspidal in the sense of
`Aubert.General.IsCuspidal` for the actual families `parabolic i ν`,
`levi i ν`, `unipotent i ν`: every proper standard normalized Jacquet module
vanishes.

Write `H⁰ = Plancherel.rationalCommonNormKernel G` (Renard's `⁰G`),
`ρH = π.representation.comp H⁰.subtype` for the entire restriction of π to
`H⁰`, and `Π₁ = rationalNormKernelCompactInduction G π` for its compact
induction to `G(F)`, with carrier in `Type (max uF uV)`. The block is
`RationalInertiaBlock G (rationalInertiaBaseLift G π)`, the full subcategory of
smooth representations with carrier in `Type (max uF uV)` all of whose
irreducible subquotients are isomorphic to an unramified twist of the lift of π
to that universe. The theorem proves `IsRationalNormKernelSmallProgenerator G π`:

- **membership**: every irreducible subquotient of Π₁ lies in the unramified
  orbit of the lifted π, so Π₁ is an object `P` of the block;
- **projective lifting**: for every epimorphism `q : X ⟶ Y` of the block and
  every `f : P ⟶ Y` there is `g : P ⟶ X` with `g ≫ q = f`;
- **generation**: the integer-module Hom functor
  `Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P` is faithful;
- **coproducts**: the block has coproducts indexed by every
  `I : Type (max uF uV)`;
- **smallness**: `preadditiveCoyonedaInt P` preserves all of these coproducts.

The proof establishes block membership, projective lifting, faithfulness of the
integer-module Hom functor, coproduct existence and preservation of those
coproducts. None of these is assumed, and neither abelianness of the block nor
admissibility of π is assumed. Finite dimension of Π₁ is neither assumed nor
claimed: for the trivial representation of a split one-dimensional torus `F^×`,
Π₁ is the space of finitely supported functions on `F^× / O^× ≅ ℤ`.

## The Lean proof

The proof is one application:

```
rationalUniversalSmallProgenerator_of_jointBasis
  Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence
```

- `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`
  (module `Langlands.BruhatTits.SpecialCompact.JointBasisProof`) proves
  `JointSpecialCompactBasisExistenceStatement.{uF}` with no hypotheses: for
  every `F`, `G`, maximal split torus `i` and generic `ν` there are one
  apartment datum `D`, one special apartment vertex `x`, and a represented
  torus centralizer `Z` with closed inclusion `j`, factorization `s` and
  character-restriction bijection `h`, such that
  `K0 = D.specialCompactSubgroup x` satisfies the special compact properties,
  the Renard Cartan comparison and the simultaneous standard basis, among
  other conjuncts (Renard V.5.1–V.5.2).
  [Joint basis proof](../../BruhatTits/SpecialCompact/JointBasisProof.md)
- `rationalUniversalSmallProgenerator_of_jointBasis` (module
  `RationalUniversalSmallProgeneratorSpecialVertexReduction`) derives the
  target from that proposition.
  [Reduction](RationalUniversalSmallProgeneratorSpecialVertexReduction.md)

The rest of this page follows the composite proof through the published
theorems it unfolds to.

### Step 1: the special-vertex inputs

`rationalSpecialVertexCompactInputs_of_jointBasis` (module
`RationalCuspidalInertiaDecompositionReduction`) turns the joint witness into
`RationalSpecialVertexCompactInputsStatement.{uF}`. It keeps `D`, `x`, the
special-vertex property, `SpecialCompactProperties F i ν K0` and
`SimultaneousStandardBasisAt i ν K0`. The covering clause
`FiniteCartanCovering F i ν K0` comes from
`Aubert.General.RationalPointFamily.rationalPositiveCartanCover`, applied to the
same `Z`, `j`, `s`, `h`, the representation of the centralizer, the equality
`s ≫ j = i` and the Renard Cartan comparison
`SpecialCompactRenardComparison D x ν j s h`. The vertex `x` only fixes
`K0`; the cover itself has the form required by
`FiniteCartanCovering` (Renard V.5.1(4)): there is a finite set `F0` of actual
centralizer points such that every `g ∈ G(F)` can be written as
`g = k₁ * f * rationalPoints.map i a * k₂` with `k₁, k₂ ∈ K0`, `f ∈ F0`, and
`a` ranging over `CocharacterUniformizer.CAplus F S (simpleRelativeRoots i ν)`,
Renard's `C_A^+`: the points of the uniformizer lattice of the split torus `S`
at which every simple relative root has normalized norm at most one. The proof
of `rationalPositiveCartanCover` takes `F0` to be the image under `j` of the finite set in the positive cover of
the Renard comparison. It places `g` in the `K0`-double coset of
`rationalPoints.map j (c * f)`, where `f` lies in that finite set and
`c = rationalPoints.map s (uniformizerSection S λ)` for a cocharacter `λ`
nonnegative on the positive relative roots. With `a` the uniformizer section of
`λ`, the factorization `s ≫ j = i` gives `rationalPoints.map j c =
rationalPoints.map i a`, and `rationalPoints.map i a` is moved past
`rationalPoints.map j f`, which centralizes the split torus.

### Step 2: compact coefficients of the restriction (Renard VI.2.1)

`rationalUniversalSmallProgenerator_of_specialVertexInputs_of_restriction`
introduces every binder of the target, obtains `D`, `x` and the three properties
of `K0` from Step 1, and applies the published VI.2.1 (a) ⇒ (c) theorem
`Aubert.General.rationalCuspidalCompactRestriction` to them, to the target's own
`hStandard`, `hRoots` and `hU`, and to the cuspidality of π. The result is
`HasCompactSmoothDualCoefficients ρH`: for every vector `v` of π and every
linear form `ℓ` that is a smooth vector for the dual action of `H⁰`, the matrix
coefficient `h ↦ ℓ(ρH(h) v)` has compact support in `H⁰` (Renard VI.2.1 uses
the same smooth-dual convention).

The reduction then applies `rationalNormKernelSmallProgeneratorReduction`
(module `RationalUniversalSmallProgeneratorReduction`) to connected
reductivity, irreducibility, these compact coefficients and the published
proofs `rationalNormKernelFiniteRestriction` and
`rationalNormKernelTwistEquivalence`. The first is Renard VI.3.2(ii): `ρH` is
semisimple and of finite length over `MonoidAlgebra ℂ H⁰`; the published Lean
theorem also records the consequence of these two properties that `ρH` is
spanned by finitely many irreducible subrepresentations. The second is Renard
VI.3.2(iii), used at carrier universes `max uF uV`. The reduction theorem proves
the membership and the four conditions as follows.

### Membership

`rationalNormKernelCompactInduction_mem_of_restriction` (module
`RationalUniversalMembership`). Take the finite family `W` of irreducible
subrepresentations spanning `ρH`. Let `D` be an irreducible subquotient of Π₁.

1. The finite-family projector attached to `W` acts as the identity on `π`,
   hence on every unit vector of the compact induction, and by coset-sum
   naturality on all of Π₁ (`openNormalFamilyProjector_fixes_compactInduction`).
   Passing through the subquotient presentation of `D`,
   `openNormalFamily_compactInduction_subquotient_restricted_hom` gives a
   nonzero `H⁰`-intertwiner from the restriction of `D` to `ρH`. Openness of
   `H⁰` (`isOpen_rationalCommonNormKernel`) and compact coefficients of `ρH`
   enter here.
2. Composing with the restriction of `SmoothRep.universeLiftEquiv` gives a
   nonzero `H⁰`-intertwiner from `D` to the lifted π; it stays nonzero because
   that equivalence is injective. The lift of π is irreducible
   (`SmoothRep.isIrreducible_universeLift_iff`).
3. The twist equivalence, nonzero intertwiner ⇒ equivalent restrictions ⇒
   unramified twist, gives `χ` in the unramified characters with
   `rationalUnramifiedTwist G χ D` equivalent to the lifted π. Converting this
   equivalence to an isomorphism and applying `IsRationalInertiaRelated.symm`
   puts `D` in the orbit of the lifted π.

This is the exact `rationalInertiaBlockProperty` of Π₁.

### Projective lifting

`rationalNormKernelCompactInduction_projective` (module
`RationalUniversalProjectivity`) proves that Π₁ is projective among all smooth
representations. The restriction `ρH`, raised to the function-carrier universe
by `SmoothRep.universeLift`, has compact coefficients, so it is projective
among smooth representations of `H⁰`
(`CompactCoefficient.projective_of_compactCoefficients`: compact coefficients
make it semisimple, and each irreducible compact summand is projective, as in
Renard IV.1.6 and its Corollary). Compact induction from the open subgroup `H⁰`
is left adjoint to restriction, which preserves epimorphisms, so it preserves
projectives (`Induction.projective_smoothCompactInduction`). The carrier
equivalence identifies the result with Π₁. The topological facts needed
(Hausdorff, locally compact and totally disconnected `G(F)`) are proved from the
local field.

`rationalInertiaBlock_projective_of_projective` (module
`RationalInertiaLifting`) moves this into the block: the block property is
closed under subquotients, so an epimorphism of the block is surjective
(`rationalInertiaBlock_epi_iff_surjective`), hence an epimorphism of smooth
representations; the ambient lift is a block morphism by fullness.
`rationalNormKernelBlockProjectiveLift` chooses the lift `g` and
`rationalNormKernelBlockProjectiveLift_comp` proves `g ≫ q = f`.

### Faithful Hom functor

`rationalNormKernelHom_faithful` (module `RationalUniversalGeneration`) applies
the criterion `SmoothRep.faithful_preadditiveCoyonedaInt_of_projective_subquotients`
(module `Category.ProjectiveGeneration`). Its inputs are the ambient
projectivity above and, for every block object `Y` and irreducible subquotient
`D` of `Y`, a nonzero map Π₁ ⟶ `D`. The block property of `Y` puts `D` in the
orbit of the lifted π. Unramified characters are trivial on `H⁰`, so the
restriction of `D` to `H⁰` is equivalent to `ρH`; the open-subgroup coset sum
of this equivalence is a surjection `rationalNormKernelInertiaQuotient` from Π₁
onto `D` (module `RationalUniversalQuotients`). It is nonzero because `D` is
nonzero. The criterion then works as follows. If two block morphisms
`X ⟶ Y` have the same image under the Hom functor, every map out of Π₁ is
annihilated by their difference `d`. If `d ≠ 0`, its image is nonzero and has an
irreducible subquotient `D`, which is also a subquotient of `Y`. The nonzero map
Π₁ ⟶ `D` lifts by projectivity to a nonzero map into the image of `d`, and then
along the surjection from `X` onto that image; its composite with `d` is
nonzero, a contradiction.

### Coproduct existence

`rationalInertiaBlock_hasColimitsOfShape` (module `RationalInertiaCoproducts`),
with index universe `max uF uV`. The concrete smooth direct sum of a family of
block objects has carrier in the same universe. Every irreducible subquotient of
it is a subquotient of one summand (`SmoothRep.irreducibleSubquotient_directSum`),
so it lies in the block (`rationalInertiaBlockProperty_directSum`), and the
ambient universal property restricts to the full block.

### Coproduct preservation

`rationalNormKernelHom_preservesCoproducts_of_finiteLength` (module
`RationalUniversalSmallness`). Finite length of `ρH`, the second clause of
VI.3.2(ii), makes it Noetherian, hence finitely generated over
`MonoidAlgebra ℂ H⁰`. Since `H⁰` is open, `Induction.finite_compactInduced_of_finite`
makes Π₁ finitely generated over `MonoidAlgebra ℂ G(F)`. Then
`hom_preservesFullSubcategoryCoproducts` (module
`Category.FiniteGenerationCoproducts`), with the block's direct-sum closure,
shows that the Hom functor of a finitely generated object preserves every
`Discrete I` coproduct: a map into a direct sum is determined on finitely many
generators, so it has finitely many nonzero components.

## Comparison with Renard

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, VI.4.1 Proposition and the following Remark, printed
pp.149–150 / PDF pp.155–156 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). The Remark
states that Π₁ = `ind_{⁰G}^G Res_{⁰G} π` is a progenerator by the argument given
for the single-summand Π, with finite generation from finite length of the
restriction.

- Renard's π is supercuspidal and the decomposition of `Res_{⁰G} π` into compact
  representations is cited from VI.3.2. Here π is cuspidal along the proper
  actual standard parabolics, and compactness of `ρH` comes from VI.2.1
  (a) ⇒ (c), whose structural inputs at a special vertex are supplied by the
  joint special-compact basis.
- Projectivity: Renard uses projectivity of compact representations (IV.1.6) and
  the adjunction (VI.4.1.1); the Lean proof is the same argument for the entire
  restriction, followed by an explicit transfer into the full block.
- Generation: Renard uses semisimplicity of restrictions to `⁰G` of objects of
  the block to find `ρ` inside every nonzero block object. The Lean proof
  instead maps Π₁ onto each irreducible subquotient in the orbit and uses
  projectivity to detect nonzero morphisms, without a semisimplicity argument
  for arbitrary block objects.
- Smallness: finite generation of Π₁, as in the Remark.
- Membership of Π₁ in `M(G)_{[π]}`, implicit in Renard, is proved from the finite
  spanning family and the twist criterion VI.3.2(iii).
- Coproduct existence in the block, implicit in Renard, is proved by the direct
  sum construction.
