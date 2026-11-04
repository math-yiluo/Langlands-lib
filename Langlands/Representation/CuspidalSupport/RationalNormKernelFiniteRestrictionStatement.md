# Renard VI.3.2(ii): finite semisimple restriction to the actual norm kernel

`Langlands.CuspidalSupport.RationalNormKernelFiniteRestrictionStatement` is a
closed proposition definition, not a proof. It formulates part (ii) of the
proposition in David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, VI.3.2, printed pp.143–144 /
PDF pp.149–150, together with its finite spanning-family consequence. The
registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Source statement

Renard, VI.3.2, printed p.143 / PDF p.149: let `(π, V)` be an irreducible
representation of `G`. Part (ii) says that the restriction of `(π, V)` to
`⁰G` is semisimple and of finite length. Here `G` is the group of `F`-points
of a connected reductive group defined over a nonarchimedean local field `F`
(V.1–V.2.3, PDF pp.109–111). Section VI.3 studies the category `M(G)` of
smooth complex representations (its title is “Décomposition de `M(G)`”), so
`(π, V)` is an irreducible smooth complex representation. The subgroup `⁰G` is defined in V.2.3, printed p.105 /
PDF p.111, as the kernel of `H_G : G → X^*(G)^∨`,
`⟨χ, H_G(g)⟩ = v_F(χ(g))`. Renard notes that equivalently
`⁰G = ⋂_{χ ∈ X^*(G)} ker |χ|_F`, where `X^*(G)` is the group of rational
characters of `G` defined over `F`. The proposition on printed p.106 / PDF
p.112 shows that `⁰G` is open, closed and normal, contains every compact
subgroup and contains the derived group.

Parts (i) and (iii) of the source proposition (the single `G`-orbit of
constituents and the three equivalent conditions on two restrictions) are not
formulated here.

## Lean inputs

The declaration quantifies over independent universes `u` (field and scheme)
and `uV` (representation carrier), and over:

- every `F : Type u` with `Field F`, `ValuativeRel F`, `TopologicalSpace F`
  and `IsNonarchimedeanLocalField F`. There is no restriction on the
  characteristic and no finite-extension-of-`ℚ_p` assumption, matching
  Renard's arbitrary nonarchimedean local field (V.1, PDF p.109);
- every `G : GroupScheme (Spec (CommRingCat.of F))` with
  `hG : GroupScheme.IsConnectedReductive G`. This is the shared structure:
  smooth, affine structure morphism, connected total space and trivial
  geometric unipotent radical. No splitness, quasi-splitness or general
  linear realization is assumed.

From `hG` the declaration derives `IsAffine G.X.left` with `haveI`, from
`hG.isAffineHom` and `isAffine_of_isAffineHom` (an affine morphism to the
affine base has affine source). It then installs exactly
`Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology F G.X` on
`GroupScheme.rationalPoints G` with `letI`. No further topological hypothesis
(local compactness, Hausdorff, nonarchimedean group) is displayed, because
none is needed to state the proposition. Nothing else is derived from `hG`.

For every `π : SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints G)`, an
actual smooth complex representation in the canonical smooth category, the
only hypothesis is `π.IsIrreducible`, that is,
`Representation.IsIrreducible π.representation`: the lattice of invariant
subspaces is a simple order, so the carrier is nonzero and its only invariant
subspaces are `0` and the whole carrier. This is the source's irreducibility.

The declaration then puts

- `H := Plancherel.rationalCommonNormKernel G`, the existing subgroup of
  `GroupScheme.rationalPoints G` defined in
  `Langlands.Representation.Plancherel.RationalCharacterValuation` as the
  intersection, over all actual rational characters
  `χ : GroupScheme.rationalCharacters G`, of the kernels of
  `g ↦ |χ(g)|_F` for the published residue-normalized absolute value. This is
  Renard's `⋂_{χ ∈ X^*(G)} ker |χ|_F = ⁰G`. Its normality is the existing
  instance `rationalCommonNormKernel_normal`; its openness for the canonical
  topology is proved in `RationalNormKernelTopology`, which this statement
  does not need to import;
- `ρH : Representation ℂ H π := π.representation.comp H.subtype`, the
  actual action of `π` restricted along the inclusion of `H`, on the same
  carrier as `π`. This is Renard's `Res^G_{⁰G}(π, V)`.

No central character, scalar central action, admissibility, finite
generation, finite index, compactness, semisimplicity, finite length,
candidate family or structural theorem is a hypothesis.

## Conclusions

The proposition asserts the conjunction of three clauses.

1. `Representation.IsSemisimpleRepresentation ρH`. In Mathlib this means
   that the lattice `Subrepresentation ρH` is complemented: every
   `H`-invariant subspace has an `H`-invariant complement. This is the
   source's “semi-simple”.
2. `IsFiniteLength (MonoidAlgebra ℂ H) ρH.asModule`. This is finite
   composition length over the actual subgroup group algebra `ℂ[H]`, the
   convention of `SmoothRep.HasFiniteLength`; it is not finite dimension over
   `ℂ`. The `ℂ[H]`-submodules of `ρH.asModule` are the `H`-invariant
   subspaces of the carrier, and subrepresentations and quotients of a smooth
   representation are smooth, so this is the source's “de longueur finie” for
   the restriction as a smooth representation of `⁰G`.
3. There exist `m : ℕ` and `W : Fin m → Subrepresentation ρH` such that every
   `(W i).toRepresentation` is irreducible and
   `(⨆ i, (W i).toSubmodule) = ⊤`: finitely many irreducible `H`-invariant
   subspaces together span the carrier of `π`.

“Finite” in clause 3 refers only to the number `m` of members. The carrier of
`π` and the members `W i` may be infinite dimensional. The family need not be
canonical or pairwise inequivalent, and the sum is not asserted to be direct.
No positivity condition on `m` is stated: the carrier of an irreducible `π` is
nonzero, so the spanning equation excludes `m = 0`.

## Correspondence of the finite-family clause

Clause 3 is the finite spanning-family consequence of the source's
conclusion. By standard module theory, a semisimple module of finite length
is the direct sum of finitely many simple submodules. Applied to the
`ℂ[H]`-module `ρH.asModule`, the summands are irreducible subrepresentations
of `ρH`, finitely many in number, whose sum is the whole carrier; forgetting
directness gives clause 3. Conversely, a sum of finitely many simple
submodules is semisimple and of finite length, so clause 3 also implies
clauses 1 and 2. The three clauses are stated separately as the task
requires, with clause 2 explicit, rather than relying on these implications.
This section explains the relation between the clauses; no Lean proof of
either implication is part of this unit.

## Source proof and the obligations it creates

Renard's proof on printed pp.143–144 fixes a set `Γ` of representatives in
`G` of `G/Z(G)⁰G`. It is finite by the proposition of V.2.6, printed p.108 /
PDF p.114, which shows that `G/⁰G A_G` is finite, where the split component
`A_G` of the centre lies in `Z(G)`. By Schur's lemma `Z(G)` acts on `V` by
the central character `χ_π`. Hence `Res^G_{⁰G}(π, V)` is finitely generated
and has an irreducible quotient `(σ, W)`. For a nonzero
`f ∈ Hom_{⁰G}(Res^G_{⁰G}(π, V), (σ, W))`, the map
`φ = ⊕_{γ ∈ Γ} f ∘ π(γ)` into `⊕_{γ ∈ Γ}(σ^{γ⁻¹}, W)` has `G`-stable
kernel, so it is injective by irreducibility of `V`. The restriction is
therefore isomorphic to a subrepresentation of a semisimple representation
of finite length, and the criterion of Lemma A.VII(iii) gives (ii).

The finiteness used by the source concerns `G/(⁰G Z(G))`, not `G/⁰G`: in
general `⁰G` has infinite index, since `G/⁰G` is isomorphic to the lattice
`Λ(G)`. The scalar central action, the finite index of `H` joined with the
centre, and the finite-length and semisimplicity deductions are proof
obligations of a proof of this proposition, not premises. Existing tools that
a proof may reuse include the conditional normal-subgroup result
`Langlands.FiniteIndexRestriction.finite_irreducible_restriction`, which
assumes finite index of `H ⊔ Subgroup.center` and scalar central action and
returns clauses 1 and 3, and `Langlands.Plancherel.finite_rationalCentralQuotient`,
which assumes an actual central split component and finite index of its
valuation image. Neither discharges those inputs for an arbitrary connected
reductive `G`, and neither yields clause 2 by itself. The general linear
product-Levi statement `Langlands.CuspidalSupport.LeviFiniteRestrictionTheorem`
is a special case on different groups.

## Scope

The module defines only this proposition. It imports the canonical smooth
representation category, the published norm kernel, the rational-point
topology, the connected reductive structure and Mathlib's semisimplicity API,
without changing their Lean or Markdown files. It states no proof, adds no
group, topology or norm-kernel definition, and does not establish VI.3.2(i),
VI.3.2(iii) or the VI.3.3.1 inertia decomposition.
