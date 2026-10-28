# Open-subgroup invariants of actual rational quotient sections

Worker 36 constructed this derived interface over the published
`OpenSubgroupTransport` category and its actual rational quotient algebras.

The hypotheses are a complete ultrametric normed field `K`, a presented strict
affinoid algebra `P`, a topological group `G`, and a
`RationalSpectralAction G P`. The universes of `K` and `G` are independent.
The action retains the published restricted rational spectral topology. For
an object `X`, write `U = X.subgroup` and `B = X.domain.obj.algebra`.
Here `U` is an actual open subgroup and `B` is the actual complete closed-ideal
Tate quotient for the chosen invariant unit-radius rational presentation.
Invariance of the domain means preservation of its locus as a set.

## Fixed subalgebras and their norm topology

`sectionOperator X k`, for `k : U`, is the forward bounded algebra operator
on `B` obtained from the published `sectionAction`. The map from `U` into the
locus stabilizer is the constructed `invariantStabilizerInclusion`. Thus this
definition acts on actual quotient elements.

`invariantSubalgebra X` is the `K`-subalgebra

`B^U = ⋂ (k : U), equalizer (sectionOperator X k) id`.

The theorem `mem_invariantSubalgebra` identifies membership exactly with
`∀ k : U, sectionOperator X k b = b`. The intersection uses Mathlib's
subalgebra lattice and algebra-homomorphism equalizers, so the algebra
operations and constants are inherited from `B`.

`isClosed_invariantSubalgebra` expresses the carrier as the intersection of
the sets `{b | sectionOperator X k b = b}`. Each operator is bounded and hence
continuous, so each equality locus is closed in the norm topology of `B`.
Arbitrary intersections remain closed. The resulting `CompleteSpace` instance
uses closedness inside the complete quotient `B`. This proof needs no
continuity of the operators as a function of the group parameter.

`invariantInclusion X` is the bounded subtype inclusion `B^U → B`, with
positive bound one. Its application theorem states that it sends a fixed
section to its underlying quotient element. The fixed algebra carries the
inherited norm; the construction does not give it a finite affinoid
presentation.

## Actual pullbacks preserve invariants

For `f : X ⟶ Y` labelled by `g : G`, put `V = Y.subgroup` and
`C = Y.domain.obj.algebra`. The category supplies the actual continuous
homomorphism `f.groupHom : U → V`, given by `k ↦ g k g⁻¹`.
Its `Hom.restriction` is the constructed bounded pullback `C → B`.

`Hom.restriction_mem_invariantSubalgebra` proves that a section fixed by `V`
pulls back to one fixed by `U`. The proof evaluates the published
`Hom.sectionAction_restriction` equality on the section. This equality says

`f.restriction (sectionOperator Y (f.groupHom k) c) =`
`sectionOperator X k (f.restriction c)`.

For a fixed `c`, the left side is `f.restriction c`; reversing the equality
gives the required fixed-point equation in the source. The subgroup condition
on the arrow ensures that `f.groupHom k` lies in the target subgroup.

`Hom.invariantRestriction f : C^V → B^U` restricts that same algebra
pullback to the two subalgebras. Its positive norm bound is inherited
unchanged from `f.restriction`. The application theorem identifies its
underlying quotient element with `f.restriction c`.
`Hom.invariantRestriction_inclusion` proves the square of bounded maps

`X.invariantInclusion.comp f.invariantRestriction =`
`f.restriction.comp Y.invariantInclusion`.

`Hom.invariantRestriction_id` and `Hom.invariantRestriction_comp` prove the
identity and contravariant composition equations. They reduce equality in the
fixed subalgebras to equality of underlying elements and then use the
published restriction laws.

## Presheaf and subgroup restriction

`invariantAlgebraPresheaf` is the functor

`(ρ.OpenSubgroupTransport)ᵒᵖ ⥤ CommAlgCat K`

with values `B^U` and maps `Hom.invariantRestriction`, after forgetting
the norms of these bounded maps. Its functor laws are the preceding identity
and composition equations.

`invariantAlgebraInclusion` is a natural transformation from this functor to
the published full quotient `algebraPresheaf`. Its components are the
constructed fixed-section inclusions. Naturality is exactly the bounded-map
square above after forgetting bounds.
`invariantAlgebraInclusion_injective` proves that every component is
injective by subtype extensionality.

If `V ≤ U` and `d` is a `U`-invariant rational presentation, the published
`subgroupRestriction` arrow goes from `(V,d)` to `(U,d)`. Its quotient
pullback is the identity on the unchanged quotient algebra. The theorem
`subgroupRestriction_invariantRestriction_apply` proves that the induced
map `B^U → B^V` sends a section to the same underlying quotient element,
now fixed by the smaller subgroup.

## Provenance and scope

This is derived local algebraic infrastructure. The fixed subalgebras,
closedness, bounded maps and natural transformation are constructed here from
the published quotient operators and their conjugation compatibility.
The proof route uses Mathlib's equalizers, subalgebra lattice and closed-subset
completeness, together with the actual quotient restriction laws. No invariant
algebra or restriction map is supplied as an assumed output object.

Berkovich's unfinished *Etale equivariant sheaves on p-adic analytic spaces*
(1995–1996), the retained `Equish_1996` manuscript, section 1.1,
printed/PDF p. 3, defines morphisms of spaces with operators using a continuous
homomorphism from the source operator group to the target, and gives the
conjugation formula used by the imported category. In section 1.2,
printed/PDF pp. 4–5, the manuscript constructs the smooth global-section
functor using open subgroups and identifies its open-subgroup invariants with
sections on the corresponding induced object. These passages motivate
retaining the actual open subgroups and their fixed sections here.
They do not identify these rational quotient algebras with those sheaf
sections or state this restricted presheaf construction verbatim.

The registered source folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
SHA256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The member *Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf* has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The cited passage is motivation for this internal derivation, rather than
an assertion that the full construction in that passage has been formalized.

The module allows empty loci, zero or nonreduced quotients, an action with
kernel and a trivially valued base field. It proves no sheaf condition for
the invariant presheaf and makes no finite-presentation claim for its values.
Analytic atlases, full etale and quasi-etale sites, induced analytic spaces,
the sheaf interpretation of these fixed sections, smooth global sections,
cohomology and Harris towers remain separate obligations.
