# Unconditional facts used for Renard VI.10.4

Worker 117. Helper module for Task 5545, which proves Renard, *Représentations
des groupes réductifs p-adiques*, French version dated 9 July 2026
(`renard-2026-representations-groupes-reductifs-padiques`), VI.10.4, Theorem
and Remarks 1–2, printed p.212 / PDF p.218. The targets are the statements of
`Langlands.Representation.CuspidalSupport.BernsteinCenterFunctionsStatements`.

The module proves only small, unconditional facts. None of them is a separate
assertion of Renard. They are the routine steps behind Remark 1, "the value of
`z ∈ ℨ(G)` at the point `(M, ρ)` is the scalar by which `z` acts on
`i_P^G(ρ)`", for every point of the component, that is for every twist
`ρ ⊗ ω`, `ω ∈ X(M)`. It also adds no hypothesis to any Library statement.

## Central elements and scalars (namespace `Langlands.SmoothRep`)

Let `C` be a category with a functor `Φ : C ⥤ SmoothRep ℂ G` and let
`z : CatCenter C` be a natural endotransformation of the identity functor.

- `centerScalar_of_surjective`: if `Φ (z_A)` acts on `Φ A` by the scalar `c`
  and `f : A ⟶ B` has surjective underlying map `Φ f`, then `Φ (z_B)` acts on
  `Φ B` by `c`.
  *Proof.* Write `y = Φ f x`. Naturality `z_A ≫ f = f ≫ z_B` gives
  `Φ(z_B)(Φ f x) = Φ f (c • x) = c • y`.
- `centerScalar_of_injective`: if `Φ (z_B)` acts by `c` and `Φ f` is injective,
  then `Φ (z_A)` acts by `c`.
  *Proof.* Apply `Φ f` to both sides and use the same naturality square.
- `scalar_unique`: two scalars `c`, `d` by which one endomorphism of a nonzero
  smooth representation acts are equal.
  *Proof.* For `x ≠ 0`, `(c - d) • x = 0`, so `c - d = 0`.
- `centerScalar_of_isSubquotient`: an element of the centre of
  `SmoothRep ℂ G` acting by `c` on `V` acts by `c` on every subquotient `W` of
  `V` (`IsSubquotient W V`).
  *Proof.* `isSubquotient_iff_exists` gives `D` with an injective map `D → V`
  and a surjective map `D → W`. Apply the two lemmas above with `Φ` the
  identity functor.
- `fullSubcategory_centerScalar_of_isSubquotient`: the same for an element of
  the centre of a full subcategory `P.FullSubcategory`, when `P` is closed under
  subquotients and `V`, `W` both satisfy `P`.
  *Proof.* The intermediate `D` satisfies `P` because it is a subrepresentation
  of `V`. Apply the two lemmas with `Φ = P.ι` and the morphisms
  `ObjectProperty.homMk`.
- `nontrivial_of_isIrreducible`: an irreducible smooth representation is
  nonzero.
  *Proof.* If it were a subsingleton, its bottom and top subrepresentations
  would have equal underlying submodules, contradicting `⊥ ≠ ⊤`, which is part
  of irreducibility.

## Twisted cuspidal data (namespace `Langlands.CuspidalSupport`)

Fix a standard family `family` of a group `G` over a non-archimedean local
field (`BernsteinStandardFamily i ν`). Let `a = (M, ρ)` be a
`BernsteinCuspidalDatum` and `ω` an element of the group
`unramifiedCharacters (fun χ => (rationalNormCharacters M χ).toMul)` of
unramified characters of `M`.

- `BernsteinCuspidalDatum.unramifiedTwist a ω` is the datum `(M, ρ ⊗ ω)`. It is
  defined with the Library's `BernsteinCuspidalDatum.replaceInertia`, using
  `rationalUnramifiedTwist M ω ρ`. Irreducibility comes from
  `isIrreducible_rationalUnramifiedTwist_iff`, and the inertia relation is
  witnessed by `ω` and the identity isomorphism. Its roots are those of `a`
  (`unramifiedTwist_roots`, by `rfl`).
- `BernsteinCuspidalDatum.inertia_unramifiedTwist`: `a` and its twist are
  inertially related (`inertia_replaceInertia`).
- `bernsteinInertialClass_unramifiedTwist`: they have the same inertial class
  (`bernsteinInertialClass_eq_iff`).
- `bernsteinInduction_replaceInertia`: the Bernstein induction of
  `b.replaceInertia D …` is `i_P^G(D)`. The proof unfolds both definitions with
  `dsimp only`. This avoids an expensive unification of the new datum with `b`.
- `bernsteinInduction_unramifiedTwist`: the Bernstein induction of the twisted
  datum is exactly the representation
  `(normalizedInductionFunctor (family.decomposition a.roots) (family.closedUnipotent a.roots)).obj
  (bernsteinLiteralLeviRep i ν a.roots (rationalUnramifiedTwist _ ω a.representation))`
  that the VI.10.4 statements call `inda ω`.
- `twistInduction_mem_saturatedBlock`: every `i_P^G(ρ ⊗ ω)` lies in the
  saturated Bernstein block of the inertial class of `a`
  (`bernsteinSaturatedBlockProperty`).
  *Proof.* The Library's `bernsteinInduction_mem_saturatedBlock` puts the
  induction of the twisted datum in the block of the twisted datum's class.
  Rewrite that class with `bernsteinInertialClass_unramifiedTwist` and the
  induction with `bernsteinInduction_unramifiedTwist`.
- `nontrivial_bernsteinInduction`: the Bernstein induction of every cuspidal
  datum is nonzero.
  *Proof.* `ρ` is nonzero by `nontrivial_of_isIrreducible`. The Library's
  `nontrivial_normalizedInduction` then applies; its continuity hypothesis on
  the standard projection is `continuous_standard_projection` for the family's
  connected reductive group, maximal split torus and generic cocharacter.

## Technical notes

The module uses `backward.isDefEq.respectTransparency.types false`, like the
statement module, and the same local instances: the affine, closed-immersion,
finite-type and topology instances of the standard Levi subgroups, which the
statements supply by `haveI`/`letI`. No heartbeat options are used.

The nontriviality of an irreducible smooth representation is supplied by the
existing `Langlands.Classification.SegmentHeadSupport.nontrivial_of_isIrreducible`
in `SegmentHeadSupportGeneric`; no second nontriviality helper is declared here.
