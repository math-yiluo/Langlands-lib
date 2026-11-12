# Lifting a cocharacter of a closed split torus over a Henselian local ring

All rings and schemes use one arbitrary universe `u`.

## Base change of exponent cocharacters followed by a homomorphism

The reused `LocalRootGroup.baseChangeCocharacter_groupHom_comp` works over an arbitrary base
morphism `b : S' ⟶ S`. For a finite type `I`, an exponent vector `n : I → ℤ`, and a
homomorphism `j : splitTorus S I ⟶ H`, the published base change of the cocharacter
`exponentCocharacter S I n` followed by `j` equals the exponent cocharacter over
`S'` with the same exponents, followed by the inverse of the canonical
identification `splitTorus.baseChangeIso b I` and the base change of `j`. It is a
direct consequence of the published `splitTorus.groupHom_exponentCocharacter_baseChange`.
The lemma is imported from the published module `Reductive.LocalRootGroupFibre`.

## Lifting

`exists_cocharacter_baseChange_eq_comp_iso` takes a Henselian local ring `R`
(`HenselianLocalRing R`) and a group scheme `G` over `Spec R` that is smooth and
affine. Write `f₀ : Spec κ ⟶ Spec R` for the Mathlib morphism
`fromSpecResidueField` at the closed point, `κ` the scheme residue field there,
and `G₀` for the base change of `G` along `f₀`. Given a commutative group scheme
`A` over `Spec κ` that is a split torus, a homomorphism `a : A ⟶ G₀` that is a
closed subgroup, and a cocharacter `ν` of `A`, it produces a cocharacter
`χ : Gm(Spec R) ⟶ G` and an automorphism `B` of `G₀` such that

```text
Dynamic.baseChangeCocharacter f₀ χ = ν ≫ a ≫ B.hom.
```

The automorphism `B` is a composite of canonical base-change comparisons. The
theorem does not claim that `B` is the identity.

Proof.

1. The published `relativeSplitTorusLifting` lifts `a` to a closed split torus of
   the base change of `G` to an étale neighbourhood `p : U ⟶ Spec R` with a point
   `b` over `f₀`. The published `henselianEtaleSection` gives a section `σ` of `p`
   through `b`, since `R` is Henselian.
2. Pulling back along `σ` gives a split torus over `Spec R`, isomorphic to
   `splitTorus (Spec R) I` for a finite `I`, and a homomorphism
   `ic : splitTorus (Spec R) I ⟶ G`. The published helpers
   `sectionPullbackIso` and `baseChange_map_sectionPullback` of
   `StrictHenselianMaximalReduction`, used exactly as in the proof there, give
   isomorphisms `Aiso` and `B` with `(baseChange f₀).map ic = Aiso.hom ≫ a ≫ B.hom`.
3. The cocharacter `ν ≫ Aiso.inv`, read in `splitTorus (Spec κ) I` through
   `splitTorus.baseChangeIso`, is an exponent cocharacter over the field `κ`
   (`splitTorus.cocharacterLatticeEquiv` and
   `exponentCocharacter_eq_cocharacterLatticeEquiv_symm`) with some exponents `m`.
4. Take `χ` to be `exponentCocharacter (Spec R) I m` followed by `ic`. The first
   section describes the reused lemma computing its base change along `f₀`, and the three
   identifications cancel.

## Provenance

This is an internal lemma combining the published relative lifting of split tori
and Henselian étale sections, in the pattern of the published proof
`strictHenselianSplitMaximalTorusReduction`. It supplies the integral cocharacter
whose closed fibre centralizes a maximal split torus in the Levi step of Maculan
(2017), proof of Lemma 5.1 (printed p. 14 / PDF p. 15). The Lean statements are not
quoted from that source.
