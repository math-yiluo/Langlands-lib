# Effective descent along composite families

Module `Langlands.CategoryTheory.Sites.StackComposite`. This is internal support for the fpqc
stack proof for line bundles (`Langlands.AlgebraicGeometry.Picard.LineBundleFpqcStackProof`).
It contains general category theory about a pseudofunctor
`F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, in the language of Mathlib's
`Mathlib.CategoryTheory.Sites.Descent` files (`DescentData`, `pullHom`, `IsPrestack`).
None of these results is taken from the literature as stated. They are standard facts about
stacks (compare the Stacks Project, Tag 026F, for prestacks and descent data), written in the
form the fpqc proof needs.

## Main results

- `isPrestack_of_small`. Let `K` be a precoverage that is stable under base change and
  `Small.{w}`, on a category with pullbacks. Suppose `F` satisfies morphism descent
  (`IsPrestackFor`) along every `w`-indexed covering family of `K`
  (`Precoverage.ZeroHypercover.{w} K S`). Then `F` is a prestack for `K.toGrothendieck`.
  This is the small-index version of Mathlib's `Pseudofunctor.IsPrestack.of_precoverage`.
  The proof is the same, except that it uses Mathlib's
  `Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small` on the induced
  precoverage of `Over S`.

- `essSurj_toDescentData_comp` (effective descent along composites). Let `F` be a prestack
  for a Grothendieck topology `J`. Let `r i : U i ⟶ S` be a family, and for each `i` let
  `s i k : V i k ⟶ U i` be a family whose sieve is `J`-covering. Assume the descent functors
  `F.toDescentData r` and `F.toDescentData (s i)` are essentially surjective. Then the descent
  functor of the composite family `⟨i, k⟩ ↦ s i k ≫ r i` is essentially surjective. The family
  `r` itself need not be covering.

## Proof outline

1. **Gluing morphisms** (`hom_ext_of_sieve`, `exists_glue`). Morphisms
   `x₁^* A ⟶ x₂^* B` over `Y` are determined by their `pullHom` restrictions along the
   arrows of a covering sieve. Compatible families of such restrictions glue. Both facts use
   full faithfulness of `F.toDescentData` for the family of all arrows of the sieve
   (Mathlib's `fullyFaithfulToDescentData`). Two associativity coherences for `mapComp'`
   (`map_mapComp'_inv_comp_mapComp'_inv`, `mapComp'_hom_comp_map_mapComp'_hom`, taken from
   Mathlib's strict-pseudofunctor lemmas) move between `F.map g` and `pullHom` (`map_conj`).
2. **Local data.** A descent datum `D` for the composite family restricts to descent data
   `restrict D i` for each family `s i`. Essential surjectivity gives objects `M i` over `U i`
   and isomorphisms `e i : F.toDescentData (s i) (M i) ≅ restrict D i`. For every
   factorization `a ≫ s i k = x`, the maps `β`/`β'` compare `x^* M i` with `a^* D_{i,k}`.
   Their key properties are compatibility with `D.hom` (`β_comp_hom`, `hom_comp_β'`) and
   compatibility with `pullHom` (`pullHom_β`, `pullHom_β'`).
3. **Local sections.** For `y₁, y₂` with factorizations `a₁, a₂` through the `s` families,
   `Φ = β ≫ D.hom ≫ β'` is a morphism `y₁^* M i₁ ⟶ y₂^* M i₂`. It does not depend on the chosen
   factorizations (`Φ_indep`), it is compatible with `pullHom` (`pullHom_Φ`), it is the identity
   on the diagonal (`Φ_self`), and it satisfies the cocycle identity (`Φ_comp`).
4. **Gluing descent data.** For `f₁ ≫ r i₁ = q = f₂ ≫ r i₂`, the maps `Φ` on the covering sieve
   `sieveT s f₁ f₂` (maps along which both `f₁` and `f₂` factor through the `s` families) glue
   to `ehom`. The descent axioms of `glued : F.DescentData r` then follow from separatedness
   (`hom_ext_of_sieve`) together with steps 3 and 4.
5. **Comparison.** Pulling `glued` back to the composite family with Mathlib's `pullFunctor`
   gives back `D` (`pullGluedIso`, built from the isomorphisms `e i`). Finally, essential
   surjectivity of `F.toDescentData r` and Mathlib's `toDescentDataCompPullFunctorIso`
   (together with `F.mapId`) give an object over `S` whose descent datum is isomorphic to `D`.
