# Abelian sheaves with finite closed support: proof

`Langlands.Cohomology.finiteClosedSupportSheaf` proves the Library proposition
`Langlands.Cohomology.FiniteClosedSupportSheafStatement.{u}` from
`Langlands.Cohomology.FiniteClosedSupportSheafStatement`, for every universe `u`.

The proved assertion is the statement's exact scope. Let `X : TopCat.{u}`, let
`F : TopCat.Sheaf AddCommGrpCat.{u} X` be an abelian sheaf and let `S : Set X`.
Assume that `S` is finite, that `{x}` is closed for every `x ∈ S`, and that the
stalk `(TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.obj` is a zero object
for every `x ∉ S`. Then `F.obj` satisfies Mathlib's `TopCat.Presheaf.IsFlasque`,
and the global-section group `F.obj.obj (op ⊤)` is a zero object if and only if
`F` is a zero object of the category of abelian sheaves on `X`. There is no
separation axiom on `X`; the empty space and `S = ∅` are included, and `S` may
contain points whose stalk is zero.

## The implemented proof

The helper lemmas are in the namespace
`Langlands.Cohomology.FiniteClosedSupportSheaf`. Each takes the hypotheses of the
statement as explicit arguments `hS`, `hcl` and `hz`.

1. `isClosed_inter`: for every set `U`, the set `S ∩ U` is closed. It is finite
   (`Set.Finite.inter_of_left`) and equals the finite union
   `⋃ x ∈ S ∩ U, {x}` of closed singletons (`Set.biUnion_of_singleton`), so
   `Set.Finite.isClosed_biUnion` applies.

2. `complOpen hS hcl U` is the open set `(S ∩ U)ᶜ`, for an open `U`.
   `le_sup_complOpen` shows `V ≤ U ⊔ complOpen hS hcl U` for all opens `U` and
   `V`: a point outside `U` is not in `S ∩ U`.

3. `eq_zero_of_forall_not_mem`: if an open `V` contains no point of `S`, every
   section `s` of `F` over `V` is zero. By Mathlib's
   `TopCat.Presheaf.section_ext`, it suffices that `s` and `0` have equal germs at
   every `x ∈ V`. For such `x`, `x ∉ S`, so the stalk at `x` is a zero object of
   `AddCommGrpCat` and hence a subsingleton
   (`AddCommGrpCat.subsingleton_of_isZero`).

4. `exists_res_eq`: every section `s` over an open `U` is the restriction of a
   section `t` over `U ⊔ complOpen hS hcl U`. The overlap
   `U ⊓ complOpen hS hcl U` contains no point of `S`: a point of `S` lying in `U`
   lies in `S ∩ U` and so not in the complement. By step 3 the restriction of `s`
   to the overlap is zero, which is the restriction of the zero section over
   `complOpen hS hcl U`. The two-open gluing lemma
   `Langlands.Cohomology.Cech.exists_glue₂` from the published module
   `Langlands.Cohomology.CechFlasque` then glues `s` with zero.

5. `surjective_res`: for opens `V ≤ U`, the restriction homomorphism
   `Langlands.Cohomology.Cech.res h : F(U) →+ F(V)` (Library module
   `Langlands.Cohomology.CechCochains`, defined as the underlying homomorphism of
   `F.obj.map (homOfLE h).op`) is surjective. Given `s` over `V`, step 4 gives `t`
   over `V ⊔ complOpen hS hcl V` restricting to `s`. Since
   `U ≤ V ⊔ complOpen hS hcl V` by step 2, the restriction of `t` to `U` is a
   section over `U`, and its restriction to `V` equals the restriction of `t` to
   `V`, namely `s` (`Langlands.Cohomology.Cech.res_res`).

6. `isFlasque`: `TopCat.Presheaf.IsFlasque F.obj`. Mathlib's class asks that
   `F.obj.map i` be an epimorphism for every morphism `i` of `(Opens X)ᵒᵖ`. In
   `AddCommGrpCat` this is surjectivity (`AddCommGrpCat.epi_iff_surjective`),
   which is step 5 for the inclusion `leOfHom i.unop`.

7. `isZero_of_isZero_top`: if `F.obj.obj (op ⊤)` is a zero object, then `F` is a
   zero object. Using step 6, every restriction `F(⊤) ⟶ F(U)` is an epimorphism
   out of a zero object, so every `F(U)` is a zero object (`IsZero.of_epi`).
   Hence the presheaf `F.obj` is a zero object (`Functor.isZero`), so every
   stalk is a zero object (`Functor.map_isZero` for the additive stalk functor),
   and Mathlib's `TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero` gives
   `IsZero F`.

The closing theorem `Langlands.Cohomology.finiteClosedSupportSheaf` introduces
`X`, `F`, `S` and the three hypotheses, and returns step 6 together with the
equivalence. Its forward direction is step 7. Its reverse direction applies
`Functor.map_isZero` to the additive forgetful functor
`TopCat.Sheaf.forget AddCommGrpCat X` from sheaves to presheaves, then evaluates
the zero presheaf at `op ⊤` (`IsZero.obj`).

## Provenance and scope

The proof is derived and follows the elementary route described with the
statement: glue with zero across the cover of `X` by `U` and the complement of
the closed set `S ∩ U`. The support convention (the nonzero-stalk locus, without
closure) is the one of the Stacks Project, `modules.tex`, Definition
`definition-support`, as recorded in the statement's Markdown. The implication
itself is not quoted from a source.

Only standard axioms are used: `propext`, `Classical.choice` and `Quot.sound`.
The module imports the statement module, the published module
`Langlands.Cohomology.CechFlasque` and Mathlib's
`Mathlib.Algebra.Category.Grp.Zero`; it changes no existing Library file.

This is the topological assertion about abelian sheaves only. Scheme cohomology,
higher-direct-image support, proper base change, Leray assertions, and module or
cohomology adapters for the geometric support tasks are separate work.
