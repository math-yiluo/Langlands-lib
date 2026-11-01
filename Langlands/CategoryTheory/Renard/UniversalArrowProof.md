# Renard A.III.1: proofs for universal arrows

Worker 1217 proves the published closed proposition
`Langlands.Renard.UniversalArrow.UniversalArrowStatements.{vA,vB,uA,uB}`,
imported from `Langlands.CategoryTheory.Renard.UniversalArrowStatements`.
The final theorem is
`Langlands.Renard.UniversalArrow.universalArrowStatements_proof`.
The four object and morphism universes remain independent. The theorem has no
extra assumptions or parameters.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, Appendix A.III.1, printed pp.251–252 /
one-based PDF257–258, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These original pages were read for this proof. The existing statement companion
explains the source-to-Lean formulation and the compatible-isomorphism convention.
The discrepancy in the module-localization example recorded in
`notes/renard/appendix-a-corrections.md` does not affect these generic assertions.

## Implemented proof

`rightCharacterization_proof` starts with the source factorization property
`∀ Z f, ∃! g, i ≫ F.map g = f`. Classical choice selects its unique factor
for each actual structured arrow `c`. `StructuredArrow.homMk` turns the factor
into a morphism from `StructuredArrow.mk i` to `c`, using precisely the given
factorization equation. Uniqueness of factors and
`StructuredArrow.hom_ext` show that every morphism to `c` is the chosen one.
`Limits.IsInitial.ofUniqueHom` therefore constructs actual initiality data.
The data is enclosed in the required `Nonempty`. Conversely,
`StructuredArrow.IsUniversal.existsUnique` applied to
`StructuredArrow.mk f` extracts the required unique factor.

`leftCharacterization_proof` performs the dual construction in the actual
costructured-arrow category. A chosen factor becomes a morphism from `c`
to `CostructuredArrow.mk j` via `CostructuredArrow.homMk`.
`CostructuredArrow.hom_ext` and factor uniqueness supply the hypotheses of
`Limits.IsTerminal.ofUniqueHom`. In the reverse direction,
`CostructuredArrow.IsUniversal.existsUnique` yields the factors with equation
`F.map g ≫ j = f`.

`rightComparison_proof` follows the two-factor argument of the source remark.
Universality gives `f : X ⟶ X'` with `i ≫ F.map f = i'` and
`g : X' ⟶ X` with `i' ≫ F.map g = i`. Functoriality and associativity
show that `f ≫ g` and the identity both factor `i` through itself.
Uniqueness gives `f ≫ g = 𝟙 X`; the other universal property gives
`g ≫ f = 𝟙 X'`. These equations construct an actual isomorphism with
forward map `f`. For any compatible isomorphism, uniqueness of the factor
of `i'` identifies its forward map with `f`, and `Iso.ext` identifies the
isomorphisms.

`leftComparison_proof` uses the dual equations
`F.map f ≫ j' = j` and `F.map g ≫ j = j'`. Applying the two left
factorization uniqueness properties to the composites and identities gives
the inverse equations. Compatibility and uniqueness again follow from the
chosen factor and `Iso.ext`. Thus each comparison is unique among
isomorphisms satisfying the displayed compatibility equation.

The final theorem joins these four closed proofs in the order of the
published conjunction. It changes neither the statement pair nor any of
its imports.

## Scope

This proves the two characterizations and the two compatible comparisons.
It assumes no solution to an arbitrary universal problem. Examples,
module-localization comparisons and exactness, functoriality, adjunctions,
representability and the remaining assertions of Appendix A require
separate work. Worker 1193's actual-module categorical branch and Worker 1214's
occurring-character branch are outside this proof.
