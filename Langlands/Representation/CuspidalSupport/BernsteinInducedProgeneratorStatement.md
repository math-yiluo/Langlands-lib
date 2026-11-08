# The induced progenerator of a Bernstein block: statement

Author: Worker 6. Module `Langlands.Representation.CuspidalSupport.BernsteinInducedProgeneratorStatement`, namespace `Langlands.CuspidalSupport`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.10.1, Theorem and proof, printed p.208 / PDF p.214, with the construction of `Π_Ω` on printed p.207 / PDF p.213. The progenerator `Π_D` is that of VI.4.1, printed p.149 / PDF p.155. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The source

Let `Ω` be a connected component of `Ω(G)` and `(M, (ρ, W))` a cuspidal datum in `Ω`, with `M` a standard Levi and `P = MN` the standard parabolic. Let `D = [M, ρ]_M`, `Π_D` the progenerator of `M(M)_D` of VI.4.1, and `Π_Ω = i_P^G(Π_D)`. The theorem reads: `Π_Ω` is a finitely generated progenerator of `M(G)_Ω`. In the proof, projectivity comes from second adjointness and exactness of `r_{P̄}^G`, finite generation from VI.7.5, and the generator property from VII.1.3 and the VI.10.1 Proposition.

## The Lean statement

`BernsteinInducedProgeneratorStatement` states the theorem in the published framework of actual standard cuspidal data and Bernstein blocks (modules `BernsteinData` and `BernsteinBlock`, Worker 1153). It is a statement unit: nothing is proved.

### Hypotheses

- A nonarchimedean local field `F : Type uF` and a group scheme `G` over `Spec F` with `[IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]`. `G(F)` carries the canonical topology `pointTopology` and is assumed locally compact and nonarchimedean.
- `T`, `i : T.toGrp ⟶ G`, `ν`, and `family : BernsteinStandardFamily i ν`, the published structural hypotheses: `G` connected reductive, `i` maximal split, `ν` generic, finitely many simple roots, and the semidirect decompositions and closedness of the standard subgroups.
- A cuspidal datum `a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family`: a standard Levi `M = bernsteinLeviScheme i ν a.roots` with an irreducible cuspidal smooth representation `a.representation` of `M(F)`. This is Renard's `(M, (ρ, W))`.
- `ρ₀ : SmoothRep ℂ (Plancherel.rationalCommonNormKernel M)`, irreducible, with an injective morphism into `SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel M) a.representation`. This is the choice of an irreducible summand of `ρ|_{⁰M}` in VI.4.1, matching the hypotheses of the published VI.4.1 statement `RationalSummandSmallProgeneratorStatement`.

The instances on `M` (`IsClosedImmersion` of the standard Levi embedding, `IsAffine`, `LocallyOfFiniteType` and the canonical topology `rationalPointTopology F M.X`) are the ones that `BernsteinData` installs locally. They are restated here because local instances do not leave their module.

### The objects

- `Π_D` is `rationalNormKernelSummandInduction M ρ₀`, the published compact induction `ind_{⁰M(F)}^{M(F)} ρ₀`.
- `Π_Ω` is `(normalizedInductionFunctor (family.decomposition a.roots) (family.closedUnipotent a.roots)).obj (bernsteinLiteralLeviRep i ν a.roots Π_D)`. This is the published normalized induction along the standard parabolic of `a.roots`, applied to `Π_D` transported to the literal standard Levi subgroup. It is the same construction as the published `bernsteinInduction a`, with `Π_D` in place of `a.representation`, and it lies in `SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)`.
- `M(G)_Ω` is the published full subcategory `BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a)`: smooth representations, at the carrier universe `max uF uV` of normalized induction, all of whose irreducible actual subquotients have inertial support the class of `a`.

### Conclusion

There is a proof `hmem` that `Π_Ω` satisfies the block property, i.e. `Π_Ω ∈ M(G)_Ω`. For the object `P = ⟨Π_Ω, hmem⟩` of the block:

1. **Projective.** For all objects `Y`, `Z` of the block, every epimorphism `q : Y ⟶ Z` and every `f : P ⟶ Z`, there is `g : P ⟶ Y` with `g ≫ q = f`. The published `IsRationalInertiaSmallProgenerator` of VI.4.1 uses the same formulation.
2. **Finitely generated.** `Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) Π_Ω.representation.asModule`. This is the finite-type notion of the published VI.1.3 and VI.7.5 statements.
3. **Generator.** For all objects `X`, `Y` and morphisms `f ≠ g : X ⟶ Y` of the block, there is `h : P ⟶ X` with `h ≫ f ≠ h ≫ g`, i.e. `Hom(P, -)` is faithful.

A finitely generated projective object is small (A.VIII.2), so these three conditions say that `Π_Ω` is a finitely generated progenerator in Renard's sense.

## Remarks

- The source works with a standard Levi and standard parabolic, which is exactly what the published standard-family framework provides. The companion VI.10.1 statement `InducedProgeneratorIndependenceStatement` (Worker 6, candidate `c0d59fd5-20a5-4eff-bf52-51f85ed140aa`) asserts that the isomorphism class does not depend on this choice.
- The block is defined with the published induction-occurrence support relation, not with a Jacquet-defined cuspidal support; its comparison with Renard's `M(G)_Ω` is the remaining support-uniqueness obligation recorded in `BernsteinBlock`.
- The proof is not formalized here.
