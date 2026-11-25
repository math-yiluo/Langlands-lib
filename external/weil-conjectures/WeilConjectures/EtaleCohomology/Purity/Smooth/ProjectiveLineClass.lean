/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartBoundary
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# The hyperplane class of the projective line

The hyperplane class `h ∈ H²(ℙ¹_S, Λ(1))` of the projective line, defined without excision
isomorphisms: it is the Gysin image of the fundamental class of the section at infinity, and
this fundamental class is the Kummer boundary `∂κ(s)` of the coordinate `s = T_∞ / T₀` of the
chart `D₊(T₀) ≅ 𝔸¹_S` at infinity.

*Sign.* Forgetting supports, the Kummer boundary `∂κ(f)` of a local equation `f` of a divisor
`D` is `c₁(𝒪(-D)) = -c₁(𝒪(D))`, not `c₁(𝒪(D))`: the Kummer and the support connecting maps
anticommute (the notes' cycle class `c_D` of a Cartier divisor is `-∂κ(f)`). The auxiliary
objects carry that sign: `AlgebraicGeometry.Etale.projectiveLineHyperplaneClassAux` is
`c₁(𝒪(-∞)) = -c₁(𝒪(1))`, and the auxiliary trace `AlgebraicGeometry.Etale.projectiveLineTraceAux`,
normalized by `Tr ∘ (-h)♭ = 1`, is `-t_q`. The main objects are their negatives, so that they match
the notes: the hyperplane class `AlgebraicGeometry.Etale.projectiveLineHyperplaneClass` is
`h = c₁(𝒪(1))`, and the trace `AlgebraicGeometry.Etale.projectiveLineTrace`, normalized by
`Tr_q ∘ h♭ = 1`, is the trace `t_q` of the notes, normalized by `t_q(c₁(𝒪(1))) = 1`. The
constructions below are carried out for the auxiliary class, which is used consistently; the sign
enters only in the passage to the main objects.

More precisely, let `V ⊆ X` be an open, `s` a function on `V` and `i : Z ⟶ V` the zero locus of
`s`, and assume that `i' = i ≫ (V ⊆ X)` is a closed immersion (`Z` is closed in `X`). The Kummer
boundary `∂κ(s) ∈ H²_Z(V, Λ(1))` (`AlgebraicGeometry.Etale.kummerBoundary`) has an adjoint
`Λ_Z ⟶ Ri^! Λ_V(1)[2]`. Since `V ⊆ X` is an open immersion, `Ri^! Λ_V(1) ≅ Ri'^! Λ_X(1)`, the
base change isomorphism of the exceptional inverse image along the open immersion
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion`) for
the cartesian square `𝟙 ≫ i' = i ≫ (V ⊆ X)`. The resulting class `Λ_Z ⟶ Ri'^! Λ_X(1)[2]` is
pushed forward along the proper `i'`:
`Λ_X ⟶ Ri'_* Λ_Z ⟶ Ri'_* Ri'^! Λ_X(1)[2] ≅ Ri'_! Ri'^! Λ_X(1)[2] ⟶ Λ_X(1)[2]`.

Every step is a canonical morphism or the inverse of a canonical isomorphism; no choice of an
isomorphism is made.

## Main definitions

- `AlgebraicGeometry.Etale.gysinClass`: the Gysin image `Λ_X ⟶ L[n]` of a class
  `Λ_Z ⟶ Ri^! L[n]` along a proper morphism `i : Z ⟶ X`.
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekCompOpenImmersionIso`:
  `R(i ≫ j)^! L ≅ Ri^! Lj^* L` for an open immersion `j`.
- `AlgebraicGeometry.Etale.kummerBoundaryAdjoint`: the adjoint `Λ_Z ⟶ Ri^! Λ_U(1)[2]` of the
  Kummer boundary.
- `AlgebraicGeometry.Etale.chartBoundaryClass`: the class `Λ_X ⟶ Λ_X(1)[2]` of the zero locus
  of a function on an open, when this zero locus is closed in `X`.
- `AlgebraicGeometry.Etale.projectiveLineHyperplaneClass`: `h = -c₁(𝒪(1))` on `ℙ¹_S`.
- `AlgebraicGeometry.Etale.projectiveLineDecompositionMap`:
  `(1, h) : Λ_S(1)[2] ⊕ Λ_S ⟶ Rq_*(Λ_{ℙ¹_S}(1)[2])`.
- `AlgebraicGeometry.Etale.projectiveLineTrace`: the trace `Rq_*(Λ_{ℙ¹_S}(1)[2]) ⟶ Λ_S`, given
  that the decomposition map is an isomorphism.

## Main statements

- The decomposition map is an isomorphism (blueprint `lemma-cohomology-projective-line-trace`):
  `AlgebraicGeometry.Etale.isIso_projectiveLineDecompositionMap`, in
  `WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomology`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Gysin

variable [Finite Λ] {X Z : Scheme.{u}}

/-- The *Gysin image* of a class `a : Λ_Z ⟶ Ri^! L[n]` along a proper morphism `i : Z ⟶ X`:
the composite
`Λ_X ⟶ Ri_* Li^* Λ_X ≅ Ri_* Λ_Z ⟶ Ri_*(Ri^! L[n]) ≅ Ri_!(Ri^! L[n]) ≅ (Ri_! Ri^! L)[n] ⟶ L[n]`
of the unit of `Li^* ⊣ Ri_*`, `Ri_*(a)`, the identification `Ri_! ≅ Ri_*` of the proper `i`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`) and the counit of
`Ri_! ⊣ Ri^!`. For `a` the fundamental class of a closed subscheme it is the cycle class. -/
noncomputable def gysinClass (i : Z ⟶ X) [IsProper i]
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    (a : constantComplex Λ Z ⟶ ((R(i)^![Λ]).obj L)⟦n⟧) :
    constantComplex Λ X ⟶ L⟦n⟧ :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app _ ≫
    (R((i)_*[ModuleCat.{u + 1} Λ])).map ((leftDerivedUpperStarConstantComplexIso Λ i).hom ≫ a) ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i).inv.app _ ≫
        ((R(i)_![ModuleCat.{u + 1} Λ]).commShiftIso n).hom.app _ ≫
          ((rightDerivedUpperShriekAdjunction Λ i).counit.app L)⟦n⟧'

end Gysin

section Excision

variable {Z V X : Scheme.{u}} (i : Z ⟶ V) (j : V ⟶ X)

/-- For a monomorphism `j`, the square `𝟙 ≫ (i ≫ j) = i ≫ j` is cartesian. -/
lemma isPullback_id_comp_of_mono [Mono j] : IsPullback (𝟙 Z) i (i ≫ j) j :=
  IsPullback.of_horiz_isIso_mono ⟨by simp⟩

variable [Finite Λ] [IsClosedImmersion i] [IsOpenImmersion j] [IsClosedImmersion (i ≫ j)]

/-- *Excision for the exceptional inverse image*: for a closed immersion `i : Z ⟶ V`, an open
immersion `j : V ⟶ X` and `i ≫ j` a closed immersion, `R(i ≫ j)^! L ≅ Ri^!(Lj^* L)`, the base
change isomorphism of the exceptional inverse image along the open immersion `j`
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion`) for the
cartesian square `𝟙 ≫ (i ≫ j) = i ≫ j`, read through `L𝟙^* ≅ 𝟭`. -/
noncomputable def rightDerivedUpperShriekCompOpenImmersionIso
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(i ≫ j)^![Λ]).obj L ≅
      (R(i)^![Λ]).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj L) :=
  haveI := isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion Λ
    (isPullback_id_comp_of_mono i j)
  ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Z).app _).symm ≪≫
    (asIso (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_id_comp_of_mono i j))).app L

end Excision

variable [Finite Λ] [HasKummerClass Λ]

section Kummer

variable {U : Scheme.{u}} [HasInvertibleExponent Λ U] (f : Γ(U, ⊤))

/-- The *adjoint* `Λ_Z ⟶ Ri^! Λ_U(1)[2]` of the Kummer boundary
`∂κ(f) : Λ_U ⟶ (Ri_! Ri^! Λ_U(1))[2]` (`AlgebraicGeometry.Etale.kummerBoundary`), where
`i : Z ⟶ U` is the zero locus of `f`: the transpose of `∂κ(f)` along the forget-supports map
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekTranspose`), read through `Li^* Λ_U ≅ Λ_Z`.
Under the rank-one normalisation it is the fundamental class of `Z` when `Z` is the zero section
of an affine line. -/
noncomputable def kummerBoundaryAdjoint :
    constantComplex Λ (U.zeroLocusSubscheme {f}) ⟶
      ((R(U.zeroLocusSubschemeι {f})^![Λ]).obj (tateObject Λ U 1))⟦(2 : ℤ)⟧ :=
  (compactificationConstantComplexIso Λ (U.zeroLocusSubschemeι {f})).inv ≫
    rightDerivedLowerShriekTranspose (ModuleCat.{u + 1} Λ) (U.zeroLocusSubschemeι {f})
      (kummerBoundary Λ f ≫
        ((R(U.zeroLocusSubschemeι {f})_![ModuleCat.{u + 1} Λ]).commShiftIso (2 : ℤ)).inv.app _)

end Kummer

section ChartBoundary

variable {X : Scheme.{u}} [HasInvertibleExponent Λ X] (V : X.Opens) (s : Γ(X, V))
  [IsClosedImmersion (V.toScheme.zeroLocusSubschemeι {V.topIso.inv s} ≫ V.ι)]

/-- The *class of the zero locus of a function on an open*: for an open `V ⊆ X` and a function
`s` on `V` whose zero locus `i : Z ⟶ V` is closed in `X`, the Gysin image along the closed
immersion `i' = i ≫ (V ⊆ X)` of the adjoint `Λ_Z ⟶ Ri^! Λ_V(1)[2]` of the Kummer boundary
`∂κ(s)`, read through `Ri^! Λ_V(1) ≅ Ri^! L(V ⊆ X)^* Λ_X(1) ≅ Ri'^! Λ_X(1)`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekCompOpenImmersionIso`):

`Λ_X ⟶ Λ_X(1)[2]`.

No excision isomorphism is chosen. It is the blueprint's class `cl(Z)` of a divisor
(`lemma-cycle-class-cartier-divisor`), which forgets supports to `c₁(𝒪_X(-Z)) = -c₁(𝒪_X(Z))`
(`lemma-cycle-class-cartier-divisor` (b)), not to `c₁(𝒪_X(Z))`. -/
noncomputable def chartBoundaryClass : constantComplex Λ X ⟶ (tateObject Λ X 1)⟦(2 : ℤ)⟧ :=
  haveI : HasInvertibleExponent Λ V := .of_hom V.ι
  gysinClass Λ (V.toScheme.zeroLocusSubschemeι {V.topIso.inv s} ≫ V.ι) _ 2
    (kummerBoundaryAdjoint Λ (V.topIso.inv s) ≫
      ((R(V.toScheme.zeroLocusSubschemeι {V.topIso.inv s})^![Λ]).map
          (leftDerivedUpperStarTateObjectIso V.ι 1).inv ≫
        (rightDerivedUpperShriekCompOpenImmersionIso Λ _ V.ι _).inv)⟦(2 : ℤ)⟧')

end ChartBoundary

/-- The characteristic of `Λ` is invertible on relative projective space over a scheme on which
it is invertible. -/
instance hasInvertibleExponent_projectiveSpace {n : Type u} {S : Scheme.{u}}
    [HasInvertibleExponent Λ S] : HasInvertibleExponent Λ ℙ(n; S) :=
  .of_hom (ℙ(n; S) ↘ S)

section ProjectiveLine

variable (S : Scheme.{u}) [HasInvertibleExponent Λ S]

/-- *The hyperplane class of the projective line*, the class `h` of blueprint
`lemma-cohomology-projective-line-trace` up to sign:

`h = -c₁(𝒪(1)) : Λ_{ℙ¹_S} ⟶ Λ_{ℙ¹_S}(1)[2]`

on `ℙ¹_S = ℙ(Option (ULift (Fin 1)); S)`, the class of the section at infinity
(`AlgebraicGeometry.Etale.chartBoundaryClass`): the zero locus of the coordinate
`s = T_∞ / T₀` of the chart `D₊(T₀)` at infinity, which is closed in `ℙ¹_S`, the complement of
the standard chart `D₊(T_∞) ≅ 𝔸¹_S` (`AlgebraicGeometry.ProjectiveSpace.range_chartBoundaryι`).
The sign comes from `AlgebraicGeometry.Etale.chartBoundaryClass`, which forgets supports to
`c₁(𝒪(-Z))` (the notes' cycle class of a Cartier divisor, clause (b)): this is `-c₁(𝒪(1))`, the
auxiliary convention of the construction; the hyperplane class of the notes is its negative
`AlgebraicGeometry.Etale.projectiveLineHyperplaneClass`. The decomposition of the cohomology of
the projective line holds for `h` and `-h` alike. -/
noncomputable def projectiveLineHyperplaneClassAux :
    constantComplex Λ ℙ(Option (ULift.{u} (Fin 1)); S) ⟶
      (tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧ :=
  chartBoundaryClass Λ (ProjectiveSpace.standardOpen _ S (some ⟨0⟩))
    (ProjectiveSpace.coordRatio (Option (ULift.{u} (Fin 1))) S (some ⟨0⟩) none)

/-- The *hyperplane class* `h = c₁(𝒪(1)) : Λ_{ℙ¹_S} ⟶ Λ_{ℙ¹_S}(1)[2]` of the projective line, the
class of the divisor at infinity with the sign of the notes (the cycle class `c_D` of a Cartier
divisor `D` is the class of `𝒪(D)`): the negative of the boundary class `c₁(𝒪(-∞))` of the chart
at infinity (`AlgebraicGeometry.Etale.projectiveLineHyperplaneClassAux`). -/
noncomputable def projectiveLineHyperplaneClass :
    constantComplex Λ ℙ(Option (ULift.{u} (Fin 1)); S) ⟶
      (tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧ :=
  -projectiveLineHyperplaneClassAux Λ S

/-- The *decomposition map* of the projective line `q : ℙ¹_S ⟶ S`, twisted by `(1)[2]`:

`(1, h) : Λ_S(1)[2] ⊕ Λ_S ⟶ Rq_*(Λ_{ℙ¹_S}(1)[2])`,

whose first component is the unit of `Lq^* ⊣ Rq_*` read through
`Lq^*(Λ_S(1)[2]) ≅ Λ_{ℙ¹_S}(1)[2]`, and whose second component is adjoint to the auxiliary
hyperplane class `-h : Lq^* Λ_S ≅ Λ_{ℙ¹_S} ⟶ Λ_{ℙ¹_S}(1)[2]`
(`AlgebraicGeometry.Etale.projectiveLineHyperplaneClassAux`): the auxiliary form of the
decomposition `Λ_S ⊕ Λ_S(-1)[-2] ⟶ Rq_* Λ_{ℙ¹_S}` of `lemma-cohomology-projective-line-trace`,
see `AlgebraicGeometry.Etale.projectiveLineDecompositionMap` for the one with the sign of the
notes. -/
noncomputable def projectiveLineDecompositionMapAux :
    (tateObject Λ S 1)⟦(2 : ℤ)⟧ ⊞ constantComplex Λ S ⟶
      (R(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
        ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧) :=
  biprod.desc
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)).unit.app _ ≫
      (R(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_*[ModuleCat.{u + 1} Λ])).map
        (((L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).commShiftIso
            (2 : ℤ)).hom.app _ ≫
          (leftDerivedUpperStarTateObjectIso
            (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) 1).hom⟦(2 : ℤ)⟧'))
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)).homEquiv _ _
      ((leftDerivedUpperStarConstantComplexIso Λ (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)).hom ≫
        projectiveLineHyperplaneClassAux Λ S))

/-- The *decomposition map* of the projective line `q : ℙ¹_S ⟶ S`, twisted by `(1)[2]`, with the
hyperplane class `h = c₁(𝒪(1))` of the notes
(`AlgebraicGeometry.Etale.projectiveLineHyperplaneClass`):

`(1, h) : Λ_S(1)[2] ⊕ Λ_S ⟶ Rq_*(Λ_{ℙ¹_S}(1)[2])`

(`AlgebraicGeometry.Etale.projectiveLineDecompositionMap_eq`). It is the auxiliary decomposition
map `(1, -h)` (`AlgebraicGeometry.Etale.projectiveLineDecompositionMapAux`) precomposed with the
sign change `1 ⊕ (-1)` of the second summand, so that both are isomorphisms together. -/
noncomputable def projectiveLineDecompositionMap :
    (tateObject Λ S 1)⟦(2 : ℤ)⟧ ⊞ constantComplex Λ S ⟶
      (R(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
        ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧) :=
  biprod.map (𝟙 _) (-𝟙 _) ≫ projectiveLineDecompositionMapAux Λ S

/-- The decomposition map is `(1, h)`: its first component is the unit of `Lq^* ⊣ Rq_*` read
through `Lq^*(Λ_S(1)[2]) ≅ Λ_{ℙ¹_S}(1)[2]`, its second component is adjoint to the hyperplane
class `h` (`AlgebraicGeometry.Etale.projectiveLineHyperplaneClass`). -/
lemma projectiveLineDecompositionMap_eq :
    projectiveLineDecompositionMap Λ S =
      biprod.desc
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)).unit.app _ ≫
          (R(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_*[ModuleCat.{u + 1} Λ])).map
            (((L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).commShiftIso
                (2 : ℤ)).hom.app _ ≫
              (leftDerivedUpperStarTateObjectIso
                (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) 1).hom⟦(2 : ℤ)⟧'))
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)).homEquiv _ _
          ((leftDerivedUpperStarConstantComplexIso Λ (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)).hom ≫
            projectiveLineHyperplaneClass Λ S)) := by
  ext
  · simp [projectiveLineDecompositionMap, projectiveLineDecompositionMapAux]
  · simp [projectiveLineDecompositionMap, projectiveLineDecompositionMapAux,
      projectiveLineHyperplaneClass, Adjunction.homEquiv_unit]

/-- The decomposition map with the hyperplane class of the notes is an isomorphism exactly when
the auxiliary one is: they differ by the automorphism `1 ⊕ (-1)`. -/
lemma isIso_projectiveLineDecompositionMap_iff :
    IsIso (projectiveLineDecompositionMap Λ S) ↔
      IsIso (projectiveLineDecompositionMapAux Λ S) := by
  have : IsIso (biprod.map (𝟙 ((tateObject Λ S 1)⟦(2 : ℤ)⟧)) (-𝟙 (constantComplex Λ S))) :=
    ⟨biprod.map (𝟙 _) (-𝟙 _), by ext <;> simp, by ext <;> simp⟩
  unfold projectiveLineDecompositionMap
  exact ⟨fun _ ↦ IsIso.of_isIso_comp_left (biprod.map (𝟙 _) (-𝟙 _)) _, fun _ ↦ inferInstance⟩

end ProjectiveLine

end Etale

end AlgebraicGeometry
