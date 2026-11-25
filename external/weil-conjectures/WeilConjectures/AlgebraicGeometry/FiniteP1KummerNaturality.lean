/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineTrace
import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctBaseChange
import WeilConjectures.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase

/-! # Naturality of the hyperplane Kummer class

the universal-base argument of lem-sp-tower-p1-arbitrary-base-integrals, steps 1–4.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace
  projectiveLineTraceTransport projectiveLineTraceDatum

/-- The ordered source of the finite P1 decomposition, constructed as a biproduct.
Source: blueprint lemma-cohomology-projective-line-trace, after twisting by A(1)[2].
(auxiliary; not a blueprint node). -/
@[implicit_reducible]
def ordinaryFiniteP1SplittingSource (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) : DerivedCategoryModule A S :=
  (ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S

/-- The target of the finite P1 decomposition, constructed by derived direct image.
Source: blueprint lemma-cohomology-projective-line-trace, after twisting by A(1)[2].
(auxiliary; not a blueprint node). -/
@[implicit_reducible]
def ordinaryFiniteP1SplittingTarget (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) : DerivedCategoryModule A S :=
  (ordinaryFinitePushforward A (X := ProjectiveLine S) (Y := S)
    (ProjectiveLine S ↘ S)).obj
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)

/-- The two specified components, before asserting invertibility.
Source: blueprint lemma-cohomology-projective-line-trace, after twisting by A(1)[2].
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteP1SplittingMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :
    ordinaryFiniteP1SplittingSource A N hA S ⟶ ordinaryFiniteP1SplittingTarget A N hA S :=
  biprod.desc (ordinaryFiniteP1Unit A N hA t S hS)
    (ordinaryFiniteP1ChernPushforward A N hA S c)

private theorem splitting_map_naturality
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {X Y Z : C} {X' Y' Z' : D}
    (a : X ⟶ Z) (b : Y ⟶ Z) (a' : X' ⟶ Z') (b' : Y' ⟶ Z')
    (e : F.obj X ≅ X') (e' : F.obj Y ≅ Y') (v : F.obj Z ⟶ Z')
    (ha : F.map a ≫ v = e.hom ≫ a') (hb : F.map b ≫ v = e'.hom ≫ b') :
    F.map (biprod.desc a b) ≫ v =
      biprod.lift (F.map biprod.fst ≫ e.hom) (F.map biprod.snd ≫ e'.hom) ≫
        biprod.desc a' b' := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  apply (cancel_epi (F.mapBiprod X Y).inv).mp
  apply biprod.hom_ext' <;>
    simp [← Functor.map_comp_assoc, ha, hb]

/-- The hyperplane Kummer class and its two-component map are natural over every base.
Over a Noetherian base this is the already normalized Chern morphism.
Source: blueprint lemma-cohomology-projective-line-trace, arbitrary-base compatibility, and
lem-sp-tower-p1-arbitrary-base-integrals, steps 2–3.
(auxiliary; not a blueprint node)

Proof: the hyperplane equation is t on the first standard chart and the unit ideal
on the other. It is Cartier after every change of base, and its dual ideal has the
O(1) transition function. The supported Kummer class, composed with the constant
unit, has the prescribed abelian Kummer image. Module-derived Hom from the constant
free rank-one sheaf is naturally abelian cohomology after forgetting coefficients
and evaluating at one. Indeed resolve the target by injective module sheaves; Hom
from the constant free module is sections degreewise, and forgetting an injective
module gives a global-sections-acyclic abelian sheaf. Evaluation on the integral
generator one identifies the comparison with ordinaryFiniteClass itself. Thus this
image determines the module-derived arrow c, not just an arbitrary isomorphism of
cohomology groups. The kernel inclusion of roots is monic, so the root normalization
determines its pullback comparison uniquely; the pure-tensor generators determine
the line comparison uniquely. Hence the normalized transport in the supported
Kummer theorem agrees with the fixed projectiveLineTraceTransport.
The supported Kummer pullback equation and the mate unit identity identify its
pullback with the corresponding arrow over the new base. This proves both the
Chern specification and agreement with the normalized Noetherian datum. Taking
adjoints gives naturality of the Chern direct-image component. The exchange mate
formula and adjunction triangles give naturality of the twisted unit component.
The biproduct universal property combines these two equations into the displayed
square. All chart equations remain valid over the zero ring; when N=1 the same
cohomology construction gives the unique zero-coefficient arrows. -/
theorem exists_ordinaryFiniteP1KummerNaturality (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    ∃ c : ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
        ordinaryFiniteUnit A (ProjectiveLine S) ⟶
          (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧,
      (∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
        ordinaryFiniteP1ChernSpec A N hA S
          ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
            hS.map (ProjectiveLine S ↘ S).appTop.hom) (c S hS) ∧
        (∀ [IsNoetherian S],
          c S hS = (projectiveLineTraceDatum N hN A hA S hS).chern)) ∧
      ∀ {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
          (hS' : IsUnit (N : Γ(S', ⊤))),
        (ordinaryFinitePullback A (X := S') (Y := S) f).map (ordinaryFiniteP1SplittingMap A N hA
            (projectiveLineTraceTransport N hN A hA) S hS (c S hS)) ≫
          ordinaryFiniteP1Exchange A f
            ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
          (ordinaryFinitePushforward A (X := ProjectiveLine S') (Y := S')
            (ProjectiveLine S' ↘ S')).map
            (ordinaryFiniteShiftedLinePullback A N hA
              (projectiveLineTraceTransport N hN A hA)
              (X := ProjectiveLine S') (Y := ProjectiveLine S)
              (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
              ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
                hS.map (ProjectiveLine S ↘ S).appTop.hom)).hom =
        ordinaryFiniteP1DecompositionSourceMap A N hA
            (projectiveLineTraceTransport N hN A hA) f hS ≫
          ordinaryFiniteP1SplittingMap A N hA
            (projectiveLineTraceTransport N hN A hA) S' hS' (c S' hS') := by
  classical
  have hex (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
      ∃ c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
          (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧,
        ordinaryFiniteP1ChernSpec A N hA S
          ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
            hS.map (ProjectiveLine S ↘ S).appTop.hom) c :=
    (ordinaryFiniteClass_bijective_arbitraryBase A (ProjectiveLine S)
      (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA) 2).2 _
  choose c hc using hex
  refine ⟨c, ?_, ?_⟩
  · intro S hS
    refine ⟨hc S hS, ?_⟩
    intro hnoeth
    apply (ordinaryFiniteClass_bijective_arbitraryBase A (ProjectiveLine S)
      (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA) 2).1
    exact (hc S hS).trans (projectiveLineTraceDatum N hN A hA S hS).chern_spec.symm
  · intro S' S f hS hS'
    let : (ordinaryFinitePullback A f).Additive :=
      additive_leftDerivedUpperStar (ModuleCat.{u + 1} A) f
    let t := projectiveLineTraceTransport N hN A hA
    have hu := ordinaryFiniteP1_twisted_unit_baseChange A N hN hA t f hS hS'
    have hh := ordinaryFiniteP1_chern_adjunct_baseChange A N hN hA t f hS hS'
      (c S hS) (c S' hS') (hc S hS) (hc S' hS')
    unfold ordinaryFiniteP1SplittingMap ordinaryFiniteP1DecompositionSourceMap
    exact splitting_map_naturality (ordinaryFinitePullback A f)
      (ordinaryFiniteP1Unit A N hA t S hS)
      (ordinaryFiniteP1ChernPushforward A N hA S (c S hS))
      (ordinaryFiniteP1Unit A N hA t S' hS')
      (ordinaryFiniteP1ChernPushforward A N hA S' (c S' hS'))
      (ordinaryFiniteShiftedLinePullback A N hA t f hS)
      (ordinaryFiniteUnitPullback A f) _ hu hh

end AlgebraicGeometry.Etale
