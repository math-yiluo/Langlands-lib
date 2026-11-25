/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassChern
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Line.TowerLineEvaluationUniversal
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteTateLineUniversal

/-! # Diagonal for canonical tower classes

Source: blueprint main-20261015, chap-Smooth-purity,
`sk-prop-sp-tower-geometric-classes` (blueprint: def-sp-tower-class-diagonal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The divisor line is the dual of the actual diagonal ideal.
Source: classes (3), def-pc-divisor-line-bundle
(blueprint: def-sp-tower-class-diagonal). -/
def diagonalLine (S : Scheme.{u}) : (diagonalSurface S).Modules :=
  Scheme.Modules.dual ((diagonalImmersion S).ker.toModules)

/-- The divisor line is invertible because the specified diagonal ideal is Cartier.
Source: classes (3) (blueprint: def-sp-tower-class-diagonal).
Proof: the equations b-a and 1-ab are regular on the standard charts. The
recorded Cartier theorem makes the ideal invertible, and its dual is invertible
by def-pc-divisor-line-bundle. -/
theorem diagonalLine_invertible (S : Scheme.{u}) :
    Scheme.Modules.IsInvertible (diagonalLine S) := by
  exact (diagonalImmersion_cartier S).isInvertible_dual_toModules

/-- The Picard class of the actual diagonal divisor line.
Source: classes (3) (blueprint: def-sp-tower-class-diagonal). -/
def diagonalPic (S : Scheme.{u}) : (diagonalSurface S).Pic :=
  @Scheme.Pic.ofIsInvertible _ (diagonalLine S) (diagonalLine_invertible S)

/-- The standard negative-projection Cartier boundary with values in all pro-etale
units. The dependency's positive projection class is negated before the canonical
units comparison and the exact constant-tower functor are applied.
Source: classes (3), beta = a[1](-p v inverse)
(blueprint: def-sp-tower-class-diagonal). -/
def diagonalBoundary (S : Scheme.{u}) :
    (DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).obj
      ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)) ⟶
      ((DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).obj
        (units (diagonalSurface S)))⟦(1 : ℤ)⟧ :=
  mapSingleArrow (constant (diagonalSurface S)) (1 : ℤ)
    (extensionArrow (-diagonalIntegralBoundary S) ≫
      ((DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface S)) 0).map
        (cartierUnitsComparison (diagonalSurface S)))⟦(1 : ℤ)⟧')

/-- The actual hyperplane line on the recorded relative projective line.
Source: classes (4), def-pc-projective-space-twist
(blueprint: def-sp-tower-class-diagonal). -/
def hyperplanePic (S : Scheme.{u}) : (ProjectiveLine S).Pic :=
  Scheme.Pic.mk (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1)

/-- Canonical pullback of the coefficient unit: after taking the ordinary
adjoint and evaluating, its sections are the actual constant-ring restriction.
Source: classes (3)--(4), tower units (blueprint: def-sp-tower-class-diagonal). -/
structure CoefficientPullback (b : SpTowerShriek.Base l E) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : SpTowerShriek.Geometry l E b f) where
  iso : g.pull.obj (coefficient Y (Arings l E Y)) ≅ coefficient X (Arings l E X)
  normalization : ∀ (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : ((SpTowerShriek.B l E Y n).obj.obj U))
    (x' : ((SpTowerShriek.ev l E Y n).obj (coefficient Y (Arings l E Y))).val.obj U),
    HEq x x' → HEq
      (((g.ordinaryPushEvaluation n).hom.app (coefficient X (Arings l E X))).val.app U
        (((SpTowerShriek.ev l E Y n).map
          ((g.ordinaryAdjunction.homEquiv _ _) iso.hom)).val.app U x'))
      ((Scheme.proEtaleConstantDirectImageMap.{u, u + 2} f CommRingCat.{u + 1}
        (CommRingCat.of.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n)))).hom.app U x)

/-- Exact localization of the canonical ordinary coefficient pullback.
Source: classes (3)--(4) (blueprint: def-sp-tower-class-diagonal). -/
def CoefficientPullback.derivedIso {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}}
    {f : X ⟶ Y} {g : SpTowerShriek.Geometry l E b f}
    (p : CoefficientPullback l E b f g) :
    (SpTowerShriek.pull l E b g).obj (unit Y (Arings l E Y)) ≅
      unit X (Arings l E X) :=
  (g.pull.mapDerivedCategorySingleFunctor 0).app (coefficient Y (Arings l E Y)) ≪≫
    (DerivedCategory.singleFunctor (Systems X (Arings l E X)) 0).mapIso p.iso

/-- The actual coefficient unit of the derived geometric adjunction.
Source: classes (3)--(4) (blueprint: def-sp-tower-class-diagonal). -/
def unitArrow {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}}
    {f : X ⟶ Y} {g : SpTowerShriek.Geometry l E b f}
    (p : CoefficientPullback l E b f g) :
    unit Y (Arings l E Y) ⟶ (SpTowerShriek.push l E b g).obj (unit X (Arings l E X)) :=
  (SpTowerShriek.adjunction l E b g).unit.app (unit Y (Arings l E Y)) ≫
    (SpTowerShriek.push l E b g).map (p.derivedIso l E).hom

/-- The canonical supported integral unit, transported by the actual site comparison.
Source: classes (3), Cartier extension (blueprint: def-sp-tower-class-diagonal). -/
def supportedIntegralUnit (S : Scheme.{u}) :
    ((constantSheaf (Scheme.ProEt.topology (diagonalSurface S)) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ diagonalIntegralSource S :=
  (integerComparison (diagonalSurface S)).inv ≫
    (comparisonUpperStar AddCommGrpCat.{u + 1} (diagonalSurface S)).map
      (Etale.supportedIntegralUnit (diagonalImmersion S)) ≫
    (cartierIntegralSourceIso (diagonalImmersion S)).hom

/-- The supported source after the same two canonical derived scalar extensions.
Source: classes (3) (blueprint: def-sp-tower-class-diagonal). -/
def diagonalExtendedSource {S : Scheme.{u}} (c : Chern l E (diagonalSurface S)) :
    D (diagonalSurface S) (Arings l E (diagonalSurface S)) :=
  c.scalar.T.obj (c.reduction.derived.obj
    ((DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).obj
      ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))))

/-- The supported coefficient generator is the scalar extension of the integral unit.
Source: classes (3), quotient-unit normalization (blueprint: def-sp-tower-class-diagonal). -/
def diagonalExtendedUnit {S : Scheme.{u}} (c : Chern l E (diagonalSurface S)) :
    unit (diagonalSurface S) (Arings l E (diagonalSurface S)) ⟶
      diagonalExtendedSource l E c :=
  c.scalarUnit.inv ≫ c.scalar.T.map
    (c.unitIso.inv ≫ c.reduction.derived.map
      ((DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).map
        ((constant (diagonalSurface S)).map (supportedIntegralUnit S))))

/-- The diagonal arrow is the specified coefficient extension of beta_Delta.
Its supported source is fixed by a quotient-unit-preserving isomorphism below.
Source: classes (3), beta = a[1](-p v inverse)
(blueprint: def-sp-tower-class-diagonal). -/
def diagonalArrow {S : Scheme.{u}} (c : Chern l E (diagonalSurface S))
    {b : SpTowerShriek.Base l E}
    {g : SpTowerShriek.Geometry l E b (diagonalImmersion S)}
    (s : diagonalExtendedSource l E c ≅
      (SpTowerShriek.push l E b g).obj (unit (ProjectiveLine S)
        (Arings l E (ProjectiveLine S)))) :
    (SpTowerShriek.push l E b g).obj
        (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))) ⟶
      (line l E c)⟦(2 : ℤ)⟧ :=
  s.inv ≫ c.scalar.T.map
    (c.reduction.derived.map (diagonalBoundary S) ≫ c.rootIso.hom) ≫
    (c.scalar.T.commShiftIso (2 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor (Systems (diagonalSurface S)
        (Rrings l (diagonalSurface S))) 0).obj c.rootModule) ≫
    (lineComparison l E c)⟦(2 : ℤ)⟧'

/-- The canonical diagonal construction, with the supported source fixed by its
quotient unit and the forget-support map equal to c1 of the actual divisor line.
All sources and targets are the recorded module derived categories and geometry.
Source: classes (3) (blueprint: def-sp-tower-class-diagonal). -/
structure Diagonal (b : SpTowerShriek.Base l E) (S : Scheme.{u})
    (c : Chern l E (diagonalSurface S)) where
  geometry : SpTowerShriek.Geometry l E b (diagonalImmersion S)
  coefficientPullback : CoefficientPullback l E b (diagonalImmersion S) geometry
  sourceIso : diagonalExtendedSource l E c ≅
    (SpTowerShriek.push l E b geometry).obj
      (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
  source_normalization : diagonalExtendedUnit l E c ≫ sourceIso.hom =
    unitArrow l E coefficientPullback
  chern_normalization : unitArrow l E coefficientPullback ≫
      diagonalArrow l E c sourceIso = firstChern l E c (diagonalPic S)

/-- The actual positive-level coefficient ring.
Source: coefficient convention (blueprint: def-sp-tower-class-diagonal). -/
abbrev FiniteRing (n : ℕ) := ULift.{u + 1} (SpTowerShriek.R l E n)

/-- The unital Z/ell^(n+1) coefficient map, before taking constant sheaves.
Source: coefficient convention (blueprint: def-sp-tower-class-diagonal). -/
def finiteScalar (n : ℕ) : ZMod (l ^ (n + 1)) →+* FiniteRing l E n :=
  ULift.ringEquiv.symm.toRingHom.comp
    (ZMod.castHom (ringChar.dvd (coefficient_annihilates l E n)) (SpTowerShriek.R l E n))

/-- The recorded finite Tate line, with no independently chosen line object.
Source: definition-tate-twists (blueprint: def-sp-tower-class-diagonal). -/
abbrev finiteLine (T : Scheme.{u}) (n : ℕ) :=
  Scheme.tateFiniteLine T l (FiniteRing l E n) n (finiteScalar l E n)

private theorem section_cast_heq {A B : AddCommGrpCat.{u + 1}}
    (h : A = B) (x : A) : HEq ((eqToHom h) x) x := by
  subst B
  rfl

/-- The finite comparison is fixed on every scalar multiple of every root generator.
Source: classes (2), evaluation of coefficient extension
(blueprint: def-sp-tower-class-diagonal).
Proof: restriction to a sequence-site slice commutes with the sheafified ordinary
scalar extension. The underlying root module is identified by rootForget. Both
sides are sheafifications of the same local tensor product; send a tensor to the
identical tensor. This commutes with restrictions and quotient transitions.
These local pure tensors generate the tensor sheaf, giving uniqueness. -/
theorem lineEvaluation_existsUnique {T : Scheme.{u}} (c : Chern l E T) (n : ℕ) :
    ∃! e : (SpTowerShriek.ev l E T n).obj (lineModule l E c) ≅ finiteLine l E T n,
      ∀ (U : T.ProEtᵒᵖ) (a : (SpTowerShriek.B l E T n).obj.obj U)
        (x : c.rootModule.val.obj (op (n, U.unop)))
        (x' : ((c.reduction.forget.F.obj c.rootModule).obj (op n)).obj.obj U)
        (v : ((SpTowerShriek.ev l E T n).obj (lineModule l E c)).val.obj U),
        HEq x x' →
        HEq v (a • SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
          (coefficientSystemMap l E T) c.scalar c.rootModule (op (n, U.unop)) x) →
        e.hom.val.app U v =
          Scheme.tateFiniteTensor T l (FiniteRing l E n) n (finiteScalar l E n)
            U.unop a ((c.rootForget.hom.app (op n)).hom.app U x') := by
  let M := (SpTowerShriek.ev l E T n).obj (lineModule l E c)
  let L := finiteLine l E T n
  obtain ⟨Φ, hΦ, pΦ⟩ := towerLineEvaluation_universal l E c n
  obtain ⟨Ψ, hΨ, pΨ⟩ :=
    finiteTateLine_universal T l (FiniteRing l E n) n (finiteScalar l E n)
  let f : M ⟶ L := (Φ L).symm (Ψ L (𝟙 L))
  let g : L ⟶ M := (Ψ M).symm (Φ M (𝟙 M))
  have hf : Φ L f = Ψ L (𝟙 L) := (Φ L).apply_symm_apply _
  have hg : Ψ M g = Φ M (𝟙 M) := (Ψ M).apply_symm_apply _
  have hfg : f ≫ g = 𝟙 M := by
    apply (Φ M).injective
    erw [hΦ, hf, ← hΨ, Category.id_comp, hg]
  have hgf : g ≫ f = 𝟙 L := by
    apply (Ψ L).injective
    erw [hΨ, hg, ← hΦ, Category.id_comp, hf]
  let e : M ≅ L := ⟨f, g, hfg, hgf⟩
  have hp : ∀ (U : T.ProEtᵒᵖ) (a : (SpTowerShriek.B l E T n).obj.obj U)
      (x : c.rootModule.val.obj (op (n, U.unop)))
      (x' : ((c.reduction.forget.F.obj c.rootModule).obj (op n)).obj.obj U)
      (v : M.val.obj U),
      HEq x x' →
      HEq v (a • SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
        (coefficientSystemMap l E T) c.scalar c.rootModule (op (n, U.unop)) x) →
      f.val.app U v = Scheme.tateFiniteTensor T l (FiniteRing l E n) n
        (finiteScalar l E n) U.unop a ((c.rootForget.hom.app (op n)).hom.app U x') := by
    intro U a x x' v hx hv
    rw [pΦ L f U a x x' v hx hv, hf]
    exact pΨ L (𝟙 L) U a _
  refine ⟨e, hp, ?_⟩
  intro e' he'
  apply Iso.ext
  apply (Φ L).injective
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  let x' := (c.rootForget.inv.app (op n)).hom.app U z
  let x := (eqToHom (c.reduction.forget.sections c.rootModule n U)) x'
  have hx : HEq x x' := section_cast_heq _ _
  let v : M.val.obj U :=
    SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
      (coefficientSystemMap l E T) c.scalar c.rootModule (op (n, U.unop)) x
  have hv : HEq v ((1 : (SpTowerShriek.B l E T n).obj.obj U) •
      SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
        (coefficientSystemMap l E T) c.scalar c.rootModule (op (n, U.unop)) x) := by
    simpa only [one_smul] using (HEq.rfl : HEq v v)
  have hz : (c.rootForget.hom.app (op n)).hom.app U x' = z := by
    have h := congrArg (fun k => (k.hom.app U) z)
      (NatTrans.congr_app c.rootForget.inv_hom_id (op n))
    exact h
  have h₁ := pΦ L e'.hom U 1 x x' v hx hv
  have h₂ := pΦ L f U 1 x x' v hx hv
  have h₃ := he' U 1 x x' v hx hv
  have h₄ := hp U 1 x x' v hx hv
  have hval : e'.hom.val.app U v = f.val.app U v := h₃.trans h₄.symm
  simpa only [one_smul, hz] using h₁.symm.trans (hval.trans h₂)

/-- The uniquely normalized finite Tate-line realization.
Source: classes (2) (blueprint: def-sp-tower-class-diagonal). -/
def lineEvaluation {T : Scheme.{u}} (c : Chern l E T) (n : ℕ) :=
  (lineEvaluation_existsUnique l E c n).exists.choose

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
