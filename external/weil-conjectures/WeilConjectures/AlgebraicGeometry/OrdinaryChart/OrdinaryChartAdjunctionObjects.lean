/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-! # Ordinary chart adjunctions and their counit-normalized comparisons

These constructions use only ordinary etale compact supports. No site realization
or constructible-origin choice is used to define a chart comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale

namespace OrdinaryChart

/-- The ordered affine-space left functor compared with a specified compactification.
Every factor is the proper/open composition or common-refinement comparison.
The identity step uses the two exact identity functors, so no orientation is chosen. -/
def affineLeftIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) :
    (c : Compactification (affineTraceProjection S d)) →
    Etale.affineTraceLeft A S d ≅
      Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  Nat.rec (motive := fun n ↦ ∀ c : Compactification (affineTraceProjection S n),
      Etale.affineTraceLeft A S n ≅
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (fun c ↦
      (Functor.isoWhiskerRight
          (Etale.mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ Etale.rightDerivedLowerStarIdIso A S).symm ≪≫
        Etale.rightDerivedLowerShriekOfCompactificationIso A
          (Compactification.ofIsProper (𝟙 S)) c)
    (fun n ih c ↦
      let cp := HasCompactification.compactification (affineTraceProjection S n)
      let ce := c.ofComp cp
      Functor.isoWhiskerRight
          (Etale.rightDerivedLowerShriekOfCompactificationIso A
            (affineTraceLineCompactification (affineTraceTower S n)) ce.restrict) _ ≪≫
        Functor.isoWhiskerLeft _ (ih cp) ≪≫
        Etale.rightDerivedLowerShriekOfCompactificationCompIso A cp ce ≪≫
        Etale.rightDerivedLowerShriekOfCompactificationIso A (cp.comp ce) c) d

/-- The chart right adjunction is literally sum/evaluation followed by the specified
ordered affine-space adjunction. The inverse-image model comparison is the canonical
exact-to-left-derived comparison. -/
def adjunction (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) [IsNoetherian S] (N : ℕ) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA t T hT)
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    {U : Scheme.{u}} (e : U ⟶ affineTraceTower S d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        Etale.affineTraceLeft A S d ⊣
      Etale.affineTraceRight A N hA S d ⋙ Etale.ordinaryFinitePullback A e :=
  ((Etale.derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).ofNatIsoRight
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm).comp
      (Etale.affineTraceAdjunction A N hA t D S hS d)

/-- Canonical chart left comparison: graph-normalized sum extension, ordered affine
composition, common refinement, then inverse source-open comparison. -/
def leftIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (M : Etale.EtaleCompactSupportNormalization A)
    {X S U : Scheme.{u}} [IsNoetherian X] [IsNoetherian S] [IsNoetherian U]
    (f : X ⟶ S) (i : U ⟶ X) [IsOpenImmersion i]
    (d : ℕ) (e : U ⟶ affineTraceTower S d) [AlgebraicGeometry.Etale e] [IsSeparated e]
    (he : i ≫ f = e ≫ affineTraceProjection S d)
    (cf : Compactification f) :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        Etale.affineTraceLeft A S d ≅
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) i inferInstance).mapDerivedCategory ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf :=
  letI := affineTraceNoetherian S d
  let cp := HasCompactification.compactification (affineTraceProjection S d)
  let cg := HasCompactification.compactification (e ≫ affineTraceProjection S d)
  Functor.isoWhiskerLeft _ (affineLeftIso A S d cp) ≪≫
    Etale.etaleAmbientLeftComparison A M e (affineTraceProjection S d) cp cg ≪≫
    (Etale.etaleAmbientLeftComparison A M i f cf (cg.copy he)).symm

/-- The chart identification is the unique counit-preserving right-adjoint comparison
for the preceding left comparison. It is therefore normalized by actual affine trace
and summation over e, with no free scalar or arbitrary right-functor isomorphism. -/
def rightIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (M : Etale.EtaleCompactSupportNormalization A)
    {X S U : Scheme.{u}} [IsNoetherian X] [IsNoetherian S] [IsNoetherian U]
    (f : X ⟶ S) (i : U ⟶ X) [IsOpenImmersion i]
    (d : ℕ) (e : U ⟶ affineTraceTower S d) [AlgebraicGeometry.Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ f = e ≫ affineTraceProjection S d) (cf : Compactification f)
    (G : Etale.DerivedCategoryModule A S ⥤ Etale.DerivedCategoryModule A X)
    (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf ⊣ G)
    (N : ℕ) (hA : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA t T hT) (hS : IsUnit (N : Γ(S, ⊤))) :
    G ⋙ Etale.ordinaryFinitePullback A i ≅
      Etale.affineTraceRight A N hA S d ⋙ Etale.ordinaryFinitePullback A e :=
  (((Etale.derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) i inferInstance).ofNatIsoRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) i).symm).comp
        adj).rightAdjointUniq
    ((adjunction A S N hA t D hS d e).ofNatIsoLeft
      (leftIso A M f i d e he cf))

end OrdinaryChart

end AlgebraicGeometry.Etale
