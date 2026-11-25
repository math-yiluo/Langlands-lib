/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.EmbeddedFiniteCoefficientRealization
import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.EmbeddedFirstReductionOrdinary
import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.EmbeddedIntegralRestrictionKFlat
import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.EmbeddedFiniteScalarIsIso
import all WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # The normalized first reduction under constant scalar restriction

## References

* Stacks Tags 099L and 06YQ
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsEmbedded

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  finiteRealization integralModelIntrinsicRealization
  IntegralModelsStacks.smallDerivedObject IntegralModelsStacks.smallModules
  IntegralModelsStacks.smallMap
  upperStarLowerStarAdjunction pointUpperStar
  Mod.extendScalars Mod.comap Mod.extendScalarsIsoComapInv
  Functor.mapHomologicalComplex DerivedCategory.Q
  Functor.mapHomologicalComplexCompIso NatIso.mapHomologicalComplex
  NatTrans.mapHomologicalComplex
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  Functor.leftDerivedFunctorIsoMapDerivedCategory Functor.rightExact_cochainCounit

/-- Lift a comparison of three ordinary additive functors degreewise. -/
private def tripleComplexIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (T : A ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [T.Additive]
    (c : (F ⋙ G) ⋙ H ≅ T) (P : CochainComplex A ℤ) :
    (H.mapHomologicalComplex (.up ℤ)).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≅
      (T.mapHomologicalComplex (.up ℤ)).obj P :=
  (H.mapHomologicalComplex (.up ℤ)).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).app P) ≪≫
    (Functor.mapHomologicalComplexCompIso c (.up ℤ)).app P

/-- Derive an ordinary square on a K-flat representative. -/
private theorem deriveOrdinarySquare
    (X : Scheme.{u})
    {R B S T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj B] [IsCommMonObj B]
    [MonObj S] [IsCommMonObj S] [MonObj T] [IsCommMonObj T]
    (φ : R ⟶ B) [IsMonHom φ] (q : R ⟶ S) [IsMonHom q]
    (e : S ⟶ T) [IsMonHom e] [IsIso e] (p : B ⟶ T) [IsMonHom p]
    (c : (Mod.comap φ ⋙ Mod.extendScalars q) ⋙ Mod.extendScalars e ≅
      Mod.extendScalars p)
    (hr : ∀ P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B) ℤ,
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
          (((Mod.comap φ).mapHomologicalComplex (.up ℤ)).obj P))
    (K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B)) :
    Nonempty
      ((Mod.extendScalars e).leftDerivedFunctor.obj
        ((Mod.extendScalars q).leftDerivedFunctor.obj ((Mod.comap φ).mapDerivedCategory.obj K)) ≅
        (Mod.extendScalars p).leftDerivedFunctor.obj K) := by
  have hlim : PreservesFiniteLimits (Mod.extendScalars e) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv e).symm
  let L := DerivedCategory.Q.objPreimage K
  obtain ⟨P, f, hf, _, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat L
  have := hf
  let a : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let Pr := ((Mod.comap φ).mapHomologicalComplex (.up ℤ)).obj P
  have hcq := (Mod.extendScalars q).rightExact_cochainCounit_isIso Pr (hr P hP)
  have hcp := (Mod.extendScalars p).rightExact_cochainCounit_isIso P hP
  let r := (Mod.comap φ).mapDerivedCategoryFactors.app P
  let cq := asIso ((Mod.extendScalars q).rightExact_cochainCounit Pr)
  let cp := asIso ((Mod.extendScalars p).rightExact_cochainCounit P)
  let Pq := ((Mod.extendScalars q).mapHomologicalComplex (.up ℤ)).obj Pr
  let ce := (Mod.extendScalars e).leftDerivedFunctorIsoMapDerivedCategory.app
    (DerivedCategory.Q.obj Pq) ≪≫ (Mod.extendScalars e).mapDerivedCategoryFactors.app Pq
  let j := tripleComplexIso
    (Mod.comap φ) (Mod.extendScalars q) (Mod.extendScalars e) (Mod.extendScalars p) c P
  let d₁ := (Mod.extendScalars q).leftDerivedFunctor.mapIso r ≪≫ cq
  let d₂ := (Mod.extendScalars e).leftDerivedFunctor.mapIso d₁ ≪≫ ce
  let d₃ := DerivedCategory.Q.mapIso j
  let d := d₂ ≪≫ d₃ ≪≫ cp.symm
  let A := (Mod.comap φ).mapDerivedCategory ⋙ (Mod.extendScalars q).leftDerivedFunctor ⋙
    (Mod.extendScalars e).leftDerivedFunctor
  exact ⟨A.mapIso a.symm ≪≫ d ≪≫ (Mod.extendScalars p).leftDerivedFunctor.mapIso a⟩

set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] integralModel_coefficientMonObj in
/-- The first reduction after restriction and the continuous first reduction become
isomorphic under the specified constant-function scalar realization. This assertion
concerns only the derived scalar square, with no constructibility or Tor condition. -/
theorem firstReductionComparison
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) [IsNoetherian X]
    [Finite (completedResidue ℓ E π 0)] [DiscreteTopology (completedResidue ℓ E π 0)]
    (K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (integralCoefficientObject X ℓ E))) :
    letI : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
      CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
    letI : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
      CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
    Nonempty
      ((constantResidueRealization ℓ E π X).obj K ≅
        (continuousResidueRealization ℓ E π X).obj K) := by
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  obtain ⟨c⟩ := embeddedFirstReductionOrdinary ℓ E π hπ X
  have he := embeddedFiniteScalarIsIso X (completedResidue ℓ E π 0)
  obtain ⟨d⟩ := deriveOrdinarySquare X (scalarMap ℓ E X) (residueMap ℓ E π X)
    (finiteScalarMap X (completedResidue ℓ E π 0))
    (integralModelReductionMap X ℓ E π 1).hom c
    (fun P hP ↦ embeddedIntegralRestrictionKFlat ℓ E π hπ X P hP) K
  let F := (integralModelIntrinsicRealization X
    (completedResidue ℓ E π 0)).rightDerivedFunctor
  unfold constantResidueRealization continuousResidueRealization
  unfold constantFirstReduction continuousFirstReduction finiteRealization
  exact ⟨F.mapIso d⟩

end AlgebraicGeometry.ProEtale.IntegralModelsEmbedded
