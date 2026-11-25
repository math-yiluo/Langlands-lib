/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicImmersionResidueTransport
import all WeilConjectures.AlgebraicGeometry.ConstantCoefficientLocalModelsComparison
import all WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import all WeilConjectures.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModelsComparison
import WeilConjectures.ConstructibleSheaf.Pullback

/-! # Finite lisse sheaves in the explicit etale coefficient model

Source: Stacks Project, Tags 03RU, 03RW, 03CY and 03A0.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private instance adicImmersionResidueLisseInst1 : JointlySurjective etalePrecoverage.{u} :=
  inferInstanceAs (JointlySurjective (precoverage @Etale))

private theorem finiteValueCover {S : Scheme.{u}} (k : Type (u + 1)) [CommRing k]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} k))
    [IsFiniteLocallyConstantSheaf F] :
    ∃ d : LocallyConstantDatum F, ∀ j : d.cover.I₀,
      ∃ M : ModuleCat.{u + 1} k, Module.Finite k M ∧ Nonempty
        (F.over (d.cover.etalePrecoverageToEtale j) ≅
          (constantSheaf (S.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale j))
            (ModuleCat.{u + 1} k)).obj M) := by
  classical
  obtain ⟨d₀⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  let 𝒰 : Cover.{u} etalePrecoverage S :=
    { I₀ := { j : d₀.cover.I₀ // Nonempty (d₀.cover.X j) }
      X j := d₀.cover.X j.1
      f j := d₀.cover.f j.1
      mem₀ := by
        refine (presieve₀_mem_precoverage_iff _).mpr
          ⟨fun y ↦ ?_, fun j ↦ d₀.cover.map_prop j.1⟩
        obtain ⟨j, x, hx⟩ := d₀.cover.exists_eq y
        exact ⟨⟨j, ⟨x⟩⟩, x, hx⟩ }
  let d : LocallyConstantDatum F := ⟨𝒰, fun j ↦ d₀.isConstant j.1⟩
  refine ⟨d, fun j ↦ ?_⟩
  have := d.isConstant j
  obtain ⟨M, ⟨e⟩⟩ := (F.over (d.cover.etalePrecoverageToEtale j)).mem_essImage_of_isConstant
  let U := d.cover.etalePrecoverageToEtale j
  have : Nonempty U.left := j.2
  let x : U.left := Classical.arbitrary _
  let Ω := SeparableClosure (U.left.residueField x)
  let t : Spec (.of Ω) ⟶ U.left := (SpecToEquivOfField Ω _).2
    ⟨x, CommRingCat.ofHom (algebraMap (U.left.residueField x) Ω)⟩
  have hgen := (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
    (F := F) Ω (t ≫ U.hom)).of_iso (constantValueStalkIso F U M e.symm t)
  exact ⟨M, (ModuleCat.isFinitelyGenerated_iff M).1 hgen, ⟨e.symm⟩⟩

private def constantOverMapIso {S : Scheme.{u}} (k : Type (u + 1)) [CommRing k]
    {U W : S.Etale} (h : W ⟶ U) :
    constantSheaf (S.smallEtaleTopology.over U) (ModuleCat.{u + 1} k) ⋙
      S.smallEtaleTopology.overMapPullback (ModuleCat.{u + 1} k) h ≅
        constantSheaf (S.smallEtaleTopology.over W) (ModuleCat.{u + 1} k) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const (Over U)ᵒᵖ)
      ((Over.map h).pushforwardContinuousSheafificationCompatibility
        (ModuleCat.{u + 1} k) (S.smallEtaleTopology.over W)
        (S.smallEtaleTopology.over U)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.constCompWhiskeringLeftIso _ (Over.map h).op)
      (presheafToSheaf (S.smallEtaleTopology.over W) (ModuleCat.{u + 1} k))

private theorem finiteLisse_fixedModels {S : Scheme.{u}} (k : Type (u + 1)) [CommRing k]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} k))
    [IsFiniteLocallyConstantSheaf F] : ProFiniteModels.fixedModels S.smallEtaleTopology k F := by
  intro V
  let B := ModuleCat.{u + 1} k
  have : IsFiniteLocallyConstantSheaf ((Etale.upperStar B V.hom).obj F) :=
    IsFiniteLocallyConstantSheaf.upperStar V.hom F
  obtain ⟨d, hd⟩ := finiteValueCover k ((Etale.upperStar B V.hom).obj F)
  let U (j : ULift.{u + 1, u} d.cover.I₀) : S.Etale :=
    Etale.mk (d.cover.f j.down ≫ V.hom)
  let f (j : ULift.{u + 1, u} d.cover.I₀) : U j ⟶ V :=
    MorphismProperty.Over.homMk (d.cover.f j.down) rfl
  refine ⟨Sieve.ofArrows U f, ?_, ?_⟩
  · apply (ofArrows_mem_smallEtaleTopology_iff (f := f)).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨j, y, hy⟩ := d.cover.exists_eq x
    exact Set.mem_iUnion.mpr ⟨⟨j⟩, y, hy⟩
  · intro W g hg
    obtain ⟨j, h, rfl⟩ := (Sieve.mem_ofArrows_iff U f g).mp hg
    obtain ⟨M, hM, ⟨e⟩⟩ := hd j.down
    let T := d.cover.etalePrecoverageToEtale j.down
    let : (Etale.overEquiv T).inverse.IsDenseSubsite
        T.left.smallEtaleTopology (V.left.smallEtaleTopology.over T) :=
      Etale.overEquiv_inverse_isDenseSubsite T
    let E := Etale.overSheafEquiv (U j) B
    let e' : (Etale.upperStar B (U j).hom).obj F ≅
        (constantSheaf (U j).left.smallEtaleTopology B).obj M :=
      (Etale.upperStarComp B (d.cover.f j.down) V.hom).app F ≪≫
        (overSheafEquivFunctorObjOverIso B T _).symm ≪≫
        (Etale.overSheafEquiv T B).functor.mapIso e ≪≫
        ((Etale.overEquiv T).constantSheafSheafCongrIso
          (V.left.smallEtaleTopology.over T) T.left.smallEtaleTopology B
          CategoryTheory.Over.mkIdTerminal).app M
    let eU : F.over (U j) ≅
        (constantSheaf (S.smallEtaleTopology.over (U j)) B).obj M :=
      E.functor.preimageIso
        (overSheafEquivFunctorObjOverIso B (U j) F ≪≫ e' ≪≫
          (((Etale.overEquiv (U j)).constantSheafSheafCongrIso
            (S.smallEtaleTopology.over (U j)) (U j).left.smallEtaleTopology B
            CategoryTheory.Over.mkIdTerminal).app M).symm)
    exact ⟨M, hM, ⟨(S.smallEtaleTopology.overMapPullback B h).mapIso eU ≪≫
      (constantOverMapIso k h).app M⟩⟩

/-- Finite local constancy on the original etale site gives finite module values in
its explicit constant-ring small model. The coefficient ring need not be finite.

Source: Stacks Project, Tags 03RU, 03RW(3), 03CY and 03A0
(auxiliary; not a blueprint node).
Proof: choose a locally constant cover of F and discard its empty members. This still
covers S, since a member covering a point is nonempty. On each remaining member U,
choose a constant module value V and a geometric point of U. Pullback to U and the
constant-sheaf stalk comparison identify V with the geometric stalk of F, as modules.
The finite-sheaf hypothesis says that this stalk is finitely generated; hence V is
finitely generated. Transport this cover along AsSmall.down, which is an equivalence
of sites and preserves covering sieves. The scalar-restriction equivalence commutes
with localization and identifies the constant module sheaf with the constant
fixed-scalar sheaf. Its inverse therefore identifies the transported trivializations
with constantCoefficientModule(V). Restrict the transported covering sieve to each
object to obtain exactly IsLocallyConstantFiniteTypeModules. Empty S and empty slice
objects use the empty covering sieve and require no choice of a geometric point. -/
theorem sfbEtaleResidueModel_finiteLisse (S : Scheme.{u})
    (k : Type (u + 1)) [CommRing k]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} k))
    (hF : IsFiniteLocallyConstantSheaf F) :
    SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, 0} S) k
      ((sfbEtaleResidueModel S k).functor.obj F) := by
  have := hF
  let J := smallModelComparisonEtaleTopology.{u, 0} S
  let H := (sfbImmersionEtaleModel S k).functor.obj F
  let E := (ConstantScalarRestriction.restriction J k).asEquivalence
  let M := E.inverse.obj H
  let c := (constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of k)
  have hsmall : ProFiniteModels.fixedModels J k H :=
    (ProFiniteModels.fixedModels_asSmall S.smallEtaleTopology k F).mp
      (finiteLisse_fixedModels k F)
  have hfixed : ProFiniteModels.fixedModels J k
      ((ConstantScalarRestriction.restriction J k).obj M) :=
    ProFiniteModels.fixedModels_of_iso J k (E.counitIso.app H).symm hsmall
  have hring := (ProFiniteModels.fixedModels_constantRing J k
    ((SheafOfModules.restrictScalars c.inv).obj M)).mp hfixed
  exact (SheafOfModules.compare_of_iso J k c
    (SheafOfModules.coefficientRingIso_fac J k) M).mpr hring

/-- The concrete residue model has locally constant finite type cohomology.
Source: Stacks Project, Tags 03RU, 03CY and 03A0
(auxiliary; not a blueprint node).
Proof: choose locally constant trivializing covers for each original cohomology sheaf,
transport them through the AsSmall site equivalence and the scalar restriction
Equivalence, and use the exact homology comparison. The stalk modules on each cover
are finitely generated because the original finite sheaf has finitely generated
geometric stalks; scalar restriction preserves finite generation. The transported
cover therefore witnesses the displayed predicate. -/
theorem sfbImmersionResidue_lisse {X S : Scheme.{u}} (i : S ⟶ X)
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (C : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))) ℤ)
    (h : ∀ q : ℤ, IsFiniteLocallyConstantSheaf
      ((Etale.upperStar.{u + 2, u} (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) i).obj
        (C.homology q))) :
    ∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, 0} S) (A ⧸ I ^ (0 + 1))
      ((adicResidueCohomology.{u + 1}
        (ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, 0} S) A I 0)
        q).obj (sfbImmersionResidue i I C)) := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod
    (ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, 0} S) A I 0))
  intro q V
  let F := sfbImmersionResidueFunctor i (A ⧸ I ^ (0 + 1))
  let e := (DerivedCategory.homologyFunctorFactors _ q).app
      ((F.mapHomologicalComplex (.up ℤ)).obj C) ≪≫
    (F.mapHomologicalComplexHomologyIso (.up ℤ) q).app C
  obtain ⟨T, hT, ht⟩ := sfbEtaleResidueModel_finiteLisse S (A ⧸ I ^ (0 + 1))
    ((Etale.upperStar.{u + 2, u} (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) i).obj
      (C.homology q)) (h q) V
  refine ⟨T, hT, ?_⟩
  intro U f hf
  obtain ⟨N, hN, ⟨eN⟩⟩ := ht U f hf
  exact ⟨N, hN, ⟨(SheafOfModules.overFunctor _ U).mapIso e ≪≫ eN⟩⟩

end AlgebraicGeometry.Scheme
