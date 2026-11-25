/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import WeilConjectures.AlgebraicGeometry.AdicPerfectModelLocalResidueBounds
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import all WeilConjectures.AlgebraicGeometry.ProEtaleOperations
import all WeilConjectures.AlgebraicGeometry.ProEtaleTorLocalGlobal

/-! # Bounds from stratified perfect models

Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private instance boundsWEquals (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
    u + 1, u + 2, u + 1} (ProEt.topology X)

private noncomputable def inverseImageIdentityIso {X S : Scheme.{u}} (i : S ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    proEtaleRingModulePullback i R
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _) ≅
      proEtaleModuleInverseImage i R := by
  let B := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
  let H := proEtaleModuleInverseImage i R
  let r : SheafOfModules.restrictScalars ((adicLisseForget S).map (𝟙 B)) ≅
      𝟭 (proEtaleRingModules S B) :=
    NatIso.ofComponents (fun M ↦
      (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk
          (fun U ↦ ModuleCat.restrictScalarsId'App _ rfl (M.val.obj U))
          (by intros; ext x; rfl))) (by intros; ext U x; rfl)
  let a := proEtaleRingExtensionAdjunction i R B (Iso.refl _)
  let b := (Adjunction.id (C := proEtaleRingModules S B)).ofNatIsoRight r.symm
  exact Functor.isoWhiskerLeft H (a.leftAdjointUniq b) ≪≫ Functor.rightUnitor H

private instance criterionSliceDerived (S : Scheme.{u})
    (R : Sheaf (ProEt.topology S) CommRingCat.{u + 1}) (U : S.ProEt) :
    HasDerivedCategory (SheafOfModules.{u + 1} (((adicLisseForget S).obj R).over U)) :=
  HasDerivedCategory.standard _

private noncomputable abbrev restrictionFunctor {X S : Scheme.{u}} (i : S ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : S.ProEt) :=
  proEtaleModuleInverseImage i R ⋙ ProEtaleLocalRestriction.restriction i R U

private noncomputable def localRestrictionIso {X S : Scheme.{u}} (i : S ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : S.ProEt)
    (K : DerivedCategory (proEtaleRingModules X R)) :
    sfbLocalRestriction i R U K ≅ (restrictionFunctor i R U).mapDerivedCategory.obj K := by
  let B := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
  let G := proEtaleRingModulePullback i R B (Iso.refl _)
  let H := proEtaleModuleInverseImage i R
  let T := ProEtaleLocalRestriction.restriction i R U
  let e : G ≅ H := inverseImageIdentityIso i R
  have : H.Additive := (proEtaleModuleInverseImageAdjunction i R).left_adjoint_additive
  let C := DerivedCategory.Q.objPreimage K
  let L := G.mapDerivedCategory.obj K
  let D := DerivedCategory.Q.objPreimage L
  change DerivedCategory.Q.obj ((T.mapHomologicalComplex (.up ℤ)).obj D) ≅ _
  refine (T.mapDerivedCategoryFactors.app D).symm ≪≫
    T.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso L) ≪≫
    T.mapDerivedCategory.mapIso
      (G.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K).symm) ≪≫
    T.mapDerivedCategory.mapIso (G.mapDerivedCategoryFactors.app C) ≪≫
    T.mapDerivedCategory.mapIso (DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app C)) ≪≫
    (T.mapDerivedCategoryFactors.app _ ) ≪≫ ?_
  exact ((restrictionFunctor i R U).mapDerivedCategoryFactors.app C).symm ≪≫
    (restrictionFunctor i R U).mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso K)

private theorem modelHomology_zero (X : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] (I : Ideal A) (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (q : ℤ) (hq : IsZero (P.X q)) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj (sfbCompletedModel X I P)) := by
  let := CompletedConstantReduction.constant_additive X A
  let C := ((completedAdicChange X (CompletedConstantReduction.base X I)).mapHomologicalComplex
    (.up ℤ)).obj ((CompletedConstantReduction.constantComplex X A).obj P)
  have hz : IsZero (C.X q) :=
    (completedAdicChange X (CompletedConstantReduction.base X I)).map_isZero
      ((adicLisseConstantModules X A).map_isZero hq)
  exact ((C.sc q).isZero_homology_of_isZero_X₂ hz).of_iso
    ((DerivedCategory.homologyFunctorFactors _ q).app C)

private theorem localModelHomology_zero {X S : Scheme.{u}} (i : S ⟶ X)
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) (U : S.ProEt)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (e : sfbLocalRestriction i (adicLisseCompletedRing X I) U K ≅
      sfbLocalRestriction i (adicLisseCompletedRing X I) U (sfbCompletedModel X I P))
    (q : ℤ) (hq : IsZero (P.X q)) :
    IsZero ((restrictionFunctor i (adicLisseCompletedRing X I) U).obj
      ((DerivedCategory.homologyFunctor _ q).obj K)) := by
  let R := adicLisseCompletedRing X I
  let F := restrictionFunctor i R U
  let L := sfbCompletedModel X I P
  let c : F.obj ((DerivedCategory.homologyFunctor _ q).obj K) ≅
      F.obj ((DerivedCategory.homologyFunctor _ q).obj L) :=
    (F.mapDerivedCategoryHomologyFunctorIso q).app K ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso
        ((localRestrictionIso i R U K).symm ≪≫ e ≪≫ localRestrictionIso i R U L) ≪≫
      (F.mapDerivedCategoryHomologyFunctorIso q).symm.app L
  exact (F.map_isZero (modelHomology_zero X I P q hq)).of_iso c

private theorem compact_terminal (S : Scheme.{u}) [CompactSpace S] :
    CompactSpace (⊤_ S.ProEt).left := by
  have ht : IsTerminal (ProEt.mk (𝟙 S)) :=
    IsTerminal.ofUniqueHom
      (fun U ↦ MorphismProperty.Over.homMk U.hom (Category.comp_id _) (by trivial)) (by
      intro U f
      apply MorphismProperty.Over.Hom.ext
      have hw := MorphismProperty.Over.w f
      change f.left ≫ 𝟙 S = U.hom at hw
      exact (Category.comp_id _).symm.trans hw)
  let e : (⊤_ S.ProEt).left ≅ S :=
    (ProEt.forget S ⋙ Over.forget S).mapIso (terminalIsTerminal.uniqueUpToIso ht)
  exact QuasiCompact.compactSpace_of_compactSpace e.hom

private theorem moduleZero_of_strata (X : Scheme.{u}) [IsNoetherian X]
    (s : Stratification X) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : proEtaleRingModules X R)
    (hM : ∀ α : Fin s.n, IsZero ((proEtaleModuleInverseImage (s.immersion α) R).obj M)) :
    IsZero M := by
  let (α : Fin s.n) : TopologicalSpace.NoetherianSpace (s.domain α) :=
    (s.immersion α).isEmbedding.noetherianSpace
  let (α : Fin s.n) : QuasiCompact (s.immersion α) := inferInstance
  let F := SheafOfModules.toSheaf ((adicLisseForget X).obj R)
  have hz : IsZero (F.obj M) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply AlgebraicGeometry.ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp
      s.immersion
    · intro x
      obtain ⟨α, hα⟩ := Set.mem_iUnion.mp
        (s.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
      exact ⟨α, (s.range_immersion α).symm ▸ hα⟩
    · intro α
      rw [(AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1}
        (s.immersion α)).map_id]
      obtain ⟨e⟩ := (proEtale_moduleInverseImage_comparison (s.immersion α) R).1
      exact (((SheafOfModules.toSheaf _).map_isZero (hM α)).of_iso
        (e.app M).symm).eq_of_src _ _
  apply (IsZero.iff_id_eq_zero M).2
  apply F.map_injective
  simpa using hz.eq_of_src (F.map (𝟙 M)) (F.map 0)

private theorem perfectModels_bounds (X : Scheme.{u}) [IsNoetherian X]
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (hK : IsSfbStratifiedPerfect X I K) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
  classical
  obtain ⟨s, -, hs⟩ := hK
  let (α : Fin s.n) : TopologicalSpace.NoetherianSpace (s.domain α) :=
    (s.immersion α).isEmbedding.noetherianSpace
  let (α : Fin s.n) : QuasiCompact (s.immersion α) := inferInstance
  let (α : Fin s.n) : CompactSpace (⊤_ (s.domain α).ProEt).left :=
    compact_terminal (s.domain α)
  choose W hW hw using hs
  choose J hJ V f hV hf using
    fun α ↦ ProEt.qc_finite_cover (s.domain α) (⊤_ (s.domain α).ProEt) (W α) (hW α)
  let := hJ
  have hmodels (α : Fin s.n) (j : J α) := hw α (V α j) (f α j) (hf α j)
  choose P a b hp ha hb hfin he using hmodels
  let T := Σ α : Fin s.n, J α
  let : Fintype T := Fintype.ofFinite T
  let lo : ℤ := -∑ t : T, |a t.1 t.2|
  let hi : ℤ := ∑ t : T, |b t.1 t.2|
  refine ⟨lo, hi, ?_, ?_⟩
  · have hl : 0 ≤ ∑ t : T, |a t.1 t.2| := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
    have hh : 0 ≤ hi := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
    exact (neg_nonpos.mpr hl).trans hh
  · intro q hq
    apply moduleZero_of_strata X s (adicLisseCompletedRing X I)
    intro α
    have hcV : (ProEt.topology (s.domain α)).CoversTop (V α) :=
      ((ProEt.topology (s.domain α)).coversTop_iff_of_isTerminal
        (⊤_ (s.domain α).ProEt) terminalIsTerminal (V α)).mpr
          ((ProEt.topology (s.domain α)).superset_covering
            (Sieve.ofArrows_le_ofObjects (V α) (f α)) (hV α))
    apply CategoryTheory.isZero_of_slice_cover _ (V α) hcV
    intro j
    apply localModelHomology_zero (s.immersion α) I (V α j) K (P α j) (he α j).some q
    rcases hq with hq | hq
    · have hsum := Finset.single_le_sum
        (f := fun t : T ↦ |a t.1 t.2|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ (⟨α, j⟩ : T))
      have hlt : q < a α j := by dsimp [lo] at hq; linarith [neg_abs_le (a α j)]
      let := ha α j
      exact (P α j).isZero_of_isStrictlyGE (a α j) q hlt
    · have hsum := Finset.single_le_sum
        (f := fun t : T ↦ |b t.1 t.2|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ (⟨α, j⟩ : T))
      have hlt : b α j < q := by dsimp [hi] at hq; linarith [le_abs_self (b α j)]
      let := hb α j
      exact (P α j).isZero_of_isStrictlyLE (b α j) q hlt

private theorem abelianZero_of_slice_cover {C : Type*} [Category C]
    {J : GrothendieckTopology C} {ι : Type*} (V : ι → C) (hV : J.CoversTop V)
    (F : Sheaf J AddCommGrpCat.{u + 1})
    (hF : ∀ j, IsZero ((J.overPullback AddCommGrpCat.{u + 1} (V j)).obj F)) :
    IsZero F := by
  apply (IsZero.iff_id_eq_zero F).2
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply F.property.hom_ext (hV.cover U.unop)
  rintro ⟨W, f, ⟨j, ⟨g⟩⟩⟩
  have hz := congrArg (fun k ↦ k.hom.app (op (Over.mk g)))
    ((hF j).eq_of_src (𝟙 _) 0)
  change (𝟙 (F.obj.obj (op W))) = 0 at hz
  change (𝟙 _ : F.obj.obj U ⟶ _) ≫ _ = 0 ≫ _
  simp only [Category.id_comp, zero_comp]
  rw [← Category.comp_id (F.obj.map f.op), hz, comp_zero]

private theorem residueModels_bounds (X : Scheme.{u}) [IsNoetherian X]
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.IsMaximal)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (hK : IsSfbStratifiedPerfect X I K) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (DerivedCategory.Q.obj (sfbResidueComplex X I K))) := by
  classical
  obtain ⟨s, -, hs⟩ := hK
  let (α : Fin s.n) : TopologicalSpace.NoetherianSpace (s.domain α) :=
    (s.immersion α).isEmbedding.noetherianSpace
  let (α : Fin s.n) : QuasiCompact (s.immersion α) := inferInstance
  let (α : Fin s.n) : CompactSpace (⊤_ (s.domain α).ProEt).left :=
    compact_terminal (s.domain α)
  choose W hW hw using hs
  choose J hJ V f hV hf using
    fun α ↦ ProEt.qc_finite_cover (s.domain α) (⊤_ (s.domain α).ProEt) (W α) (hW α)
  let := hJ
  have hmodels (α : Fin s.n) (j : J α) := hw α (V α j) (f α j) (hf α j)
  choose P a b hp ha hb hfin he using hmodels
  let T := Σ α : Fin s.n, J α
  let : Fintype T := Fintype.ofFinite T
  let lo : ℤ := -∑ t : T, |a t.1 t.2|
  let hi : ℤ := ∑ t : T, |b t.1 t.2|
  refine ⟨lo, hi, ?_, ?_⟩
  · have hl : 0 ≤ ∑ t : T, |a t.1 t.2| := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
    have hh : 0 ≤ hi := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
    exact (neg_nonpos.mpr hl).trans hh
  · intro q hq
    let M := (DerivedCategory.homologyFunctor _ q).obj
      (DerivedCategory.Q.obj (sfbResidueComplex X I K))
    let F := sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) AddCommGrpCat.{u + 1})
    have hz : IsZero (F.obj M) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply AlgebraicGeometry.ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp
        s.immersion
      · intro x
        obtain ⟨α, hα⟩ := Set.mem_iUnion.mp
          (s.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
        exact ⟨α, (s.range_immersion α).symm ▸ hα⟩
      · intro α
        rw [(AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1}
          (s.immersion α)).map_id]
        have hcV : (ProEt.topology (s.domain α)).CoversTop (V α) :=
          ((ProEt.topology (s.domain α)).coversTop_iff_of_isTerminal
            (⊤_ (s.domain α).ProEt) terminalIsTerminal (V α)).mpr
              ((ProEt.topology (s.domain α)).superset_covering
                (Sieve.ofArrows_le_ofObjects (V α) (f α)) (hV α))
        have hlocal : IsZero ((proEtaleSheafInverseImage (s.immersion α)
            AddCommGrpCat.{u + 1}).obj (F.obj M)) := by
          apply abelianZero_of_slice_cover (V α) hcV
          intro j
          apply adicPerfectModel_localResidueBounds (s.immersion α) I hI (V α j) K
            (P α j) (a α j) (b α j) (ha α j) (hb α j) (hfin α j) (he α j).some q
          rcases hq with hq | hq
          · have hsum := Finset.single_le_sum
              (f := fun t : T ↦ |a t.1 t.2|) (fun _ _ ↦ abs_nonneg _)
              (Finset.mem_univ (⟨α, j⟩ : T))
            exact Or.inl (by dsimp [lo] at hq; linarith [neg_abs_le (a α j)])
          · have hsum := Finset.single_le_sum
              (f := fun t : T ↦ |b t.1 t.2|) (fun _ _ ↦ abs_nonneg _)
              (Finset.mem_univ (⟨α, j⟩ : T))
            exact Or.inr (by dsimp [hi] at hq; linarith [le_abs_self (b α j)])
        exact hlocal.eq_of_src _ _
    apply (IsZero.iff_id_eq_zero M).2
    apply F.map_injective
    simpa using hz.eq_of_src (F.map (𝟙 M)) (F.map 0)

/-- The object and its canonical residue have globally bounded cohomology.
Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication, and Lemma 6.5.3.
(auxiliary; not a blueprint node).

Proof: choose finite subcovers of the covering sieves on the Noetherian strata.
For the finitely many selected coefficient models with intervals [a_j,b_j], take
[-sum |a_j|,sum |b_j|]. This interval is ordered even when no charts are selected.
A zero term of a coefficient model stays zero under additive constant realization
and completed scalar extension, so its completed model has zero cohomology there.
Exact inverse image and slice restriction transport this vanishing through the
specified local isomorphisms. Sheaf separation on each cover and detection on the
jointly surjective family of stratum immersions give the global bound for K.
Apply adicPerfectModel_localResidueBounds on each selected chart for the residue,
using the same interval. Slice separation and stratum detection for the underlying
additive sheaf give global residue vanishing; the forgetful functor is faithful. -/
theorem adicPerfectModels_cohomologicalBounds (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.IsMaximal ∧ ∀ J : Ideal A, J.IsMaximal → J = I)
    [IsAdicComplete I A]
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (hK : IsSfbStratifiedPerfect X I K) :
    (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) ∧
    (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (DerivedCategory.Q.obj (sfbResidueComplex X I K)))) := by
  exact ⟨perfectModels_bounds X I K hK, residueModels_bounds X I hI.1 K hK⟩

end AlgebraicGeometry.Scheme
