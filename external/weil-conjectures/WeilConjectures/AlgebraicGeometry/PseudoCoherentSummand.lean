/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.Algebra.Homology.RingPseudoCoherentSummand
import WeilConjectures.AlgebraicGeometry.AffineDerivedSummandModels
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Pseudo-coherence is preserved by direct summands

Source: literature/stacks-project/cohomology.tex, Tag 08CE
(blueprint: lem-pc-pseudo-coherent-summand).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem summand_affine_free_iso (S : Scheme.{u}) (U : S.Opens)
    (hU : IsAffineOpen U) (m : ℕ) :
    Nonempty ((affinePerfectSheafification S U hU).obj
      (ModuleCat.of (S.presheaf.obj (.op U))
        (ULift.{u} (Fin m) →₀ (S.presheaf.obj (.op U)))) ≅
      SheafOfModules.free (R := (moduleRings S.toRingedSpace).over U)
        (ULift.{u} (Fin m))) := by
  let R := S.presheaf.obj (.op U)
  let F := Modules.restrictFunctor hU.isoSpec.hom
  let G := (Modules.overEquiv U).inverse
  have : F.IsLeftAdjoint := (Modules.restrictAdjunction hU.isoSpec.hom).isLeftAdjoint
  let eF := (SheafOfModules.mapFreeIso F (ULift.{u} (Fin m))
    (Modules.restrictUnitIso hU.isoSpec.hom).symm).symm
  let eG := (SheafOfModules.mapFreeIso G (ULift.{u} (Fin m))
    (U.sheafOfModulesEquivOverInverseUnit S.ringCatSheaf).symm).symm
  exact ⟨G.mapIso (F.mapIso (tildeFinsupp (R := R) (ULift.{u} (Fin m))) ≪≫ eF) ≪≫ eG⟩

private theorem summand_affine_finiteFree_model (S : Scheme.{u}) (U : S.Opens)
    (hU : IsAffineOpen U)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
    (hb : ∃ N : ℤ, ∀ i : ℤ, N < i → Limits.IsZero (P.X i))
    (hf : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin r)))) :
    ∃ M : CochainComplex (ModuleCat.{u} (S.presheaf.obj (.op U))) ℤ,
      ∃ b : ℤ, M.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Free (S.presheaf.obj (.op U)) (M.X i) ∧
          Module.Finite (S.presheaf.obj (.op U)) (M.X i)) ∧
        Nonempty (((affinePerfectSheafification S U hU).mapHomologicalComplex (.up ℤ)).obj M
          ≅ P) := by
  classical
  let R := S.presheaf.obj (.op U)
  let rF := Modules.restrictFunctor hU.isoSpec.hom
  let rG := Modules.restrictFunctor hU.isoSpec.inv
  let e := CategoryTheory.Equivalence.mk rF rG
    ((Modules.restrictFunctorId).symm ≪≫
      Modules.restrictFunctorCongr (by simp) ≪≫
      Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom)
    ((Modules.restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).symm ≪≫
      Modules.restrictFunctorCongr (by simp) ≪≫ Modules.restrictFunctorId)
  have : rF.IsEquivalence := e.isEquivalence_functor
  let F := affinePerfectSheafification S U hU
  have : F.Full := by unfold F affinePerfectSheafification; infer_instance
  have : F.Faithful := by unfold F affinePerfectSheafification; infer_instance
  choose r hr using hf
  let X (i : ℤ) := ModuleCat.of R (ULift.{u} (Fin (r i)) →₀ R)
  let ei (i : ℤ) : F.obj (X i) ≅ P.X i :=
    (summand_affine_free_iso S U hU (r i)).some ≪≫ (hr i).some.symm
  let d (i j : ℤ) : X i ⟶ X j := F.preimage ((ei i).hom ≫ P.d i j ≫ (ei j).inv)
  have hd (i j : ℤ) : F.map (d i j) = (ei i).hom ≫ P.d i j ≫ (ei j).inv :=
    F.map_preimage _
  let M : CochainComplex (ModuleCat.{u} R) ℤ :=
    { X := X
      d := d
      shape := by
        intro i j hij
        apply F.map_injective
        rw [hd, P.shape i j hij]
        simp
      d_comp_d' := by
        intro i j k _ _
        apply F.map_injective
        rw [Functor.map_comp, hd, hd]
        simp [Category.assoc] }
  let eC : (F.mapHomologicalComplex (.up ℤ)).obj M ≅ P :=
    HomologicalComplex.Hom.isoOfComponents ei (by
      intro i j _
      change (ei i).hom ≫ P.d i j = F.map (d i j) ≫ (ei j).hom
      rw [hd]
      simp)
  obtain ⟨b, hb⟩ := hb
  refine ⟨M, b, ?_, fun _ ↦ ⟨inferInstance, inferInstance⟩, ⟨eC⟩⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply F.map_injective
  rw [F.map_id, F.map_zero]
  exact ((ei i).isZero_iff.mpr (hb i hi)).eq_of_src _ _



/-- If a pseudo-coherent object of `D(𝒪_X)` is isomorphic to a binary biproduct,
both summands are pseudo-coherent. Source: Stacks Project, Cohomology of Sheaves,
Tag 08CE, with More on Algebra, Tag 064X (blueprint: lem-pc-pseudo-coherent-summand).

Proof:
1. At each point choose the bounded-above finite-free witness from
   `def-pur-pseudo-coherent-complex` and refine its neighbourhood to an affine open V.
   Exact restriction preserves zero terms and finite-free terms. Its derived
   factorization and composition comparisons transport the representing isomorphism.
2. Lift the finite-free terms and their differentials through the fully faithful
   affine sheafification functor. Explicit finite bases and preimages of the matrix
   differentials construct a bounded-above finite-free module complex A.
3. Restrict the given biproduct decomposition and apply
   `lem-pc-affine-derived-summand-models`: the summands have module preimages C and D
   with Q(A) ≅ C ⊞ D. The explicit model A witnesses ring pseudo-coherence of C ⊞ D.
   Apply the last clause of `lem-pc-ring-pseudo-coherent-summand` to C and D.
4. Sheafify their bounded-above finite-free representatives, using the comparison
   with derived sheafification and the preimage isomorphisms. The resulting local
   models, one for each summand at every point, witness pseudo-coherence on X.
   This includes the empty scheme and either summand being zero.
-/
theorem pseudoCoherent_of_isIso_biproduct (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L M : schemeDerivedCategory X)
    (h : Nonempty (K ≅ L ⊞ M))
    (hK : IsPseudoCoherent X K) :
    IsPseudoCoherent X L ∧ IsPseudoCoherent X M := by
  classical
  -- Share the site instances across the affine restriction and both summand models.
  have : ∀ U : X.Opens,
      HasSheafify ((Opens.grothendieckTopology X.toRingedSpace).over U)
        AddCommGrpCat.{u} := inferInstance
  have : ∀ U : X.Opens,
      ((Opens.grothendieckTopology X.toRingedSpace).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u} := inferInstance
  obtain ⟨e⟩ := h
  have local_models (x : X) :
      (∃ U : X.Opens, x ∈ U ∧
        ∃ P : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
          (∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i)) ∧
          (∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
            (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r)))) ∧
          Nonempty ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj L ≅
              DerivedCategory.Q.obj P)) ∧
      (∃ U : X.Opens, x ∈ U ∧
        ∃ P : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
          (∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i)) ∧
          (∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
            (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r)))) ∧
          Nonempty ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj M ≅
              DerivedCategory.Q.obj P)) := by
    obtain ⟨U, hxU, P, hb, hf, ⟨eP⟩⟩ := hK x
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (U := U) hxU
    let F := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hVU)
    let H := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
    let J := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V
    let PV := (F.mapHomologicalComplex (.up ℤ)).obj P
    have hbV : ∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (PV.X i) := by
      obtain ⟨N, hN⟩ := hb
      exact ⟨N, fun i hi ↦ F.map_isZero (hN i hi)⟩
    have hfV (i : ℤ) : ∃ r : ℕ, Nonempty (PV.X i ≅ SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin r))) := by
      obtain ⟨r, ⟨ei⟩⟩ := hf i
      let ef := (SheafOfModules.mapFreeIso F (ULift.{u} (Fin r))
        (SheafOfModules.overMapUnitIso
          (R := moduleRings X.toRingedSpace) (homOfLE hVU)).symm).symm
      exact ⟨r, ⟨F.mapIso ei ≪≫ ef⟩⟩
    have : PreservesFiniteLimits (H ⋙ F) := comp_preservesFiniteLimits _ _
    have : PreservesFiniteColimits (H ⋙ F) := comp_preservesFiniteColimits _ _
    let eV : J.mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj PV :=
      (Functor.mapDerivedCategoryNatIso
        (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE hVU))).symm.app K ≪≫
        (Functor.mapDerivedCategoryCompIso H F).symm.app K ≪≫ F.mapDerivedCategory.mapIso eP ≪≫
          F.mapDerivedCategoryFactors.app P
    obtain ⟨A, b, hAb, hAf, ⟨eA⟩⟩ :=
      summand_affine_finiteFree_model X V hV PV hbV hfV
    let R := X.presheaf.obj (.op V)
    let : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
    let T := (affinePerfectSheafification X V hV).mapHomologicalComplex (.up ℤ)
    have : PreservesBinaryBiproducts J.mapDerivedCategory :=
      preservesBinaryBiproducts_of_preservesBinaryProducts _
    let dec : DerivedCategory.Q.obj (T.obj A) ≅
        J.mapDerivedCategory.obj L ⊞ J.mapDerivedCategory.obj M :=
      DerivedCategory.Q.mapIso eA ≪≫ eV.symm ≪≫ J.mapDerivedCategory.mapIso e ≪≫
        J.mapDerivedCategory.mapBiprod L M
    obtain ⟨G, hG, ⟨cmp⟩, C, D, ⟨cd⟩, ⟨eC⟩, ⟨eD⟩⟩ :=
      affine_derived_summand_models X V hV A _ _ ⟨dec⟩
    have hsum : DerivedCategory.IsPseudoCoherent (C ⊞ D) :=
      ⟨A, b, hAb, hAf, ⟨cd⟩⟩
    obtain ⟨hC, hD⟩ := DerivedCategory.pseudoCoherent_summand C D hsum
    have model (E : schemeDerivedCategory X)
        (B : DerivedCategory (ModuleCat.{u} R))
        (iso : J.mapDerivedCategory.obj E ≅ G.obj B)
        (hB : DerivedCategory.IsPseudoCoherent B) :
        ∃ Q : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ,
          (∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (Q.X i)) ∧
          (∀ i : ℤ, ∃ r : ℕ, Nonempty (Q.X i ≅ SheafOfModules.free
            (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin r)))) ∧
          Nonempty (J.mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj Q) := by
      obtain ⟨B', b', hb', hf', ⟨eB⟩⟩ := hB
      refine ⟨T.obj B', ⟨b', ?_⟩, ?_, ?_⟩
      · intro i hi
        exact (affinePerfectSheafification X V hV).map_isZero
          (B'.isZero_of_isStrictlyLE b' i hi)
      · intro i
        have : Module.Free R (B'.X i) := (hf' i).1
        have : Module.Finite R (B'.X i) := (hf' i).2
        let r := Fintype.card (Module.Free.ChooseBasisIndex R (B'.X i))
        let basis := (Module.Free.chooseBasis R (B'.X i)).reindex
          ((Fintype.equivFin _).trans (Equiv.ulift.symm : Fin r ≃ ULift.{u} (Fin r)))
        exact ⟨r, ⟨(affinePerfectSheafification X V hV).mapIso basis.repr.toModuleIso ≪≫
          (summand_affine_free_iso X V hV r).some⟩⟩
      · exact ⟨iso ≪≫ G.mapIso eB.symm ≪≫ cmp.app B'⟩
    obtain ⟨PC, hbC, hfC, hiC⟩ := model L C eC hC
    obtain ⟨PD, hbD, hfD, hiD⟩ := model M D eD hD
    exact ⟨⟨V, hxV, PC, hbC, hfC, hiC⟩, ⟨V, hxV, PD, hbD, hfD, hiD⟩⟩
  exact ⟨fun x ↦ (local_models x).1, fun x ↦ (local_models x).2⟩

end AlgebraicGeometry.Scheme
