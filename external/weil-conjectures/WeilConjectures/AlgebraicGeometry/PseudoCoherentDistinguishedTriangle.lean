/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.AffineLocalizedDerivedSheafification
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Pseudo-coherence is closed under distinguished triangles

Source: Stacks Project, Cohomology of Sheaves, Tag 08CD,
`lemma-cone-pseudo-coherent`, part (2) for every integer m
(blueprint: lem-pc-pseudo-coherent-distinguished-triangle).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme

private theorem restrict_finiteFree_model (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (E : schemeDerivedCategory Y) {U V : Y.Opens} (hVU : V ≤ U)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) ℤ)
    (hb : ∃ N : ℤ, ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero (P.X i))
    (hf : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
      (R := (moduleRings Y.toRingedSpace).over U) (ULift.{u} (Fin r))))
    (he : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings Y.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj P)) :
    ∃ Q : CochainComplex
        (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V)) ℤ,
      (∃ N : ℤ, ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero (Q.X i)) ∧
      (∀ i : ℤ, ∃ r : ℕ, Nonempty (Q.X i ≅ SheafOfModules.free
        (R := (moduleRings Y.toRingedSpace).over V) (ULift.{u} (Fin r)))) ∧
      Nonempty ((SheafOfModules.overFunctor.{u}
        (moduleRings Y.toRingedSpace) V).mapDerivedCategory.obj E ≅
          DerivedCategory.Q.obj Q) := by
  let A := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U
  let F := SheafOfModules.overMap.{u} (moduleRings Y.toRingedSpace) (homOfLE hVU)
  let Q := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  refine ⟨Q, ?_, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := hb
    exact ⟨N, fun i hi ↦ F.map_isZero (hN i hi)⟩
  · intro i
    obtain ⟨r, ⟨e⟩⟩ := hf i
    refine ⟨r, ⟨F.mapIso e ≪≫ ?_⟩⟩
    exact (SheafOfModules.mapFreeIso F (ULift.{u} (Fin r))
      (SheafOfModules.overMapUnitIso (homOfLE hVU)).symm).symm
  · have : CategoryTheory.Limits.PreservesFiniteLimits (A ⋙ F) :=
      CategoryTheory.Limits.comp_preservesFiniteLimits A F
    have : CategoryTheory.Limits.PreservesFiniteColimits (A ⋙ F) :=
      CategoryTheory.Limits.comp_preservesFiniteColimits A F
    let e := (Functor.mapDerivedCategoryCompIso A F) ≪≫
      Functor.mapDerivedCategoryNatIso
        (SheafOfModules.overFunctorMap.{u} (moduleRings Y.toRingedSpace) (homOfLE hVU))
    obtain ⟨j⟩ := he
    exact ⟨(e.app E).symm ≪≫ F.mapDerivedCategory.mapIso j ≪≫
      F.mapDerivedCategoryFactors.app P⟩

private theorem finiteFree_mappingCone (Y : Scheme.{u}) (U : Y.Opens)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) ℤ)
    (hbP : ∃ N : ℤ, ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero (P.X i))
    (hbQ : ∃ N : ℤ, ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero (Q.X i))
    (hfP : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
      (R := (moduleRings Y.toRingedSpace).over U) (ULift.{u} (Fin r))))
    (hfQ : ∀ i : ℤ, ∃ r : ℕ, Nonempty (Q.X i ≅ SheafOfModules.free
      (R := (moduleRings Y.toRingedSpace).over U) (ULift.{u} (Fin r))))
    (g : P⟦(-1 : ℤ)⟧ ⟶ Q) :
    (∃ N : ℤ, ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero ((CochainComplex.mappingCone g).X i)) ∧
      (∀ i : ℤ, ∃ r : ℕ, Nonempty
        ((CochainComplex.mappingCone g).X i ≅ SheafOfModules.free
          (R := (moduleRings Y.toRingedSpace).over U) (ULift.{u} (Fin r)))) := by
  constructor
  · obtain ⟨a, ha⟩ := hbP
    obtain ⟨b, hb⟩ := hbQ
    refine ⟨max a b, fun i hi ↦ ?_⟩
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨(P.shiftFunctorObjXIso (-1) (i + 1) i (by omega)).isZero_iff.mpr
      (ha i (lt_of_le_of_lt (le_max_left a b) hi)),
      hb i (lt_of_le_of_lt (le_max_right a b) hi)⟩
  · intro i
    obtain ⟨a, ⟨ea⟩⟩ := hfP i
    obtain ⟨b, ⟨eb⟩⟩ := hfQ i
    let e := (HomologicalComplex.homotopyCofiber.XIsoBiprod g i (i + 1) rfl) ≪≫
      CategoryTheory.Limits.biprod.mapIso
        (P.shiftFunctorObjXIso (-1) (i + 1) i (by omega) ≪≫ ea) eb ≪≫
      CategoryTheory.Limits.biprod.isoCoprod _ _ ≪≫
      SheafOfModules.freeSumIso (ULift.{u} (Fin a)) (ULift.{u} (Fin b))
    let t : (ULift.{u} (Fin a) ⊕ ULift.{u} (Fin b)) ≃ ULift.{u} (Fin (a + b)) :=
      (Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
        ((finSumFinEquiv).trans Equiv.ulift.symm)
    exact ⟨a + b, ⟨e ≪≫ (SheafOfModules.freeFunctor
      (R := (moduleRings Y.toRingedSpace).over U)).mapIso (Equiv.toIso t)⟩⟩

/-- Termwise affine sections give a K-projective module model for a bounded-above
finite-free complex. The affine counit is an isomorphism on each finite-free term.
Source: Stacks Project, Tag 06Z0, and the bounded-above projective criterion. -/
private theorem affine_finiteFree_module_model (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U)
    (K : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hbK : ∃ N : ℤ, ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero (K.X i))
    (hfK : ∀ i : ℤ, ∃ r : ℕ, Nonempty (K.X i ≅ SheafOfModules.free
      (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r)))) :
    ∃ P : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op U))) ℤ,
      P.IsKProjective ∧
      Nonempty (((affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ)).obj P
        ≅ K) := by
  let R := X.presheaf.obj (.op U)
  let S := SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace)
  let D := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let rF := Modules.restrictFunctor hU.isoSpec.hom
  let rG := Modules.restrictFunctor hU.isoSpec.inv
  let e : S ≌ (U : Scheme.{u}).Modules := CategoryTheory.Equivalence.mk rF rG
    ((Modules.restrictFunctorId).symm ≪≫
      Modules.restrictFunctorCongr (by simp [R]) ≪≫
      Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom)
    ((Modules.restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).symm ≪≫
      Modules.restrictFunctorCongr (by simp) ≪≫ Modules.restrictFunctorId)
  let E : S ≌ D := e.trans (Modules.overEquiv U).symm
  have : CategoryTheory.Limits.HasBinaryBiproducts S :=
    CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryProducts
  have : CategoryTheory.Limits.HasBinaryBiproducts D :=
    CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryProducts
  have : CategoryTheory.Limits.PreservesBinaryBiproducts E.functor :=
      CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : CategoryTheory.Limits.PreservesBinaryBiproducts E.inverse :=
      CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : E.functor.Additive := Functor.additive_of_preservesBinaryBiproducts _
  have : E.inverse.Additive := Functor.additive_of_preservesBinaryBiproducts _
  let T := tilde.functor R
  let H := E.inverse ⋙ moduleSpecΓFunctor (R := R)
  let F := T ⋙ E.functor
  let adj : F ⊣ H := tilde.adjunction.comp E.toAdjunction
  have : H.IsRightAdjoint := adj.isRightAdjoint
  have : (moduleSpecΓFunctor (R := R)).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ rfl⟩
  have : H.PreservesZeroMorphisms := inferInstance
  have : CategoryTheory.Limits.PreservesBinaryBiproducts H :=
      CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : H.Additive := Functor.additive_of_preservesBinaryBiproducts _
  let P : CochainComplex (ModuleCat.{u} R) ℤ := (H.mapHomologicalComplex (.up ℤ)).obj K
  have hfree (m : ℕ) : Nonempty (F.obj
      (ModuleCat.of R (ULift.{u} (Fin m) →₀ R)) ≅
      SheafOfModules.free (R := (moduleRings X.toRingedSpace).over U)
        (ULift.{u} (Fin m))) := by
    let unitIso := (Modules.overEquiv U).inverse.mapIso
      ((Modules.restrictUnitIso hU.isoSpec.hom) ≪≫
        Modules.overEquivFunctorObjUnitIso U) ≪≫
        ((Modules.overEquiv U).unitIso.app
          (SheafOfModules.unit ((moduleRings X.toRingedSpace).over U))).symm
    exact ⟨E.functor.mapIso (tildeFinsupp (ULift.{u} (Fin m))) ≪≫
      (SheafOfModules.mapFreeIso E.functor (ULift.{u} (Fin m)) unitIso.symm).symm⟩
  have hcounit (n : ℤ) : IsIso (adj.counit.app (K.X n)) := by
    obtain ⟨m, ⟨eK⟩⟩ := hfK n
    obtain ⟨ef⟩ := hfree m
    exact adj.isIso_counit_app_of_iso (eK ≪≫ ef.symm)
  have hproj (n : ℤ) : Projective (P.X n) := by
    obtain ⟨m, ⟨eK⟩⟩ := hfK n
    let ι := eK.hom
    let π := eK.inv
    have hιπ : ι ≫ π = 𝟙 _ := eK.hom_inv_id
    obtain ⟨ef⟩ := hfree m
    let eH := H.mapIso ef.symm ≪≫ (asIso (adj.unit.app _)).symm
    have hm : Projective (ModuleCat.of R (ULift.{u} (Fin m) →₀ R)) :=
      ModuleCat.projective_of_categoryTheory_projective _
    have hp : Projective (H.obj
        (SheafOfModules.free (R := (moduleRings X.toRingedSpace).over U)
          (ULift.{u} (Fin m)))) := eH.retract.projective
            (p := by
              change Projective (ModuleCat.of R (ULift.{u} (Fin m) →₀ R))
              exact hm)
    exact (Retract.map (⟨ι, π, hιπ⟩ : Retract _ _) H).projective
  obtain ⟨b, hb⟩ := hbK
  have : CochainComplex.IsStrictlyLE P b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact H.map_isZero (hb n hn)
  have : ∀ n : ℤ, Projective (P.X n) := hproj
  refine ⟨P, CochainComplex.isKProjective_of_projective P b, ⟨?_⟩⟩
  let ε := (NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app K
  have : IsIso ε := by
    have : ∀ n : ℤ, IsIso (ε.f n) := hcounit
    exact HomologicalComplex.Hom.isIso_of_components ε
  exact (asIso ε) ≪≫ (Functor.mapHomologicalComplexIdIso D (.up ℤ)).app K

/-- Full affine derived sheafification and K-projectivity lift derived arrows to
chain maps between bounded-above finite-free sheaf complexes.
Source: Stacks Project, Tag 06Z0; Mathlib's K-projective localization theorem. -/
private theorem affine_finiteFree_map_representative (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (hU : IsAffineOpen U)
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hbA : ∃ N : ℤ, ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero (A.X i))
    (hbB : ∃ N : ℤ, ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero (B.X i))
    (hfA : ∀ i : ℤ, ∃ r : ℕ, Nonempty (A.X i ≅ SheafOfModules.free
      (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r))))
    (hfB : ∀ i : ℤ, ∃ r : ℕ, Nonempty (B.X i ≅ SheafOfModules.free
      (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r))))
    (f : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj B) :
    ∃ α : A ⟶ B, DerivedCategory.Q.map α = f := by
  let R := X.presheaf.obj (.op U)
  let : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
  let F := (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ)
  obtain ⟨P, hP, ⟨eA⟩⟩ := affine_finiteFree_module_model X U hU A hbA hfA
  obtain ⟨T, _, ⟨eB⟩⟩ := affine_finiteFree_module_model X U hU B hbB hfB
  have : P.IsKProjective := hP
  obtain ⟨G, hG, ⟨c⟩⟩ := affine_localized_derived_sheafification X U hU
  have : G.Full := hG
  let a := c.app P ≪≫ DerivedCategory.Q.mapIso eA
  let b := c.app T ≪≫ DerivedCategory.Q.mapIso eB
  let g : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj T :=
    G.preimage (a.hom ≫ f ≫ b.inv)
  obtain ⟨β, hβ⟩ := CochainComplex.IsKProjective.exists_Q_map_eq P T g
  refine ⟨eA.inv ≫ F.map β ≫ eB.hom, ?_⟩
  have hc := c.hom.naturality β
  change G.map (DerivedCategory.Q.map β) ≫ (c.app T).hom =
    (c.app P).hom ≫ DerivedCategory.Q.map (F.map β) at hc
  rw [hβ] at hc
  have hg : G.map g = a.hom ≫ f ≫ b.inv := G.map_preimage _
  rw [hg] at hc
  have hc' : DerivedCategory.Q.map (F.map β) =
      (c.app P).inv ≫ a.hom ≫ f ≫ b.inv ≫ (c.app T).hom := by
    calc
      _ = (c.app P).inv ≫ ((c.app P).hom ≫
          DerivedCategory.Q.map (F.map β)) := by simp
      _ = _ := by rw [← hc]; simp only [Category.assoc]
  simp only [Functor.map_comp, hc', Category.assoc]
  dsimp [a, b]
  simp

/-- In a distinguished triangle in `D(𝒪_Y)`, pseudo-coherence of the first and third
objects implies pseudo-coherence of the second.

Source: Stacks Project, Cohomology of Sheaves, Tag 08CD, part (2) for every m
(blueprint: lem-pc-pseudo-coherent-distinguished-triangle).

Proof:
1. Intersect the two neighbourhoods supplied by pseudo-coherence and choose an affine
   open inside the intersection containing the given point. Restrict both models with
   `overMap`. It preserves zero objects and finite free sheaves; its derived composition
   isomorphism identifies the restricted models with the two restricted objects.
2. Transport a bounded-above finite-free complex from the localized affine site to the
   spectrum of the ring of sections. Apply global sections termwise. The affine
   tilde/Gamma adjunction's counit is an isomorphism on finite-free terms, naturally in
   the differentials, so sheafification recovers the complex. The sections complex is
   bounded above and termwise projective, hence K-projective.
3. Restrict the triangle and inverse-rotate it. Conjugate its first arrow by the models
   of C[-1] and A. Full affine derived sheafification lifts this arrow to modules;
   K-projectivity represents it by a chain map. Sheafify and use the factorization
   isomorphism's naturality to obtain a chain map g : P_C[-1] → P_A representing it.
4. Compare the cone triangle with the inverse-rotated triangle using the isomorphism
   of their first arrows. The third component of the resulting triangle isomorphism
   identifies B with Q(cone(g)). The cone has terms P_C^i ⊕ P_A^i: they vanish above
   the maximum of the two upper bounds and are finite free on the disjoint union of
   the two finite bases. This model on the affine neighbourhood proves the claim. -/
theorem isPseudoCoherent_of_distinguished_triangle (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (T : Triangle (schemeDerivedCategory Y))
    (hT : T ∈ distTriang (schemeDerivedCategory Y))
    (hA : IsPseudoCoherent Y T.obj₁) (hC : IsPseudoCoherent Y T.obj₃) :
    IsPseudoCoherent Y T.obj₂ := by
  intro y
  obtain ⟨UA, hyA, PA, hbA, hfA, heA⟩ := hA y
  obtain ⟨UC, hyC, PC, hbC, hfC, heC⟩ := hC y
  obtain ⟨U, hU, hyU, hsub⟩ :=
    exists_isAffineOpen_mem_and_subset (show y ∈ UA ⊓ UC from ⟨hyA, hyC⟩)
  have hUA : U ≤ UA := fun z hz ↦ (hsub hz).1
  have hUC : U ≤ UC := fun z hz ↦ (hsub hz).2
  obtain ⟨A, hbA, hfA, ⟨eA⟩⟩ :=
    restrict_finiteFree_model Y T.obj₁ hUA PA hbA hfA heA
  obtain ⟨C, hbC, hfC, ⟨eC⟩⟩ :=
    restrict_finiteFree_model Y T.obj₃ hUC PC hbC hfC heC
  let F := (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U).mapDerivedCategory
  let S := (F.mapTriangle.obj T).invRotate
  have hS : S ∈ distTriang _ :=
    inv_rot_of_distTriang _ (F.map_distinguished T hT)
  let e₁ : S.obj₁ ≅ DerivedCategory.Q.obj (C⟦(-1 : ℤ)⟧) :=
    (shiftFunctor _ (-1)).mapIso eC ≪≫
      ((DerivedCategory.Q.commShiftIso (-1)).app C).symm
  have hbC' : ∃ N : ℤ, ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero ((C⟦(-1 : ℤ)⟧).X i) := by
    obtain ⟨N, hN⟩ := hbC
    refine ⟨N + 1, fun i hi ↦ ?_⟩
    exact (C.shiftFunctorObjXIso (-1) i (i - 1) (by omega)).isZero_iff.mpr
      (hN (i - 1) (by omega))
  have hfC' : ∀ i : ℤ, ∃ r : ℕ, Nonempty ((C⟦(-1 : ℤ)⟧).X i ≅
      SheafOfModules.free (R := (moduleRings Y.toRingedSpace).over U)
        (ULift.{u} (Fin r))) := by
    intro i
    obtain ⟨r, ⟨e⟩⟩ := hfC (i - 1)
    exact ⟨r, ⟨C.shiftFunctorObjXIso (-1) i (i - 1) (by omega) ≪≫ e⟩⟩
  obtain ⟨g, hg⟩ := affine_finiteFree_map_representative Y U hU
    (C⟦(-1 : ℤ)⟧) A hbC' hbA hfC' hfA (e₁.inv ≫ S.mor₁ ≫ eA.hom)
  have hcomm : DerivedCategory.Q.map g ≫ eA.inv = e₁.inv ≫ S.mor₁ := by
    rw [hg]
    simp
  obtain ⟨e, _, _⟩ := exists_iso_of_arrow_iso
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle g)) S
    (DerivedCategory.mappingCone_triangle_distinguished g) hS
    (Arrow.isoMk e₁.symm eA.symm hcomm.symm)
  obtain ⟨hb, hf⟩ := finiteFree_mappingCone Y U C A hbC hbA hfC hfA g
  exact ⟨U, hyU, CochainComplex.mappingCone g, hb, hf,
    ⟨(Triangle.π₃.mapIso e).symm⟩⟩

end AlgebraicGeometry.Scheme
