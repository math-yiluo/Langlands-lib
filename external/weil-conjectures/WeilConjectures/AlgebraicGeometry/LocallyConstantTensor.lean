/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.AlgebraicGeometry.SiteLocallyConstantFiniteType
import WeilConjectures.AlgebraicGeometry.SiteFiniteFreeTruncationModels
import WeilConjectures.AlgebraicGeometry.SiteTensorLocalModelComparison
import WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact

/-! # Derived tensor preserves locally constant finite type cohomology

Source: Stacks Project, Cohomology on Sites, Tag 094H
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace SheafOfModules

section ConstantRealization

variable {C : Type u} [Category.{u} C]

set_option quotPrecheck false in
set_option hygiene false in
local notation "𝓡(" J ", " B ")" => (sheafCompose J
  (forget₂ CommRingCat.{u} RingCat.{u})).obj
    ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B))
set_option quotPrecheck false in
set_option hygiene false in
local notation "cB(" J ", " B ")" => strictPerfectConstantPresheaf (C := C) B ⋙
  PresheafOfModules.sheafification.{u} (R := 𝓡(J, B)) (Functor.whiskerRight
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
    (forget₂ CommRingCat.{u} RingCat.{u}))
private theorem constant_realization_homology (J : GrothendieckTopology C) (B : Type u) [CommRing B]
    (T : CochainComplex (ModuleCat.{u} B) ℤ) (i : ℤ) :
    Nonempty ((((cB(J, B)).mapHomologicalComplex (.up ℤ)).obj T).homology i ≅
      (cB(J, B)).obj (T.homology i)) := by
  let := constant_preservesFiniteLimits (C := C) B
  let := constant_preservesFiniteColimits (C := C) B
  have : PreservesFiniteLimits (cB(J, B)) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (cB(J, B)) := comp_preservesFiniteColimits _ _
  exact ⟨(T.sc i).mapHomologyIso (cB(J, B))⟩

private theorem restriction_homology
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (B : Type u) [CommRing B]
    (G : CochainComplex (SheafOfModules.{u} (𝓡(J.toGrothendieck, B))) ℤ)
    (U : C) (i : ℤ) :
    Nonempty
      ((((overFunctor.{u} (𝓡(J.toGrothendieck, B)) U).mapHomologicalComplex
        (.up ℤ)).obj G).homology i ≅
        (overFunctor.{u} (𝓡(J.toGrothendieck, B)) U).obj (G.homology i)) := by
  have hres := localizedModule_adjunction_exact J
    ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)) U
  have := hres.1
  have := hres.2.1
  exact ⟨(G.sc i).mapHomologyIso (overFunctor.{u} (𝓡(J.toGrothendieck, B)) U)⟩

end ConstantRealization

set_option synthInstance.maxSize 2048 in
private theorem finite_tensor_terms (B : Type u) [CommRing B]
    (E F : CochainComplex (ModuleCat.{u} B) ℤ)
    (bE bF : ℤ)
    (hEb : ∀ j : ℤ, bE < j → IsZero (E.X j))
    (hFb : ∀ j : ℤ, bF < j → IsZero (F.X j))
    (hE : ∀ j : ℤ, Module.Finite B (E.X j))
    (hF : ∀ j : ℤ, Module.Finite B (F.X j))
    (i : ℤ) :
    Module.Finite B ((CochainComplex.mapBifunctor E F
      (curriedTensor (ModuleCat B))).X i) := by
  classical
  let T := CochainComplex.mapBifunctor E F (curriedTensor (ModuleCat B))
  let I := {p : ℤ // p ∈ Finset.Icc (i - bF) bE}
  let G : I → ModuleCat B := fun p ↦ E.X p.val ⊗ F.X (i - p.val)
  let π : (∐ G) ⟶ T.X i := Sigma.desc (fun p ↦
    HomologicalComplex.ιMapBifunctor E F (curriedTensor _) (.up ℤ)
      p.val (i - p.val) i (by simp))
  have hπ : Epi π := by
    constructor
    intro Y g h hgh
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpq' : p + q = i := hpq
    by_cases hp : p ∈ Finset.Icc (i - bF) bE
    · have he := congrArg ((Sigma.ι G ⟨p, hp⟩) ≫ ·) hgh
      have hq : q = i - p := by omega
      subst q
      simpa only [π, ← Category.assoc, Sigma.ι_comp_desc] using he
    · have hz : IsZero ((E.X p ⊗ F.X q) : ModuleCat B) := by
        by_cases hpe : bE < p
        · exact Functor.map_isZero (tensorRight (F.X q)) (hEb p hpe)
        · have hq : bF < q := by simp only [Finset.mem_Icc] at hp; omega
          exact Functor.map_isZero (tensorLeft (E.X p)) (hFb q hq)
      exact hz.eq_of_src _ _
  have hG (p : I) : Module.Finite B (G p) := by
    have := hE p.val
    have := hF (i - p.val)
    change Module.Finite B (E.X p.val ⊗[B] F.X (i - p.val))
    infer_instance
  have : ∀ p : I, Module.Finite B (G p) := hG
  let e : ModuleCat.of B (∀ p : I, G p) ≅ ∐ G :=
    (ModuleCat.biproductIsoPi G).symm ≪≫ biproduct.isoCoproduct G
  have : Module.Finite B ((∐ G) : ModuleCat B) := Module.Finite.of_surjective e.hom.hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  exact Module.Finite.of_surjective π.hom ((ModuleCat.epi_iff_surjective _).1 hπ)

private theorem locallyConstantFiniteType_of_iso
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (B : Type u) [CommRing B]
    {F G : SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B)))}
    (e : F ≅ G) (hG : IsLocallyConstantFiniteType J B G) :
    IsLocallyConstantFiniteType J B F := by
  intro V
  obtain ⟨S, hS, h⟩ := hG V
  refine ⟨S, hS, ?_⟩
  intro U f hf
  obtain ⟨M, hM, ⟨eM⟩⟩ := h U f hf
  exact ⟨M, hM, ⟨(overFunctor _ U).mapIso e ≪≫ eM⟩⟩

set_option synthInstance.maxSize 2048 in
/-- Over a Noetherian coefficient ring, tensoring bounded-above derived objects with
locally constant finite type cohomology again has locally constant finite type cohomology.
`P` and `Q` are arbitrary K-flat representatives of the derived objects; the conclusion
computes derived tensor by their total tensor, exactly as in the node's convention.

Source: Stacks Project, Cohomology on Sites, Tag 094H
(auxiliary; not a blueprint node).

Proof:
1. Transport homology bounds and local constancy along the representative isomorphisms.
2. For the cutoffs i-bL and i-bK, use local finite-free truncation models and intersect
   their covering sieves. Apply the local tensor-model comparison on each covering arrow.
3. In total degree j, only indices j-bF <= p <= bE contribute. The coproduct over this
   finite interval surjects onto the total term, so every total term is a finite module.
4. Cycles are submodules of finite modules over a Noetherian ring, hence finite; their
   homology quotient is finite as well.
5. Constant module presheaves preserve finite limits and colimits by evaluation. Compose
   with exact module sheafification and apply the short-complex homology comparison.
6. The comparison and the finite module H^i(T) give the required trivialization on each
   arrow of the intersection cover, exactly as in the definition of local constancy.
-/
theorem locallyConstantFiniteType_derivedTensor
    {C : Type u} [Category.{u} C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B))))]
    (K L : DerivedCategory (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))))
    (hK : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) i).obj K))
    (hL : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) i).obj L))
    (hKlc : ∀ i : ℤ, IsLocallyConstantFiniteType J.toGrothendieck B
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) i).obj K))
    (hLlc : ∀ i : ℤ, IsLocallyConstantFiniteType J.toGrothendieck B
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) i).obj L))
    (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))) ℤ)
    (hP : CochainComplex.IsKFlatTensor P) (hQ : CochainComplex.IsKFlatTensor Q)
    (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ L) :
    ∀ i : ℤ, IsLocallyConstantFiniteType J.toGrothendieck B
      ((CochainComplex.mapBifunctor P Q
        (@CategoryTheory.MonoidalCategory.curriedTensor _ _
          (SheafOfModules.monoidalCategory
            ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj
              (CommRingCat.of B))))).homology i) := by
  classical
  let A := SheafOfModules.{u} ((sheafCompose J.toGrothendieck
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)))
  have ePH (j : ℤ) : P.homology j ≅ (DerivedCategory.homologyFunctor A j).obj K :=
    ((DerivedCategory.homologyFunctorFactors A j).app P).symm ≪≫
      (DerivedCategory.homologyFunctor A j).mapIso eP
  have eQH (j : ℤ) : Q.homology j ≅ (DerivedCategory.homologyFunctor A j).obj L :=
    ((DerivedCategory.homologyFunctorFactors A j).app Q).symm ≪≫
      (DerivedCategory.homologyFunctor A j).mapIso eQ
  obtain ⟨bP, hbP⟩ := hK
  obtain ⟨bQ, hbQ⟩ := hL
  have hPb (j : ℤ) (hj : bP < j) : IsZero (P.homology j) :=
    (hbP j hj).of_iso (ePH j)
  have hQb (j : ℤ) (hj : bQ < j) : IsZero (Q.homology j) :=
    (hbQ j hj).of_iso (eQH j)
  have hPlc (j : ℤ) : IsLocallyConstantFiniteType J.toGrothendieck B (P.homology j) :=
    locallyConstantFiniteType_of_iso J.toGrothendieck B (ePH j) (hKlc j)
  have hQlc (j : ℤ) : IsLocallyConstantFiniteType J.toGrothendieck B (Q.homology j) :=
    locallyConstantFiniteType_of_iso J.toGrothendieck B (eQH j) (hLlc j)
  intro i V
  obtain ⟨S, hS, hSE⟩ := exists_site_finiteFree_truncation_models J B P
    ⟨bP, hPb⟩ hPlc (i - bQ) V
  obtain ⟨R, hR, hRF⟩ := exists_site_finiteFree_truncation_models J B Q
    ⟨bQ, hQb⟩ hQlc (i - bP) V
  refine ⟨S ⊓ R, J.toGrothendieck.intersection_covering hS hR, ?_⟩
  intro U f hf
  obtain ⟨E, bE, hEb, hE, eE⟩ := hSE U f hf.1
  obtain ⟨F, bF, hFb, hF, eF⟩ := hRF U f hf.2
  have eT := site_tensor_local_model_comparison J.toGrothendieck B P Q hP hQ
    bP bQ hPb hQb i U E F ⟨bE, hEb⟩ ⟨bF, hFb⟩ hE hF eE eF
  let T := CochainComplex.mapBifunctor E F (MonoidalCategory.curriedTensor (ModuleCat B))
  have hT (j : ℤ) : Module.Finite B (T.X j) :=
    finite_tensor_terms B E F bE bF hEb hFb (fun p ↦ (hE p).2) (fun q ↦ (hF q).2) j
  let c := strictPerfectConstantPresheaf (C := C) B ⋙
    PresheafOfModules.sheafification.{u} (R := ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B))))
      (Functor.whiskerRight
        (toSheafify J.toGrothendieck ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
        (forget₂ CommRingCat.{u} RingCat.{u}))
  obtain ⟨eH⟩ := constant_realization_homology J.toGrothendieck B T i
  obtain ⟨eR⟩ := restriction_homology J B
    (CochainComplex.mapBifunctor P Q (@MonoidalCategory.curriedTensor _ _
      (monoidalCategory ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj
        (CommRingCat.of B))))) U i
  obtain ⟨eRC⟩ := restriction_homology J B
    ((c.mapHomologicalComplex (.up ℤ)).obj T) U i
  exact ⟨T.homology i, finite_module_homology B T hT i,
    ⟨eR.symm ≪≫ eT.some ≪≫ eRC ≪≫ (overFunctor _ U).mapIso eH⟩⟩

end SheafOfModules
