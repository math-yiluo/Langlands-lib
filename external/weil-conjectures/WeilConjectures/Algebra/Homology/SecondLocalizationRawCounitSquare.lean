/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.SecondLocalizationMap
/-! # Raw cohomological counit square for second localization
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-second-localization-raw-counit-square). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Homology preserves adjoint transposes for exact scalar extension.
This is the short-complex homology-data argument of the private helper in
`FlatIteratedScalarExtensionHomologySquare`, using Stacks Tags 00HD and 05G3. -/
private theorem adjoint_homology
    (E D : Type u) [CommRing E] [CommRing D] (k : E →+* D) (hk : k.Flat)
    (Q : CochainComplex (ModuleCat.{u} E) ℤ)
    (T : CochainComplex (ModuleCat.{u} D) ℤ)
    (epsilon : ((ModuleCat.extendScalars k).mapHomologicalComplex (.up ℤ)).obj Q ⟶ T)
    (φ : Q ⟶ ((ModuleCat.restrictScalars k).mapHomologicalComplex (.up ℤ)).obj T)
    (htrans : ∀ j, φ.f j = (ModuleCat.extendRestrictScalarsAdj k).homEquiv _ _ (epsilon.f j))
    (i : ℤ) :
    let F := ModuleCat.extendScalars k
    let G := ModuleCat.restrictScalars k
    letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hk
    (ModuleCat.extendRestrictScalarsAdj k).homEquiv _ _
        (((Q.sc i).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap epsilon i) =
      HomologicalComplex.homologyMap φ i ≫ ((T.sc i).mapHomologyIso G).hom := by
  let F := ModuleCat.extendScalars k
  let G := ModuleCat.restrictScalars k
  let adj := ModuleCat.extendRestrictScalarsAdj k
  have : CategoryTheory.Limits.PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hk
  let S := Q.sc i
  let U := T.sc i
  let ψ : S.map F ⟶ U := (HomologicalComplex.shortComplexFunctor _ _ i).map epsilon
  let τ : S ⟶ U.map G := (HomologicalComplex.shortComplexFunctor _ _ i).map φ
  let h := S.homologyData.left
  let k := U.homologyData.left
  let γ : ShortComplex.LeftHomologyMapData ψ (h.map F) k := default
  let δ : ShortComplex.LeftHomologyMapData τ h (k.map G) :=
    { φK := (adj.homEquiv _ _) γ.φK
      φH := (adj.homEquiv _ _) γ.φH
      commi := by
        change (adj.homEquiv _ _) γ.φK ≫ G.map k.i = h.i ≫ τ.τ₂
        rw [← adj.homEquiv_naturality_right]
        change _ = h.i ≫ φ.f i
        rw [htrans i]
        change _ = h.i ≫ (adj.homEquiv S.X₂ U.X₂) ψ.τ₂
        erw [← adj.homEquiv_naturality_left]
        exact congrArg (adj.homEquiv _ _) γ.commi
      commf' := by
        rw [ShortComplex.LeftHomologyData.map_f']
        change h.f' ≫ (adj.homEquiv _ _) γ.φK = τ.τ₁ ≫ G.map k.f'
        rw [← adj.homEquiv_naturality_left]
        change _ = φ.f ((ComplexShape.up ℤ).prev i) ≫ G.map k.f'
        rw [htrans, ← adj.homEquiv_naturality_right]
        change (adj.homEquiv S.X₁ k.K) (F.map h.f' ≫ γ.φK) =
          (adj.homEquiv S.X₁ k.K) (ψ.τ₁ ≫ k.f')
        apply congrArg (adj.homEquiv S.X₁ k.K)
        simpa only [ShortComplex.LeftHomologyData.map_f'] using γ.commf'
      commπ := by
        change h.π ≫ (adj.homEquiv _ _) γ.φH =
          (adj.homEquiv _ _) γ.φK ≫ G.map k.π
        rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
        exact congrArg (adj.homEquiv _ _) γ.commπ }
  have heq : ((adj.homEquiv _ _).symm
      (HomologicalComplex.homologyMap φ i ≫ (U.mapHomologyIso G).hom)) =
      F.map h.homologyIso.hom ≫ γ.φH ≫ k.homologyIso.inv := by
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_left,
      adj.homEquiv_naturality_right]
    change ShortComplex.homologyMap τ ≫ (U.mapHomologyIso G).hom = _
    rw [δ.homologyMap_eq, k.mapHomologyIso_eq G]
    simp [δ, Category.assoc]
    rfl
  change (adj.homEquiv _ _) ((S.mapHomologyIso F).inv ≫ ShortComplex.homologyMap ψ) =
    ShortComplex.homologyMap τ ≫ (U.mapHomologyIso G).hom
  apply (adj.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  change _ = (adj.homEquiv _ _).symm
    (HomologicalComplex.homologyMap φ i ≫ (U.mapHomologyIso G).hom)
  rw [heq]
  change ((S.mapHomologyIso F).inv ≫ ShortComplex.homologyMap ψ) = _
  rw [h.mapHomologyIso_eq F, γ.homologyMap_eq]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc,
    Iso.inv_hom_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- At an ordinary complex, the lifted flat homology comparison is the ordinary
exact-functor homology comparison, after the two localization factorizations. -/
private theorem flat_homology_factor
    (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [HasDerivedCategory.{w} (ModuleCat.{u} C)]
    (hf : (algebraMap B C).Flat) (i : ℤ)
    (P : CochainComplex (ModuleCat.{u} B) ℤ) :
    let E := ModuleCat.extendScalars (algebraMap B C)
    letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
    let EP := (E.mapHomologicalComplex (.up ℤ)).obj P
    let qB := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)
    let qC := HomotopyCategory.quotient (ModuleCat.{u} C) (.up ℤ)
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} C) i
    (flatDerivedHomologyIso B C hf i).inv.app (DerivedCategory.Qh.obj (qB.obj P)) ≫
      H.map (E.mapDerivedCategoryFactorsh.hom.app (qB.obj P)) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} C) i).hom.app (qC.obj EP) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} C) (.up ℤ) i).hom.app EP =
    E.map ((DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.app
      (qB.obj P) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app P) ≫
      ((P.sc i).mapHomologyIso E).inv := by
  dsimp only
  simp only [Functor.comp_obj]
  rw [Functor.mapDerivedCategoryFactorsh_hom_app,
    DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj,
    DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj]
  simp only [Functor.mapHomotopyCategory_obj, HomotopyCategory.quotient_obj_as,
    Functor.comp_obj, Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rw [← reassoc_of% (flatDerivedHomologyIso B C hf i).inv.naturality
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} B)).hom.app P)]
  congr 1
  dsimp [flatDerivedHomologyIso]
  rw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Iso.refl_hom, Iso.refl_inv,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc]
  simp only [NatTrans.id_app, NatIso.ofComponents_inv_app,
    CategoryTheory.Functor.map_id, Category.id_comp,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Category.id_comp, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem extendScalars_eq_one_tmul
    {S T : Type u} [CommRing S] [CommRing T]
    {f g : S →+* T} (h : f = g) (M : ModuleCat.{u} S) (x : M) :
    (eqToIso (congrArg (fun k : S →+* T ↦ ModuleCat.extendScalars.{u} k) h)).hom.app M
        ((1 : T) ⊗ₜ[S,f] x) = (1 : T) ⊗ₜ[S,g] x := by
  subst h
  rfl

variable (R A B Bp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Bp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra B Bp] [Algebra R Bp]
  [tRB : IsScalarTower R B Bp]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[R] Bp) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
include tRB in
/-- Flat coefficient extension commutes with the raw derived counits on homology.
Source: Stacks Project, Tag 06Y6, lemma-derived-base-change; Tag 0DJ8.
(blueprint: lem-pc-second-localization-raw-counit-square).

Proof: install K.universal and apply leftDerived_fac to the lift defining
secondLocalizationDerivedMap. Its composite with K.counit is L.counit extended
along B to Bp, followed by the scalar-extension associator. Evaluate this
identity at the homotopy class of the restriction of Q to R and apply homology.
Naturality of flatDerivedHomologyIso moves homology of the extended L.counit
to extension of homology of L.counit. At an ordinary complex the defining
localization factorization of that isomorphism is precisely mapHomologyIso
for exact scalar extension, composed with the homotopy/derived homology
factorization isomorphisms. Transpose along extension/restriction of scalars.
The unit on complexes is termwise x mapped to 1 tensor x. Naturality of exact
restriction homology identifies this transpose with homology of the termwise
unit followed by the scalar-extension associator. That map sends b tensor x
to image(b) tensor x; tensor induction and hχ identify it with χ. Cancelling
the exact-restriction homology isomorphism gives the displayed identity.
This is only the raw counit calculation: it uses neither ordinaryIso,
cohomologyIso nor comparison of either model. Zero complexes and zero rings
are covered by tensor induction and the same categorical identities. -/
theorem secondLocalization_raw_counit_square
    (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D) :
    let T := ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
      (.up ℤ)).obj Q
    let P := ((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex
      (.up ℤ)).obj T
    let Pp := ((ModuleCat.extendScalars (algebraMap R Bp)).mapHomologicalComplex
      (.up ℤ)).obj T
    let U := ModuleCat.restrictScalars (algebraMap B Bp)
    let qR := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
    let qB := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)
    let qBp := HomotopyCategory.quotient (ModuleCat.{u} Bp) (.up ℤ)
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
    let Hp := DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i
    let X := DerivedCategory.Qh.obj (qR.obj T)
    let c := H.map (L.counit.app (qR.obj T)) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.app (qB.obj P) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app P
    let cp := Hp.map (K.counit.app (qR.obj T)) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} Bp) i).hom.app (qBp.obj Pp) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} Bp) (.up ℤ) i).hom.app Pp
    letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
    let d := (flatDerivedHomologyIso B Bp hflat i).inv.app (L.derived.obj X) ≫
      Hp.map ((secondLocalizationDerivedMap R A B Bp D hflat Q L K).app X)
    ∀ (χ : P ⟶ (U.mapHomologicalComplex (.up ℤ)).obj Pp)
      (_hχ : ∀ (j : ℤ) (b : B) (x : Q.X j),
        χ.f j (b ⊗ₜ[R,algebraMap R B] (show T.X j from x)) =
          algebraMap B Bp b ⊗ₜ[R,algebraMap R Bp] (show T.X j from x)),
      c ≫ HomologicalComplex.homologyMap χ i =
        (ModuleCat.extendRestrictScalarsAdj (algebraMap B Bp)).homEquiv _ _ (d ≫ cp) ≫
          ((Pp.sc i).mapHomologyIso U).inv := by
  let T := ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
    (.up ℤ)).obj Q
  let P := ((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex
    (.up ℤ)).obj T
  let Pp := ((ModuleCat.extendScalars (algebraMap R Bp)).mapHomologicalComplex
    (.up ℤ)).obj T
  let U := ModuleCat.restrictScalars (algebraMap B Bp)
  let qR := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  let qB := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)
  let qBp := HomotopyCategory.quotient (ModuleCat.{u} Bp) (.up ℤ)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let Hp := DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i
  let X := DerivedCategory.Qh.obj (qR.obj T)
  let c := H.map (L.counit.app (qR.obj T)) ≫
    (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.app (qB.obj P) ≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app P
  let cp := Hp.map (K.counit.app (qR.obj T)) ≫
    (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} Bp) i).hom.app (qBp.obj Pp) ≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} Bp) (.up ℤ) i).hom.app Pp
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  let d := (flatDerivedHomologyIso B Bp hflat i).inv.app (L.derived.obj X) ≫
    Hp.map ((secondLocalizationDerivedMap R A B Bp D hflat Q L K).app X)
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap B Bp)
  let E := ModuleCat.extendScalars (algebraMap B Bp)
  let EC := E.mapHomologicalComplex (.up ℤ)
  let e := (ModuleCat.extendScalarsComp (algebraMap R B) (algebraMap B Bp)).symm ≪≫
    eqToIso (congrArg (fun f : R →+* Bp ↦ ModuleCat.extendScalars.{u} f)
      (IsScalarTower.algebraMap_eq R B Bp).symm)
  let ε : EC.obj P ⟶ Pp := (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app T
  change ∀ (χ : P ⟶ (U.mapHomologicalComplex (.up ℤ)).obj Pp), _
  intro χ hχ
  let := K.universal
  have hfac : (secondLocalizationDerivedMap R A B Bp D hflat Q L K).app X ≫
      K.counit.app (qR.obj T) =
      E.mapDerivedCategory.map (L.counit.app (qR.obj T)) ≫
        E.mapDerivedCategoryFactorsh.hom.app (qB.obj P) ≫
          DerivedCategory.Qh.map (qBp.map ε) := by
    dsimp [secondLocalizationDerivedMap]
    rw [Functor.leftDerived_fac_app]
    rfl
  have hn : Hp.map (DerivedCategory.Qh.map (qBp.map ε)) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} Bp) i).hom.app (qBp.obj Pp) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} Bp) (.up ℤ) i).hom.app Pp =
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} Bp) i).hom.app
        (qBp.obj (EC.obj P)) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} Bp) (.up ℤ) i).hom.app
        (EC.obj P) ≫ HomologicalComplex.homologyMap ε i := by
    let γ := (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} Bp) i).hom
    let δ := (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} Bp) (.up ℤ) i).hom
    rw [reassoc_of% γ.naturality (qBp.map ε)]
    erw [δ.naturality ε]
    rfl
  have hd : d ≫ cp = E.map c ≫ ((P.sc i).mapHomologyIso E).inv ≫
      HomologicalComplex.homologyMap ε i := by
    dsimp only [d, cp]
    simp only [Category.assoc]
    rw [← Hp.map_comp_assoc, hfac]
    simp only [Functor.map_comp, Category.assoc]
    rw [← reassoc_of% (flatDerivedHomologyIso B Bp hflat i).inv.naturality
      (L.counit.app (qR.obj T))]
    rw [hn]
    erw [reassoc_of% flat_homology_factor B Bp hflat i P]
    simp only [c, E, Functor.map_comp, Category.assoc]
    rfl
  have htrans : ∀ j, χ.f j = adj.homEquiv _ _ (ε.f j) := by
    intro j
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    erw [hχ j 1 x, map_one]
    change (1 : Bp) ⊗ₜ[R,algebraMap R Bp] (show T.X j from x) =
      (eqToIso (congrArg (fun f : R →+* Bp ↦ ModuleCat.extendScalars.{u} f)
        (IsScalarTower.algebraMap_eq R B Bp).symm)).hom.app (T.X j)
        ((ModuleCat.extendScalarsComp (algebraMap R B) (algebraMap B Bp)).inv.app (T.X j)
          ((1 : Bp) ⊗ₜ[B,algebraMap B Bp]
            ((1 : B) ⊗ₜ[R,algebraMap R B] (show T.X j from x))))
    rw [← ModuleCat.extendScalarsComp_hom_app_one_tmul
      (algebraMap R B) (algebraMap B Bp) (T.X j) x]
    have hi :
        (ModuleCat.extendScalarsComp (algebraMap R B) (algebraMap B Bp)).inv.app (T.X j)
          ((ModuleCat.extendScalarsComp (algebraMap R B) (algebraMap B Bp)).hom.app
            (T.X j) ((1 : Bp) ⊗ₜ[R,(algebraMap B Bp).comp (algebraMap R B)] x)) =
        ((1 : Bp) ⊗ₜ[R,(algebraMap B Bp).comp (algebraMap R B)] x) :=
      ((ModuleCat.extendScalarsComp (algebraMap R B) (algebraMap B Bp)).app
        (T.X j)).toLinearEquiv.symm_apply_apply _
    exact (extendScalars_eq_one_tmul (IsScalarTower.algebraMap_eq R B Bp).symm
      (T.X j) x).symm.trans (congrArg
        (fun y ↦ (eqToIso (congrArg
          (fun f : R →+* Bp ↦ ModuleCat.extendScalars.{u} f)
          (IsScalarTower.algebraMap_eq R B Bp).symm)).hom.app (T.X j) y) hi.symm)
  have ha := adjoint_homology B Bp (algebraMap B Bp) hflat P Pp ε χ htrans i
  change c ≫ HomologicalComplex.homologyMap χ i =
    adj.homEquiv _ _ (d ≫ cp) ≫ ((Pp.sc i).mapHomologyIso U).inv
  rw [hd, adj.homEquiv_naturality_left]
  erw [ha]
  simp only [U, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end RingTensorCohomology
