/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.TruncationCouple
import WeilConjectures.CategoryTheory.TruncationTriangle

/-! # Naturality of the raw truncation maps

Source: Stacks Project, Remark 08J5 and Tags 015J, 05TC.
(blueprint: lem-pc-raw-truncation-couple-naturality).
-/

@[expose] public section

universe v uA uB wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TruncationCouple

variable {A : Type uA} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
  [HasDerivedCategory.{wB} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]

/-- The degree-n canonical truncation inclusion, after RF and the inverse bridge.
Source: Stacks Tag 05TC (2) (blueprint: lem-pc-raw-truncation-couple-naturality). -/
noncomputable def abutmentMap (K : CochainComplex.Plus A) (n : ℤ) :
    D F K 0 n ⟶ (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).obj
      (DerivedCategory.Q.obj K.obj) :=
  eqToHom (by unfold D; rw [zero_add]) ≫
    (bridgeIso F (truncation K n) n).inv ≫
    (DerivedCategory.homologyFunctor B n).map
      (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE n)))

/-- The first shift comparison, without comparison to ordinary right derived functors.
Source: Stacks Tags 015J, 05TC (blueprint: lem-pc-raw-truncation-couple-naturality). -/
noncomputable def singleIso (K : CochainComplex.Plus A) (p q : ℤ) :
    E F K p q ≅
      (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor B p).obj (K.obj.homology q) :=
  (bridgeIso F (cohomologyComplex K q) (p + q)).symm ≪≫
    (DerivedCategory.homologyFunctor B (p + q)).mapIso
      (F.rightDerivedFunctor.mapIso
        (((DerivedCategory.singleFunctors A).shiftIso (-q) q 0
          (by omega)).app (K.obj.homology q)).symm) ≪≫
    (DerivedCategory.homologyFunctor B (p + q)).mapIso
      ((F.rightDerivedFunctor.commShiftIso (-q)).app
        ((DerivedCategory.singleFunctor A 0).obj (K.obj.homology q))) ≪≫
    ((DerivedCategory.homologyFunctor B 0).shiftIso (-q) (p + q) p
      (by omega)).app
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor A 0).obj (K.obj.homology q)))

/-- Transport derived cohomology of a map to cohomology of its representing complexes.
Source: derived localization, Stacks Tag 05S7
(blueprint: lem-pc-raw-truncation-couple-naturality). -/
noncomputable def homologyMap {K N : CochainComplex.Plus A}
    (c : DerivedCategory.Q.obj K.obj ⟶ DerivedCategory.Q.obj N.obj) (q : ℤ) :
    K.obj.homology q ⟶ N.obj.homology q :=
  ((DerivedCategory.homologyFunctorFactors A q).app K.obj).inv ≫
    (DerivedCategory.homologyFunctor A q).map c ≫
    ((DerivedCategory.homologyFunctorFactors A q).app N.obj).hom

private lemma lift_map_eq
    {C D₀ E₀ : Type*} [Category C] [Category D₀] [Category E₀]
    (W : MorphismProperty C) (L : C ⥤ D₀) [L.IsLocalization W]
    (G : C ⥤ E₀) (hG : W.IsInvertedBy G) (G' : D₀ ⥤ E₀)
    (e : L ⋙ G' ≅ G) (K N : C) (c : L.obj K ⟶ L.obj N) :
    (Localization.fac G hG L).inv.app K ≫
        (Localization.lift G hG L).map c ≫ (Localization.fac G hG L).hom.app N =
      e.inv.app K ≫ G'.map c ≫ e.hom.app N := by
  let : Localization.Lifting L W G G' := ⟨e⟩
  let a := Localization.liftNatIso L W G G
    (Localization.lift G hG L) G' (Iso.refl G)
  have h := congrArg (fun t ↦ (Localization.fac G hG L).inv.app K ≫
    t ≫ e.hom.app N) (a.hom.naturality c)
  dsimp [a, Localization.liftNatIso, Localization.liftNatTrans_app,
    Localization.fac] at h
  simp only [Localization.liftNatTrans_app, NatTrans.id_app] at h
  change (Localization.fac G hG L).inv.app K ≫
    ((Localization.lift G hG L).map c ≫
      ((Localization.fac G hG L).hom.app N ≫ 𝟙 _ ≫ e.inv.app N)) ≫ e.hom.app N =
    (Localization.fac G hG L).inv.app K ≫
      (((Localization.fac G hG L).hom.app K ≫ 𝟙 _ ≫ e.inv.app K) ≫
        G'.map c) ≫ e.hom.app N at h
  simpa [Category.assoc] using h

private lemma lift_naturality
    {C D₀ E₀ : Type*} [Category C] [Category D₀] [Category E₀]
    (W : MorphismProperty C) (L : C ⥤ D₀) [L.IsLocalization W]
    {G H : C ⥤ E₀} (hG : W.IsInvertedBy G) (hH : W.IsInvertedBy H)
    (τ : G ⟶ H) (K N : C) (c : L.obj K ⟶ L.obj N) :
    τ.app K ≫ ((Localization.fac H hH L).inv.app K ≫
      (Localization.lift H hH L).map c ≫ (Localization.fac H hH L).hom.app N) =
    ((Localization.fac G hG L).inv.app K ≫
      (Localization.lift G hG L).map c ≫ (Localization.fac G hG L).hom.app N) ≫
        τ.app N := by
  let τD := Localization.liftNatTrans L W G H
    (Localization.lift G hG L) (Localization.lift H hH L) τ
  have h := congrArg (fun t ↦ (Localization.fac G hG L).inv.app K ≫
    t ≫ (Localization.fac H hH L).hom.app N) (τD.naturality c)
  simpa [τD, Localization.liftNatTrans_app, Localization.fac, Category.assoc] using h.symm

omit [IsGrothendieckAbelian.{v} A] in
private lemma trunc_inverts (q : ℤ) :
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).IsInvertedBy
      ((ComplexShape.embeddingUpIntLE q).truncLEFunctor A ⋙ DerivedCategory.Q) := by
  intro K N s hs
  have : QuasiIso s := hs
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso A _).2
  exact (CochainComplex.quasiIso_truncLEMap_iff s q).2 (fun _ _ ↦ inferInstance)

private noncomputable def truncMap {K N : CochainComplex.Plus A}
    (c : DerivedCategory.Q.obj K.obj ⟶ DerivedCategory.Q.obj N.obj) (q : ℤ) :
    DerivedCategory.Q.obj (truncation K q).obj ⟶
      DerivedCategory.Q.obj (truncation N q).obj :=
  (Localization.fac _ (trunc_inverts q) DerivedCategory.Q).inv.app K.obj ≫
    (Localization.lift _ (trunc_inverts q) DerivedCategory.Q).map c ≫
      (Localization.fac _ (trunc_inverts q) DerivedCategory.Q).hom.app N.obj

omit [IsGrothendieckAbelian.{v} A] in
private lemma single_map_eq {K N : CochainComplex.Plus A}
    (c : DerivedCategory.Q.obj K.obj ⟶ DerivedCategory.Q.obj N.obj) (q : ℤ)
    (hH : (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).IsInvertedBy
      ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙
        CochainComplex.singleFunctor A q) ⋙ DerivedCategory.Q)) :
    (Localization.fac _ hH DerivedCategory.Q).inv.app K.obj ≫
        (Localization.lift _ hH DerivedCategory.Q).map c ≫
          (Localization.fac _ hH DerivedCategory.Q).hom.app N.obj =
      (DerivedCategory.singleFunctor A q).map (homologyMap c q) := by
  let e : DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor A q ⋙
      DerivedCategory.singleFunctor A q) ≅
      ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙
        CochainComplex.singleFunctor A q) ⋙ DerivedCategory.Q) :=
    Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors A q)
      (DerivedCategory.singleFunctor A q)
  rw [lift_map_eq _ _ _ hH _ e]
  simp [e, homologyMap, Functor.map_comp]

open CategoryTheory.Pretriangulated in
private noncomputable def triangleMap {K N : CochainComplex.Plus A}
    (c : DerivedCategory.Q.obj K.obj ⟶ DerivedCategory.Q.obj N.obj) (q : ℤ) :
    triangle K q ⟶ triangle N q := by
  have squares :
      (triangle K q).mor₁ ≫ truncMap c q =
        truncMap c (q - 1) ≫ (triangle N q).mor₁ ∧
      (triangle K q).mor₂ ≫ (DerivedCategory.singleFunctor A q).map (homologyMap c q) =
        truncMap c q ≫ (triangle N q).mor₂ ∧
      (triangle K q).mor₃ ≫ (truncMap c (q - 1))⟦(1 : ℤ)⟧' =
        (DerivedCategory.singleFunctor A q).map (homologyMap c q) ≫
          (triangle N q).mor₃ := by
    obtain ⟨h₀, h₁, hH, h⟩ := (DerivedCategory.truncation_triangle A q).2.1
    have hj (L : CochainComplex.Plus A) :
        (projection L q).f q ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (L.obj.homology q)).hom =
            (L.obj.truncLEXIsoCycles q).hom ≫ L.obj.homologyπ q := by
      simp [projection, HomologicalComplex.mkHomToSingle_f]
    have hd (L : CochainComplex.Plus A) :
        triangle L q ∈ distTriang (DerivedCategory A) :=
      (Classical.choose_spec (existsUnique_boundary L q)).1
    obtain ⟨hi, hj, hk⟩ := h K.obj N.obj (transition K q) (projection K q)
      (transition N q) (projection N q) (transition_comp_ιTruncLE K q) (hj K)
      (transition_comp_ιTruncLE N q) (hj N) (triangle K q).mor₃ (triangle N q).mor₃
      (hd K) (hd N) c
    rw [single_map_eq c q hH] at hj hk
    exact ⟨hi, hj, hk⟩
  exact
    { hom₁ := truncMap c (q - 1)
      hom₂ := truncMap c q
      hom₃ := (DerivedCategory.singleFunctor A q).map (homologyMap c q)
      comm₁ := squares.1
      comm₂ := squares.2.1
      comm₃ := squares.2.2 }

omit [IsGrothendieckAbelian.{v} A] in
private lemma truncMap_comp_inclusion {K N : CochainComplex.Plus A}
    (c : DerivedCategory.Q.obj K.obj ⟶ DerivedCategory.Q.obj N.obj) (q : ℤ) :
    truncMap c q ≫ DerivedCategory.Q.map (N.obj.ιTruncLE q) =
      DerivedCategory.Q.map (K.obj.ιTruncLE q) ≫ c := by
  let τ := Functor.whiskerRight ((ComplexShape.embeddingUpIntLE q).ιTruncLENatTrans A)
    DerivedCategory.Q
  have h := lift_naturality (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    DerivedCategory.Q (trunc_inverts q)
    (Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso A _))
    τ K.obj N.obj c
  rw [lift_map_eq _ _ _ _ (𝟭 _) (Functor.rightUnitor DerivedCategory.Q)] at h
  simpa [τ, truncMap, truncation, CochainComplex.truncLE,
    CochainComplex.ιTruncLE] using h.symm

private noncomputable def bridgeMap (L M : CochainComplex.Plus A)
    (a : DerivedCategory.Q.obj L.obj ⟶ DerivedCategory.Q.obj M.obj) (r : ℤ) :
    F.rightDerivedCohomologyWithResolution L
        (CochainComplex.grothendieckKInjectiveResolutionChoice L.obj) r ⟶
      F.rightDerivedCohomologyWithResolution M
        (CochainComplex.grothendieckKInjectiveResolutionChoice M.obj) r :=
  (bridgeIso F L r).inv ≫
    (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B r).map a ≫
      (bridgeIso F M r).hom

omit [IsGrothendieckAbelian.{v} B] in
private lemma abutment_aux (L M : CochainComplex.Plus A)
    {X Y : DerivedCategory A} (a : DerivedCategory.Q.obj L.obj ⟶
      DerivedCategory.Q.obj M.obj) (iL : DerivedCategory.Q.obj L.obj ⟶ X)
    (iM : DerivedCategory.Q.obj M.obj ⟶ Y) (c : X ⟶ Y)
    (h : a ≫ iM = iL ≫ c) (r n : ℤ) (hr : r = n) :
    bridgeMap F L M a r ≫
        eqToHom (congrArg (fun t ↦ F.rightDerivedCohomologyWithResolution M
          (CochainComplex.grothendieckKInjectiveResolutionChoice M.obj) t) hr) ≫
        (bridgeIso F M n).inv ≫
        (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).map iM =
      eqToHom (congrArg (fun t ↦ F.rightDerivedCohomologyWithResolution L
          (CochainComplex.grothendieckKInjectiveResolutionChoice L.obj) t) hr) ≫
        (bridgeIso F L n).inv ≫
        (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).map iL ≫
        (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).map c := by
  subst r
  simp only [bridgeMap, eqToHom_refl, Category.id_comp, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, h]

omit [IsGrothendieckAbelian.{v} B] in
private lemma bridge_square (L M L' M' : CochainComplex.Plus A)
    (a : DerivedCategory.Q.obj L.obj ⟶ DerivedCategory.Q.obj M.obj)
    (b : DerivedCategory.Q.obj L'.obj ⟶ DerivedCategory.Q.obj M'.obj)
    (iL : DerivedCategory.Q.obj L.obj ⟶ DerivedCategory.Q.obj L'.obj)
    (iM : DerivedCategory.Q.obj M.obj ⟶ DerivedCategory.Q.obj M'.obj)
    (h : a ≫ iM = iL ≫ b) (r s : ℤ) (hrs : r = s) :
    bridgeMap F L M a r ≫ bridgeMap F M M' iM r ≫
        eqToHom (congrArg (fun t ↦ F.rightDerivedCohomologyWithResolution M'
          (CochainComplex.grothendieckKInjectiveResolutionChoice M'.obj) t) hrs) =
      bridgeMap F L L' iL r ≫
        eqToHom (congrArg (fun t ↦ F.rightDerivedCohomologyWithResolution L'
          (CochainComplex.grothendieckKInjectiveResolutionChoice L'.obj) t) hrs) ≫
        bridgeMap F L' M' b s := by
  subst s
  simp only [bridgeMap, eqToHom_refl, Category.comp_id, Category.id_comp,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, h]

omit [IsGrothendieckAbelian.{v} A] in
private lemma truncMap_transport {K N : CochainComplex.Plus A}
    (c : DerivedCategory.Q.obj K.obj ⟶ DerivedCategory.Q.obj N.obj)
    (q q' : ℤ) (h : q = q') :
    DerivedCategory.Q.map (eqToHom (congrArg (fun r ↦ K.obj.truncLE r) h)) ≫
        truncMap c q' =
      truncMap c q ≫
        DerivedCategory.Q.map (eqToHom (congrArg (fun r ↦ N.obj.truncLE r) h)) := by
  subst q'
  simp only [eqToHom_refl, Functor.map_id, Category.id_comp, Category.comp_id]

omit [IsGrothendieckAbelian.{v} A] in
private lemma alpha_square {K N : CochainComplex.Plus A}
    (c : DerivedCategory.Q.obj K.obj ⟶ DerivedCategory.Q.obj N.obj) (q : ℤ) :
    truncMap c q ≫ DerivedCategory.Q.map
        (eqToHom (congrArg (fun r ↦ N.obj.truncLE r)
          (by omega : q = (q + 1) - 1)) ≫ transition N (q + 1)) =
      DerivedCategory.Q.map
        (eqToHom (congrArg (fun r ↦ K.obj.truncLE r)
          (by omega : q = (q + 1) - 1)) ≫ transition K (q + 1)) ≫
        truncMap c (q + 1) := by
  have h := (triangleMap c (q + 1)).comm₁
  change DerivedCategory.Q.map (transition K (q + 1)) ≫ truncMap c (q + 1) =
    truncMap c ((q + 1) - 1) ≫ DerivedCategory.Q.map (transition N (q + 1)) at h
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, ← truncMap_transport c q ((q + 1) - 1) (by omega),
    Category.assoc, ← h]

omit [IsGrothendieckAbelian.{v} B] in
private lemma boundary_aux (L M L' M' : CochainComplex.Plus A)
    (a : DerivedCategory.Q.obj L.obj ⟶ DerivedCategory.Q.obj M.obj)
    (b : DerivedCategory.Q.obj L'.obj ⟶ DerivedCategory.Q.obj M'.obj) (n m s : ℤ)
    (δL : (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).obj
        (DerivedCategory.Q.obj L.obj) ⟶
      (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B m).obj
        (DerivedCategory.Q.obj L'.obj))
    (δM : (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).obj
        (DerivedCategory.Q.obj M.obj) ⟶
      (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B m).obj
        (DerivedCategory.Q.obj M'.obj))
    (h : (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).map a ≫ δM =
      δL ≫ (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B m).map b)
    (hms : m = s) :
    bridgeMap F L M a n ≫ (bridgeIso F M n).inv ≫ δM ≫ (bridgeIso F M' m).hom ≫
        eqToHom (congrArg (fun t ↦ F.rightDerivedCohomologyWithResolution M'
          (CochainComplex.grothendieckKInjectiveResolutionChoice M'.obj) t) hms) =
      (bridgeIso F L n).inv ≫ δL ≫ (bridgeIso F L' m).hom ≫
        eqToHom (congrArg (fun t ↦ F.rightDerivedCohomologyWithResolution L'
          (CochainComplex.grothendieckKInjectiveResolutionChoice L'.obj) t) hms) ≫
        bridgeMap F L' M' b s := by
  subst s
  simp only [bridgeMap, eqToHom_refl, Category.id_comp, Category.comp_id,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc _ _ (bridgeIso F M' m).hom, h, Category.assoc]

private noncomputable def dMap {K N : CochainComplex.Plus A}
    (c : DerivedCategory.Q.obj K.obj ⟶ DerivedCategory.Q.obj N.obj) (p q : ℤ) :
    D F K p q ⟶ D F N p q :=
  (bridgeIso F (truncation K q) (p + q)).inv ≫
    (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B (p + q)).map
      (truncMap c q) ≫ (bridgeIso F (truncation N q) (p + q)).hom

private noncomputable def eMap {K N : CochainComplex.Plus A}
    (c : DerivedCategory.Q.obj K.obj ⟶ DerivedCategory.Q.obj N.obj) (p q : ℤ) :
    E F K p q ⟶ E F N p q :=
  (bridgeIso F (cohomologyComplex K q) (p + q)).inv ≫
    (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B (p + q)).map
      ((DerivedCategory.singleFunctor A q).map (homologyMap c q)) ≫
        (bridgeIso F (cohomologyComplex N q) (p + q)).hom

omit [IsGrothendieckAbelian.{v} B] in
/-- Naturality of the raw maps, the canonical abutment inclusion and the first
shift comparison. This concerns two fixed complexes and a single derived morphism;
no exactness, lower bound, choice of representatives, or invertibility of abutment
maps is asserted.

Source: Stacks Project, Remark 08J5, with Tags 015J and 05TC; step 4 of
lem-pc-natural-bounded-below-truncation-couples.
(blueprint: lem-pc-raw-truncation-couple-naturality).

Proof:
1. Descend the functors tau<=q and H^q(-)[-q] along Q. On the two complexes,
conjugate the descended maps by Localization.fac. Apply the triangulated RF,
homology in degree p+q, and the bridge isomorphisms to define tD and tE.
2. The three squares of truncation_triangle give the alpha, projection and
boundary squares. For the boundary square use naturality of the connecting
morphism in the homology sequence of the mapped triangle. Bridge factors
cancel; the equality transports preserve total degrees, giving the three raw
squares below.
3. Descending the natural transformation tau<=n -> identity gives its square
for every derived morphism. Apply RF and H^n and cancel the bridge factors;
this is the abutment equation.
4. The single-functor shift comparison, RF commutation with shifts, and homology
shift comparison are natural isomorphisms. Their composite singleIso is therefore
natural. The homologyFunctorFactors comparison identifies the descended H^q map
with homologyMap; cancellation of the bridge yields the final equation.
The zero map and zero objects satisfy the same equations. No representative map
of complexes is needed, so arbitrary roofs in D(A) are covered. -/
theorem raw_naturality (K N : CochainComplex.Plus A)
    (c : DerivedCategory.Q.obj K.obj ⟶ DerivedCategory.Q.obj N.obj) :
    ∃ (tD : ∀ p q : ℤ, D F K p q ⟶ D F N p q)
      (tE : ∀ p q : ℤ, E F K p q ⟶ E F N p q),
      (∀ p q : ℤ, tD p q ≫ alpha F N p q =
        alpha F K p q ≫ tD (p - 1) (q + 1)) ∧
      (∀ p q : ℤ, tE p q ≫ f F N p q = f F K p q ≫ tD (p + 2) (q - 1)) ∧
      (∀ p q : ℤ, tD p q ≫ g F N p q = g F K p q ≫ tE p q) ∧
      (∀ n : ℤ, tD 0 n ≫ abutmentMap F N n = abutmentMap F K n ≫
        (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).map c) ∧
      (∀ p q : ℤ, tE p q ≫ (singleIso F N p q).hom = (singleIso F K p q).hom ≫
        (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor B p).map (homologyMap c q)) := by
  refine ⟨dMap F c, eMap F c, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q
    simpa only [dMap, alpha, bridgeMap, D, Functor.comp_map, Category.assoc] using
      bridge_square F (truncation K q) (truncation N q)
        (truncation K (q + 1)) (truncation N (q + 1)) (truncMap c q)
        (truncMap c (q + 1))
        (DerivedCategory.Q.map (eqToHom (congrArg (fun r ↦ K.obj.truncLE r)
          (by omega : q = (q + 1) - 1)) ≫ transition K (q + 1)))
        (DerivedCategory.Q.map (eqToHom (congrArg (fun r ↦ N.obj.truncLE r)
          (by omega : q = (q + 1) - 1)) ≫ transition N (q + 1)))
        (alpha_square c q) (p + q) ((p - 1) + (q + 1)) (by omega)
  · intro p q
    let τ := F.rightDerivedFunctor.mapTriangle.map (triangleMap c q)
    have h := (DerivedCategory.homologyFunctor B 0).homologySequenceδ_naturality
      τ (p + q) (p + q + 1) rfl
    change
      (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B (p + q)).map
          ((DerivedCategory.singleFunctor A q).map (homologyMap c q)) ≫
        DerivedCategory.HomologySequence.δ (derivedTriangle F N q) (p + q) (p + q + 1) =
      DerivedCategory.HomologySequence.δ (derivedTriangle F K q) (p + q) (p + q + 1) ≫
        (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B (p + q + 1)).map
          (truncMap c (q - 1)) at h
    simpa only [eMap, dMap, bridgeMap, f, D, E, Functor.comp_map, Category.assoc] using
      boundary_aux F (cohomologyComplex K q) (cohomologyComplex N q)
        (truncation K (q - 1)) (truncation N (q - 1))
        ((DerivedCategory.singleFunctor A q).map (homologyMap c q))
        (truncMap c (q - 1)) (p + q) (p + q + 1) ((p + 2) + (q - 1))
        (DerivedCategory.HomologySequence.δ (derivedTriangle F K q) (p + q) (p + q + 1))
        (DerivedCategory.HomologySequence.δ (derivedTriangle F N q) (p + q) (p + q + 1))
        h (by omega)
  · intro p q
    have h := congrArg
      ((F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B (p + q)).map)
      (triangleMap c q).comm₂
    simpa [dMap, eMap, g, derivedTriangle, triangle, triangleMap,
      Functor.mapTriangle, Functor.map_comp,
      Category.assoc] using congrArg
        (fun t ↦ (bridgeIso F (truncation K q) (p + q)).inv ≫ t ≫
          (bridgeIso F (cohomologyComplex N q) (p + q)).hom) h.symm
  · intro n
    simpa only [dMap, bridgeMap, abutmentMap, Category.assoc, Functor.comp_map, D] using
      abutment_aux F (truncation K n) (truncation N n) (truncMap c n)
        (DerivedCategory.Q.map (K.obj.ιTruncLE n))
        (DerivedCategory.Q.map (N.obj.ιTruncLE n)) c
        (truncMap_comp_inclusion c n) (0 + n) n (zero_add n)
  · intro p q
    let e : DerivedCategory.singleFunctor A q ⋙ F.rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor B (p + q) ≅
        DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor B p :=
      Functor.isoWhiskerRight
        ((DerivedCategory.singleFunctors A).shiftIso (-q) q 0 (by omega)).symm
        (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B (p + q)) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.singleFunctor A 0)
        (Functor.isoWhiskerRight (F.rightDerivedFunctor.commShiftIso (-q))
          (DerivedCategory.homologyFunctor B (p + q))) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor)
        ((DerivedCategory.homologyFunctor B 0).shiftIso (-q) (p + q) p (by omega))
    have h := e.hom.naturality (homologyMap c q)
    simpa [eMap, singleIso, e, Category.assoc] using congrArg
      (fun t ↦ (bridgeIso F (cohomologyComplex K q) (p + q)).inv ≫ t) h

end CategoryTheory.TruncationCouple
