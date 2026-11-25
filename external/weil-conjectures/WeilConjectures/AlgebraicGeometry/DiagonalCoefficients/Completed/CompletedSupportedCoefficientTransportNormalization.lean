/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedPushSquare

/-! # Ordinary normalization for completed supported coefficient transport

Source: diagonal tower coefficient changes, initial supported-source identification.
(blueprint: lem-diagonal-completed-supported-transport-normalization).

The theorem below is the ordinary (degree-zero) normalization step in the
transport argument.  It is independent of the derived acyclicity argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- The completed coefficient is a large limit construction. Its underlying
-- sheaf, not the construction of its ring operations, is used in this argument.
attribute [local irreducible] Scheme.purTwistZlCompletionOfUniverses
  diagonalCompletedCoefficientMap

private theorem ordinary_normalization_transport
    {C D : Type*} [Category C] [Category D]
    (H : D ⥤ C) (K : C ⥤ D) (c : K ⋙ H ≅ 𝟭 C)
    {A B V T : C} {E S : D}
    (hS : S = K.obj A) (hT : T = H.obj S) (p : A ⟶ B)
    (q : E ≅ S) (i : E ≅ K.obj B) (v : V ≅ H.obj E) (t : V ≅ T)
    (r : T ⟶ A) (n : V ⟶ B)
    (hs : HEq (v.hom ≫ H.map q.hom) t.hom)
    (hi : HEq (q.inv ≫ i.hom) (K.map p))
    (ha : HEq r (c.hom.app A)) (hn : n = t.hom ≫ r ≫ p) :
    H.map i.inv ≫ v.inv ≫ n = c.hom.app B := by
  subst S
  subst T
  have hs := eq_of_heq hs
  have hi := eq_of_heq hi
  have ha := eq_of_heq ha
  rw [ha] at hn
  have hsinv : v.inv ≫ t.hom = H.map q.hom := by
    rw [← hs, v.inv_hom_id_assoc]
  have hi_hom : i.hom = q.hom ≫ K.map p := by
    simpa only [← Category.assoc, q.hom_inv_id, Category.id_comp] using
      congrArg (fun z ↦ q.hom ≫ z) hi
  calc
    _ = H.map i.inv ≫ v.inv ≫ t.hom ≫ c.hom.app A ≫ p := by rw [hn]
    _ = H.map i.inv ≫ H.map q.hom ≫ c.hom.app A ≫ p := by
      rw [← Category.assoc v.inv t.hom, hsinv]
    _ = H.map i.inv ≫ H.map q.hom ≫ H.map (K.map p) ≫ c.hom.app B := by
      have hc : H.map (K.map p) ≫ c.hom.app B = c.hom.app A ≫ p :=
        c.hom.naturality p
      exact congrArg (fun z ↦ H.map i.inv ≫ H.map q.hom ≫ z) hc.symm
    _ = c.hom.app B := by
      rw [← Category.assoc (H.map q.hom) (H.map (K.map p)), ← H.map_comp,
        ← hi_hom, ← H.map_comp_assoc, i.inv_hom_id, H.map_id, Category.id_comp]

private theorem underlying_inverse_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (V : D ⥤ E) (U : C ⥤ E) (e : F ⋙ V ≅ U)
    {A B : C} {T : D} (a : A ≅ B) (u : F.obj A ≅ T) :
    V.map (F.map a.inv ≫ u.hom) =
      (e.app B).hom ≫ U.map a.inv ≫ e.inv.app A ≫ V.map u.hom := by
  rw [V.map_comp]
  simpa only [Functor.comp_map, Category.assoc, Iso.app_hom] using
    congrArg (fun z ↦ z ≫ V.map u.hom) (NatIso.naturality_2 e a.inv).symm

private theorem composite_inverse
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : E ⥤ D) {A B : C} {M N : E} {T : D}
    (u : F.obj A ≅ T) (a : A ≅ B) (v : F.obj B ≅ G.obj M) (i : M ≅ N) :
    (u.symm ≪≫ F.mapIso a ≪≫ v ≪≫ G.mapIso i).inv =
      G.map i.inv ≫ v.inv ≫ F.map a.inv ≫ u.hom := by
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]

private theorem completed_forget_obj (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (M : DiagonalCompleted l X) :
    (diagonalCompletedRestriction l X ⋙ diagonalForget l X).obj M =
      (SheafOfModules.toSheaf.{u + 1}
        (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))).obj M := by
  rfl

private theorem completed_push_forget (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) (M : DiagonalCompleted l X) :
    (diagonalCompletedRestriction l S ⋙ diagonalForget l S).obj
        ((diagonalTracePush l f).obj M) =
      (lowerStar Ab.{u + 1} f).obj
        ((diagonalCompletedRestriction l X ⋙ diagonalForget l X).obj M) := by
  rw [completed_forget_obj, completed_forget_obj]
  rfl

private theorem completed_source_forget (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    (diagonalCompletedRestriction l (diagonalSurface Y) ⋙
      diagonalForget l (diagonalSurface Y)).obj (diagonalCompletedSource l Y) =
    (lowerStar Ab.{u + 1} (diagonalImmersion Y)).obj
      ((diagonalCompletedRestriction l (ProjectiveLine Y) ⋙
        diagonalForget l (ProjectiveLine Y)).obj
          (SheafOfModules.unit (Scheme.purTwistRing (ProjectiveLine Y)
            (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)))) := by
  rw [completed_forget_obj, completed_forget_obj]
  rfl

private theorem lowerStar_map_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    {X S : Scheme.{u}} (f : X ⟶ S) {M N : Modules Λ X} (g : M ⟶ N) :
    ((CondensedRing.lowerStar Λ f).map g).hom = (lowerStar Ab.{u + 1} f).map g.hom := by
  rfl

private theorem module_normalization_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (Y : Scheme.{u}) (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (c : lowerStar Ab.{u + 1} (diagonalImmersion Y) ⋙ lowerStar Ab.{u + 1} f ≅ 𝟭 _)
    {A T : Sheaf (Scheme.ProEt.topology (ProjectiveLine Y)) Ab.{u + 1}}
    {S : Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) Ab.{u + 1}}
    {V : Modules Λ (ProjectiveLine Y)} {E : Modules Λ (diagonalSurface Y)}
    (hS : S = (lowerStar Ab.{u + 1} (diagonalImmersion Y)).obj A)
    (hT : T = (lowerStar Ab.{u + 1} f).obj S)
    (p : A ⟶ condensedRingObj Λ (ProjectiveLine Y)) (q : E.X ≅ S)
    (i : E ≅ source Λ Y) (v : V ≅ (CondensedRing.lowerStar Λ f).obj E)
    (t : V.X ≅ T) (r : T ⟶ A)
    (n : V ⟶ Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
    (hs : HEq (v.hom.hom ≫ (lowerStar Ab.{u + 1} f).map q.hom) t.hom)
    (hi : HEq (q.inv ≫ i.hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map p))
    (ha : HEq r (c.hom.app A)) (hn : n.hom = t.hom ≫ r ≫ p) :
    HEq (((CondensedRing.lowerStar Λ f).map i.inv ≫ v.inv ≫ n).hom)
      (c.hom.app (condensedRingObj Λ (ProjectiveLine Y))) := by
  have he := ordinary_normalization_transport (lowerStar Ab.{u + 1} f)
    (lowerStar Ab.{u + 1} (diagonalImmersion Y)) c hS hT p q
    ((Mod.forget _).mapIso i) ((Mod.forget _).mapIso v) t r n.hom hs hi ha hn
  simpa only [Mod.comp_hom', lowerStar_map_hom, Category.assoc,
    Functor.mapIso_inv, Mod.forget_map] using heq_of_eq he

private theorem realized_module_normalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (Y : Scheme.{u}) (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (c : lowerStar Ab.{u + 1} (diagonalImmersion Y) ⋙ lowerStar Ab.{u + 1} f ≅ 𝟭 _)
    {C : Type*} [Category C] (F : C ⥤ Modules Λ (ProjectiveLine Y))
    (U : C ⥤ Sheaf (Scheme.ProEt.topology (ProjectiveLine Y)) Ab.{u + 1})
    (e : F ⋙ Mod.forget _ ≅ U) {N M : C} (a : N ≅ M)
    (u : F.obj N ≅ Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
    {E : Modules Λ (diagonalSurface Y)}
    {S : Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) Ab.{u + 1}}
    (q : E.X ≅ S) (v : F.obj M ≅ (CondensedRing.lowerStar Λ f).obj E)
    (i : E ≅ source Λ Y)
    (hS : S = (lowerStar Ab.{u + 1} (diagonalImmersion Y)).obj (U.obj N))
    (hT : U.obj M = (lowerStar Ab.{u + 1} f).obj S)
    (hs : HEq (v.hom.hom ≫ (lowerStar Ab.{u + 1} f).map q.hom) (e.hom.app M))
    (hi : HEq (q.inv ≫ i.hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (e.inv.app N ≫ u.hom.hom)))
    (ha : HEq (U.map a.inv) (c.hom.app (U.obj N))) :
    HEq ((u.symm ≪≫ F.mapIso a ≪≫ v ≪≫ (CondensedRing.lowerStar Λ f).mapIso i).inv.hom)
      (c.hom.app (condensedRingObj Λ (ProjectiveLine Y))) := by
  have hn := underlying_inverse_naturality F (Mod.forget _) U e a u
  have he := module_normalization_transport Λ Y f c hS hT
    (e.inv.app N ≫ u.hom.hom) q i v (e.app M) (U.map a.inv)
    (F.map a.inv ≫ u.hom) hs hi ha hn
  exact (heq_of_eq (congrArg (fun z ↦ z.hom)
    (composite_inverse F (CondensedRing.lowerStar Λ f) u a v i))).trans he

-- Compare the two standard names for the additive category before evaluating
-- at a completed coefficient object: that object is a large limit construction.
private theorem additive_comparison_ab (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y))
    (A : Sheaf (Scheme.ProEt.topology (ProjectiveLine Y)) Ab.{u + 1}) :
    HEq (((lowerStarComp AddCommGrpCat.{u + 1} (diagonalImmersion Y) f) ≪≫
      lowerStarCongr AddCommGrpCat.{u + 1} h ≪≫
        lowerStarId AddCommGrpCat.{u + 1} (ProjectiveLine Y)).hom.app A)
      (((lowerStarComp Ab.{u + 1} (diagonalImmersion Y) f) ≪≫
        lowerStarCongr Ab.{u + 1} h ≪≫
          lowerStarId Ab.{u + 1} (ProjectiveLine Y)).hom.app A) := by
  let c (B : Σ C : Type (u + 2), Category.{u + 1} C) :=
    letI := B.2
    (lowerStarComp B.1 (diagonalImmersion Y) f) ≪≫
      lowerStarCongr B.1 h ≪≫ lowerStarId B.1 (ProjectiveLine Y)
  have hc := congr_arg_heq c
    (show (⟨AddCommGrpCat.{u + 1}, inferInstance⟩ :
        Σ C : Type (u + 2), Category.{u + 1} C) = ⟨Ab.{u + 1}, inferInstance⟩ from rfl)
  have hc' : ((lowerStarComp AddCommGrpCat.{u + 1} (diagonalImmersion Y) f) ≪≫
      lowerStarCongr AddCommGrpCat.{u + 1} h ≪≫
        lowerStarId AddCommGrpCat.{u + 1} (ProjectiveLine Y)) =
      ((lowerStarComp Ab.{u + 1} (diagonalImmersion Y) f) ≪≫
        lowerStarCongr Ab.{u + 1} h ≪≫ lowerStarId Ab.{u + 1} (ProjectiveLine Y)) :=
    eq_of_heq hc
  exact heq_of_eq (congrArg (fun e ↦ e.hom.app A) hc')

/-- The composite ordinary comparison has the support normalization required
by a normalized source.  This is the ordinary part of the proof of
`completedSupportedCoefficient_transport`; the derived square and acyclicity
are handled separately there.

Source: diagonal tower coefficient changes, initial supported-source
identification; the ordinary normalization paragraph of the proof.
Proof: expand the composite, use naturality of the completed realization's
underlying comparison, cancel the coefficient-unit isomorphism, and apply the
normalizations of the input supported source and ordinary square together with
the prescribed normalization of the coefficient isomorphism.
(blueprint: lem-diagonal-completed-supported-transport-normalization). -/
theorem completedSupportedCoefficient_transport_normalization
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (R : DiagonalRightDerived (diagonalTracePush l f))
    (a : DiagonalTrace.SupportedSource l Y f R)
    (eP : CompletedRealization l (ProjectiveLine Y))
    (eW : CompletedRealization l (diagonalSurface Y))
    (s : CompletedOrdinarySquare l f eW eP)
    (i : eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (hi : HEq (eW.underlying.inv.app (diagonalCompletedSource l Y) ≫ i.hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (eP.underlying.inv.app (SheafOfModules.unit
          (Scheme.purTwistRing (ProjectiveLine Y)
            (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≫
          eP.unitIso.hom.hom))) :
    SupportNormalization (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y f
      (eP.unitIso.symm ≪≫ (eP.F.mapIso a.iso) ≪≫
        (s.ordinary.app (diagonalCompletedSource l Y)) ≪≫
        ((CondensedRing.lowerStar
          (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).mapIso i)) a.over_eq := by
  let M := diagonalCompletedSource l Y
  let U := diagonalCompletedRestriction l (ProjectiveLine Y) ⋙
    diagonalForget l (ProjectiveLine Y)
  let c := (lowerStarComp AddCommGrpCat.{u + 1} (diagonalImmersion Y) f) ≪≫
    lowerStarCongr AddCommGrpCat.{u + 1} a.over_eq ≪≫
      lowerStarId AddCommGrpCat.{u + 1} (ProjectiveLine Y)
  have hn := realized_module_normalization (Profinite.continuousMapRingObj.{u} ℤ_[l])
    Y f c eP.F U eP.underlying a.iso eP.unitIso
    (eW.underlying.app M) (s.ordinary.app M) i
    (completed_source_forget l Y) (completed_push_forget l f M)
    (s.normalization M) hi a.normalization
  exact hn.trans (additive_comparison_ab Y f a.over_eq _)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
