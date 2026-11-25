/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation
public import WeilConjectures.WeilSheaf.StalkConstantSheaf

/-!
# Global sections and invariants of the Weil fundamental representation

For a lisse Weil sheaf `ℱ` on a curve `C₀`, restriction to the stalk at the base point `t`
identifies the global sections `Γ(C, ℱ)` of `ℱ` on the geometric curve with the invariants
`V^{π₁(C)}` of its Weil fundamental representation `(V, ρ)`, compatibly with the Frobenius of
the global sections and `ρ(γ)` for any element `γ` of degree one
(`AlgebraicGeometry.WeilGroup.exists_globalSections_linearEquiv_invariants`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.LisseMonodromy

open Scheme.FiniteEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} {Ω : Type u} [Field Ω]
  (M : LisseMonodromy l Y Ω)

/-- The restriction `Γ(Y, G) → G_t` of global sections of a lisse sheaf to its stalk at a
geometric point `t`, as a `ℚ̄_ℓ`-linear map. -/
noncomputable def sectionsRes (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y) :
    (WeilCoefficients.toModuleCat l).obj ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj G.obj.X)
      →ₗ[PadicAlgCl l] StalkSpace t G :=
  ((WeilCoefficients.toModuleCat l).map ((globalSectionsToUpperStar _ t).app G.obj.X)).hom

/-- Restrictions of global sections are invariant under the monodromy. -/
lemma rep_sectionsRes (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y)
    (g : Aut (fiber t)) (a) :
    M.rep t G g (sectionsRes t G a) = sectionsRes t G a := by
  have h := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom a)
    (M.mono_globalSections g.asIso G)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- The restriction of the global section `v(1)` of a morphism `v : ℚ̄_ℓ ⟶ G` is the image of the
restriction of the unit section under the stalk of `v`. -/
lemma sectionsRes_globalSectionOfModHom (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (G : LisseSheaf l Y) (v : LisseSheaf.unit l ⟶ G) :
    sectionsRes t G (globalSectionOfModHom v.hom) =
      ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map v)).hom
        (sectionsRes t (LisseSheaf.unit l) (oneGlobalSection Y)) := by
  rw [globalSectionOfModHom_eq]
  change ((WeilCoefficients.toModuleCat l).map ((globalSectionsToUpperStar _ t).app G.obj.X)).hom
    (((WeilCoefficients.toModuleCat l).map ((Sheaf.Γ _ _).map v.hom.hom)).hom
      (oneGlobalSection Y)) = _
  have h := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom (oneGlobalSection Y))
    ((globalSectionsToUpperStar (WeilCoefficients.{u} l) t).naturality v.hom.hom)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- The restriction of the unit section to the stalk of `ℚ̄_ℓ` is nonzero. -/
lemma sectionsRes_one_ne_zero (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) :
    sectionsRes t (LisseSheaf.unit l) (oneGlobalSection Y) ≠ 0 :=
  globalSectionsToUpperStar_oneGlobalSection_ne_zero t

/-- The restriction of the unit section spans the stalk of `ℚ̄_ℓ`. -/
lemma exists_smul_sectionsRes_one (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (x : StalkSpace t (LisseSheaf.unit l)) :
    ∃ c : PadicAlgCl l, c • sectionsRes t (LisseSheaf.unit l) (oneGlobalSection Y) = x :=
  (finrank_eq_one_iff_of_nonzero' (K := PadicAlgCl l)
    (V := StalkSpace t (LisseSheaf.unit l)) _ (sectionsRes_one_ne_zero t)).1
    (finrank_globalSections_upperStar_adicConstantSheaf t) x

/-- The monodromy acts trivially on the stalk of `ℚ̄_ℓ`. -/
lemma rep_unit (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (g : Aut (fiber t))
    (x : StalkSpace t (LisseSheaf.unit l)) : M.rep t (LisseSheaf.unit l) g x = x := by
  obtain ⟨c, rfl⟩ := exists_smul_sectionsRes_one t x
  rw [map_smul, rep_sectionsRes]

variable {M}

/-- Restriction of global sections of a lisse sheaf to the stalk at `t` is injective, if the
monodromy at `t` is an equivalence. -/
lemma sectionsRes_injective {t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (hM : M.IsEquivalenceAt t)
    (G : LisseSheaf l Y) : Function.Injective (sectionsRes t G) := by
  intro a a' h
  obtain ⟨v, rfl⟩ := (bijective_globalSectionOfModHom G.obj).2 a
  obtain ⟨v', rfl⟩ := (bijective_globalSectionOfModHom G.obj).2 a'
  have hv : (ObjectProperty.homMk v : LisseSheaf.unit l ⟶ G) = ObjectProperty.homMk v' := by
    refine hM.faithful _ _ (WeilCoefficients.hom_ext_toModuleCat (LinearMap.ext fun x ↦ ?_))
    obtain ⟨c, rfl⟩ := exists_smul_sectionsRes_one t x
    rw [map_smul, map_smul]
    congr 1
    rw [← sectionsRes_globalSectionOfModHom, ← sectionsRes_globalSectionOfModHom]
    exact h
  rw [show v = v' from congrArg (fun f ↦ f.hom) hv]

/-- Every monodromy-invariant vector of the stalk at `t` is the restriction of a global section, if
the monodromy at `t` is an equivalence. -/
lemma exists_sectionsRes_eq {t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (hM : M.IsEquivalenceAt t)
    (G : LisseSheaf l Y) (w : StalkSpace t G) (hw : ∀ g, M.rep t G g w = w) :
    ∃ a, sectionsRes t G a = w := by
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one (PadicAlgCl l)
    (sectionsRes_one_ne_zero (l := l) t)
  let φ : StalkSpace t (LisseSheaf.unit l) →ₗ[PadicAlgCl l] StalkSpace t G :=
    LinearMap.toSpanSingleton _ _ w ∘ₗ ℓ
  obtain ⟨f, hf⟩ := hM.full φ fun g x ↦ by
    rw [rep_unit]
    simp only [φ, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, map_smul, hw]
  refine ⟨globalSectionOfModHom f.hom, ?_⟩
  rw [sectionsRes_globalSectionOfModHom, hf]
  rw [LinearMap.comp_apply, hℓ, LinearMap.toSpanSingleton_apply, one_smul]

end AlgebraicGeometry.ProEtale.LisseMonodromy

namespace AlgebraicGeometry.WeilGroup

open ProEtale Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)] [IsCurve (C ↘ Spec (.of K))]
  {W : WeilGroup (C ↘ Spec (.of K))}
  {M : LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber K}
  {B : BasePointData W} (D : WeilMonodromyData B)

omit [IsCurve (C ↘ Spec (.of K))] [Fact (ringChar K ≠ l)] in
/-- Restriction of global sections along the Frobenius `Fr`, followed by `Fr^* ≅ (Fr⁻¹)_*`, is the
identification `Γ(C, ℱ) ≅ Γ(C, (Fr⁻¹)_* ℱ)`. -/
lemma globalSectionsToUpperStar_frobenius_comp (X : Sheaf (Scheme.ProEt.topology
    (C ↘ Spec (.of K)).geometricFiber) (WeilCoefficients.{u} l)) :
    (globalSectionsToUpperStar _ (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom).app X ≫
      (Sheaf.Γ _ _).map ((upperStarIsoLowerStarInv _
        (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso).hom.app X) =
    (globalSectionsLowerStarIso _
      (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.inv).inv.app X := by
  have h' := globalSectionsToUpperStar_app_comp_globalSectionsUpperStarIso
    (WeilCoefficients.{u} l) (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso X
  simp only [globalSectionsUpperStarIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] at h'
  rw [← Category.assoc] at h'
  exact (Iso.comp_hom_eq_id ((globalSectionsLowerStarIso _
    (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.inv).app _)).1 h'

omit [IsCurve (C ↘ Spec (.of K))] in
/-- The underlying morphism of sheaves of the Weil structure `Fr^* ℱ ≅ ℱ` of a lisse Weil
sheaf. -/
lemma lisseFrobStr_hom_hom_hom (F : WeilSheaf K l C) (hF : F.IsLisse) :
    (F.lisseFrobStr hF).hom.hom.hom =
      (upperStarIsoLowerStarInv _ (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso).hom.app
        F.obj.carrier.X ≫ (AdicSheaf.forget _).map F.obj.str.hom := by
  rw [← adicUpperStarIsoLowerStarInv_hom_app_hom]
  rfl

variable (M B) in
/-- **Restriction of global sections and the Frobenius**, as morphisms: restricting the image of
a global section under the Frobenius `Γ(C, ℱ) ≅ Γ(C, (Fr⁻¹)_* ℱ) → Γ(C, ℱ)` to the stalk at `t` is
applying `Φ` to its restriction. -/
lemma globalSections_frobenius_comp_res (F : WeilSheaf K l C) (hF : F.IsLisse) :
    ((globalSectionsLowerStarIso _
        (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.inv).symm.app F.obj.carrier.X ≪≫
        (Sheaf.Γ _ _).mapIso ((AdicSheaf.forget _).mapIso F.obj.str)).hom ≫
      (globalSectionsToUpperStar _ B.t).app F.obj.carrier.X =
    (globalSectionsToUpperStar _ B.t).app F.obj.carrier.X ≫ (frobStalkIso M B F hF).hom := by
  have e₁ : (globalSectionsToUpperStar _ B.t).app F.obj.carrier.X ≫
      (M.mono B.frobPath).hom.app (F.toLisse hF) =
      (globalSectionsToUpperStar _
        (B.t ≫ (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom)).app F.obj.carrier.X :=
    M.mono_globalSections B.frobPath (F.toLisse hF)
  have e₂ := globalSectionsToUpperStar_comp (WeilCoefficients.{u} l) B.t
    (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom F.obj.carrier.X
  have e₃ : (lisseStalk l B.t).map (F.lisseFrobStr hF).hom =
      (Sheaf.Γ _ _).map (((B.t)^*[WeilCoefficients.{u} l]).map
        ((F.lisseFrobStr hF).hom.hom.hom)) := rfl
  have e₄ := ((globalSectionsToUpperStar (WeilCoefficients.{u} l) B.t).naturality
    ((F.lisseFrobStr hF).hom.hom.hom)).symm
  simp only [Functor.comp_map] at e₄
  have e₅ := globalSectionsToUpperStar_frobenius_comp (l := l) F.obj.carrier.X
  simp only [frobStalkIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, upperStarStalkIso]
  rw [reassoc_of% e₁, reassoc_of% e₂, e₃]
  erw [e₄]
  rw [lisseFrobStr_hom_hom_hom, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% e₅]
  rfl

omit [IsCurve (C ↘ Spec (.of K))] in
/-- The Frobenius of the global sections of a Weil sheaf, unfolded. -/
lemma globalSections_frobenius_eq' [QuasiCompact (C ↘ Spec (.of K))]
    [LocallyOfFiniteType (C ↘ Spec (.of K))] (F : WeilSheaf K l C) :
    F.globalSections.frobenius = WeilCoefficients.linearEquivOfIso
      ((globalSectionsLowerStarIso _
        (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.inv).symm.app F.obj.carrier.X ≪≫
        (Sheaf.Γ _ _).mapIso ((AdicSheaf.forget _).mapIso F.obj.str)) :=
  rfl

variable (M B) in
/-- **Restriction of global sections and the Frobenius**: `res(Frob a) = Φ(res a)`. -/
lemma sectionsRes_frobenius (F : WeilSheaf K l C) (hF : F.IsLisse)
    (a : F.globalSections.carrier) :
    LisseMonodromy.sectionsRes B.t (F.toLisse hF) (F.globalSections.frobenius a) =
      frobStalk M B F hF (LisseMonodromy.sectionsRes B.t (F.toLisse hF) a) := by
  have h := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom a)
    (globalSections_frobenius_comp_res M B F hF)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [globalSections_frobenius_eq']
  exact h

/-- A vector of the stalk is invariant under the geometric part of the Weil fundamental
representation if and only if it is invariant under the monodromy. -/
lemma mem_invariants_fundamentalRep_iff (F : WeilSheaf K l C) (hF : F.IsLisse)
    (w : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    w ∈ Representation.invariants ((fundamentalRep M D F hF).comp W.geometric.subtype) ↔
      ∀ g, M.rep B.t (F.toLisse hF) g w = w := by
  rw [Representation.mem_invariants]
  constructor
  · intro h g
    have := h (D.geomEquiv g)
    rwa [MonoidHom.comp_apply, Subgroup.subtype_apply, fundamentalRep_geometric,
      ContinuousMulEquiv.symm_apply_apply] at this
  · intro h u
    rw [MonoidHom.comp_apply, Subgroup.subtype_apply, fundamentalRep_geometric]
    exact h _

/-- **Global sections are invariants**: restriction to the stalk at the base point identifies the
global sections `Γ(C, ℱ)` of a lisse Weil sheaf with the `π₁(C)`-invariants of its Weil
fundamental representation, carrying the Frobenius of the global sections to the action of an
element `γ` of degree one. -/
theorem exists_globalSections_linearEquiv_invariants (hM : M.IsEquivalenceAt B.t)
    (F : WeilSheaf K l C) (hF : F.IsLisse) (γ : W.carrier)
    (hγ : W.deg γ = Multiplicative.ofAdd 1) :
    ∃ f : F.globalSections.carrier ≃ₗ[PadicAlgCl l]
        Representation.invariants ((fundamentalRep M D F hF).comp W.geometric.subtype),
      ∀ v, (f (F.globalSections.frobenius v) : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) =
        fundamentalRep M D F hF γ (f v) := by
  let res := LisseMonodromy.sectionsRes B.t (F.toLisse hF)
  let f₀ : F.globalSections.carrier →ₗ[PadicAlgCl l]
      Representation.invariants ((fundamentalRep M D F hF).comp W.geometric.subtype) :=
    res.codRestrict _ fun a ↦ (mem_invariants_fundamentalRep_iff D F hF _).2
      fun g ↦ LisseMonodromy.rep_sectionsRes M B.t (F.toLisse hF) g a
  have hbij : Function.Bijective f₀ := by
    refine ⟨fun a b h ↦ LisseMonodromy.sectionsRes_injective hM (F.toLisse hF)
      (congrArg Subtype.val h), fun w ↦ ?_⟩
    obtain ⟨a, ha⟩ := LisseMonodromy.exists_sectionsRes_eq hM (F.toLisse hF) w
      ((mem_invariants_fundamentalRep_iff D F hF w).1 w.2)
    exact ⟨a, Subtype.ext ha⟩
  refine ⟨LinearEquiv.ofBijective f₀ hbij, fun v ↦ ?_⟩
  change res (F.globalSections.frobenius v) = fundamentalRep M D F hF γ (res v)
  rw [sectionsRes_frobenius M]
  have hmem : D.frobLift⁻¹ * γ ∈ W.geometric := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, D.deg_frobLift, hγ, inv_mul_cancel]
  have hγ' : γ = D.frobLift * (D.frobLift⁻¹ * γ) := by group
  rw [hγ', map_mul, Module.End.mul_apply, fundamentalRep_geometric M D F hF ⟨_, hmem⟩,
    LisseMonodromy.rep_sectionsRes, fundamentalRep_frobLift]
  rfl

end AlgebraicGeometry.WeilGroup
