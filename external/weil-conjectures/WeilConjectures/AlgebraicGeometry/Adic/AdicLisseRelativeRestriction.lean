/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement

import all WeilConjectures.AlgebraicGeometry.Pbc.PbcFinitePullbackConstructibility
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement

/-! # Restriction of adic-lisse modules to inverse-image coefficients

Source: Stacks Project, proetale.tex, Tag 09BT, clause (3), and
sites.tex, Tag 00YV (functoriality of algebraic structures in topoi).
(blueprint: lem-weil-pbc-adic-lisse-relative-restriction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private instance underlying_preserves_tower_limits
    (Z : Scheme.{u}) (R : Sheaf (ProEt.topology Z) RingCat.{u + 1}) :
    PreservesLimitsOfShape ℕᵒᵖ (SheafOfModules.toSheaf.{u + 1} R) := by
  have : PreservesLimitsOfShape ℕᵒᵖ
      (SheafOfModules.toSheaf.{u + 1} R ⋙
        sheafToPresheaf (ProEt.topology Z) AddCommGrpCat.{u + 1}) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (SheafOfModules.forget.{u + 1} R ⋙ PresheafOfModules.toPresheaf R.obj))
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf (ProEt.topology Z) AddCommGrpCat.{u + 1})

private noncomputable def underlyingDiagramComparison
    (Z : Scheme.{u}) {R R' : Sheaf (ProEt.topology Z) RingCat.{u + 1}}
    (α : R ⟶ R') (S : ℕᵒᵖ ⥤ SheafOfModules.{u + 1} R)
    (S' : ℕᵒᵖ ⥤ SheafOfModules.{u + 1} R')
    (e : S ≅ S' ⋙ SheafOfModules.restrictScalars α) :
    S ⋙ SheafOfModules.toSheaf R ≅ S' ⋙ SheafOfModules.toSheaf R' :=
  Functor.isoWhiskerRight e (SheafOfModules.toSheaf R)

private noncomputable def modelLimitComparison
    (Z : Scheme.{u}) {R R' : Sheaf (ProEt.topology Z) RingCat.{u + 1}}
    (α : R ⟶ R') (S : ℕᵒᵖ ⥤ SheafOfModules.{u + 1} R)
    (S' : ℕᵒᵖ ⥤ SheafOfModules.{u + 1} R')
    (e : S ≅ S' ⋙ SheafOfModules.restrictScalars α) :
    (SheafOfModules.toSheaf R).obj (limit S) ≅
      (SheafOfModules.toSheaf R').obj (limit S') :=
  preservesLimitIso (SheafOfModules.toSheaf R) S ≪≫
    HasLimit.isoOfNatIso (underlyingDiagramComparison Z α S S' e) ≪≫
    (preservesLimitIso (SheafOfModules.toSheaf R') S').symm

private theorem modelLimitComparison_π
    (Z : Scheme.{u}) {R R' : Sheaf (ProEt.topology Z) RingCat.{u + 1}}
    (α : R ⟶ R') (S : ℕᵒᵖ ⥤ SheafOfModules.{u + 1} R)
    (S' : ℕᵒᵖ ⥤ SheafOfModules.{u + 1} R')
    (e : S ≅ S' ⋙ SheafOfModules.restrictScalars α) (n : ℕᵒᵖ) :
    (modelLimitComparison Z α S S' e).hom ≫
        (SheafOfModules.toSheaf R').map (limit.π S' n) =
      (SheafOfModules.toSheaf R).map (limit.π S n) ≫
        (underlyingDiagramComparison Z α S S' e).hom.app n := by
  dsimp only [modelLimitComparison, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, Category.assoc, preservesLimitIso_inv_π,
    HasLimit.isoOfNatIso_hom_π, ← Category.assoc, preservesLimitIso_hom_π]

private theorem localModel_restrict
    (Z : Scheme.{u})
    {R₀ Rhat R₀' Rhat' : Sheaf (ProEt.topology Z) RingCat.{u + 1}}
    {Rₙ Rₙ' : ℕ → Sheaf (ProEt.topology Z) RingCat.{u + 1}}
    (ρ : ∀ n, R₀ ⟶ Rₙ n) (π : ∀ n, Rhat ⟶ Rₙ n)
    (ρ' : ∀ n, R₀' ⟶ Rₙ' n) (π' : ∀ n, Rhat' ⟶ Rₙ' n)
    (α : R₀ ⟶ R₀') (β : Rhat ⟶ Rhat') (γ : ∀ n, Rₙ n ⟶ Rₙ' n)
    (hρ : ∀ n, ρ n ≫ γ n = α ≫ ρ' n)
    (hπ : ∀ n, π n ≫ γ n = β ≫ π' n)
    (S : ℕᵒᵖ ⥤ SheafOfModules.{u + 1} R₀)
    (S' : ℕᵒᵖ ⥤ SheafOfModules.{u + 1} R₀')
    (e : S ≅ S' ⋙ SheafOfModules.restrictScalars α)
    (F : SheafOfModules.{u + 1} Rhat') (V : Z.ProEt)
    (hF : IsAdicLisseLocalModel Z R₀' Rhat' Rₙ' ρ' π' S' F V) :
    IsAdicLisseLocalModel Z R₀ Rhat Rₙ ρ π S
      ((SheafOfModules.restrictScalars β).obj F) V := by
  obtain ⟨t, ht⟩ := hF
  let c := modelLimitComparison Z α S S' e
  let cV := ((ProEt.topology Z).overPullback AddCommGrpCat.{u + 1} V).mapIso c
  refine ⟨t ≪≫ cV.symm, ?_⟩
  intro n W r a x har
  have hres : (ρ' n).hom.app (op W.unop.left) (α.hom.app _ a) =
      (π' n).hom.app (op W.unop.left) (β.hom.app _ r) := by
    have ha := congrArg (fun f ↦ f.hom.app (op W.unop.left) a) (hρ n)
    have hr := congrArg (fun f ↦ f.hom.app (op W.unop.left) r) (hπ n)
    dsimp at ha hr
    exact ha.symm.trans ((congrArg ((γ n).hom.app _) har).trans hr)
  have hc (y : ((SheafOfModules.toSheaf R₀').obj (limit S')).obj.obj
      (op W.unop.left)) :
      (e.hom.app (op n)).val.app (op W.unop.left)
          ((limit.π S (op n)).val.app (op W.unop.left) (c.inv.hom.app _ y)) =
        (limit.π S' (op n)).val.app (op W.unop.left) y := by
    have hh : c.inv ≫ (SheafOfModules.toSheaf R₀).map (limit.π S (op n)) ≫
        (underlyingDiagramComparison Z α S S' e).hom.app (op n) =
          (SheafOfModules.toSheaf R₀').map (limit.π S' (op n)) := by
      rw [← modelLimitComparison_π Z α S S' e (op n)]
      exact c.inv_hom_id_assoc _
    exact congrArg (fun f ↦ (f.hom.app (op W.unop.left)).hom y) hh
  have : IsIso (e.hom.app (op n)).val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget R₀).map (e.hom.app (op n))))
  have : IsIso ((e.hom.app (op n)).val.app (op W.unop.left)) :=
    inferInstanceAs (IsIso ((PresheafOfModules.evaluation R₀.obj (op W.unop.left)).map
      (e.hom.app (op n)).val))
  apply (ConcreteCategory.bijective_of_isIso
    ((e.hom.app (op n)).val.app (op W.unop.left))).1
  change (e.hom.app (op n)).val.app (op W.unop.left)
      ((limit.π S (op n)).val.app (op W.unop.left)
        (c.inv.hom.app _ (t.hom.hom.app W
          ((β.hom.app _ r) • (show F.val.obj (op W.unop.left) from x))))) =
    (e.hom.app (op n)).val.app (op W.unop.left)
      (a • (limit.π S (op n)).val.app (op W.unop.left)
        (c.inv.hom.app _ (t.hom.hom.app W x)))
  rw [hc, (e.hom.app (op n)).val.app _ |>.hom.map_smul, hc]
  exact ht n W (β.hom.app _ r) (α.hom.app _ a) x hres

@[irreducible] private noncomputable def constantEncodingNatIso (Z : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} A) ≅
      adicLisseConstantModules Z A ⋙ scalarRestriction Z A := by
  let J := ProEt.topology Z
  let R := adicLisseRing Z A
  let a := adicLisseConstantUnit Z A
  let f (M : ModuleCat.{u + 1} A) :=
    ConstantScalarComparison.constantComparisonHom J A R a M
  have hf (M : ModuleCat.{u + 1} A) : IsIso (f M) :=
    ConstantScalarComparison.constantComparisonHom_isIso J A R a M
  refine NatIso.ofComponents (fun M ↦ asIso (f M)) ?_
  intro M N g
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ ((scalarRestriction Z A).obj
    ((adicLisseConstantModules Z A).obj N)).property
  have hfac (M : ModuleCat.{u + 1} A) :
      toSheafify J ((Functor.const Z.ProEtᵒᵖ).obj M) ≫ (f M).hom =
        { app := fun U ↦ ((PresheafOfModules.sheafificationAdjunction a).unit.app
            (ConstantScalarComparison.constantPresheaf A M)).app U
          naturality := by
            intro U V b
            ext x
            exact ConcreteCategory.congr_hom
              (((PresheafOfModules.sheafificationAdjunction a).unit.app
                (ConstantScalarComparison.constantPresheaf A M)).naturality b) x } :=
    ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv _ _).apply_symm_apply _
  change toSheafify J _ ≫ (sheafifyMap J ((Functor.const Z.ProEtᵒᵖ).map g) ≫
      (f N).hom) = toSheafify J _ ≫ ((f M).hom ≫ _)
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc, hfac,
    ← Category.assoc, hfac]
  ext U x
  let φ : ConstantScalarComparison.constantPresheaf (C := Z.ProEt) A M ⟶
      ConstantScalarComparison.constantPresheaf (C := Z.ProEt) A N :=
    { app := fun _ ↦ g
      naturality := by intros; ext x; rfl }
  exact ConcreteCategory.congr_hom
    (congrArg (fun t ↦ t.app U)
      ((PresheafOfModules.sheafificationAdjunction a).unit.naturality φ)) x

@[irreducible] private noncomputable def concreteConstantModuleComparison
    {X Y : Scheme.{u}} (h : Y ⟶ X) (A : Type (u + 1)) [CommRing A] :
    adicLisseConstantModules X A ⋙
        proEtaleModuleInverseImage h (adicLisseConstantRing X A) ≅
      adicLisseConstantModules Y A ⋙ SheafOfModules.restrictScalars
        ((adicLisseForget Y).map (constantCoefficients h A).hom) := by
  let c := constantCoefficients h A
  let E := proEtaleScalarEquivalence Y ((adicLisseForget Y).mapIso c)
  let CX := adicLisseConstantModules X A
  let CY := adicLisseConstantModules Y A
  let L := proEtaleModuleInverseImage h (adicLisseConstantRing X A)
  let EY := scalarRestriction Y A
  let B := ProEtale.upperStar (ModuleCat.{u + 1} A) h
  let k : constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A) ⋙ B ≅
      constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A) :=
    (((constantSheafΓAdj _ (ModuleCat.{u + 1} A)).comp
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h)).ofNatIsoRight
        (ProEtale.globalSectionsLowerStarIso (ModuleCat.{u + 1} A) h)).leftAdjointUniq
          (constantSheafΓAdj _ (ModuleCat.{u + 1} A))
  let q : CX ⋙ L ⋙ E.inverse ⋙ EY ≅ CY ⋙ EY :=
    Functor.isoWhiskerLeft CX (relativeEncoding h A) ≪≫
      Functor.isoWhiskerRight (constantEncodingNatIso X A).symm B ≪≫
      k ≪≫ constantEncodingNatIso Y A
  let q' : CX ⋙ L ⋙ E.inverse ≅ CY := Functor.fullyFaithfulCancelRight EY q
  exact Functor.isoWhiskerLeft (CX ⋙ L) E.counitIso.symm ≪≫
    Functor.isoWhiskerRight q' E.functor

@[irreducible] private noncomputable def concreteModuleSystemComparison
    {X Y : Scheme.{u}} (h : Y ⟶ X) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (N : ModuleCat.{u + 1} A) :
    adicLisseModuleSystem X I N ⋙
        proEtaleModuleInverseImage h (adicLisseConstantRing X A) ≅
      adicLisseModuleSystem Y I N ⋙ SheafOfModules.restrictScalars
        ((adicLisseForget Y).map (constantCoefficients h A).hom) := by
  let e := concreteConstantModuleComparison h A
  let η : adicLisseModuleSystem X I N ⋙
        proEtaleModuleInverseImage h (adicLisseConstantRing X A) ⟶
      adicLisseModuleSystem Y I N ⋙ SheafOfModules.restrictScalars
        ((adicLisseForget Y).map (constantCoefficients h A).hom) :=
    NatTrans.ofOpSequence (fun n ↦ e.hom.app
      (ModuleCat.of A (N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N)))) (by
        intro n
        simpa only [Functor.comp_map, adicLisseModuleSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          e.hom.naturality (ModuleCat.ofHom (Submodule.factorPowSucc I N (n + 1))))
  have (n : ℕᵒᵖ) : IsIso (η.app n) :=
    inferInstanceAs (IsIso (e.hom.app
      (ModuleCat.of A (N ⧸ (I ^ (n.unop + 1) • ⊤ : Submodule A N)))))
  have : IsIso η := NatIso.isIso_of_isIso_app η
  exact asIso η

/-- A projection-compatible coefficient map turns an adic-lisse module on the target
site into a relatively adic-lisse module over the inverse-image completed coefficients.

Source: Stacks Project, Tag 09BT, clause (3); Tag 00YV, parts (2), (5), (6).
(blueprint: lem-weil-pbc-adic-lisse-relative-restriction).

Proof: retain the covering sieve and the complete A-modules N in the adic-lisse
local models. For each A-module M, inverse image of its constant module sheaf on X
is the restriction of its constant module sheaf on Y along the canonical constant
ring comparison. Indeed, inverse image preserves constant abelian sheaves and their
scalar-action maps, and the canonical comparison sends a constant section to the
same section. This identification is natural in M, hence gives an isomorphism of
the actual quotient-module diagrams for N and all their transitions. Restriction of
scalars preserves limits, so taking limits and forgetting to abelian sheaves gives
an isomorphism between the relative model and the absolute model, without commuting
inverse image with an infinite limit. Compose its inverse with each original local
trivialization. Given a scalar a in the inverse-image constant A-ring and a completed
scalar r with equal nth residues, apply the canonical constant quotient-ring
comparison. Naturality on A -> A/I^(n+1) and the assumed equation for beta show that
the images of a and beta(r) have equal nth residues on Y. The original local model's
linearity proves the scalar identity after applying the diagram comparison; its
inverse proves the relative identity. Completeness and finite generation of N/IN
are unchanged. This also treats the empty site, zero modules and zero rings, and
I=0 or I=top: neither a residue lift nor a nonzero scalar is chosen. -/
theorem adicLisse_relative_restrict {X Y : Scheme.{u}} (h : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (β : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (adicLisseCompletedRing X I) ⟶ adicLisseCompletedRing Y I)
    (hβ : ∀ n : ℕ, β ≫ limit.π (adicLisseRingSystem Y I) (op n) =
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (limit.π (adicLisseRingSystem X I) (op n)) ≫
          proEtaleConstantInverseImageMap h CommRingCat.{u + 1}
            (CommRingCat.of (A ⧸ I ^ (n + 1))))
    (F : ringedSiteModules.{u + 1}
      ((adicLisseForget Y).obj (adicLisseCompletedRing Y I)))
    (hF : IsAdicLisseModule Y I F) :
    IsRelativelyAdicLisseModule h I
      ((SheafOfModules.restrictScalars ((adicLisseForget Y).map β)).obj F) := by
  classical
  obtain ⟨T, hT, hmodels⟩ := hF
  refine ⟨T, hT, ?_⟩
  intro V f hf
  obtain ⟨N, hN, hfin, hm⟩ := hmodels V f hf
  refine ⟨N, hN, hfin, ?_⟩
  apply localModel_restrict Y _ _ _ _
    ((adicLisseForget Y).map (constantCoefficients h A).hom)
    ((adicLisseForget Y).map β)
    (fun n ↦ (adicLisseForget Y).map
      (proEtaleConstantInverseImageMap h CommRingCat.{u + 1}
        (CommRingCat.of (A ⧸ I ^ (n + 1)))))
    _ _ _ _ (concreteModuleSystemComparison h I N) F V hm
  · intro n
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simpa only [constantCoefficients, asIso_hom] using
      proEtaleConstantInverseImageMap_naturality h
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))
  · intro n
    simpa only [← Functor.map_comp] using
      congrArg ((adicLisseForget Y).map) (hβ n).symm

end AlgebraicGeometry.Scheme
