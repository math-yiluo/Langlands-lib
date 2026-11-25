/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.EtaleZariskiAbelianPositiveComparison
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyAgree

/-! # Étale and Zariski cohomology of quasi-coherent modules

Source: Stacks Project, Descent, Proposition 03DW (2), and Étale Cohomology,
Theorem 03P2 (blueprint: lem-sc-etale-zariski-qcoh-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

attribute [local irreducible] tensorPullback tensorPullbackObj

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private noncomputable def sectionsUnitOf {A B : Scheme.{u}} (a : A ⟶ B)
    (L : B.Modules ⥤ A.Modules) (adj : L ⊣ pushforward a) (F : B.Modules) :
    Γ(F, ⊤) ⟶ Γ(L.obj F, ⊤) :=
  (adj.unit.app F).app ⊤ ≫ (L.obj F).presheaf.map (homOfLE a.preimage_top.ge).op

private theorem sectionsUnitOf_natural {A B : Scheme.{u}} (a : A ⟶ B)
    (L : B.Modules ⥤ A.Modules) (adj : L ⊣ pushforward a)
    {F G : B.Modules} (φ : F ⟶ G) :
    φ.app ⊤ ≫ sectionsUnitOf a L adj G =
      sectionsUnitOf a L adj F ≫ (L.map φ).app ⊤ := by
  ext s
  have hu := congrArg (fun ψ ↦ ψ.app ⊤ s) (adj.unit.naturality φ)
  have hn := congrArg (fun ψ ↦ ψ ((adj.unit.app F).app ⊤ s))
    ((L.map φ).mapPresheaf.naturality
      (homOfLE a.preimage_top.ge).op)
  change (adj.unit.app G).app ⊤ (φ.app ⊤ s) =
    (L.map φ).app (a ⁻¹ᵁ ⊤) ((adj.unit.app F).app ⊤ s) at hu
  change (L.map φ).app ⊤
      ((L.obj F).presheaf.map (homOfLE a.preimage_top.ge).op
        ((adj.unit.app F).app ⊤ s)) =
    (L.obj G).presheaf.map (homOfLE a.preimage_top.ge).op
      ((L.map φ).app (a ⁻¹ᵁ ⊤) ((adj.unit.app F).app ⊤ s)) at hn
  exact (congrArg
    ((L.obj G).presheaf.map (homOfLE a.preimage_top.ge).op) hu).trans hn.symm

private theorem sectionsRestrictionOf_natural
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (a : A ⟶ B), L a ⊣ pushforward a)
    (c : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
      L b ⋙ L a ≅ L (a ≫ b)) {X : Scheme.{u}}
    {F G : X.Modules} (φ : F ⟶ G) {U V : X.Etale} (g : V ⟶ U) :
    ((L U.hom).map φ).app ⊤ ≫ (sectionsUnitOf g.left (L g.left) (adj g.left) ((L U.hom).obj G) ≫
      ((c g.left U.hom).hom.app G).app ⊤ ≫
      (eqToHom (congrArg (fun a ↦ (L a).obj G) g.w)).app ⊤) =
      (sectionsUnitOf g.left (L g.left) (adj g.left) ((L U.hom).obj F) ≫
      ((c g.left U.hom).hom.app F).app ⊤ ≫
      (eqToHom (congrArg (fun a ↦ (L a).obj F) g.w)).app ⊤) ≫ ((L V.hom).map φ).app ⊤ := by
  ext s
  let t := sectionsUnitOf g.left (L g.left) (adj g.left) ((L U.hom).obj F) s
  have hu := congrArg (fun f ↦ f s)
    (sectionsUnitOf_natural g.left (L g.left) (adj g.left) ((L U.hom).map φ))
  change sectionsUnitOf g.left (L g.left) (adj g.left) ((L U.hom).obj G)
      (((L U.hom).map φ).app ⊤ s) =
    ((L g.left).map ((L U.hom).map φ)).app ⊤ t at hu
  have hc := congrArg (fun ψ ↦ ψ.app ⊤ t)
    ((c g.left U.hom).hom.naturality φ)
  change ((c g.left U.hom).hom.app G).app ⊤
      (((L g.left).map ((L U.hom).map φ)).app ⊤ t) =
    ((L (g.left ≫ U.hom)).map φ).app ⊤
      (((c g.left U.hom).hom.app F).app ⊤ t) at hc
  have he := congrArg (fun ψ ↦ ψ.app ⊤
      (((c g.left U.hom).hom.app F).app ⊤ t))
    ((eqToHom (congrArg L g.w) :
      L (g.left ≫ U.hom) ⟶ L V.hom).naturality φ)
  simp only [Hom.comp_app, eqToHom_app] at he
  change (eqToHom (congrArg (fun f ↦ (L f).obj G) g.w)).app ⊤
      (((L (g.left ≫ U.hom)).map φ).app ⊤
        (((c g.left U.hom).hom.app F).app ⊤ t)) =
    ((L V.hom).map φ).app ⊤
      ((eqToHom (congrArg (fun f ↦ (L f).obj F) g.w)).app ⊤
        (((c g.left U.hom).hom.app F).app ⊤ t)) at he
  change (eqToHom (congrArg (fun f ↦ (L f).obj G) g.w)).app ⊤
      (((c g.left U.hom).hom.app G).app ⊤
        (sectionsUnitOf g.left (L g.left) (adj g.left) ((L U.hom).obj G)
          (((L U.hom).map φ).app ⊤ s))) = _
  erw [hu]
  exact (congrArg ((eqToHom
    (congrArg (fun f ↦ (L f).obj G) g.w)).app ⊤) hc).trans he

private theorem sectionsUnit_natural {A B : Scheme.{u}} (a : A ⟶ B)
    {F G : B.Modules} (φ : F ⟶ G) :
    φ.app ⊤ ≫ tensorSectionsUnit a G =
      tensorSectionsUnit a F ≫ ((tensorPullback a).map φ).app ⊤ :=
  sectionsUnitOf_natural a (tensorPullback a)
    (Classical.choose (exists_tensorPullbackAdjunction a)) φ

private theorem sectionsRestriction_natural {X : Scheme.{u}}
    {F G : X.Modules} (φ : F ⟶ G) {U V : X.Etale} (g : V ⟶ U) :
    ((tensorPullback U.hom).map φ).app ⊤ ≫ etaleTensorSectionsRestriction G g =
      etaleTensorSectionsRestriction F g ≫ ((tensorPullback V.hom).map φ).app ⊤ :=
  sectionsRestrictionOf_natural (@tensorPullback)
    (fun {_A _B} a ↦ Classical.choose (exists_tensorPullbackAdjunction a))
    (@tensorSectionsComp) φ g

private noncomputable def etaleSectionsMap {X : Scheme.{u}}
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    etaleTensorSectionsSheaf F ⟶ etaleTensorSectionsSheaf G :=
  ⟨{ app := fun U ↦ ((tensorPullback U.unop.hom).map φ).app ⊤
     naturality := fun _ _ g ↦ (sectionsRestriction_natural φ g.unop).symm }⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem terminal_structure_isIso (X : Scheme.{u}) :
    IsIso (⊤_ X.Etale).hom := by
  let e : (⊤_ X.Etale) ≅ Scheme.Etale.mk (𝟙 X) := terminalIsTerminal.uniqueUpToIso
    (MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale.{u}) X)
  have h : (Scheme.Etale.forget X ⋙ Over.forget X).map e.hom = (⊤_ X.Etale).hom := by
    have h := e.hom.w
    change e.hom.left ≫ 𝟙 X = (⊤_ X.Etale).hom at h
    erw [Category.comp_id] at h
    exact h
  rw [← h]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionsUnitOf_isIso {A B : Scheme.{u}} (a : A ⟶ B)
    (L : B.Modules ⥤ A.Modules) (adj : L ⊣ pushforward a)
    [(pushforward a).IsEquivalence] (F : B.Modules) :
    IsIso (sectionsUnitOf a L adj F) := by
  have : IsIso (adj.unit.app F) := inferInstance
  have : IsIso (homOfLE a.preimage_top.ge) :=
    homOfLE_isIso_of_eq _ a.preimage_top
  unfold sectionsUnitOf
  infer_instance

private theorem sectionsUnit_isIso {A B : Scheme.{u}} (a : A ⟶ B) [IsIso a]
    (F : B.Modules) : IsIso (tensorSectionsUnit a F) := by
  let E : B.Modules ≌ A.Modules :=
    CategoryTheory.Equivalence.mk (pushforward (inv a)) (pushforward a)
      ((pushforwardId B).symm ≪≫
        pushforwardCongr (by simp only [IsIso.inv_hom_id]) ≪≫ (pushforwardComp _ _).symm)
      (pushforwardComp _ _ ≪≫
        pushforwardCongr (by simp only [IsIso.hom_inv_id]) ≪≫ pushforwardId A)
  let : (pushforward a).IsEquivalence := inferInstanceAs E.inverse.IsEquivalence
  exact sectionsUnitOf_isIso a (tensorPullback a)
    (Classical.choose (exists_tensorPullbackAdjunction a)) F

/-- Étale and Zariski cohomology of quasi-coherent modules agree naturally in the module.
The morphisms `m` have exactly the prescribed components `Γ(U, u^*φ)`. The family `c`
is chosen simultaneously for all quasi-coherent modules and all nonnegative degrees.
In degree zero, its value on the canonical image of a global section is that section
pulled back to the terminal étale object, i.e. the identity under `id_X^*F ≅ F`.
We use the standard large Ext model of étale cohomology `Sheaf.H`; it computes the
right-derived global sections of `def-weil-pbc-etale-cohomology`. This changes no sheaf
or section group and places no smallness hypothesis on `X` or `F`.

Source: Stacks Project, Descent, Proposition 03DW (2), and Étale Cohomology, Theorem 03P2
(blueprint: lem-sc-etale-zariski-qcoh-comparison).

Proof:
1. Construct the sheaf map with components `Γ(U,u^*φ)`. The naturality of the
   adjunction unit on sections, of the tensor composition isomorphism, and of
   equality transport proves compatibility with all restrictions.
2. In degree `n+1`, compose `zariskiModuleAbelianCohomologyAgree` with
   `etaleZariskiAbelianPositiveComparison`. Evaluate the former natural
   isomorphism's naturality equation and then use the latter's naturality equation.
3. In degree zero, the left-exact global-sections functor identifies its zeroth
   derived functor with sections. The chosen terminal étale object's structure
   morphism is an isomorphism, by uniqueness of terminal objects. Pushforward along
   it is an equivalence, so the tensor-pullback adjunction unit is an isomorphism.
   Compose these two section equivalences with the inverse of `Sheaf.H.equiv₀`.
   Their naturality proves the degree-zero square. Cancellation of the canonical
   derived-zero map and of `Sheaf.H.equiv₀` gives precisely `tensorSectionsUnit`
   on every section. Assemble degree zero and all positive degrees by `Nat.casesOn`. -/
theorem etale_zariski_qcoh_comparison (X : Scheme.{u}) :
    ∃ m : ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent],
        (F ⟶ G) → (etaleTensorSectionsSheaf F ⟶ etaleTensorSectionsSheaf G),
      (∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
          (φ : F ⟶ G) (U : X.Etale),
        (m F G φ).hom.app (op U) = ((tensorPullback U.hom).map φ).app ⊤) ∧
      ∃ c : ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
          ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≃+
            @Sheaf.H _ _ X.smallEtaleTopology (etaleTensorSectionsSheaf F)
              inferInstance (HasExt.standard _) q,
        (∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
            (φ : F ⟶ G) (q : ℕ)
            (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F),
          c G q (((RingedSpace.moduleCohomology X.toRingedSpace q).map φ).hom x) =
            @Sheaf.H.map _ _ X.smallEtaleTopology inferInstance (HasExt.standard _)
              _ _ (m F G φ) q (c F q x)) ∧
        (∀ (F : X.Modules) [F.IsQuasicoherent] (s : Γ(F, ⊤)),
          @Sheaf.H.equiv₀ _ _ X.smallEtaleTopology inferInstance (HasExt.standard _)
            (etaleTensorSectionsSheaf F) _ terminalIsTerminal
            (c F 0 (((@Functor.toRightDerivedZero _ _ _ _ _
              (@InjectiveResolution.instHasInjectiveResolutions _ _ _
                (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2) _
              (RingedSpace.globalSectionsFunctor X.toRingedSpace) _).app F).hom s)) =
          tensorSectionsUnit (⊤_ X.Etale).hom F s) := by
  classical
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : EnoughInjectives
      (Sheaf (_root_.Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
    @IsGrothendieckAbelian.enoughInjectives _ _ _
      (Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
        (_root_.Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
  let : HasExt.{u}
      (Sheaf (_root_.Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let V := forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    AddCommGrpCat.{u}
  let : PreservesFiniteLimits S :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings X.toRingedSpace) (op ⊤)))
  let τ := S.rightDerivedZeroIsoSelf
  have : IsIso (⊤_ X.Etale).hom := terminal_structure_isIso X
  have hunit (F : X.Modules) : IsIso (tensorSectionsUnit (⊤_ X.Etale).hom F) :=
    sectionsUnit_isIso _ F
  let e₀ (F : X.Modules) [F.IsQuasicoherent] :=
    @Sheaf.H.equiv₀.{u + 1, u, u, u + 1} _ _ X.smallEtaleTopology
      inferInstance (HasExt.standard _) (etaleTensorSectionsSheaf F) _ terminalIsTerminal
  let c₀ (F : X.Modules) [F.IsQuasicoherent] :
      ((RingedSpace.moduleCohomology X.toRingedSpace 0).obj F) ≃+
      @Sheaf.H _ _ X.smallEtaleTopology (etaleTensorSectionsSheaf F)
        inferInstance (HasExt.standard _) 0 :=
    ((V.mapIso (τ.app F)).addCommGroupIsoToAddEquiv.trans
      (asIso (tensorSectionsUnit (⊤_ X.Etale).hom F)).addCommGroupIsoToAddEquiv).trans
        (e₀ F).symm
  have hc₀ (F : X.Modules) [F.IsQuasicoherent]
      (x : (RingedSpace.moduleCohomology X.toRingedSpace 0).obj F) :
      e₀ F (c₀ F x) =
        tensorSectionsUnit (⊤_ X.Etale).hom F ((τ.hom.app F).hom x) :=
    (e₀ F).apply_symm_apply _
  obtain ⟨α, _⟩ := zariskiModuleAbelianCohomologyAgree X
  obtain ⟨β, hβ⟩ := etaleZariskiAbelianPositiveComparison X
    (fun F G _ _ φ ↦ etaleSectionsMap F G φ) (fun _ _ _ _ _ _ ↦ rfl)
  let cpos (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :=
    ((α (n + 1)).app F).addCommGroupIsoToAddEquiv.trans (β F n)
  refine ⟨fun F G _ _ φ ↦ etaleSectionsMap F G φ, (fun _ _ _ _ _ _ ↦ rfl),
    (fun F _ q ↦ Nat.casesOn q (c₀ F) (cpos F)), ?_, ?_⟩
  · intro F G _ _ φ q x
    cases q with
    | zero =>
      change c₀ G (((RingedSpace.moduleCohomology X.toRingedSpace 0).map φ).hom x) =
        @Sheaf.H.map.{u + 1, u, u, u + 1} _ _ X.smallEtaleTopology inferInstance (HasExt.standard _)
          _ _ (etaleSectionsMap F G φ) 0 (c₀ F x)
      apply (e₀ G).injective
      rw [← @Sheaf.H.equiv₀_naturality.{u + 1, u, u, u + 1}
        _ _ _ _ (HasExt.standard _) _ terminalIsTerminal _ _ (etaleSectionsMap F G φ)]
      change (e₀ G) (c₀ G _) =
        (etaleSectionsMap F G φ).hom.app (op (⊤_ X.Etale)) ((e₀ F) (c₀ F x))
      erw [hc₀ G, hc₀ F]
      have ht := congrArg (fun f ↦ (V.map f).hom x) (τ.hom.naturality φ)
      change (τ.hom.app G).hom
          (((RingedSpace.moduleCohomology X.toRingedSpace 0).map φ).hom x) =
        φ.app ⊤ ((τ.hom.app F).hom x) at ht
      change tensorSectionsUnit (⊤_ X.Etale).hom G
          ((τ.hom.app G).hom
            (((RingedSpace.moduleCohomology X.toRingedSpace 0).map φ).hom x)) =
        ((tensorPullback (⊤_ X.Etale).hom).map φ).app ⊤
          (tensorSectionsUnit (⊤_ X.Etale).hom F ((τ.hom.app F).hom x))
      rw [ht]
      exact congrArg (fun f ↦ f ((τ.hom.app F).hom x))
        (sectionsUnit_natural (⊤_ X.Etale).hom φ)
    | succ n =>
      change cpos G n
          (((RingedSpace.moduleCohomology X.toRingedSpace (n + 1)).map φ).hom x) =
        @Sheaf.H.map.{u + 1, u, u, u + 1} _ _ X.smallEtaleTopology inferInstance (HasExt.standard _)
          _ _ (etaleSectionsMap F G φ) (n + 1) (cpos F n x)
      have ht := congrArg (fun f ↦ f.hom x) ((α (n + 1)).hom.naturality φ)
      change ((α (n + 1)).hom.app G)
          (((RingedSpace.moduleCohomology X.toRingedSpace (n + 1)).map φ).hom x) =
        (((Sheaf.cohomologyPresheafFunctor
          (_root_.Opens.grothendieckTopology X.carrier) (n + 1)).map
            ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).map φ)).app (op ⊤))
          (((α (n + 1)).hom.app F) x) at ht
      change β G n (((α (n + 1)).hom.app G)
        (((RingedSpace.moduleCohomology X.toRingedSpace (n + 1)).map φ).hom x)) = _
      rw [ht]
      exact hβ F G φ n _
  · intro F _ s
    change (e₀ F) (c₀ F (S.toRightDerivedZero.app F s)) =
      tensorSectionsUnit (⊤_ X.Etale).hom F s
    erw [hc₀ F]
    have ht := S.rightDerivedZeroIsoSelf_inv_hom_id_app F
    have hs := congrArg (fun f ↦ f.hom s) ht
    change (τ.hom.app F).hom (S.toRightDerivedZero.app F s) = s at hs
    change tensorSectionsUnit (⊤_ X.Etale).hom F
      ((τ.hom.app F).hom (S.toRightDerivedZero.app F s)) = _
    rw [hs]


end AlgebraicGeometry.Scheme.Modules
