/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Local lifting of maps from finite free constant sheaves

Source: Stacks Project, Tag 093U, `lemma-kernel-finite-locally-constant`, extension paragraph.
(blueprint: lem-pc-finite-free-constant-local-lift)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- A linear lift of the adjunct over an étale object yields a lift from the constant sheaf
on that object. This statement needs neither an epimorphism nor a free module.

Source: Stacks Project, Tag 093U, extension paragraph: extend the lifted generators linearly
and obtain the morphism from the constant sheaf.
(blueprint: lem-pc-finite-free-constant-local-lift)

Proof: Identify étale pullback with restriction along the localization functor using
Etale.upperStarIsoLocalizationRestriction. Under this identification its sections over the
terminal object are F(U). Apply the constant-sheaf/global-sections adjunction to b to obtain
the required morphism r. Naturality in the target identifies the adjunct of r followed by
f with b followed by f(U). The assumed equation identifies this with the restriction of
the adjunct of a. Naturality in the site identifies that last adjunct with the adjunct of
the pullback of a precomposed with the inverse constant-sheaf comparison. This comparison
is upperStarConstantSheafIso, since it is defined by uniqueness of left adjoints to the
same sections functor. Injectivity of the adjunction homEquiv gives the asserted equality.
The argument applies to the zero module, empty schemes, and noncommutative rings. -/
private theorem exists_constant_lift_of_sections_lift {X : Scheme.{u}}
    {Λ : Type (u + 1)} [Ring Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : F ⟶ G) (M : ModuleCat.{u + 1} Λ)
    (a : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ⟶ G)
    (U : X.Etale) (b : M ⟶ F.obj.obj (Opposite.op U))
    (hb : b ≫ f.hom.app (Opposite.op U) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app (Opposite.op U) ≫
        a.hom.app (Opposite.op U)) :
    ∃ r : (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ⟶
        (Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj F,
      r ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom).map f =
        ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) U.hom).app M).inv ≫
          (Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom).map a := by
  let A := ModuleCat.{u + 1} Λ
  let L := Etale.upperStar A U.hom
  let R := Etale.localizationRestriction A U.hom U.prop
  let adjL := Etale.upperStarLowerStarAdjunction A U.hom
  let adjR := Etale.localizationRestrictionLowerStarAdjunction A U.hom U.prop
  let k : L ≅ R := Etale.upperStarIsoLocalizationRestriction A U.hom U.prop
  let adjX := constantSheafAdj X.smallEtaleTopology A terminalIsTerminal
  let adjU := constantSheafAdj U.left.smallEtaleTopology A terminalIsTerminal
  let β := Etale.lowerStarCompSheafSectionsTerminalIso A U.hom
  let adj := (adjX.comp adjL).ofNatIsoRight β
  let W : X.Etale := (MorphismProperty.Over.map ⊤ U.prop).obj (⊤_ U.left.Etale)
  let e : W ≅ U :=
    (MorphismProperty.Over.map ⊤ U.prop).mapIso
      (terminalIsTerminal.uniqueUpToIso (MorphismProperty.Over.mkIdTerminal _ _)) ≪≫
      MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp U.hom).symm
  let t : (constantSheaf U.left.smallEtaleTopology A).obj M ⟶ R.obj F :=
    (adjU.homEquiv M (R.obj F)).symm (b ≫ F.obj.map e.hom.op)
  refine ⟨t ≫ k.inv.app F, ?_⟩
  change (t ≫ k.inv.app F) ≫ L.map f =
    (upperStarConstantSheafIso A U.hom).inv.app M ≫ L.map a
  rw [← cancel_epi ((upperStarConstantSheafIso A U.hom).hom.app M)]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  apply (adj.homEquiv M (L.obj G)).injective
  have hc (m : (constantSheaf U.left.smallEtaleTopology A).obj M ⟶ L.obj G) :
      adj.homEquiv M (L.obj G)
        ((upperStarConstantSheafIso A U.hom).hom.app M ≫ m) =
      adjU.homEquiv M (L.obj G) m := by
    change adj.homEquiv _ _ ((adj.leftAdjointUniq adjU).hom.app M ≫ m) = _
    rw [adj.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
      Adjunction.homEquiv_unit]
    rfl
  simp only [Category.assoc]
  rw [hc]
  apply (cancel_mono ((k.hom.app G).hom.app (Opposite.op (⊤_ U.left.Etale)))).mp
  change adjU.homEquiv M (L.obj G) (t ≫ k.inv.app F ≫ L.map f) ≫
      ((sheafSections U.left.smallEtaleTopology A).obj (Opposite.op (⊤_ U.left.Etale))).map
        (k.hom.app G) = _
  rw [← adjU.homEquiv_naturality_right]
  have ht : (t ≫ k.inv.app F ≫ L.map f) ≫ k.hom.app G = t ≫ R.map f := by
    simp only [Category.assoc]
    rw [k.hom.naturality f, k.inv_hom_id_app_assoc]
  rw [ht, adjU.homEquiv_naturality_right]
  rw [show t = (adjU.homEquiv M (R.obj F)).symm (b ≫ F.obj.map e.hom.op) from rfl,
    Equiv.apply_symm_apply]
  rw [show adj = (adjX.comp adjL).ofNatIsoRight β from rfl,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change (b ≫ F.obj.map e.hom.op) ≫ (R.map f).hom.app (Opposite.op (⊤_ U.left.Etale)) =
    (adjX.homEquiv M _ (adjL.homEquiv _ _ (L.map a)) ≫ β.hom.app (L.obj G)) ≫
      (k.hom.app G).hom.app (Opposite.op (⊤_ U.left.Etale))
  rw [adjL.homEquiv_unit, adjL.unit_naturality a,
    adjX.homEquiv_naturality_right]
  simp only [Category.assoc]
  erw [← β.hom.naturality (k.hom.app G)]
  change (b ≫ F.obj.map e.hom.op) ≫ f.hom.app (Opposite.op W) =
    adjX.homEquiv M G a ≫
      (adjL.unit.app G).hom.app (Opposite.op (⊤_ X.Etale)) ≫
      ((Etale.lowerStar A U.hom).map (k.hom.app G)).hom.app (Opposite.op (⊤_ X.Etale)) ≫
      β.hom.app (R.obj G)
  have hk : (adjL.unit.app G).hom.app (Opposite.op (⊤_ X.Etale)) ≫
        ((Etale.lowerStar A U.hom).map (k.hom.app G)).hom.app (Opposite.op (⊤_ X.Etale)) =
      (adjR.unit.app G).hom.app (Opposite.op (⊤_ X.Etale)) := by
    exact congrArg (fun h ↦ h.hom.app (Opposite.op (⊤_ X.Etale)))
      (Adjunction.unit_leftAdjointUniq_hom_app adjL adjR G)
  rw [← Category.assoc ((adjL.unit.app G).hom.app _), hk]
  let q := (PreservesTerminal.iso U.hom.Etale).inv
  let p := (MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ U.hom
    U.prop _root_.trivial).counit.app (⊤_ X.Etale)
  have hη : (adjR.unit.app G).hom.app (Opposite.op (⊤_ X.Etale)) = G.obj.map p.op := by
    rfl
  have hβ : β.hom.app (R.obj G) =
      G.obj.map ((MorphismProperty.Over.map ⊤ U.prop).map q).op := by
    rfl
  rw [hη, hβ, ← G.obj.map_comp, ← op_comp]
  have hp : (MorphismProperty.Over.map ⊤ U.prop).map q ≫ p =
      terminal.from W := terminalIsTerminal.hom_ext _ _
  rw [hp]
  let τ := toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M) ≫ a.hom
  have hτ {V W : X.Etale} (g : V ⟶ W) :
      τ.app (Opposite.op W) ≫ G.obj.map g.op = τ.app (Opposite.op V) :=
    (τ.naturality g.op).symm.trans (Category.id_comp _)
  calc
    (b ≫ F.obj.map e.hom.op) ≫ f.hom.app (Opposite.op W) =
        (b ≫ f.hom.app (Opposite.op U)) ≫ G.obj.map e.hom.op := by
      rw [Category.assoc, f.hom.naturality, ← Category.assoc]
    _ = τ.app (Opposite.op U) ≫ G.obj.map e.hom.op := by rw [hb]; rfl
    _ = τ.app (Opposite.op W) := hτ e.hom
    _ = adjX.homEquiv M G a ≫ G.obj.map (terminal.from W).op := by
      rw [show adjX = constantSheafAdj X.smallEtaleTopology A terminalIsTerminal from rfl,
        constantSheafAdj_homEquiv_apply]
      exact (hτ (terminal.from W)).symm

/-- A map from a finite free constant sheaf locally lifts along any epimorphism.

Source: Stacks Project, Tag 093U, `lemma-kernel-finite-locally-constant`, extension paragraph,
lifting the finitely many generators.
(blueprint: lem-pc-finite-free-constant-local-lift)

Proof: By the constant-sheaf/global-sections adjunction, the given map is a linear map
from the free module to the sections of G over the terminal etale object. Evaluate on
the standard basis. An epimorphism of module-valued sheaves is locally surjective after
forgetting to sets, so each of these finitely many sections lifts on a covering sieve.
Intersect these finitely many sieves; the intersection is covering by the topology axioms.
For each point of X choose an arrow in the intersection whose image contains that point.
This gives a cover indexed in the universe of X. On each cover member all basis sections
have lifts; extend them linearly and use the constant-sheaf adjunction on that member to
obtain r. The equality after composition holds on every basis element, hence on the free
module and, by the adjunction, on its constant sheaf. The comparison with restriction is
precisely upperStarConstantSheafIso, natural in the free module. When n is zero no
sections need lifting and the identity cover suffices; on an empty base use the empty cover.
This argument needs neither a finite coefficient ring nor a constant target. -/
theorem exists_finiteFreeConstant_local_lift {X : Scheme.{u}}
    {Λ : Type (u + 1)} [Ring Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : F ⟶ G) [Epi f] (n : ℕ)
    (a : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ (Fin n → Λ)) ⟶ G) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i,
      ∃ r : (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin n → Λ)) ⟶
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj F,
        r ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).map f =
          ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) (𝒰.f i)).app
            (ModuleCat.of Λ (Fin n → Λ))).inv ≫
            (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).map a := by
  classical
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  let P := ModuleCat.of Λ (Fin n → Λ)
  let s : P ⟶ G.obj.obj (Opposite.op T) :=
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).homEquiv P G a
  let e := Pi.basisFun Λ (Fin n)
  have : Sheaf.IsLocallySurjective f :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := f)).2 inferInstance
  let S : Sieve T := ⨅ j : Fin n, Presheaf.imageSieve f.hom (s (e j))
  have hS : S ∈ X.smallEtaleTopology T :=
    X.smallEtaleTopology.iInf_mem _ fun j ↦
      Presheaf.imageSieve_mem X.smallEtaleTopology f.hom (s (e j))
  choose V g hg hx using (mem_smallEtaleTopology_iff S).mp hS
  have hmap (x : X) : (g x).left = (V x).hom := by
    have h := (g x).w
    change (g x).left ≫ 𝟙 X = (V x).hom at h
    exact (Category.comp_id _).symm.trans h
  let 𝒰 : Cover.{u} etalePrecoverage X :=
    Cover.mkOfCovers X (fun x ↦ (V x).left) (fun x ↦ (V x).hom)
      (fun x ↦ by
        obtain ⟨y, hy⟩ := hx x
        rw [hmap x] at hy
        exact ⟨x, y, hy⟩) (fun x ↦ (V x).prop)
  refine ⟨𝒰, fun x ↦ ?_⟩
  have hl (j : Fin n) : ∃ y : F.obj.obj (Opposite.op (V x)),
      f.hom.app (Opposite.op (V x)) y = G.obj.map (g x).op (s (e j)) := by
    exact (iInf_le (fun j ↦ Presheaf.imageSieve f.hom (s (e j))) j) _ (hg x)
  choose y hy using hl
  let b : P ⟶ F.obj.obj (Opposite.op (V x)) := ModuleCat.ofHom (e.constr ℤ y)
  have hb : b ≫ f.hom.app (Opposite.op (V x)) = s ≫ G.obj.map (g x).op := by
    apply ModuleCat.hom_ext
    apply e.ext
    intro j
    simpa [b] using hy j
  apply exists_constant_lift_of_sections_lift f P a (V x) b
  rw [hb]
  dsimp only [s]
  rw [constantSheafAdj_homEquiv_apply, Category.assoc, ← a.hom.naturality,
    ← Category.assoc]
  congr 1
  exact ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj P)).naturality
    (g x).op).symm.trans (Category.id_comp _)

end AlgebraicGeometry.Scheme
