/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.QuasiCoherenceScalarRestriction
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover
import WeilConjectures.AlgebraicGeometry.AffineModuleTensorUnitSections
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Affine tensor comparison isomorphisms

Source: Stacks Project, Morphisms, Lemma 01SB.
(blueprint: lem-weil-pbc-affine-module-tensor-comparison-isIso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {U X : Scheme.{u}} (f : U ⟶ X)

local instance instHasLeftKanExtension_affineModuleTensorComparisonIsIso
    : ∀ (F : (Opens X)ᵒᵖ ⥤ CommRingCat.{u}),
    (Opens.map f.base).op.HasLeftKanExtension F := fun F ↦ by
  have : (Opens.map f.base).op.HasPointwiseLeftKanExtension F := fun _ ↦ inferInstance
  exact Functor.HasLeftKanExtension.mk _
    (Functor.pointwiseLeftKanExtensionUnit (Opens.map f.base).op F)

set_option hygiene false in
local notation "𝓙" T => Opens.grothendieckTopology T
set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a
set_option hygiene false in
local notation "A" => (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
set_option hygiene false in
local notation "ρ" => (show X.sheaf ⟶ A from ⟨f.c⟩)
set_option hygiene false in
local notation "R" => SheafOfModules.pushforward.{u} (F := Opens.map f.base)
  (S := 𝓡 A) (R := U.ringCatSheaf) (𝟙 (𝓡 A))
set_option hygiene false in
local notation "S" => SheafOfModules.restrictScalars.{u} (𝓻 ρ)
set_option hygiene false in
local notation "I" => TopCat.Sheaf.inverseImageModule f.base A
set_option hygiene false in
local notation "IA" => TopCat.Sheaf.inverseImageRing f.base A
set_option hygiene false in
local notation "r₀" => tensorPullbackRingMap f
set_option hygiene false in
local notation "t₀" => (TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map ρ
set_option hygiene false in
local notation "e₀" =>
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)).homEquiv A U.sheaf).symm (𝟙 A)
set_option hygiene false in
local notation "adj₀" => Classical.choose (exists_tensorPullbackAdjunction f)
set_option hygiene false in
local notation "qU" => SheafOfModules.isQuasicoherent U.ringCatSheaf
set_option hygiene false in
local notation "qA" => SheafOfModules.isQuasicoherent (𝓡 A)

set_option hygiene false in
local notation "fV" V => (Opens.map f.base).op.obj V

/-- The canonical affine tensor comparisons are isomorphisms on quasi-coherent modules.
The construction data and the formulas on units are hypotheses, so this statement only
performs the affine inverse calculation and the passage from affine opens to sheaves.
Source: Stacks Project, Morphisms, Lemma 01SB, last two paragraphs and key algebra observation.
(blueprint: lem-weil-pbc-affine-module-tensor-comparison-isIso).

Proof:
1. On an affine open V of X, W = f⁻¹(V) is affine. Write R = O_X(V), C = O_U(W),
   and N = G(V). The affine-section pullback formula identifies the first tensor
   operation with C tensor_R N; the change-of-rings affine-section formula identifies
   the second with C tensor_(C tensor_R C) (C tensor_R N).
2. The balanced map c tensor (b tensor n) ↦ cb n is linear for the C-action on the
   first factor. Its inverse is n ↦ 1 tensor (1 tensor n). Balancing moves b to c,
   and then moves cb to n, proving the inverse identity on generators; additivity
   extends the identity to every tensor. These formulas also prove C-linearity.
3. The formula for κ on the pullback unit and the formula for γ show that β on V
   is exactly this inverse. Hence β is bijective on the affine basis. For arbitrary
   opens its algebra-linearity follows by restriction to this basis and sheaf separation.
4. The counit triangle identity and the factorization equation for α show that α on W
   is the balanced map of step 2, for N = F(W). Hence α is bijective on these W.
5. H preserves quasi-coherence by hH; pushforward does so by affine pushforward and
   scalar restriction. Both source and target of the comparisons are quasi-coherent.
   Detect α on the affine cover of U pulled back from an affine cover of X, and detect
   the underlying structure-sheaf map of β on the affine cover of X. An inverse to an
   invertible algebra-linear map is algebra-linear, so β is invertible as an A-module map.
-/
theorem affine_module_tensor_comparison_isIso [IsAffineHom f]
     (B : U.toTopCat.Sheaf CommRingCat.{u})
      (b : U.sheaf ⟶ B) (t : IA ⟶ B) (ε : B ⟶ U.sheaf)
    (hring : IsPushout r₀ t₀ b t ∧ b ≫ ε = 𝟙 U.sheaf ∧ t ≫ ε = e₀)
     (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
        (pobj : ∀ G, P.obj G = SheafOfModules.changeOfRings.{u, u, u} t (I G))
        (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f)
    (hP : (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
          P.map a = eqToHom (pobj G) ≫
            SheafOfModules.changeOfRingsHom.{u, u, u} t (I G)
              (TopCat.Sheaf.inverseImageModuleMap f.base A G a) ≫
            eqToHom (pobj G').symm) ∧
        (∀ (G : SheafOfModules.{u} (𝓡 A)) (V : (Opens X)ᵒᵖ) (g : G.val.obj V),
          ((eqToHom (pobj G)).val.app (fV V))
            ((κ.inv.app G).val.app (fV V)
              (((adj₀).unit.app ((S).obj G)).val.app V g)) =
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
              (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t (I G))).app
                (fV V)
                ((1 : B.obj.obj (fV V)) ⊗ₜ[(IA).obj.obj (fV V),(t.hom.app (fV V)).hom]
                  (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                    (Opens.map f.base) AddCommGrpCat.{u} (𝓙 X) (𝓙 U)).unit.app
                      ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g))))
     (H : SheafOfModules.{u} (𝓡 A) ⥤ U.Modules)
          (hobj : ∀ G, H.obj G = SheafOfModules.changeOfRings.{u, u, u} ε (P.obj G))
          (γ : S ⋙ tensorPullback f ⟶ H)
    (hH : (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
            H.map a = eqToHom (hobj G) ≫
              SheafOfModules.changeOfRingsHom.{u, u, u} ε (P.obj G) (P.map a) ≫
              eqToHom (hobj G').symm) ∧
          (∀ (G : SheafOfModules.{u} (𝓡 A)) (W : (Opens U)ᵒᵖ)
              (p : (P.obj G).val.obj W),
            ((eqToHom (hobj G)).val.app W)
              ((γ.app G).val.app W ((κ.hom.app G).val.app W p)) =
              ((PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
                (SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε (P.obj G))).app W
                  ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W,(ε.hom.app W).hom] p)) ∧
          (∀ G : SheafOfModules.{u} (𝓡 A),
            G.IsQuasicoherent → (H.obj G).IsQuasicoherent))
     (α : R ⋙ H ⟶ 𝟭 U.Modules) (β : 𝟭 (SheafOfModules.{u} (𝓡 A)) ⟶ H ⋙ R)
    (hcomp : (∀ F : U.Modules, γ.app ((R).obj F) ≫ α.app F = (adj₀).counit.app F) ∧
            (∀ G : SheafOfModules.{u} (𝓡 A),
              (S).map (β.app G) = ((adj₀).homEquiv ((S).obj G) (H.obj G)) (γ.app G))) :
(∀ F : U.Modules, F.IsQuasicoherent → IsIso (α.app F)) ∧
            (∀ G : SheafOfModules.{u} (𝓡 A), G.IsQuasicoherent → IsIso (β.app G)) := by
  classical
  let RA := 𝓡 A
  let Rf : U.Modules ⥤ SheafOfModules.{u} RA := R
  let Sf : SheafOfModules.{u} RA ⥤ X.Modules := S
  let adj := adj₀
  have hA : (Scheme.CommAlgebraSheaf.toModule (Under.mk ρ)).IsQuasicoherent := by
    have := IsSeparated.of_isAffineHom f
    have := SheafOfModules.isQuasicoherent_unit.{u, u, u} («R» := U.ringCatSheaf)
    exact isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated f
      (SheafOfModules.unit U.ringCatSheaf)
  have hβ (G : SheafOfModules.{u} RA) (hG : G.IsQuasicoherent) :
      IsIso (β.app G) := by
    have hBasis : Opens.IsBasis (Set.range (fun V : X.affineOpens ↦ V.1)) := by
      rw [Subtype.range_coe]
      exact X.isBasis_affineOpens
    have : IsIso ((SheafOfModules.toSheaf RA).map (β.app G)) := by
      apply TopCat.Sheaf.isIso_iff_isIso_basis hBasis
      intro V
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      exact affine_module_tensor_unit_sections_bijective f B b t ε hring P pobj κ hP
        H hobj γ hH β hcomp.2 G hG V.1 V.2
    exact isIso_of_reflects_iso (β.app G) (SheafOfModules.toSheaf RA)
  refine ⟨?_, hβ⟩
  intro F hF
  have hF' : ((𝟭 U.Modules).obj F).IsQuasicoherent := hF
  have := IsSeparated.of_isAffineHom f
  have hRF : (Rf.obj F).IsQuasicoherent := by
    apply (quasiCoherent_iff_restrictScalars X (Under.mk ρ) hA (Rf.obj F)).mpr
    exact isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated f F
  have hHF : ((Rf ⋙ H).obj F).IsQuasicoherent := hH.2.2 (Rf.obj F) hRF
  have htriangle : β.app (Rf.obj F) ≫ Rf.map (α.app F) = 𝟙 (Rf.obj F) := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext m
    -- Evaluate the adjoint equation and counit factorization on sections.
    have hb := congrArg (fun k ↦ k.val.app V m) (hcomp.2 (Rf.obj F))
    simp only [Adjunction.homEquiv_unit] at hb
    have ha := congrArg (fun k ↦ k.val.app (fV V)
      ((adj.unit.app (Sf.obj (Rf.obj F))).val.app V m)) (hcomp.1 F)
    have ht := congrArg (fun k ↦ k.val.app V m) (adj.right_triangle_components F)
    exact (congrArg (fun n ↦ (α.app F).val.app (fV V) n) hb).trans (ha.trans ht)
  have := hβ (Rf.obj F) hRF
  have : IsIso (β.app (Rf.obj F) ≫ Rf.map (α.app F)) := by
    rw [htriangle]
    infer_instance
  have : IsIso (Rf.map (α.app F)) :=
    IsIso.of_isIso_comp_left (β.app (Rf.obj F)) (Rf.map (α.app F))
  apply Hom.isIso_of_bijective_on_affine_open_cover (α.app F)
    (fun V : X.affineOpens ↦ f ⁻¹ᵁ V.1)
  · apply Opens.ext
    ext x
    simp only [Opens.coe_iSup, Set.mem_iUnion]
    constructor
    · intro _
      trivial
    intro _
    obtain ⟨V, hV, hxV, _⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show f.base x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨⟨V, hV⟩, hxV⟩
  · intro V
    exact V.2.preimage f
  · intro V
    have hEval : IsIso ((Rf.map (α.app F)).val.app (op V.1)) :=
      (SheafOfModules.evaluation RA (op V.1)).map_isIso (Rf.map (α.app F))
    exact ConcreteCategory.bijective_of_isIso ((Rf.map (α.app F)).val.app (op V.1))

end
end AlgebraicGeometry.Scheme.Modules
