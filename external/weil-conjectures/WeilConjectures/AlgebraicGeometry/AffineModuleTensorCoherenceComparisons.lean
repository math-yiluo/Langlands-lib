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
import WeilConjectures.AlgebraicGeometry.AffineModuleTensorAlgebraQuasiCoherent
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import WeilConjectures.AlgebraicGeometry.QuasiCoherenceScalarRestriction
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebraChangeOfRings
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.AffineModuleTensorCounitFactor
import WeilConjectures.AlgebraicGeometry.AffineModuleTensorUnitLift
/-! # Affine module tensor CoherenceComparisons

Source: Stacks Project, Morphisms, Lemma 01SB.
(blueprint: lem-weil-pbc-affine-module-tensor-coherence-comparisons).
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

local instance instHasLeftKanExtension_affineModuleTensorCoherenceComparisons
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

private theorem naturalFactor {C : Type*} [Category C] (F H : C ⥤ C)
    (γ : F ⟶ H) (δ : F ⟶ 𝟭 C)
    (h : ∀ X, (∃ a : H.obj X ⟶ X, γ.app X ≫ a = δ.app X) ∧ Epi (γ.app X)) :
    ∃ α : H ⟶ 𝟭 C, ∀ X, γ.app X ≫ α.app X = δ.app X := by
  classical
  let a (X : C) := Classical.choose (h X).1
  have ha (X : C) : γ.app X ≫ a X = δ.app X := Classical.choose_spec (h X).1
  refine ⟨{ app := a, naturality := ?_ }, ha⟩
  intro X Y k
  have : Epi (γ.app X) := (h X).2
  apply (cancel_epi (γ.app X)).mp
  change γ.app X ≫ H.map k ≫ a Y = γ.app X ≫ a X ≫ k
  rw [← Category.assoc, ← γ.naturality k, Category.assoc, ha Y,
    ← Category.assoc, ha X]
  exact δ.naturality k

private theorem liftNatural {C D : Type*} [Category C] [Category D]
    (Q : C ⥤ D) (H : C ⥤ C) (τ : Q ⟶ H ⋙ Q)
    (hinj : ∀ X Y, Function.Injective (Q.map : (X ⟶ Y) → _))
    (h : ∀ X, ∃ a : X ⟶ H.obj X, Q.map a = τ.app X) :
    ∃ β : 𝟭 C ⟶ H, ∀ X, Q.map (β.app X) = τ.app X := by
  classical
  let a (X : C) := Classical.choose (h X)
  have ha (X : C) : Q.map (a X) = τ.app X := Classical.choose_spec (h X)
  refine ⟨{ app := a, naturality := ?_ }, ha⟩
  intro X Y k
  apply hinj _ _
  simp only [Functor.id_map, Functor.map_comp]
  rw [ha X, ha Y]
  exact τ.naturality k

private theorem tensorExtension_quasiCoherent [IsAffineHom f]
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B) (t : IA ⟶ B)
    (ε : B ⟶ U.sheaf) (hpush : IsPushout r₀ t₀ b t) (hb : b ≫ ε = 𝟙 U.sheaf)
    (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
    (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f)
    (H : SheafOfModules.{u} (𝓡 A) ⥤ U.Modules)
    (hobj : ∀ G, H.obj G = SheafOfModules.changeOfRings.{u, u, u} ε (P.obj G)) :
    ∀ G : SheafOfModules.{u} (𝓡 A), G.IsQuasicoherent → (H.obj G).IsQuasicoherent := by
  intro G hG
  let Aalg : X.CommAlgebraSheaf := Under.mk ρ
  let Balg : U.CommAlgebraSheaf := Under.mk b
  let Calg : U.CommAlgebraSheaf := Under.mk (𝟙 U.sheaf)
  let φ : Balg ⟶ Calg := Under.homMk ε hb
  have hA : Aalg.toModule.IsQuasicoherent :=
    (affine_morphism_relative_spec X).1 f inferInstance
  have hB : Balg.toModule.IsQuasicoherent :=
    affine_module_tensor_algebra_quasiCoherent f B b t hpush
  have hC : Calg.toModule.IsQuasicoherent := by
    change (SheafOfModules.unit U.ringCatSheaf).IsQuasicoherent
    exact SheafOfModules.isQuasicoherent_unit.{u, u, u}
  have hS : ((S).obj G).IsQuasicoherent :=
    (quasiCoherent_iff_restrictScalars X Aalg hA G).mp hG
  have : ((S).obj G).IsQuasicoherent := hS
  let e : tensorPullback f ≅ pullback f :=
    (adj₀).leftAdjointUniq (pullbackPushforwardAdjunction f)
  have hT : ((tensorPullback f).obj ((S).obj G)).IsQuasicoherent :=
    (qU).prop_of_iso (e.app ((S).obj G)).symm (by infer_instance)
  have hPG : ((SheafOfModules.restrictScalars (𝓻 b)).obj (P.obj G)).IsQuasicoherent :=
    (qU).prop_of_iso (κ.app G).symm hT
  have hc := (quasiCoherent_algebra_changeOfRings U Balg Calg φ
    (P.obj G) hB hC hPG).1
  rw [hobj G]
  exact hc

private theorem scalarRestriction_injective :
    ∀ G G', Function.Injective ((S).map : (G ⟶ G') → _) := by
  intro G G' a b hab
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext g
  exact congrArg (fun z ↦ z.val.app V g) hab

private theorem comparisons_from_objectwise
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) (J : E ⥤ C) (L : D ⥤ E) (adj : L ⊣ J ⋙ Q)
    (H : C ⥤ E) (γ : Q ⋙ L ⟶ H)
    (hinj : ∀ G G', Function.Injective (Q.map : (G ⟶ G') → _))
    (hf : ∀ F : E, (∃ a : H.obj (J.obj F) ⟶ F,
      γ.app (J.obj F) ≫ a = adj.counit.app F) ∧ Epi (γ.app (J.obj F)))
    (hβ : ∀ G : C, ∃ a : G ⟶ J.obj (H.obj G),
      Q.map a = (adj.homEquiv (Q.obj G) (H.obj G)) (γ.app G)) :
    ∃ (α : J ⋙ H ⟶ 𝟭 E) (β : 𝟭 C ⟶ H ⋙ J),
      (∀ F, γ.app (J.obj F) ≫ α.app F = adj.counit.app F) ∧
      (∀ G, Q.map (β.app G) = (adj.homEquiv (Q.obj G) (H.obj G)) (γ.app G)) := by
  let δ : J ⋙ (Q ⋙ L) ⟶ 𝟭 E :=
    { app := fun F ↦ adj.counit.app F
      naturality := by
        intro F F' k
        exact adj.counit.naturality k }
  obtain ⟨α, ha⟩ := naturalFactor (J ⋙ (Q ⋙ L)) (J ⋙ H)
    (Functor.whiskerLeft J γ) δ hf
  let τ : Q ⟶ (H ⋙ J) ⋙ Q :=
    { app := fun G ↦ (adj.homEquiv (Q.obj G) (H.obj G)) (γ.app G)
      naturality := by
        intro G G' k
        rw [← adj.homEquiv_naturality_left]
        have hn : L.map (Q.map k) ≫ γ.app G' = γ.app G ≫ H.map k := γ.naturality k
        rw [hn, adj.homEquiv_naturality_right]
        rfl }
  obtain ⟨β, hc⟩ := liftNatural Q (H ⋙ J) τ hinj hβ
  exact ⟨α, β, ha, hc⟩

-- Identify the composite right adjoint with the left adjoint still abstract.
private theorem tensorComparisons_from_adjunction
    (L : X.Modules ⥤ U.Modules) (adj : L ⊣ pushforward f)
    (H : SheafOfModules.{u} (𝓡 A) ⥤ U.Modules) (γ : S ⋙ L ⟶ H)
    (hf : ∀ F : U.Modules, (∃ a : H.obj ((R).obj F) ⟶ F,
      γ.app ((R).obj F) ≫ a = adj.counit.app F) ∧ Epi (γ.app ((R).obj F)))
    (hβ : ∀ G : SheafOfModules.{u} (𝓡 A), ∃ a : G ⟶ (R).obj (H.obj G),
      (S).map a = (adj.homEquiv ((S).obj G) (H.obj G)) (γ.app G)) :
    ∃ (α : R ⋙ H ⟶ 𝟭 U.Modules) (β : 𝟭 (SheafOfModules.{u} (𝓡 A)) ⟶ H ⋙ R),
      (∀ F : U.Modules, γ.app ((R).obj F) ≫ α.app F = adj.counit.app F) ∧
      (∀ G : SheafOfModules.{u} (𝓡 A),
        (S).map (β.app G) = (adj.homEquiv ((S).obj G) (H.obj G)) (γ.app G)) := by
  exact comparisons_from_objectwise
    (C := SheafOfModules.{u} (𝓡 A)) (D := X.Modules) (E := U.Modules)
    S R L adj H γ (scalarRestriction_injective f) hf hβ

private theorem tensorComparisons_from_objectwise
    (H : SheafOfModules.{u} (𝓡 A) ⥤ U.Modules) (γ : S ⋙ tensorPullback f ⟶ H)
    (hf : ∀ F : U.Modules, (∃ a : H.obj ((R).obj F) ⟶ F,
      γ.app ((R).obj F) ≫ a = (adj₀).counit.app F) ∧ Epi (γ.app ((R).obj F)))
    (hβ : ∀ G : SheafOfModules.{u} (𝓡 A), ∃ a : G ⟶ (R).obj (H.obj G),
      (S).map a = ((adj₀).homEquiv ((S).obj G) (H.obj G)) (γ.app G)) :
    ∃ (α : R ⋙ H ⟶ 𝟭 U.Modules) (β : 𝟭 (SheafOfModules.{u} (𝓡 A)) ⟶ H ⋙ R),
      (∀ F : U.Modules, γ.app ((R).obj F) ≫ α.app F = (adj₀).counit.app F) ∧
      (∀ G : SheafOfModules.{u} (𝓡 A),
        (S).map (β.app G) = ((adj₀).homEquiv ((S).obj G) (H.obj G)) (γ.app G)) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    exact tensorComparisons_from_adjunction f (tensorPullback f) (adj₀) H γ hf hβ

/-- The tensor extension is quasi-coherent and carries the canonical comparison maps.
Source: Stacks Project, Morphisms, Lemma 01SB, construction of h and elucidation.
Proof: The affine direct-image algebra A is quasi-coherent by affine relative Spec.
Scalar restriction makes a quasi-coherent A-module quasi-coherent over O_X. Pullback
preserves this property, so κ identifies the underlying O_U-module of P(G) with a
quasi-coherent module. Its algebra B is the pullback of A and is quasi-coherent by
the same base-change tensor identification. Apply quasi-coherent algebra change of
rings to B → O_U given by ε to deduce quasi-coherence of H(G).
The pullback counit is linear over B after identifying via κ: on tensor generators
(b tensor a)(b′ tensor s) is sent to bb′as, which is ε(b tensor a) times b′s.
The scalar-extension universal property therefore factors it uniquely through H(RF),
defining α. The inverse-image/direct-image unit followed by γ is A-linear: multiply
a section g by a, apply the given κ unit formula, then the γ tensor-unit formula,
and use the balanced relation and tε=e. It thus defines β. Uniqueness in the tensor
universal property proves naturality of α and β and the first comparison equation.
The canonical pullback Hom equivalence and its unit formula give the second equation.
These arguments do not require faithful scalar restriction or a nonzero ring.
(blueprint: lem-weil-pbc-affine-module-tensor-coherence-comparisons). -/
theorem affine_module_tensor_coherenceComparisons [IsAffineHom f]
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B) (t : IA ⟶ B)
    (ε : B ⟶ U.sheaf) (hpush : IsPushout r₀ t₀ b t)
    (hb : b ≫ ε = 𝟙 U.sheaf) (ht : t ≫ ε = e₀)
    (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
        (pobj : ∀ G, P.obj G = SheafOfModules.changeOfRings.{u, u, u} t (I G))
        (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f)
    (H : SheafOfModules.{u} (𝓡 A) ⥤ U.Modules)
          (hobj : ∀ G, H.obj G = SheafOfModules.changeOfRings.{u, u, u} ε (P.obj G))
          (γ : S ⋙ tensorPullback f ⟶ H)
    (hP :
        (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
          P.map a = eqToHom (pobj G) ≫
            SheafOfModules.changeOfRingsHom.{u, u, u} t (I G)
              (TopCat.Sheaf.inverseImageModuleMap f.base A G a) ≫
            eqToHom (pobj G').symm) ∧
        (∀ (G : SheafOfModules.{u} (𝓡 A)) (V : (Opens X)ᵒᵖ) (g : G.val.obj V),
          ((eqToHom (pobj G)).val.app ((Opens.map f.base).op.obj V))
            ((κ.inv.app G).val.app ((Opens.map f.base).op.obj V)
              (((adj₀).unit.app ((S).obj G)).val.app V g)) =
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
              (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t (I G))).app
                ((Opens.map f.base).op.obj V)
                ((1 : B.obj.obj ((Opens.map f.base).op.obj V))
                  ⊗ₜ[(IA).obj.obj ((Opens.map f.base).op.obj V),(t.hom.app
                    ((Opens.map f.base).op.obj V)).hom]
                  (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                    (Opens.map f.base) AddCommGrpCat.{u} (𝓙 X) (𝓙 U)).unit.app
                      ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g))))
    (hH :
          (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
            H.map a = eqToHom (hobj G) ≫
              SheafOfModules.changeOfRingsHom.{u, u, u} ε (P.obj G) (P.map a) ≫
              eqToHom (hobj G').symm) ∧
          (∀ (G : SheafOfModules.{u} (𝓡 A)) (W : (Opens U)ᵒᵖ)
              (p : (P.obj G).val.obj W),
            ((eqToHom (hobj G)).val.app W)
              ((γ.app G).val.app W ((κ.hom.app G).val.app W p)) =
              ((PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
                (SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε (P.obj G))).app W
                  ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W,(ε.hom.app W).hom] p))) :
          (∀ G : SheafOfModules.{u} (𝓡 A),
            G.IsQuasicoherent → (H.obj G).IsQuasicoherent) ∧
          ∃ (α : R ⋙ H ⟶ 𝟭 U.Modules) (β : 𝟭 (SheafOfModules.{u} (𝓡 A)) ⟶ H ⋙ R),
            (∀ F : U.Modules, γ.app ((R).obj F) ≫ α.app F = (adj₀).counit.app F) ∧
            (∀ G : SheafOfModules.{u} (𝓡 A),
              (S).map (β.app G) = ((adj₀).homEquiv ((S).obj G) (H.obj G)) (γ.app G)) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    constructor
    · exact tensorExtension_quasiCoherent f B b t ε hpush hb P κ H hobj
    · have hf := affine_module_tensor_counitFactor (U := U) (X := X) f B b t ε hpush hb ht
        P pobj κ H hobj γ hP hH
      have hβ := affine_module_tensor_unitLift (U := U) (X := X) f B b t ε hpush hb ht
        P pobj κ H hobj γ hP hH
      exact tensorComparisons_from_objectwise f H γ hf hβ

end
end AlgebraicGeometry.Scheme.Modules
