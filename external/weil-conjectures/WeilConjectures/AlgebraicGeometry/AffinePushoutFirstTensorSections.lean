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
public import Mathlib.Algebra.BigOperators.Group.List.Basic
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.QuasiCoherenceScalarRestriction
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.AffinePushoutRingAffineSections
import WeilConjectures.AlgebraicGeometry.AffinePushoutRingSectionProducts
import Mathlib.Algebra.Category.Ring.Constructions
import WeilConjectures.AlgebraicGeometry.AffinePushoutModuleSectionPresentation

/-! # Affine pushout ring and first tensor sections

Source: Stacks Project, Morphisms, Lemma 01SB, key algebra observation.
(blueprint: lem-weil-pbc-affine-pushout-first-tensor-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {U X : Scheme.{u}} (f : U ⟶ X)

local instance instHasLeftKanExtension_affinePushoutFirstTensorSections
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

/-- Affine identification of the pushout algebra and the first tensor pullback, with
both actions and the canonical unit; no assertion about the final extension module.
Source: Stacks Project, Morphisms, Tag 01SB, construction of h and affine reduction.
(blueprint: lem-weil-pbc-affine-pushout-first-tensor-sections).

Proof: Push forward the structure-sheaf unit along the affine qcqs morphism; its
underlying structure-sheaf module is quasi-coherent. Restriction of scalars therefore
makes G quasi-coherent over O_X. The affine pullback section theorem, followed by
kappa inverse, identifies P(G)(W) with C tensor_D N, where W=f inverse V.
It sends c tensor n to b(c) times the image of the pullback unit of n. Apply the same
construction to the algebra A=f_*O_U. The ring pushout universal property identifies
B with the sheafification of O_U tensor_{f inverse O_X} f inverse A, and on W the
canonical affine ring comparison identifies B(W) with C tensor_D C. The map delta
is the second tensor inclusion: on sections it is t after the inverse-image unit.
The counit equation t followed by epsilon=e makes epsilon(delta(c))=c, while the
other equation gives epsilon(b(c))=c. Pure tensors generate C tensor_D C additively,
so every element of B(W) is a finite sum of b(c)delta(d). The two actions on P(G)(W)
are b(c)(d tensor n)=cd tensor n and delta(c)(d tensor n)=d tensor cn.
These formulas follow before sheafification from tensor balancing and remain true
under its canonical map. The hP unit equation fixes the unit normalization. This argument
involves no final extension H or gamma, and is valid for zero rings, zero modules and the
empty affine open. -/
theorem affine_pushout_first_tensor_sections [IsAffineHom f]
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
    (G : SheafOfModules.{u} (𝓡 A)) (hG : G.IsQuasicoherent)
    (V : X.Opens) (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
    letI : Module Γ(X, V) (G.val.obj (op V)) :=
      Module.compHom _ (f.app V).hom
    letI : Module Γ(X, V) ((P.obj G).val.obj (op (f ⁻¹ᵁ V))) :=
      Module.compHom _ ((b.hom.app (op (f ⁻¹ᵁ V))).hom.comp (f.app V).hom)
    ∃ δ : Γ(U, f ⁻¹ᵁ V) →+* B.obj.obj (op (f ⁻¹ᵁ V)),
      (∀ c, (ε.hom.app (op (f ⁻¹ᵁ V))).hom (δ c) = c) ∧
      (∀ r : B.obj.obj (op (f ⁻¹ᵁ V)),
        ∃ l : List (Γ(U, f ⁻¹ᵁ V) × Γ(U, f ⁻¹ᵁ V)),
          r = (l.map fun x ↦ (b.hom.app (op (f ⁻¹ᵁ V))).hom x.1 * δ x.2).sum) ∧
      ∃ p : (Γ(U, f ⁻¹ᵁ V) ⊗[Γ(X, V)] (G.val.obj (op V))) ≃ₗ[Γ(X, V)]
          ((P.obj G).val.obj (op (f ⁻¹ᵁ V))),
        (∀ (c d : Γ(U, f ⁻¹ᵁ V)) (n : G.val.obj (op V)),
          (b.hom.app (op (f ⁻¹ᵁ V))).hom c • p (d ⊗ₜ[Γ(X, V)] n) =
          p ((c * d) ⊗ₜ[Γ(X, V)] n)) ∧
        (∀ (c d : Γ(U, f ⁻¹ᵁ V)) (n : G.val.obj (op V)), δ c • p (d ⊗ₜ[Γ(X, V)] n) =
          p (d ⊗ₜ[Γ(X, V)] (c • n))) ∧
        ∀ n, p ((1 : Γ(U, f ⁻¹ᵁ V)) ⊗ₜ[Γ(X, V)] n) =
          (κ.inv.app G).val.app (fV (op V))
            (((adj₀).unit.app ((S).obj G)).val.app (op V) n) := by
  classical
  dsimp only
  let : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  let : Module Γ(X, V) (G.val.obj (op V)) := Module.compHom _ (f.app V).hom
  let : Module Γ(X, V) ((P.obj G).val.obj (op (f ⁻¹ᵁ V))) :=
    Module.compHom _ ((b.hom.app (op (f ⁻¹ᵁ V))).hom.comp (f.app V).hom)
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) CommRingCat.{u} (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology U)
  let δ : Γ(U, f ⁻¹ᵁ V) →+* B.obj.obj (op (f ⁻¹ᵁ V)) :=
    (t.hom.app (op (f ⁻¹ᵁ V))).hom.comp ((adj.unit.app A).hom.app (op V)).hom
  have hεδ : ∀ c, (ε.hom.app (op (f ⁻¹ᵁ V))).hom (δ c) = c := by
    intro c
    have ht := congrArg (fun q ↦ q.hom.app (op (f ⁻¹ᵁ V)) (
      (adj.unit.app A).hom.app (op V) c)) hring.2.2
    have hu := (adj.homEquiv A U.sheaf).apply_symm_apply (𝟙 A)
    rw [Adjunction.homEquiv_unit] at hu
    have hv := congrArg (fun q ↦ q.hom.app (op V) c) hu
    exact ht.trans hv
  have hgen : ∀ r : B.obj.obj (op (f ⁻¹ᵁ V)),
      ∃ l : List (Γ(U, f ⁻¹ᵁ V) × Γ(U, f ⁻¹ᵁ V)),
        r = (l.map fun x ↦ (b.hom.app (op (f ⁻¹ᵁ V))).hom x.1 * δ x.2).sum := by
    exact affinePushoutSection_products f B b t hring.1 V hV
  refine ⟨δ, hεδ, hgen, ?_⟩
  exact affine_pushout_module_section_presentation f B b t ε hring P pobj κ hP G hG V hV δ rfl

end
end AlgebraicGeometry.Scheme.Modules
