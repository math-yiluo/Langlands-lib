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
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.QuasiCoherenceScalarRestriction
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.InverseImageChangeOfRingsUnitSmul

/-! # Affine pushout module section presentation

Source: Stacks Project, Morphisms, Lemma 01SB, key algebra observation.
(blueprint: lem-weil-pbc-affine-pushout-module-section-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Compute the two actions on ordinary modules, without unfolding sheaf section instances.
private theorem affine_pushout_first_action
    {C D N M : Type*} [CommRing C] [CommRing D] [AddCommGroup M] [Module D M]
    (b : C →+* D) (p : C → N → M) (v : N → M)
    (hp : ∀ d n, p d n = b d • v n) :
    (∀ c d n, b c • p d n = p (c * d) n) ∧ ∀ n, p 1 n = v n := by
  constructor
  · intro c d n
    simp only [hp, map_mul, mul_smul]
  · intro n
    simp only [hp, map_one, one_smul]

private theorem affine_pushout_second_action
    {C D N M : Type*} [CommRing C] [CommRing D] [SMul C N]
    [AddCommGroup M] [Module D M]
    (b δ : C →+* D) (p : C → N → M) (v : N → M)
    (hb : ∀ c d n, b c • p d n = p (c * d) n)
    (hu : ∀ n, p 1 n = v n) (hv : ∀ c n, δ c • v n = v (c • n)) :
    ∀ c d n, δ c • p d n = p d (c • n) := by
  have hp (d : C) (n : N) : p d n = b d • v n := by
    simpa only [mul_one, hu] using (hb d 1 n).symm
  intro c d n
  rw [hp, hp, smul_comm, hv]

variable {U X : Scheme.{u}} (f : U ⟶ X)

local instance instHasLeftKanExtension_affinePushoutModuleSectionPresentation
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

-- The affine-section comparison requires transport between restricted section-module instances.
/-- The affine pullback comparison, transported through κ, is linear for the first
section-ring action and sends `1 tensor n` to the canonical pullback unit. -/
private theorem affine_pushout_module_section_presentation_equiv [IsAffineHom f]
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B)
    (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
    (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f)
    (G : SheafOfModules.{u} (𝓡 A)) (hG : G.IsQuasicoherent)
    (V : X.Opens) (hV : IsAffineOpen V)
    :
    letI : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
    letI : Module Γ(X, V) (G.val.obj (op V)) :=
      Module.compHom _ (f.app V).hom
    letI : Module Γ(X, V) ((P.obj G).val.obj (op (f ⁻¹ᵁ V))) :=
      Module.compHom _ ((b.hom.app (op (f ⁻¹ᵁ V))).hom.comp (f.app V).hom)
    ∃ p : (Γ(U, f ⁻¹ᵁ V) ⊗[Γ(X, V)] (G.val.obj (op V))) ≃ₗ[Γ(X, V)]
          ((P.obj G).val.obj (op (f ⁻¹ᵁ V))),
      (∀ (c d : Γ(U, f ⁻¹ᵁ V)) (n : G.val.obj (op V)),
        (b.hom.app (op (f ⁻¹ᵁ V))).hom c • p (d ⊗ₜ[Γ(X, V)] n) =
          p ((c * d) ⊗ₜ[Γ(X, V)] n)) ∧
      ∀ n, p ((1 : Γ(U, f ⁻¹ᵁ V)) ⊗ₜ[Γ(X, V)] n) =
          (κ.inv.app G).val.app (fV (op V))
            (((adj₀).unit.app ((S).obj G)).val.app (op V) n) := by
  classical
  let : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  let : Module Γ(X, V) (G.val.obj (op V)) := Module.compHom _ (f.app V).hom
  let : Module Γ(X, V) ((P.obj G).val.obj (op (f ⁻¹ᵁ V))) :=
    Module.compHom _ ((b.hom.app (op (f ⁻¹ᵁ V))).hom.comp (f.app V).hom)
  let Aalg : X.CommAlgebraSheaf := Under.mk ρ
  have hA : Aalg.toModule.IsQuasicoherent := by
    have : (SheafOfModules.unit U.ringCatSheaf).IsQuasicoherent :=
      SheafOfModules.isQuasicoherent_unit.{u, u, u}
    change ((pushforward f).obj (SheafOfModules.unit U.ringCatSheaf)).IsQuasicoherent
    exact isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated f _
  have hS : ((S).obj G).IsQuasicoherent :=
    (quasiCoherent_iff_restrictScalars X Aalg hA G).mp hG
  let : Module Γ(X, V) Γ((tensorPullback f).obj ((S).obj G), f ⁻¹ᵁ V) :=
    Module.compHom _ (f.app V).hom
  have hc₀ := exists_tensorPullback_affine_sections f
    ⟨V, hV⟩ ⟨f ⁻¹ᵁ V, hV.preimage f⟩ le_rfl
  dsimp only at hc₀
  rw [Scheme.Hom.appLE_eq_app] at hc₀
  obtain ⟨c, hc, hlin, htmul, hnat⟩ := hc₀
  let e := LinearEquiv.ofBijective (c ((S).obj G) hS) (hc _ hS)
  let k := appLinearEquivOfIso (κ.app G).symm (f ⁻¹ᵁ V)
  let l : Γ((tensorPullback f).obj ((S).obj G), f ⁻¹ᵁ V) →ₗ[Γ(X, V)]
      ((P.obj G).val.obj (op (f ⁻¹ᵁ V))) :=
    { toFun := k
      map_add' := k.map_add
      map_smul' := fun r n ↦ k.map_smul ((f.app V).hom r) n }
  let kl := LinearEquiv.ofBijective l k.bijective
  let p : (Γ(U, f ⁻¹ᵁ V) ⊗[Γ(X, V)] (G.val.obj (op V))) ≃ₗ[Γ(X, V)]
      ((P.obj G).val.obj (op (f ⁻¹ᵁ V))) := ((TensorProduct.comm Γ(X, V) Γ(U, f ⁻¹ᵁ V)
    (G.val.obj (op V))).trans e).trans kl
  have htmul' (n : G.val.obj (op V)) (d : Γ(U, f ⁻¹ᵁ V)) :
      c ((S).obj G) hS (n ⊗ₜ[Γ(X, V)] d) =
        d • (show Γ((tensorPullback f).obj ((S).obj G), f ⁻¹ᵁ V) from
          (((adj₀).unit.app ((S).obj G)).val.app (op V) n)) := by
    have hid : ((tensorPullback f).obj ((S).obj G)).presheaf.map
        (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V from le_rfl)).op = 𝟙 _ :=
      ((tensorPullback f).obj ((S).obj G)).presheaf.map_id _
    simpa only [hid, ConcreteCategory.id_apply] using htmul ((S).obj G) hS n d
  have hp (d : Γ(U, f ⁻¹ᵁ V)) (n : G.val.obj (op V)) :
      p (d ⊗ₜ[Γ(X, V)] n) = (b.hom.app (op (f ⁻¹ᵁ V))).hom d •
        (show (P.obj G).val.obj (op (f ⁻¹ᵁ V)) from
          (κ.inv.app G).val.app (fV (op V))
            (((adj₀).unit.app ((S).obj G)).val.app (op V) n)) := by
    exact (congrArg k (htmul' n d)).trans (k.map_smul d _)
  exact ⟨p, affine_pushout_first_action (b.hom.app (op (f ⁻¹ᵁ V))).hom
    (fun d n ↦ p (d ⊗ₜ[Γ(X, V)] n)) _ hp⟩

-- The canonical unit calculation unfolds inverse-image and change-of-rings section instances.
/-- Affine first-tensor module section presentation with both actions and the canonical unit.
Source: Stacks Project, Morphisms, Tag 01SB, construction of h and affine reduction.
(blueprint: lem-weil-pbc-affine-pushout-module-section-presentation).

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
theorem affine_pushout_module_section_presentation [IsAffineHom f]
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
    (V : X.Opens) (hV : IsAffineOpen V)
    (δ : Γ(U, f ⁻¹ᵁ V) →+* B.obj.obj (op (f ⁻¹ᵁ V)))
    (hδ : δ = (t.hom.app (op (f ⁻¹ᵁ V))).hom.comp
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)).unit.app A).hom.app (op V)).hom) :
    letI : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
    letI : Module Γ(X, V) (G.val.obj (op V)) :=
      Module.compHom _ (f.app V).hom
    letI : Module Γ(X, V) ((P.obj G).val.obj (op (f ⁻¹ᵁ V))) :=
      Module.compHom _ ((b.hom.app (op (f ⁻¹ᵁ V))).hom.comp (f.app V).hom)
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
  have _ := hring
  let : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  let : Module Γ(X, V) (G.val.obj (op V)) := Module.compHom _ (f.app V).hom
  let : Module Γ(X, V) ((P.obj G).val.obj (op (f ⁻¹ᵁ V))) :=
    Module.compHom _ ((b.hom.app (op (f ⁻¹ᵁ V))).hom.comp (f.app V).hom)
  have he := affine_pushout_module_section_presentation_equiv f B b P κ G hG V hV
  rcases he with ⟨p, hb, hu⟩
  let v (n : G.val.obj (op V)) : (P.obj G).val.obj (op (f ⁻¹ᵁ V)) :=
    (κ.inv.app G).val.app (fV (op V))
      (((adj₀).unit.app ((S).obj G)).val.app (op V) n)
  have hv (c : Γ(U, f ⁻¹ᵁ V)) (n : G.val.obj (op V)) :
      δ c • v n = v (c • n) := by
    have hinj (M N : SheafOfModules.{u} (𝓡 B)) (h : M = N) :
        Function.Injective ((eqToHom h).val.app (fV (op V))) := by
      subst N
      intro x y hxy
      exact hxy
    apply hinj _ _ (pobj G)
    rw [((eqToHom (pobj G)).val.app (fV (op V))).hom.map_smul]
    change δ c • ((eqToHom (pobj G)).val.app (fV (op V))) (v n) =
      ((eqToHom (pobj G)).val.app (fV (op V))) (v (c • n))
    rw [hP.2 G (op V) n, hP.2 G (op V) (c • n)]
    subst δ
    exact inverseImage_changeOfRings_unit_smul f.base A B t G (op V) c n
  exact ⟨p, hb, affine_pushout_second_action (b.hom.app (op (f ⁻¹ᵁ V))).hom δ
    (fun d n ↦ p (d ⊗ₜ[Γ(X, V)] n)) v hb hu hv, hu⟩
end
end AlgebraicGeometry.Scheme.Modules
