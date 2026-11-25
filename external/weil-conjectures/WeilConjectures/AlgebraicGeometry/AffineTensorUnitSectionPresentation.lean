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
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.AffinePushoutFirstTensorSections
import WeilConjectures.AlgebraicGeometry.AffineModuleTensorAlgebraQuasiCoherent
import WeilConjectures.AlgebraicGeometry.QuasiCoherenceScalarRestriction
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebraChangeOfRings

/-! # Affine tensor-unit section presentation

Source: Stacks Project, Morphisms, Lemma 01SB, key algebra observation.
(blueprint: lem-weil-pbc-affine-tensor-unit-section-presentation).
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

local instance instHasLeftKanExtension_affineTensorUnitSectionPresentation
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

private theorem scalar_tensor_presentation
    {D C E N M T : Type u} [CommRing D] [CommRing C] [CommRing E] [Algebra D C]
    [AddCommGroup N] [Module D N] [Module C N] [IsScalarTower D C N]
    [AddCommGroup M] [Module D M] [Module E M]
    [AddCommGroup T] [Module D T]
    (α δ : C →+* E) (ε : E →+* C)
    (hα : ∀ c, ε (α c) = c) (hδ : ∀ c, ε (δ c) = c)
    (hgen : ∀ r : E, ∃ l : List (C × C), r = (l.map fun x ↦ α x.1 * δ x.2).sum)
    (p : (C ⊗[D] N) ≃ₗ[D] M)
    (hpα : ∀ c d n, α c • p (d ⊗ₜ[D] n) = p ((c * d) ⊗ₜ[D] n))
    (hpδ : ∀ c d n, δ c • p (d ⊗ₜ[D] n) = p (d ⊗ₜ[D] (c • n))) :
    letI : Module E C := Module.compHom C ε
    ∀ (e : (C ⊗[E] M) ≃+ T) (q : (C ⊗[D] N) →ₗ[D] T),
      (∀ z, q z = e ((1 : C) ⊗ₜ[E] p z)) →
      Function.Surjective q ∧
      LinearMap.ker q = Submodule.span D
        {z | ∃ (c : C) (n : N), z = c ⊗ₜ[D] n - (1 : C) ⊗ₜ[D] (c • n)} := by
  let : Module E C := Module.compHom C ε
  intro e q hq
  let a : (C ⊗[D] N) →ₗ[D] N :=
    TensorProduct.lift (Algebra.lsmul D D N).toLinearMap
  have ha (c : C) (n : N) : a (c ⊗ₜ[D] n) = c • n := rfl
  let τ : M →+ N := a.toAddMonoidHom.comp p.symm.toAddMonoidHom
  have hτ (z : C ⊗[D] N) : τ (p z) = a z := by simp [τ]
  have hτα (c : C) (m : M) : τ (α c • m) = c • τ m := by
    obtain ⟨z, rfl⟩ := p.surjective m
    induction z using TensorProduct.inductionOn with
    | tmul d n => rw [hpα, hτ, hτ, ha, ha, mul_smul]
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  have hτδ (c : C) (m : M) : τ (δ c • m) = c • τ m := by
    obtain ⟨z, rfl⟩ := p.surjective m
    induction z using TensorProduct.inductionOn with
    | tmul d n => rw [hpδ, hτ, hτ, ha, ha, smul_comm]
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  have hτE (r : E) (m : M) : τ (r • m) = ε r • τ m := by
    obtain ⟨l, rfl⟩ := hgen r
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.map_cons, List.sum_cons, add_smul, map_add, ih, map_mul, hα, hδ]
      rw [mul_smul, hτα, hτδ, mul_smul]
  let F : C →+ M →+ N :=
    { toFun := fun c ↦
        { toFun := fun m ↦ c • τ m
          map_zero' := by simp
          map_add' := by intros; simp [smul_add] }
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp [add_smul] }
  have hF (r : E) (c : C) (m : M) : F (r • c) m = F c (r • m) := by
    change (ε r * c) • τ m = c • τ (r • m)
    rw [hτE, mul_smul, smul_comm]
  let L : (C ⊗[E] M) →+ N := TensorProduct.liftAddHom F hF
  have hL (c : C) (m : M) : L (c ⊗ₜ[E] m) = c • τ m := rfl
  have hn (z : C ⊗[D] N) : L ((1 : C) ⊗ₜ[E] p z) = a z := by
    rw [hL, one_smul, hτ]
  have hp (c : C) (z : C ⊗[D] N) : α c • p z = p (c • z) := by
    induction z using TensorProduct.inductionOn with
    | tmul d n => simpa only [TensorProduct.smul_tmul', smul_eq_mul] using hpα c d n
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  have ht (c : C) (z : C ⊗[D] N) :
      c ⊗ₜ[E] p z = (1 : C) ⊗ₜ[E] p (c • z) := by
    rw [← hp, ← TensorProduct.smul_tmul]
    change c ⊗ₜ[E] p z = (ε (α c) * 1) ⊗ₜ[E] p z
    rw [hα, mul_one]
  have hrel (c : C) (n : N) :
      q (c ⊗ₜ[D] n) = q ((1 : C) ⊗ₜ[D] (c • n)) := by
    rw [hq, hq, ← hpδ c 1 n, ← TensorProduct.smul_tmul]
    change e ((1 : C) ⊗ₜ[E] p (c ⊗ₜ[D] n)) =
      e ((ε (δ c) * 1) ⊗ₜ[E] p ((1 : C) ⊗ₜ[D] n))
    rw [hδ, mul_one, ht c ((1 : C) ⊗ₜ[D] n)]
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  let K := Submodule.span D
    {z | ∃ (c : C) (n : N), z = c ⊗ₜ[D] n - (1 : C) ⊗ₜ[D] (c • n)}
  have hnormal (z : C ⊗[D] N) : z - (1 : C) ⊗ₜ[D] a z ∈ K := by
    induction z using TensorProduct.inductionOn with
    | tmul c n => exact Submodule.subset_span ⟨c, n, rfl⟩
    | add x y hx hy =>
      simpa only [map_add, TensorProduct.tmul_add, add_sub_add_comm] using K.add_mem hx hy
  constructor
  · intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    have hz : ∃ x, q x = e z := by
      induction z using TensorProduct.inductionOn with
      | tmul c m =>
        refine ⟨c • p.symm m, ?_⟩
        rw [hq, ← ht, p.apply_symm_apply]
      | add x y hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    exact hz
  · apply le_antisymm
    · intro z hz
      have hz0 : q z = 0 := hz
      have hz1 : (1 : C) ⊗ₜ[E] p z = 0 := by
        apply e.injective
        simpa only [← hq, map_zero] using hz0
      have haz : a z = 0 := by
        rw [← hn, hz1, map_zero]
      simpa only [haz, TensorProduct.tmul_zero, sub_zero] using hnormal z
    · apply Submodule.span_le.mpr
      rintro z ⟨c, n, rfl⟩
      change q (_ - _) = 0
      rw [map_sub, hrel, sub_self]

/-- Affine sections of the two tensor operations are the quotient of the first tensor
product by the diagonal-action relations. The map on unit tensors is canonical.
Source: Stacks Project, Morphisms, Tag 01SB, construction of h and key algebra observation.
(blueprint: lem-weil-pbc-affine-tensor-unit-section-presentation).

Proof: Put D = O_X(V), C = O_U(f⁻¹V), N = G(V), E = B(f⁻¹V), and
M = P(G)(f⁻¹V). The affine first-tensor section lemma supplies p : C tensor_D N ≃ M,
the second-factor ring map delta : C → E, additive generation of E by b(c)delta(d),
and both E-actions on pure tensors, with p(1 tensor n)=kappa inverse of the unit.
The affine pushout algebra is quasi-coherent by its existing theorem. Pushforward of
the structure-sheaf unit makes A quasi-coherent; scalar restriction and preservation
of quasi-coherence by pullback, transferred through kappa, make the underlying P(G)
quasi-coherent. Apply the affine change-of-rings theorem to epsilon and transport by
hobj to obtain an additive equivalence e : C tensor_E M ≃ H(G)(f⁻¹V).
Define q as gamma followed after kappa and p. The hH equation gives
q(z)=e(1 tensor p(z)). The private scalar_tensor_presentation proves its algebraic
properties: the map a(c tensor n)=cn, transported by p inverse, is epsilon-balanced
because b(c) and delta(c) both act on its values by c. Extend it to the outer tensor
product to show that ker q is contained in ker a. Balancing by delta(c) kills each
listed relation. Tensor induction shows z-1 tensor a(z) lies in their span, hence
ker q equals that span. Balancing by b(c) moves every outer scalar into the first
inner factor, so q is surjective. Finally p's unit formula and kappa hom-inv give
the canonical gamma-unit formula. All arguments apply to zero rings, zero modules
and the empty affine open. No beta or adjoint-comparison equation is used.
-/
theorem affine_tensor_unit_section_presentation [IsAffineHom f]
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
    (G : SheafOfModules.{u} (𝓡 A)) (hG : G.IsQuasicoherent)
    (V : X.Opens) (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
    letI : Module Γ(X, V) (G.val.obj (op V)) :=
      Module.compHom _ (f.app V).hom
    letI : Module Γ(X, V) Γ(H.obj G, f ⁻¹ᵁ V) :=
      Module.compHom _ (f.app V).hom
    ∃ q : (Γ(U, f ⁻¹ᵁ V) ⊗[Γ(X, V)] (G.val.obj (op V))) →ₗ[Γ(X, V)]
        Γ(H.obj G, f ⁻¹ᵁ V),
      Function.Surjective q ∧
      LinearMap.ker q = Submodule.span Γ(X, V)
        {z | ∃ (c : Γ(U, f ⁻¹ᵁ V)) (n : G.val.obj (op V)),
          z = c ⊗ₜ[Γ(X, V)] n - (1 : Γ(U, f ⁻¹ᵁ V)) ⊗ₜ[Γ(X, V)] (c • n)} ∧
      ∀ n : G.val.obj (op V),
        q ((1 : Γ(U, f ⁻¹ᵁ V)) ⊗ₜ[Γ(X, V)] n) =
          (γ.app G).val.app (fV (op V))
            (((adj₀).unit.app ((S).obj G)).val.app (op V) n) := by
  classical
  let : (Opens.map f.base).IsContinuous (𝓙 X) (𝓙 U.toTopCat) :=
    inferInstanceAs ((Opens.map f.base).IsContinuous (𝓙 X) (𝓙 U))
  dsimp only
  let : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  let : Module Γ(X, V) (G.val.obj (op V)) := Module.compHom _ (f.app V).hom
  let : Module Γ(X, V) Γ(H.obj G, f ⁻¹ᵁ V) := Module.compHom _ (f.app V).hom
  let : Module Γ(X, V) ((P.obj G).val.obj (op (f ⁻¹ᵁ V))) :=
    Module.compHom _ ((b.hom.app (op (f ⁻¹ᵁ V))).hom.comp (f.app V).hom)
  let : IsScalarTower Γ(X, V) Γ(U, f ⁻¹ᵁ V) (G.val.obj (op V)) :=
    ⟨fun r c n ↦ by
      change ((f.app V).hom r * c) • n = (f.app V).hom r • (c • n)
      exact mul_smul _ _ _⟩
  have hfirst :=
    affine_pushout_first_tensor_sections f B b t ε hring P pobj κ hP G hG V hV
  let δ := hfirst.choose
  have hδ := hfirst.choose_spec.1
  have hgen := hfirst.choose_spec.2.1
  let p := hfirst.choose_spec.2.2.choose
  have hpα := hfirst.choose_spec.2.2.choose_spec.1
  have hpδ := hfirst.choose_spec.2.2.choose_spec.2.1
  have hpu := hfirst.choose_spec.2.2.choose_spec.2.2
  let Aalg : X.CommAlgebraSheaf := Under.mk ρ
  let Balg : U.CommAlgebraSheaf := Under.mk b
  let Calg : U.CommAlgebraSheaf := Under.mk (𝟙 U.sheaf)
  let φ : Balg ⟶ Calg := Under.homMk ε hring.2.1
  have hA : Aalg.toModule.IsQuasicoherent := by
    have : (SheafOfModules.unit U.ringCatSheaf).IsQuasicoherent :=
      SheafOfModules.isQuasicoherent_unit.{u, u, u}
    change ((pushforward f).obj (SheafOfModules.unit U.ringCatSheaf)).IsQuasicoherent
    exact isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated f _
  have hB : Balg.toModule.IsQuasicoherent :=
    affine_module_tensor_algebra_quasiCoherent f B b t hring.1
  have hC : Calg.toModule.IsQuasicoherent := by
    change (SheafOfModules.unit U.ringCatSheaf).IsQuasicoherent
    exact SheafOfModules.isQuasicoherent_unit.{u, u, u}
  have hS : ((S).obj G).IsQuasicoherent :=
    (quasiCoherent_iff_restrictScalars X Aalg hA G).mp hG
  have : ((S).obj G).IsQuasicoherent := hS
  let ep : tensorPullback f ≅ pullback f :=
    (adj₀).leftAdjointUniq (pullbackPushforwardAdjunction f)
  have hT : ((tensorPullback f).obj ((S).obj G)).IsQuasicoherent :=
    (qU).prop_of_iso (ep.app ((S).obj G)).symm (by infer_instance)
  have hPG : ((SheafOfModules.restrictScalars (𝓻 b)).obj (P.obj G)).IsQuasicoherent :=
    (qU).prop_of_iso (κ.app G).symm hT
  have hW : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have hη := (quasiCoherent_algebra_changeOfRings U Balg Calg φ
    (P.obj G) hB hC hPG).2 (f ⁻¹ᵁ V) hW
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε (P.obj G))).app (fV (op V))
  let eh := appLinearEquivOfIso (eqToIso (hobj G)) (f ⁻¹ᵁ V)
  let e := (AddEquiv.ofBijective η.hom.toAddMonoidHom hη).trans eh.symm.toAddEquiv
  let l : ((P.obj G).val.obj (op (f ⁻¹ᵁ V))) →ₗ[Γ(X, V)]
      Γ(H.obj G, f ⁻¹ᵁ V) :=
    { toFun := fun y ↦ (γ.app G).val.app (fV (op V))
        ((κ.hom.app G).val.app (fV (op V)) y)
      map_add' := by intros; simp only [map_add]
      map_smul' := by
        intro r y
        change (γ.app G).val.app (fV (op V))
          ((κ.hom.app G).val.app (fV (op V))
            ((b.hom.app (op (f ⁻¹ᵁ V))).hom ((f.app V).hom r) • y)) = _
        exact (congrArg ((γ.app G).val.app (fV (op V)))
          (((κ.hom.app G).val.app (fV (op V))).hom.map_smul ((f.app V).hom r) y)).trans
            (((γ.app G).val.app (fV (op V))).hom.map_smul ((f.app V).hom r) _) }
  let q := l.comp p.toLinearMap
  have he (z : Γ(U, f ⁻¹ᵁ V) ⊗[Γ(X, V)] (G.val.obj (op V))) :
      q z = e ((1 : Γ(U, f ⁻¹ᵁ V)) ⊗ₜ[B.obj.obj (op (f ⁻¹ᵁ V)),
        (ε.hom.app (op (f ⁻¹ᵁ V))).hom] p z) := by
    apply eh.injective
    change ((eqToHom (hobj G)).val.app (fV (op V)))
      ((γ.app G).val.app (fV (op V)) ((κ.hom.app G).val.app (fV (op V)) (p z))) = _
    exact (hH.2.1 G (fV (op V)) (p z)).trans (eh.apply_symm_apply _).symm
  have hb (c : Γ(U, f ⁻¹ᵁ V)) :
      (ε.hom.app (op (f ⁻¹ᵁ V))).hom
        ((b.hom.app (op (f ⁻¹ᵁ V))).hom c) = c := by
    exact congrArg (fun a ↦ a.hom.app (op (f ⁻¹ᵁ V)) c) hring.2.1
  have hpresentation := scalar_tensor_presentation
    (D := Γ(X, V)) (C := Γ(U, f ⁻¹ᵁ V))
    (E := B.obj.obj (op (f ⁻¹ᵁ V))) (N := G.val.obj (op V))
    (M := (P.obj G).val.obj (op (f ⁻¹ᵁ V))) (T := Γ(H.obj G, f ⁻¹ᵁ V))
    (b.hom.app (op (f ⁻¹ᵁ V))).hom δ (ε.hom.app (op (f ⁻¹ᵁ V))).hom
    hb hδ hgen p hpα hpδ e q he
  refine ⟨q, hpresentation.1, hpresentation.2, ?_⟩
  intro n
  change l (p ((1 : Γ(U, f ⁻¹ᵁ V)) ⊗ₜ[Γ(X, V)] n)) = _
  refine (congrArg l (hpu n)).trans ?_
  change (γ.app G).val.app (fV (op V))
    ((κ.hom.app G).val.app (fV (op V))
      ((κ.inv.app G).val.app (fV (op V)) _)) = _
  have hi := congrArg (fun a ↦ a.val.app (fV (op V))
    (((adj₀).unit.app ((S).obj G)).val.app (op V) n)) (κ.inv_hom_id_app G)
  exact congrArg ((γ.app G).val.app (fV (op V))) hi

end
end AlgebraicGeometry.Scheme.Modules
