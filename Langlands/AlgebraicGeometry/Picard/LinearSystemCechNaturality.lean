import Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule
import Langlands.AlgebraicGeometry.Picard.SectionZeroIdealFrames

/-! # Naturality of the zero loci of linear-system sections in the base algebra

For a Čech representative of a line bundle `L = M` trivialized by frames on an ordered affine
cover, the section `σ_u` of `M_A` attached to `u : Q → A` has an explicit coordinate on each piece
of the base-changed cover. These coordinates are natural in `A`, so the zero locus of `σ_{φ ∘ u}`
is the pullback of the zero locus of `σ_u` along any morphism of base changes over `φ`. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule

open Scheme.TwoAffineOpenCover SectionZeroIdeal
open P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.AC3Aux

section Scalars

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
  {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  (g : pullback π (specMap R B) ⟶ pullback π (specMap R A)) (φ : A →ₐ[R] B)
  (hg₂ : g ≫ pullback.snd π (specMap R A) =
    pullback.snd π (specMap R B) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))

include hg₂ in
/-- Scalars from the base pull back along `φ`. -/
lemma appLE_algebraMap (W : (pullback π (specMap R A)).Opens)
    (W' : (pullback π (specMap R B)).Opens) (h : W' ≤ g ⁻¹ᵁ W) (a : A) :
    g.appLE W W' h ((algebraOfHom (pullback.snd π (specMap R A)) W).algebraMap a) =
      (algebraOfHom (pullback.snd π (specMap R B)) W').algebraMap (φ a) := by
  rw [algebraMap_algebraOfHom, algebraMap_algebraOfHom]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have hc : ∀ {f₁ f₂ : pullback π (specMap R B) ⟶ Spec (.of A)} (hf : f₁ = f₂) (e₁ e₂),
      f₁.appLE ⊤ W' e₁ = f₂.appLE ⊤ W' e₂ := by
    intro f₁ f₂ hf e₁ e₂; subst hf; rfl
  rw [hc hg₂ _ le_top, Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  congr 1
  have hnat := congrArg (fun F => (ConcreteCategory.hom F) a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ.toRingHom))
  simp only at hnat
  exact hnat.symm

end Scalars

section Coordinates

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) (L : LineBundle X)
  {𝒰 : X.OrderedAffineCover} (e : ∀ i, Γ(L.obj, 𝒰.U i))
  (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (𝒰.U i))

/-- The restriction of the frame to a piece of the cover. -/
abbrev eRes (s : 𝒰.Idx 0) : Γ(L.obj, 𝒰.inter s) :=
  L.obj.presheaf.map (homOfLE (𝒰.inter_le s 0)).op (e (s.1 0))

include he in
lemma isFrameOn_eRes (s : 𝒰.Idx 0) : Scheme.Modules.IsFrameOn (eRes L e s) (𝒰.inter s) :=
  ((he (s.1 0)).map (homOfLE (𝒰.inter_le s 0))).mono (𝒰.inter_le s 0)

variable (A : Type u) [CommRing A] [Algebra R A]

/-- The pulled-back frame on a piece of the base-changed cover. -/
abbrev tRes (s : 𝒰.Idx 0) :
    Γ((Scheme.Modules.pullback (pullback.fst π (specMap R A))).obj L.obj,
      (𝒰.baseChange π A).inter s) :=
  ((Scheme.Modules.pullback (pullback.fst π (specMap R A))).obj L.obj).presheaf.map
    (homOfLE (𝒰.baseChange_inter_le π A s)).op
    (Scheme.Modules.pullbackLocalSection (pullback.fst π (specMap R A)) (eRes L e s))

include he in
lemma isFrameOn_tRes (s : 𝒰.Idx 0) :
    Scheme.Modules.IsFrameOn (tRes π L e A s) ((𝒰.baseChange π A).inter s) :=
  ((Scheme.Modules.IsFrameOn.pullbackLocalSection (pullback.fst π (specMap R A))
    (isFrameOn_eRes L e he s)).map (homOfLE (𝒰.baseChange_inter_le π A s))).mono
    (𝒰.baseChange_inter_le π A s)

variable {L} {π} (C : CechRep π L.obj 𝒰)

/-- The coordinate of the Čech comparison on a piece of the base-changed cover. -/
def coordΘ (x : A ⊗[R] C.K₀) (s : 𝒰.Idx 0) :
    Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter s) :=
  frameEquiv (isFrameOn_tRes π L e he A s) (C.Θ A x s)

lemma frameEquiv_symm_apply {Z : Scheme.{u}} {N : Z.Modules} {U : Z.Opens} {t : Γ(N, U)}
    (ht : Scheme.Modules.IsFrameOn t U) (b : Γ(Z, U)) : (frameEquiv ht).symm b = b • t := rfl

lemma eq_frameEquiv_smul {Z : Scheme.{u}} {N : Z.Modules} {U : Z.Opens} {t : Γ(N, U)}
    (ht : Scheme.Modules.IsFrameOn t U) (m : Γ(N, U)) : m = frameEquiv ht m • t := by
  rw [← frameEquiv_symm_apply ht, LinearEquiv.symm_apply_apply]

/-- The coordinate of `Θ (a ⊗ k)`. -/
lemma coordΘ_tmul (a : A) (k : C.K₀) (s : 𝒰.Idx 0) :
    coordΘ e he A C (a ⊗ₜ k) s =
      (algebraOfHom (pullback.snd π (specMap R A)) ((𝒰.baseChange π A).inter s)).algebraMap a *
        (pullback.fst π (specMap R A)).appLE (𝒰.inter s) ((𝒰.baseChange π A).inter s)
          (𝒰.baseChange_inter_le π A s) (frameEquiv (isFrameOn_eRes L e he s) (C.φ k s)) := by
  rw [coordΘ, C.Θ_tmul]
  set b := frameEquiv (isFrameOn_eRes L e he s) (C.φ k s)
  have hb : C.φ k s = b • eRes L e s := eq_frameEquiv_smul (isFrameOn_eRes L e he s) _
  rw [hb, ← Scheme.Modules.pullbackLocalSection_def, Scheme.Modules.pullbackLocalSection_smul,
    OModulePresheaf.res_smul]
  change frameEquiv (isFrameOn_tRes π L e he A s)
    ((algebraOfHom (pullback.snd π (specMap R A)) ((𝒰.baseChange π A).inter s)).algebraMap a •
      ((pullback π (specMap R A)).presheaf.map (homOfLE (𝒰.baseChange_inter_le π A s)).op
        ((pullback.fst π (specMap R A)).app (𝒰.inter s) b) • tRes π L e A s)) = _
  rw [smul_smul, frameEquiv_smul]
  rfl

lemma coordΘ_add (x y : A ⊗[R] C.K₀) (s : 𝒰.Idx 0) :
    coordΘ e he A C (x + y) s = coordΘ e he A C x s + coordΘ e he A C y s := by
  rw [coordΘ, map_add]
  exact map_add _ _ _

variable {A} {B : Type u} [CommRing B] [Algebra R B]
  (g : pullback π (specMap R B) ⟶ pullback π (specMap R A)) (φ : A →ₐ[R] B)
  (hg₁ : g ≫ pullback.fst π (specMap R A) = pullback.fst π (specMap R B))
  (hg₂ : g ≫ pullback.snd π (specMap R A) =
    pullback.snd π (specMap R B) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))

include hg₁ hg₂ in
/-- **Naturality of the coordinates.** -/
lemma appLE_coordΘ (x : A ⊗[R] C.K₀) (s : 𝒰.Idx 0)
    (hle : (𝒰.baseChange π B).inter s ≤ g ⁻¹ᵁ (𝒰.baseChange π A).inter s) :
    g.appLE _ _ hle (coordΘ e he A C x s) =
      coordΘ e he B C (φ.toLinearMap.rTensor C.K₀ x) s := by
  induction x using TensorProduct.inductionOn with
  | tmul a k =>
    rw [LinearMap.rTensor_tmul, coordΘ_tmul, coordΘ_tmul, map_mul,
      appLE_algebraMap π g φ hg₂ _ _ hle a]
    congr 1
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    have hc : ∀ {f₁ f₂ : pullback π (specMap R B) ⟶ X} (hf : f₁ = f₂) (e₁ e₂),
        f₁.appLE (𝒰.inter s) ((𝒰.baseChange π B).inter s) e₁ =
          f₂.appLE (𝒰.inter s) ((𝒰.baseChange π B).inter s) e₂ := by
      intro f₁ f₂ hf e₁ e₂; subst hf; rfl
    rw [hc hg₁ _ (𝒰.baseChange_inter_le π B s)]
  | add x y hx hy =>
    rw [map_add, coordΘ_add, coordΘ_add, map_add, hx, hy]

end Coordinates

section ZeroLocus

lemma inter_eq_of_idx_zero {X : Scheme.{u}} (K : X.OrderedAffineCover) (s : K.Idx 0) :
    K.inter s = K.U (s.1 0) :=
  le_antisymm (K.inter_le s 0) (le_iInf fun j => by rw [show j = 0 from Fin.eq_zero j])

lemma isAffineOpen_inter_of_idx_zero {X : Scheme.{u}} (K : X.OrderedAffineCover) (s : K.Idx 0) :
    IsAffineOpen (K.inter s) := by
  rw [inter_eq_of_idx_zero]
  exact K.isAffineOpen _

lemma iSup_inter_idx_zero {X : Scheme.{u}} (K : X.OrderedAffineCover) :
    ⨆ s : K.Idx 0, K.inter s = ⊤ := by
  refine top_le_iff.mp fun y _ => ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (K.iSup_eq_top.ge (Set.mem_univ y))
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨fun _ => i, fun a b hab => absurd hab (by
    rw [show a = 0 from Fin.eq_zero a, show b = 0 from Fin.eq_zero b]; exact lt_irrefl _)⟩, ?_⟩
  rw [inter_eq_of_idx_zero]
  exact hi

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)} {L : LineBundle X}
  {𝒰 : X.OrderedAffineCover} (e : ∀ i, Γ(L.obj, 𝒰.U i))
  (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (𝒰.U i)) (C : CechRep π L.obj 𝒰)
  {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- The pullback of a line bundle, with the pulled-back module as its underlying module. -/
abbrev pbLB {Y Z : Scheme.{u}} (f : Y ⟶ Z) (L : LineBundle Z) : LineBundle Y :=
  ⟨(Scheme.Modules.pullback f).obj L.obj, L.property.pullback f⟩

/-- The restriction of the section attached to `u` to a piece is the Čech component. -/
lemma res_homEquivSections (u : C.Q →ₗ[R] A) (s : 𝒰.Idx 0) :
    res (pbLB (pullback.fst π (specMap R A)) L) (C.homEquivSections A u)
        ((𝒰.baseChange π A).inter s) =
      C.Θ A (Langlands.CommutativeAlgebra.CokernelDualHom.homEquiv C.δ A u).1 s := by
  have h := congrArg (fun c : (baseChangePresheaf π L.obj A).H0 (𝒰.baseChange π A) =>
      (c.1 : (baseChangePresheaf π L.obj A).cochain (𝒰.baseChange π A) 0) s)
    ((CechRep.sectionsEquivH0 (π := π) (M := L.obj) (𝒰 := 𝒰) A).apply_symm_apply
      (C.kerEquivH0 A (Langlands.CommutativeAlgebra.CokernelDualHom.homEquiv C.δ A u)))
  exact h

variable (g : pullback π (specMap R B) ⟶ pullback π (specMap R A)) (φ : A →ₐ[R] B)
  (hg₁ : g ≫ pullback.fst π (specMap R A) = pullback.fst π (specMap R B))
  (hg₂ : g ≫ pullback.snd π (specMap R A) =
    pullback.snd π (specMap R B) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))

include he hg₁ hg₂ in
/-- **The zero locus of `σ_{φ ∘ u}` is the pullback of the zero locus of `σ_u`.** -/
theorem zeroIdeal_comap_homEquivSections (u : C.Q →ₗ[R] A) :
    (zeroIdeal (pbLB (pullback.fst π (specMap R A)) L) (C.homEquivSections A u)).comap g =
      zeroIdeal (pbLB (pullback.fst π (specMap R B)) L)
        (C.homEquivSections B (φ.toLinearMap ∘ₗ u)) := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun s => ⟨(𝒰.baseChange π B).inter s, isAffineOpen_inter_of_idx_zero _ s⟩)
    (iSup_inter_idx_zero _) fun s => ?_
  have hle : (𝒰.baseChange π B).inter s ≤ g ⁻¹ᵁ (𝒰.baseChange π A).inter s := by
    rw [Scheme.OrderedAffineCover.baseChange_inter, Scheme.OrderedAffineCover.baseChange_inter,
      ← hg₁]
    exact fun y hy => hy
  rw [Scheme.IdealSheafData.ideal_comap_of_le _ g
      ⟨_, isAffineOpen_inter_of_idx_zero (𝒰.baseChange π A) s⟩ _ hle]
  have hA := zeroIdeal_ideal_of_equiv (pbLB (pullback.fst π (specMap R A)) L)
    (C.homEquivSections A u) ⟨_, isAffineOpen_inter_of_idx_zero (𝒰.baseChange π A) s⟩
    (frameEquiv (isFrameOn_tRes π L e he A s))
  have hB := zeroIdeal_ideal_of_equiv (pbLB (pullback.fst π (specMap R B)) L)
    (C.homEquivSections B (φ.toLinearMap ∘ₗ u))
    ⟨_, isAffineOpen_inter_of_idx_zero (𝒰.baseChange π B) s⟩
    (frameEquiv (isFrameOn_tRes π L e he B s))
  rw [hA, hB]
  have hrA := res_homEquivSections C u s
  have hrB := res_homEquivSections C (φ.toLinearMap ∘ₗ u) s
  erw [hrA, hrB]
  rw [Ideal.map_span, Set.image_singleton,
    Langlands.CommutativeAlgebra.CokernelDualHom.homEquiv_comp]
  have key := appLE_coordΘ e he C g φ hg₁ hg₂
    (Langlands.CommutativeAlgebra.CokernelDualHom.homEquiv C.δ A u).1 s hle
  exact congrArg (fun x => Ideal.span {x}) key

include he in
/-- **Scaling `v` by a unit does not change the zero locus of `σ_v`.** -/
theorem zeroIdeal_homEquivSections_smul (c : B) (hc : IsUnit c) (v : C.Q →ₗ[R] B) :
    zeroIdeal (pbLB (pullback.fst π (specMap R B)) L) (C.homEquivSections B (c • v)) =
      zeroIdeal (pbLB (pullback.fst π (specMap R B)) L) (C.homEquivSections B v) := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun s => ⟨(𝒰.baseChange π B).inter s, isAffineOpen_inter_of_idx_zero _ s⟩)
    (iSup_inter_idx_zero _) fun s => ?_
  have h1 := zeroIdeal_ideal_of_equiv (pbLB (pullback.fst π (specMap R B)) L)
    (C.homEquivSections B (c • v)) ⟨_, isAffineOpen_inter_of_idx_zero (𝒰.baseChange π B) s⟩
    (frameEquiv (isFrameOn_tRes π L e he B s))
  have h2 := zeroIdeal_ideal_of_equiv (pbLB (pullback.fst π (specMap R B)) L)
    (C.homEquivSections B v) ⟨_, isAffineOpen_inter_of_idx_zero (𝒰.baseChange π B) s⟩
    (frameEquiv (isFrameOn_tRes π L e he B s))
  rw [h1, h2]
  have hrA := res_homEquivSections C (c • v) s
  have hrB := res_homEquivSections C v s
  erw [hrA, hrB]
  rw [Langlands.CommutativeAlgebra.CokernelDualHom.homEquiv_smul, map_smul]
  change Ideal.span {frameEquiv (isFrameOn_tRes π L e he B s)
      ((algebraOfHom (pullback.snd π (specMap R B)) ((𝒰.baseChange π B).inter s)).algebraMap c •
        C.Θ B (Langlands.CommutativeAlgebra.CokernelDualHom.homEquiv C.δ B v).1 s)} = _
  rw [map_smul, smul_eq_mul, Ideal.span_singleton_mul_left_unit (hc.map _)]

end ZeroLocus

end Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule
