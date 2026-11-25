/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectRHomEvaluationLocal
import WeilConjectures.Topology.SheafIsomorphismLocalOpenCover
import Mathlib.CategoryTheory.Yoneda

/-! # Local computations for the perfect internal dual -/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem changeAdjunction (C : Type*) [Category C] [MonoidalCategory C]
    (K H N : C)
    (e e₀ : ∀ A : C, (A ⟶ H) ≃ (A ⊗ K ⟶ N))
    (he : ∀ (A B : C) (f : A ⟶ B) (q : B ⟶ H),
      e A (f ≫ q) = (f ▷ K) ≫ e B q)
    (he₀ : ∀ (A B : C) (f : A ⟶ B) (q : B ⟶ H),
      e₀ A (f ≫ q) = (f ▷ K) ≫ e₀ B q) :
    ∃ t : H ⟶ H, IsIso t ∧ ∀ (A : C) (f : A ⟶ H), e A f = e₀ A (f ≫ t) := by
  let t := (e₀ H).symm (e H (𝟙 H))
  have ht (A : C) (f : A ⟶ H) : e A f = e₀ A (f ≫ t) := by
    rw [he₀, Equiv.apply_symm_apply]
    simpa only [Category.comp_id] using he A H f (𝟙 H)
  refine ⟨t, ?_, ht⟩
  apply isIso_of_yoneda_map_bijective
  intro A
  have h : (fun f : A ⟶ H ↦ f ≫ t) = ⇑((e A).trans (e₀ A).symm) := by
    funext f
    exact (e₀ A).injective (by
      simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using (ht A f).symm)
  rw [h]
  exact ((e A).trans (e₀ A).symm).bijective

private theorem evaluationIso_changeAdjunction
    (C : Type*) [Category C] [MonoidalCategory C] (K : C) (H : C → C)
    (e e₀ : ∀ A N : C, (A ⟶ H N) ≃ (A ⊗ K ⟶ N))
    (he : ∀ (A B N : C) (f : A ⟶ B) (q : B ⟶ H N),
      e A N (f ≫ q) = (f ▷ K) ≫ e B N q)
    (he₀ : ∀ (A B N : C) (f : A ⟶ B) (q : B ⟶ H N),
      e₀ A N (f ≫ q) = (f ▷ K) ≫ e₀ B N q)
    (h₀ : ∀ N : C, IsIso ((e₀ (N ⊗ H (𝟙_ C)) N).symm
      ((α_ N (H (𝟙_ C)) K).hom ≫ N ◁ e₀ (H (𝟙_ C)) (𝟙_ C) (𝟙 _) ≫
        (ρ_ N).hom))) :
    ∀ N : C, IsIso ((e (N ⊗ H (𝟙_ C)) N).symm
      ((α_ N (H (𝟙_ C)) K).hom ≫ N ◁ e (H (𝟙_ C)) (𝟙_ C) (𝟙 _) ≫
        (ρ_ N).hom)) := by
  intro N
  obtain ⟨t, ht, hte⟩ := changeAdjunction C K (H N) N
    (fun A ↦ e A N) (fun A ↦ e₀ A N) (fun A B ↦ he A B N) (fun A B ↦ he₀ A B N)
  obtain ⟨t₁, ht₁, ht₁e⟩ := changeAdjunction C K (H (𝟙_ C)) (𝟙_ C)
    (fun A ↦ e A (𝟙_ C)) (fun A ↦ e₀ A (𝟙_ C))
    (fun A B ↦ he A B (𝟙_ C)) (fun A B ↦ he₀ A B (𝟙_ C))
  let φ := (e (N ⊗ H (𝟙_ C)) N).symm
    ((α_ N (H (𝟙_ C)) K).hom ≫ N ◁ e (H (𝟙_ C)) (𝟙_ C) (𝟙 _) ≫ (ρ_ N).hom)
  let φ₀ := (e₀ (N ⊗ H (𝟙_ C)) N).symm
    ((α_ N (H (𝟙_ C)) K).hom ≫ N ◁ e₀ (H (𝟙_ C)) (𝟙_ C) (𝟙 _) ≫ (ρ_ N).hom)
  have hφ : φ ≫ t = (N ◁ t₁) ≫ φ₀ := by
    apply (e₀ (N ⊗ H (𝟙_ C)) N).injective
    rw [← hte, he₀]
    dsimp only [φ, φ₀]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, ht₁e]
    simp only [Category.id_comp]
    have hunit := he₀ (H (𝟙_ C)) (H (𝟙_ C)) (𝟙_ C) t₁ (𝟙 _)
    simp only [Category.comp_id] at hunit
    rw [hunit, whiskerLeft_comp, associator_naturality_middle_assoc]
    simp only [Category.assoc]
  have : IsIso φ₀ := h₀ N
  have : IsIso (φ ≫ t) := by rw [hφ]; infer_instance
  exact IsIso.of_isIso_comp_right φ t

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensor evaluation is invertible for a perfect first argument.
Source: Stacks Project, Cohomology, Tags 08DQ and 08DM.
Proof: refine the perfect neighbourhoods to affine opens and represent K by a
bounded complex E of direct summands of finite free sheaves. Restriction of RHom
commutes with these opens, and the strictly-perfect Hom lemma computes RHom by
ordinary Hom complexes. The dual of E is again bounded and termwise finite projective,
hence K-flat. For an arbitrary complex F, the evaluation comparison is the total
of F^p tensor Hom(E^q,O) to Hom(E^q,F^p). It is an isomorphism for finite free
E^q and for its direct summands. These identifications respect differentials and the canonical
adjunction. For any natural adjunction bijection in the statement, Yoneda changes
its adjuncts by invertible natural transformations, so invertibility is unchanged.
Finally test the globally defined maps on cohomology sheaves on the open cover;
no morphisms are glued. This works for unbounded F and does not assume F is quasi-coherent.
(blueprint: lem-pc-perfect-rhom-evaluation-isomorphisms) -/
theorem perfect_rhom_evaluation_isomorphisms
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K : schemeDerivedQCohCategory X)
    (hK : Scheme.IsPerfect X K.obj)
    (adj : ∀ A B C : schemeDerivedCategory X,
      (A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)) ≃ (A ⊗ B ⟶ C))
    (hadj : ∀ (A A' B B' C C' : schemeDerivedCategory X)
      (a : A' ⟶ A) (b : B' ⟶ B) (c : C ⟶ C')
      (f : A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)),
      adj A' B' C' (a ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.op, c)) =
        (a ⊗ₘ b) ≫ adj A B C f ≫ c)
    (D : schemeDerivedCategory X)
    (hD : D =
      (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op K.obj, 𝟙_ (schemeDerivedCategory X))) :
    (∀ N : schemeDerivedCategory X,
      IsIso ((adj (N ⊗ D) K.obj N).symm
        ((α_ N D K.obj).hom ≫ N ◁
          (adj D K.obj (𝟙_ (schemeDerivedCategory X)) (eqToHom hD)) ≫ (ρ_ N).hom))) := by
  classical
  subst D
  let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
    X.toRingedSpace.sheaf
  let e₀ := schemeDerivedTensorHomEquiv.{u, w} X
  have he₀ : IsCanonicalDerivedTensorHom X e₀ :=
    Classical.choose_spec (exists_canonicalDerivedTensorHom.{u, w} X)
  have hn (A B N : schemeDerivedCategory X) (f : A ⟶ B)
      (q : B ⟶ H.obj (op K.obj, N)) :
      adj A K.obj N (f ≫ q) = (f ▷ K.obj) ≫ adj B K.obj N q := by
    have hh := hadj B A K.obj K.obj N N f (𝟙 _) (𝟙 _) q
    change adj A K.obj N (f ≫ q ≫ H.map (𝟙 (op K.obj, N))) =
      (f ⊗ₘ 𝟙 K.obj) ≫ adj B K.obj N q ≫ 𝟙 N at hh
    simpa only [H.map_id (op K.obj, N), Category.comp_id, tensorHom_id] using hh
  have hn₀ (A B N : schemeDerivedCategory X) (f : A ⟶ B)
      (q : B ⟶ H.obj (op K.obj, N)) :
      e₀ A K.obj N (f ≫ q) = (f ▷ K.obj) ≫ e₀ B K.obj N q := by
    have hh := he₀.1 B A K.obj K.obj N N f (𝟙 _) (𝟙 _) q
    change e₀ A K.obj N (f ≫ q ≫ H.map (𝟙 (op K.obj, N))) =
      (f ⊗ₘ 𝟙 K.obj) ≫ e₀ B K.obj N q ≫ 𝟙 N at hh
    simpa only [H.map_id (op K.obj, N), Category.comp_id, tensorHom_id] using hh
  apply evaluationIso_changeAdjunction (schemeDerivedCategory X) K.obj
    (fun N ↦ H.obj (op K.obj, N)) (fun A N ↦ adj A K.obj N)
    (fun A N ↦ e₀ A K.obj N) hn hn₀
  intro N
  let D := H.obj (op K.obj, 𝟙_ (schemeDerivedCategory X))
  let φ := (e₀ (N ⊗ D) K.obj N).symm
    ((α_ N D K.obj).hom ≫ N ◁ e₀ D K.obj (𝟙_ (schemeDerivedCategory X)) (𝟙 D) ≫
      (ρ_ N).hom)
  change IsIso φ
  choose U hx P hstrict hP using hK
  have hcover : ⨆ x : X, U x = ⊤ := by
    apply le_antisymm le_top
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  have hlocal (x : X) : IsIso ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) (U x)).mapDerivedCategory.map φ) :=
    strictlyPerfect_rhom_evaluation_isIso_on_open X K.obj N (U x) (P x) (hstrict x) (hP x)
  apply (DerivedCategory.isIso_iff _ φ).2
  intro n
  apply (sheaf_module_isIso_iff_isIso_over_open_cover
    X.toRingedSpace X U hcover _ _ _).2
  intro x
  have := hlocal x
  exact (NatIso.isIso_map_iff
    ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
      (U x)).mapDerivedCategoryHomologyFunctorIso n) φ).2 (by
        dsimp
        infer_instance)

end AlgebraicGeometry
