import Langlands.AlgebraicGeometry.Modules.PullbackTensor
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

/-!
# The tensor of two frames is a frame

For module sheaves `A`, `B` on a scheme `Z`, an open `W` and sections `α ∈ A(W)`, `β ∈ B(W)`
which are frames over `W` in the sense of `Scheme.Modules.IsFrameOn` (every restriction to
`W' ⊆ W` is a basis of a free module of rank one), the section `tsec α β` of the sheaf tensor
`tensorObj A B`, the image of `α ⊗ β` under the sheafification unit, is again a frame over `W`.

On `W' ⊆ W` the sectionwise tensor `A(W') ⊗ B(W')` is free of rank one on `α ⊗ β`. The
sheafification unit is locally injective and locally surjective; since the sectionwise
tensor is isomorphic to the structure sheaf on opens of `W`, these give injectivity and
surjectivity of `g ↦ g • tsec α β` by the sheaf property of the structure sheaf.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.BiCech

open Langlands.Scheme.Modules

section Algebra

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- If `a` and `b` are bases of free modules of rank one, so is `a ⊗ b`. -/
lemma smul_tmul_bijective {a : M} {b : N} (ha : Function.Bijective fun g : R => g • a)
    (hb : Function.Bijective fun g : R => g • b) :
    Function.Bijective fun g : R => g • (a ⊗ₜ[R] b) := by
  let eA : R ≃ₗ[R] M := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R M a) ha
  let eB : R ≃ₗ[R] N := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R N b) hb
  let e : R ≃ₗ[R] M ⊗[R] N := (TensorProduct.lid R R).symm.trans (TensorProduct.congr eA eB)
  have he : (fun g : R => g • (a ⊗ₜ[R] b)) = e := by
    funext g
    change g • (a ⊗ₜ[R] b) = eA 1 ⊗ₜ[R] eB g
    have h1 : eA 1 = a := by
      change (1 : R) • a = a
      exact one_smul R a
    have h2 : eB g = g • b := rfl
    rw [h1, h2, TensorProduct.tmul_smul]
  rw [he]
  exact e.bijective

end Algebra

local instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

variable {Z : Scheme.{u}} {A B : Z.Modules}

/-- The image of `a ⊗ b` under the sheafification unit `A ⊗ B ⟶ tensorObj A B`. -/
def tsec {W : Z.Opens} (a : Γ(A, W)) (b : Γ(B, W)) : Γ(tensorObj A B, W) :=
  ((tensorSheafifyUnit A B).app (op W)).hom
    ((a : A.val.obj (op W)) ⊗ₜ[Z.presheaf.obj (op W)] (b : B.val.obj (op W)))

lemma tsec_map {W W' : Z.Opens} (h : W' ≤ W) (a : Γ(A, W)) (b : Γ(B, W)) :
    (tensorObj A B).presheaf.map (homOfLE h).op (tsec a b) =
      tsec (A.presheaf.map (homOfLE h).op a) (B.presheaf.map (homOfLE h).op b) := by
  have h' := PresheafOfModules.naturality_apply (tensorSheafifyUnit A B) (homOfLE h).op
    ((a : A.val.obj (op W)) ⊗ₜ[Z.presheaf.obj (op W)] (b : B.val.obj (op W)))
  erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul] at h'
  exact h'.symm

lemma tsec_smul {W : Z.Opens} (g : Γ(Z, W)) (a : Γ(A, W)) (b : Γ(B, W)) :
    tsec (g • a) b = g • tsec a b := by
  unfold tsec
  erw [← TensorProduct.smul_tmul', LinearMap.map_smul]
  rfl

/-- Local surjectivity of the sheafification unit, elementwise. -/
lemma exists_tsec_locally {V : Z.Opens} (y : Γ(tensorObj A B, V)) (z : Z) (hz : z ∈ V) :
    ∃ (V' : Z.Opens) (hV' : V' ≤ V), z ∈ V' ∧
      ∃ x, ((tensorSheafifyUnit A B).app (op V')).hom x =
          (tensorObj A B).presheaf.map (homOfLE hV').op y := by
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Z)
      ((PresheafOfModules.toPresheaf _).map (tensorSheafifyUnit A B)) := by
    change Presheaf.IsLocallySurjective _ (CategoryTheory.toSheafify _ _)
    infer_instance
  obtain ⟨V', f, ⟨w, hw⟩, hzV'⟩ :=
    Presheaf.imageSieve_mem (Opens.grothendieckTopology Z)
      ((PresheafOfModules.toPresheaf _).map (tensorSheafifyUnit A B)) (U := op V) y z hz
  exact ⟨V', leOfHom f, hzV', w, hw⟩

/-- Local injectivity of the sheafification unit, elementwise. -/
lemma eq_locally_of_tensorSheafifyUnit {V : Z.Opens}
    (x x' : (MonoidalCategoryStruct.tensorObj A.val B.val).obj (op V))
    (h : ((tensorSheafifyUnit A B).app (op V)).hom x =
      ((tensorSheafifyUnit A B).app (op V)).hom x') (z : Z) (hz : z ∈ V) :
    ∃ (V' : Z.Opens) (hV' : V' ≤ V), z ∈ V' ∧
      (MonoidalCategoryStruct.tensorObj A.val B.val).map (homOfLE hV').op x =
        (MonoidalCategoryStruct.tensorObj A.val B.val).map (homOfLE hV').op x' := by
  have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology Z)
      ((PresheafOfModules.toPresheaf _).map (tensorSheafifyUnit A B)) := by
    change Presheaf.IsLocallyInjective _ (CategoryTheory.toSheafify _ _)
    infer_instance
  obtain ⟨V', f, hf, hzV'⟩ :=
    Presheaf.equalizerSieve_mem (Opens.grothendieckTopology Z)
      ((PresheafOfModules.toPresheaf _).map (tensorSheafifyUnit A B)) (X := op V) x x' h z hz
  exact ⟨V', leOfHom f, hzV', hf⟩

open Scheme.Modules in
/-- The tensor of two frames over `W` is a frame over `W`. -/
theorem isFrameOn_tsec {W : Z.Opens} {α : Γ(A, W)} {β : Γ(B, W)} (hα : IsFrameOn α W)
    (hβ : IsFrameOn β W) : IsFrameOn (tsec α β) W := by
  -- the restricted frames
  set a : ∀ V : Z.Opens, V ≤ W → Γ(A, V) := fun V hV => A.presheaf.map (homOfLE hV).op α
  set b : ∀ V : Z.Opens, V ≤ W → Γ(B, V) := fun V hV => B.presheaf.map (homOfLE hV).op β
  have hab : ∀ (V : Z.Opens) (hV : V ≤ W),
      Function.Bijective fun g : Γ(Z, V) =>
        g • ((a V hV : A.val.obj (op V)) ⊗ₜ[Z.presheaf.obj (op V)] (b V hV : B.val.obj (op V))) :=
    fun V hV => smul_tmul_bijective (hα hV hV) (hβ hV hV)
  -- the map `θ_V : g ↦ g • tsec α β|_V`
  have hθ : ∀ (V : Z.Opens) (hV : V ≤ W) (g : Γ(Z, V)),
      g • (tensorObj A B).presheaf.map (homOfLE hV).op (tsec α β) =
        ((tensorSheafifyUnit A B).app (op V)).hom
          (g • ((a V hV : A.val.obj (op V)) ⊗ₜ[Z.presheaf.obj (op V)]
            (b V hV : B.val.obj (op V)))) := by
    intro V hV g
    rw [tsec_map, ← tsec_smul]
    unfold tsec
    erw [← TensorProduct.smul_tmul']
    rfl
  -- the sectionwise frames `ε_V = a_V ⊗ b_V` and their restrictions
  have hres : ∀ (V V' : Z.Opens) (hV : V ≤ W) (h : V' ≤ V) (g : Γ(Z, V)),
      (MonoidalCategoryStruct.tensorObj A.val B.val).map (homOfLE h).op
          (g • ((a V hV : A.val.obj (op V)) ⊗ₜ[Z.presheaf.obj (op V)]
            (b V hV : B.val.obj (op V)))) =
        Z.presheaf.map (homOfLE h).op g •
          ((a V' (h.trans hV) : A.val.obj (op V')) ⊗ₜ[Z.presheaf.obj (op V')]
            (b V' (h.trans hV) : B.val.obj (op V'))) := by
    intro V V' hV h g
    erw [PresheafOfModules.map_smul, PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
    have ha : A.val.map (homOfLE h).op (a V hV) = a V' (h.trans hV) := by
      change A.presheaf.map (homOfLE h).op (A.presheaf.map (homOfLE hV).op α) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    have hb : B.val.map (homOfLE h).op (b V hV) = b V' (h.trans hV) := by
      change B.presheaf.map (homOfLE h).op (B.presheaf.map (homOfLE hV).op β) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [← ha, ← hb]
    rfl
  have hθnat : ∀ (V V' : Z.Opens) (hV : V ≤ W) (h : V' ≤ V) (g : Γ(Z, V)),
      (tensorObj A B).presheaf.map (homOfLE h).op
          (g • (tensorObj A B).presheaf.map (homOfLE hV).op (tsec α β)) =
        Z.presheaf.map (homOfLE h).op g •
          (tensorObj A B).presheaf.map (homOfLE (h.trans hV)).op (tsec α β) := by
    intro V V' hV h g
    rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  -- injectivity of `θ_V`
  have hinj : ∀ (V : Z.Opens) (hV : V ≤ W) (g g' : Γ(Z, V)),
      g • (tensorObj A B).presheaf.map (homOfLE hV).op (tsec α β) =
        g' • (tensorObj A B).presheaf.map (homOfLE hV).op (tsec α β) → g = g' := by
    intro V hV g g' hgg'
    rw [hθ, hθ] at hgg'
    have hloc := fun z (hz : z ∈ V) => eq_locally_of_tensorSheafifyUnit _ _ hgg' z hz
    choose U hU hzU hUeq using hloc
    refine TopCat.Sheaf.eq_of_locally_eq' Z.sheaf (fun z : V => U z.1 z.2) V
      (fun z => homOfLE (hU z.1 z.2)) ?_ g g' fun z => ?_
    · intro z hz
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzU z hz⟩
    · have h1 := hUeq z.1 z.2
      rw [hres, hres] at h1
      exact (hab _ _).1 h1
  intro V hVW _
  refine ⟨fun g g' h => hinj V hVW g g' h, fun y => ?_⟩
  -- surjectivity of `θ_V`
  have hloc := fun z (hz : z ∈ V) => exists_tsec_locally (A := A) (B := B) y z hz
  choose U hU hzU x hx using hloc
  have hg : ∀ z (hz : z ∈ V), ∃ g : Γ(Z, U z hz),
      g • ((a (U z hz) ((hU z hz).trans hVW) : A.val.obj (op (U z hz))) ⊗ₜ[Z.presheaf.obj
        (op (U z hz))] (b (U z hz) ((hU z hz).trans hVW) : B.val.obj (op (U z hz)))) = x z hz :=
    fun z hz => (hab _ _).2 (x z hz)
  choose g hg using hg
  have hθy : ∀ z (hz : z ∈ V), g z hz •
      (tensorObj A B).presheaf.map (homOfLE ((hU z hz).trans hVW)).op (tsec α β) =
        (tensorObj A B).presheaf.map (homOfLE (hU z hz)).op y := by
    intro z hz
    rw [hθ, hg, hx]
  have hcover : V ≤ ⨆ z : V, U z.1 z.2 := by
    intro z hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzU z hz⟩
  obtain ⟨G, hG⟩ : ∃ G : Γ(Z, V),
      ∀ z : V, Z.presheaf.map (homOfLE (hU z.1 z.2)).op G = g z.1 z.2 := by
    obtain ⟨G, hG, -⟩ := TopCat.Sheaf.existsUnique_gluing' Z.sheaf (fun z : V => U z.1 z.2) V
      (fun z => homOfLE (hU z.1 z.2)) hcover (fun z => g z.1 z.2) (by
      intro z w
      change Z.presheaf.map (homOfLE inf_le_left).op (g z.1 z.2) =
        Z.presheaf.map (homOfLE inf_le_right).op (g w.1 w.2)
      refine hinj _ ((inf_le_left.trans (hU z.1 z.2)).trans hVW) _ _ ?_
      rw [← hθnat _ _ ((hU z.1 z.2).trans hVW) inf_le_left,
        ← hθnat _ _ ((hU w.1 w.2).trans hVW) inf_le_right, hθy, hθy,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
    exact ⟨G, hG⟩
  refine ⟨G, TopCat.Sheaf.eq_of_locally_eq' ⟨(tensorObj A B).presheaf, (tensorObj A B).isSheaf⟩
    (fun z : V => U z.1 z.2) V (fun z => homOfLE (hU z.1 z.2)) hcover _ _ fun z => ?_⟩
  change (tensorObj A B).presheaf.map (homOfLE (hU z.1 z.2)).op
    (G • (tensorObj A B).presheaf.map (homOfLE hVW).op (tsec α β)) = _
  rw [hθnat, hG z]
  exact hθy z.1 z.2

end Langlands.AlgebraicGeometry.Modules.BiCech
