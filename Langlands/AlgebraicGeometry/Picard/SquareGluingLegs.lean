import Langlands.AlgebraicGeometry.Picard.SquareGluingRespect
import Langlands.AlgebraicGeometry.Picard.SquareGluingFullyFaithful

/-! # Legs and corners of locally realized actual gluing data -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SquareGluingDescent

section Bridge

variable {X Y : Scheme.{u}}

/-- The underlying module map of an arrow of actual line bundles. -/
def mh {M M' : PicardGroupoid X} (θ : M ⟶ M') : M.of.obj ⟶ M'.of.obj :=
  θ.iso.hom.hom

/-- The underlying module isomorphism of an arrow of actual line bundles. -/
def mi {M M' : PicardGroupoid X} (θ : M ⟶ M') : M.of.obj ≅ M'.of.obj :=
  (LineBundle.forget X).mapIso θ.iso

/-- The arrow of actual line bundles given by an isomorphism of underlying modules. -/
def pic {M M' : PicardGroupoid X} (e : M.of.obj ≅ M'.of.obj) : M ⟶ M' :=
  (Core.isoMk (ObjectProperty.isoMk _ e)).hom

lemma mi_hom {M M' : PicardGroupoid X} (θ : M ⟶ M') : (mi θ).hom = mh θ := rfl

lemma mh_pic {M M' : PicardGroupoid X} (e : M.of.obj ≅ M'.of.obj) : mh (pic e) = e.hom := rfl

lemma mh_comp {M M' M'' : PicardGroupoid X} (θ : M ⟶ M') (θ' : M' ⟶ M'') :
    mh (θ ≫ θ') = mh θ ≫ mh θ' := rfl

lemma mh_map (f : X ⟶ Y) {M M' : PicardGroupoid Y} (θ : M ⟶ M') :
    mh ((P f).map θ) = (Scheme.Modules.pullback f).map (mh θ) := rfl

lemma mh_injective {M M' : PicardGroupoid X} {θ θ' : M ⟶ M'} (h : mh θ = mh θ') : θ = θ' :=
  Core.hom_ext (ObjectProperty.hom_ext _ h)

lemma mh_sqH {X₀ X₁ X₂ : Scheme.{u}} (i₁ : X₀ ⟶ X₁) (i₂ : X₀ ⟶ X₂) (j₁ : X₁ ⟶ Y)
    (j₂ : X₂ ⟶ Y) (w : i₁ ≫ j₁ = i₂ ≫ j₂) (L : PicardGroupoid Y) :
    mh (sqH i₁ i₂ j₁ j₂ w L) =
      (Langlands.Scheme.Modules.squarePullbackIso j₂ i₁ i₂ j₁ w L.of.obj).hom :=
  SquareGluingFullyFaithful.squarePullbackIso_app i₁ i₂ j₁ j₂ w L

end Bridge

section Leg

variable {X₀ X₁ X₂ Y : Scheme.{u}}

@[reassoc]
lemma sqH_nat (i₁ : X₀ ⟶ X₁) (i₂ : X₀ ⟶ X₂) (j₁ : X₁ ⟶ Y) (j₂ : X₂ ⟶ Y)
    (w : i₁ ≫ j₁ = i₂ ≫ j₂) {L L' : PicardGroupoid Y} (a : L ⟶ L') :
    (P i₁).map ((P j₁).map a) ≫ sqH i₁ i₂ j₁ j₂ w L' =
      sqH i₁ i₂ j₁ j₂ w L ≫ (P i₂).map ((P j₂).map a) :=
  (PicardGroupoid.squarePullbackIso i₁ i₂ j₁ j₂ w).hom.naturality a

/-- An overlap identity through the two composition comparisons gives the
corresponding square-comparison identity. -/
lemma leg_of_eq (a₁ : X₀ ⟶ X₁) (b₁ : X₁ ⟶ Y) (a₂ : X₀ ⟶ X₂) (b₂ : X₂ ⟶ Y)
    (w : a₁ ≫ b₁ = a₂ ≫ b₂) {L L' : PicardGroupoid Y}
    (x : (P b₁).obj L ⟶ (P b₁).obj L') (y : (P b₂).obj L ⟶ (P b₂).obj L')
    (h : (pcI a₁ b₁ L ≫ (P a₁).map x ≫ pcH a₁ b₁ L') ≫
        eqToHom (congrArg (fun f ↦ (P f).obj L') w) =
      eqToHom (congrArg (fun f ↦ (P f).obj L) w) ≫
        pcI a₂ b₂ L ≫ (P a₂).map y ≫ pcH a₂ b₂ L') :
    (P a₁).map x ≫ sqH a₁ a₂ b₁ b₂ w L' = sqH a₁ a₂ b₁ b₂ w L ≫ (P a₂).map y := by
  rw [sqH_eq, sqH_eq, ← cancel_epi (pcI a₁ b₁ L)]
  simp only [Category.assoc, pcI_pcH_assoc]
  have h' := congrArg (· ≫ pcI a₂ b₂ L') h
  simp only [Category.assoc, pcH_pcI, Category.comp_id] at h'
  exact h'

end Leg

open CubeMap

variable {S T T' : Sq.{u}} {D : S.GD}

namespace CubeMap

lemma CompI_inv_left (c : CubeMap S T) (c' : CubeMap T T') (E : S.GD) :
    (CompI c c' E).inv.left = pcI c'.g₁ c.g₁ E.left := rfl

lemma CompI_inv_right (c : CubeMap S T) (c' : CubeMap T T') (E : S.GD) :
    (CompI c c' E).inv.right = pcI c'.g₂ c.g₂ E.right := rfl

lemma R_obj_hom (c : CubeMap S T) (E : S.GD) :
    (c.R.obj E).hom = sqH T.i₁ c.g₀ c.g₁ S.i₁ c.k₁ E.left ≫ (P c.g₀).map E.hom ≫
      (PicardGroupoid.squarePullbackIso T.i₂ c.g₀ c.g₂ S.i₂ c.k₂).inv.app E.right := rfl

end CubeMap

/-- An arrow of restrictions whose legs are restrictions of two arrows makes
the corner square of those two arrows commute after restriction. -/
lemma map_w (c : CubeMap S T) {E E' : S.GD} {l : E.left ⟶ E'.left}
    {r : E.right ⟶ E'.right} (Ψ : c.R.obj E ⟶ c.R.obj E')
    (hl : Ψ.left = (P c.g₁).map l) (hr : Ψ.right = (P c.g₂).map r) :
    (P c.g₀).map ((P S.i₁).map l ≫ E'.hom) = (P c.g₀).map (E.hom ≫ (P S.i₂).map r) := by
  have hn := (PicardGroupoid.squarePullbackIso T.i₂ c.g₀ c.g₂ S.i₂ c.k₂).inv.naturality r
  simp only [Functor.comp_map] at hn
  have h := Ψ.w
  rw [hl, hr, R_obj_hom, R_obj_hom, sqH_nat_assoc] at h
  simp only [Category.assoc] at h
  rw [← hn, cancel_epi] at h
  simp only [Functor.map_comp]
  simpa only [← Category.assoc, cancel_mono] using h

/-- Leg extraction: an identity of restricted arrows on the overlap square gives
the first-leg overlap identity. -/
lemma leg_left {c : CubeMap S T} {c' : CubeMap S T'} {E E' : S.GD}
    (Ψ₁ : c.R.obj E ⟶ c.R.obj E') (Ψ₂ : c'.R.obj E ⟶ c'.R.obj E')
    (h : pbH c (fstC c c') Ψ₁ ≫ eqToHom (congrArg (fun e ↦ e.R.obj E') (fstC_comp c c')) =
      eqToHom (congrArg (fun e ↦ e.R.obj E) (fstC_comp c c')) ≫ pbH c' (sndC c c') Ψ₂) :
    (P (fstC c c').g₁).map Ψ₁.left ≫
        sqH (fstC c c').g₁ (sndC c c').g₁ c.g₁ c'.g₁ (comp_eq_g₁ (fstC_comp c c')) E'.left =
      sqH (fstC c c').g₁ (sndC c c').g₁ c.g₁ c'.g₁ (comp_eq_g₁ (fstC_comp c c')) E.left ≫
        (P (sndC c c').g₁).map Ψ₂.left := by
  have h' := congrArg CommaMorphism.left h
  simp only [Comma.comp_left, Comma.eqToHom_left, pbH, CompI_inv_left, R_map_left,
    CompA_left] at h'
  exact leg_of_eq _ _ _ _ (comp_eq_g₁ (fstC_comp c c')) Ψ₁.left Ψ₂.left h'

/-- Leg extraction for the second leg. -/
lemma leg_right {c : CubeMap S T} {c' : CubeMap S T'} {E E' : S.GD}
    (Ψ₁ : c.R.obj E ⟶ c.R.obj E') (Ψ₂ : c'.R.obj E ⟶ c'.R.obj E')
    (h : pbH c (fstC c c') Ψ₁ ≫ eqToHom (congrArg (fun e ↦ e.R.obj E') (fstC_comp c c')) =
      eqToHom (congrArg (fun e ↦ e.R.obj E) (fstC_comp c c')) ≫ pbH c' (sndC c c') Ψ₂) :
    (P (fstC c c').g₂).map Ψ₁.right ≫
        sqH (fstC c c').g₂ (sndC c c').g₂ c.g₂ c'.g₂ (comp_eq_g₂ (fstC_comp c c')) E'.right =
      sqH (fstC c c').g₂ (sndC c c').g₂ c.g₂ c'.g₂ (comp_eq_g₂ (fstC_comp c c')) E.right ≫
        (P (sndC c c').g₂).map Ψ₂.right := by
  have h' := congrArg CommaMorphism.right h
  simp only [Comma.comp_right, Comma.eqToHom_right, pbH, CompI_inv_right, R_map_right,
    CompA_right] at h'
  exact leg_of_eq _ _ _ _ (comp_eq_g₂ (fstC_comp c c')) Ψ₁.right Ψ₂.right h'

/-- Two local realizations, linked by an arrow respecting them, and two local
identifications of a global bundle compatible with that arrow give compatible
restricted arrows of gluing data on a common refinement. -/
lemma legs_compat_of {W : Sq.{u}} (c : CubeMap S T) (c' : CubeMap S T') (a : CubeMap T W)
    (b : CubeMap T' W) (e : comp a c = comp b c') {N : PicardGroupoid S.X}
    {N₁ : PicardGroupoid T.X} {N₂ : PicardGroupoid T'.X}
    (ρ₁ : T.C.obj N₁ ≅ c.R.obj D) (ρ₂ : T'.C.obj N₂ ≅ c'.R.obj D)
    (σ₁ : (P c.t).obj N ⟶ N₁) (σ₂ : (P c'.t).obj N ⟶ N₂)
    (τ : (P a.t).obj N₁ ⟶ (P b.t).obj N₂) (hτ : Resp τ (pb c a ρ₁) (pb c' b ρ₂))
    (hσ : (P a.t).map σ₁ ≫ τ = sqH a.t b.t c.t c'.t (comp_eq_t e) N ≫ (P b.t).map σ₂) :
    pbH c a ((cIi c N).inv ≫ T.C.map σ₁ ≫ ρ₁.hom) ≫
        eqToHom (congrArg (fun e ↦ e.R.obj D) e) =
      eqToHom (congrArg (fun e ↦ e.R.obj (S.C.obj N)) e) ≫
        pbH c' b ((cIi c' N).inv ≫ T'.C.map σ₂ ≫ ρ₂.hom) := by
  obtain ⟨_, hτ⟩ := hτ
  have key : (pcI a.t c.t N ≫ (P a.t).map σ₁) ≫ τ =
      eqToHom (congrArg (fun d : CubeMap S W ↦ (P d.t).obj N) e) ≫
        pcI b.t c'.t N ≫ (P b.t).map σ₂ := by
    rw [Category.assoc, hσ, sqH_eq]
    simp only [Category.assoc, pcI_pcH_assoc]
  have hc := cIi_congr e N
  rw [pbH_phi, pbH_phi, Category.assoc, Category.assoc, ← hτ, ← Functor.map_comp_assoc, key,
    Functor.map_comp_assoc, reassoc_of% hc]

/-- `legs_compat_of` on the canonical overlap square of two cubes. -/
lemma legs_compat (c : CubeMap S T) (c' : CubeMap S T') {N : PicardGroupoid S.X}
    {N₁ : PicardGroupoid T.X} {N₂ : PicardGroupoid T'.X}
    (ρ₁ : T.C.obj N₁ ≅ c.R.obj D) (ρ₂ : T'.C.obj N₂ ≅ c'.R.obj D)
    (σ₁ : (P c.t).obj N ⟶ N₁) (σ₂ : (P c'.t).obj N ⟶ N₂)
    (τ : (P (fstC c c').t).obj N₁ ⟶ (P (sndC c c').t).obj N₂)
    (hτ : Resp τ (pb c (fstC c c') ρ₁) (pb c' (sndC c c') ρ₂))
    (hσ : (P (fstC c c').t).map σ₁ ≫ τ =
      sqH (fstC c c').t (sndC c c').t c.t c'.t (comp_eq_t (fstC_comp c c')) N ≫
        (P (sndC c c').t).map σ₂) :
    pbH c (fstC c c') ((cIi c N).inv ≫ T.C.map σ₁ ≫ ρ₁.hom) ≫
        eqToHom (congrArg (fun e ↦ e.R.obj D) (fstC_comp c c')) =
      eqToHom (congrArg (fun e ↦ e.R.obj (S.C.obj N)) (fstC_comp c c')) ≫
        pbH c' (sndC c c') ((cIi c' N).inv ≫ T'.C.map σ₂ ≫ ρ₂.hom) :=
  legs_compat_of c c' (fstC c c') (sndC c c') (fstC_comp c c') ρ₁ ρ₂ σ₁ σ₂ τ hτ hσ

end Langlands.AlgebraicGeometry.Picard.SquareGluingDescent
