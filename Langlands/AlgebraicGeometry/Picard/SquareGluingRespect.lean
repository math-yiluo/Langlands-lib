import Langlands.AlgebraicGeometry.Picard.SquareGluingDescent

/-! # Arrows respecting realizations of restricted actual gluing data -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SquareGluingDescent

section Leg

variable {X₀ X₁ X₂ Y : Scheme.{u}}

/-- The square comparison is the composite of the two composition comparisons. -/
lemma sqH_eq (i₁ : X₀ ⟶ X₁) (i₂ : X₀ ⟶ X₂) (j₁ : X₁ ⟶ Y) (j₂ : X₂ ⟶ Y)
    (w : i₁ ≫ j₁ = i₂ ≫ j₂) (L : PicardGroupoid Y) :
    sqH i₁ i₂ j₁ j₂ w L = pcH i₁ j₁ L ≫ eqToHom (by rw [w]) ≫ pcI i₂ j₂ L := by
  simp only [sqH, PicardGroupoid.squarePullbackIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  rfl

end Leg

open CubeMap

variable {S T T' T'' : Sq.{u}} {D : S.GD}

/-- An arrow of bundles on `T.X` respects two realizations of restrictions of `D`
along equal cubes. -/
def Resp {c c' : CubeMap S T} {M M' : PicardGroupoid T.X} (θ : M ⟶ M')
    (σ : T.C.obj M ≅ c.R.obj D) (σ' : T.C.obj M' ≅ c'.R.obj D) : Prop :=
  ∃ h : c = c', T.C.map θ ≫ σ'.hom = σ.hom ≫ eqToHom (congrArg (fun e ↦ e.R.obj D) h)

namespace Resp

variable {c c' c'' : CubeMap S T} {M M' M'' : PicardGroupoid T.X}
  {σ : T.C.obj M ≅ c.R.obj D} {σ' : T.C.obj M' ≅ c'.R.obj D}
  {σ'' : T.C.obj M'' ≅ c''.R.obj D}

lemma of_eq {θ : M ⟶ M'} {σ₁ : T.C.obj M' ≅ c.R.obj D} (h : T.C.map θ ≫ σ₁.hom = σ.hom) :
    Resp θ σ σ₁ :=
  ⟨rfl, by simpa using h⟩

lemma of_eq' {θ : M ⟶ M'} (h : c = c')
    (H : σ.hom = T.C.map θ ≫ σ'.hom ≫ eqToHom (congrArg (fun e ↦ e.R.obj D) h.symm)) :
    Resp θ σ σ' := by
  subst h
  exact ⟨rfl, by simpa using H.symm⟩

lemma eq {θ : M ⟶ M'} {σ₁ : T.C.obj M' ≅ c.R.obj D} (h : Resp θ σ σ₁) :
    T.C.map θ ≫ σ₁.hom = σ.hom := by
  obtain ⟨_, h⟩ := h
  simpa using h

lemma comp {θ : M ⟶ M'} {θ' : M' ⟶ M''} (h : Resp θ σ σ') (h' : Resp θ' σ' σ'') :
    Resp (θ ≫ θ') σ σ'' := by
  obtain ⟨rfl, h⟩ := h
  obtain ⟨rfl, h'⟩ := h'
  refine ⟨rfl, ?_⟩
  simp only [eqToHom_refl, Category.comp_id] at h h' ⊢
  rw [Functor.map_comp, Category.assoc, h', h]

lemma symm (θ : M ≅ M') (h : Resp θ.hom σ σ') : Resp θ.inv σ' σ := by
  obtain ⟨rfl, h⟩ := h
  refine ⟨rfl, ?_⟩
  simp only [eqToHom_refl, Category.comp_id] at h ⊢
  rw [← h, ← Category.assoc, ← Functor.map_comp, θ.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

lemma unique [T.C.Faithful] {θ θ' : M ⟶ M'} (h : Resp θ σ σ') (h' : Resp θ' σ σ') :
    θ = θ' := by
  obtain ⟨e, h⟩ := h
  obtain ⟨_, h'⟩ := h'
  apply T.C.map_injective
  rw [← cancel_mono σ'.hom, h, h']

/-- Pulling back along a further cube preserves respect. -/
lemma along (d : CubeMap T T') {θ : M ⟶ M'} (h : Resp θ σ σ') :
    Resp ((P d.t).map θ) (SquareGluingDescent.pb c d σ) (SquareGluingDescent.pb c' d σ') := by
  obtain ⟨rfl, h⟩ := h
  simp only [eqToHom_refl, Category.comp_id] at h
  exact of_eq (pb_respects c d σ σ' θ h)

end Resp

/-- The composition comparison respects successive and composite pullbacks. -/
lemma resp_pcH (c : CubeMap S T) (e : CubeMap T T') (d : CubeMap T' T'')
    {N : PicardGroupoid T.X} (ρ : T.C.obj N ≅ c.R.obj D) :
    Resp (pcH d.t e.t N) (pb (comp e c) d (pb c e ρ)) (pb c (comp d e) ρ) :=
  Resp.of_eq' (comp_assoc c e d).symm (pb_pb c e d ρ)

/-- The inverse composition comparison respects composite and successive pullbacks. -/
lemma resp_pcI (c : CubeMap S T) (e : CubeMap T T') (d : CubeMap T' T'')
    {N : PicardGroupoid T.X} (ρ : T.C.obj N ≅ c.R.obj D) :
    Resp (pcI d.t e.t N) (pb c (comp d e) ρ) (pb (comp e c) d (pb c e ρ)) :=
  Resp.symm ((PicardGroupoid.pullbackComp d.t e.t).app N) (resp_pcH c e d ρ)

/-- The equality-induced arrow along an equality of cubes respects the pullbacks. -/
lemma resp_eqToHom (c : CubeMap S T) {d d' : CubeMap T T'} (hd : d = d')
    {N : PicardGroupoid T.X} (ρ : T.C.obj N ≅ c.R.obj D) :
    Resp (eqToHom (congrArg (fun d : CubeMap T T' ↦ (P d.t).obj N) hd))
      (pb c d ρ) (pb c d' ρ) := by
  subst hd
  exact Resp.of_eq (by simp)

/-- The square comparison respects the two successive pullbacks along two
factorizations of one cube. -/
lemma resp_sqH (c : CubeMap S T) {T₁ T₂ : Sq.{u}} (d₁ : CubeMap T T₁) (e₁ : CubeMap T₁ T')
    (d₂ : CubeMap T T₂) (e₂ : CubeMap T₂ T') (hd : comp e₁ d₁ = comp e₂ d₂)
    (w : e₁.t ≫ d₁.t = e₂.t ≫ d₂.t) {N : PicardGroupoid T.X} (ρ : T.C.obj N ≅ c.R.obj D) :
    Resp (sqH e₁.t e₂.t d₁.t d₂.t w N) (pb (comp d₁ c) e₁ (pb c d₁ ρ))
      (pb (comp d₂ c) e₂ (pb c d₂ ρ)) := by
  rw [sqH_eq]
  exact (resp_pcH c d₁ e₁ ρ).comp ((resp_eqToHom c hd ρ).comp (resp_pcI c d₂ e₂ ρ))

section PullbackOfArrows

/-- Restrict an arrow between restrictions along a further cube. -/
def pbH (c : CubeMap S T) (e : CubeMap T T') {E E' : S.GD} (Ψ : c.R.obj E ⟶ c.R.obj E') :
    (comp e c).R.obj E ⟶ (comp e c).R.obj E' :=
  (CompI c e E).inv ≫ e.R.map Ψ ≫ CompA c e E'

/-- The comparison of a composite cube, solved for the inner comparison. -/
@[reassoc]
lemma cIi_comp_inv (c : CubeMap S T) (e : CubeMap T T') (L : PicardGroupoid S.X) :
    (cIi (comp e c) L).inv ≫ T'.C.map (pcI e.t c.t L) ≫ cIa e ((P c.t).obj L) =
      (CompI c e (S.C.obj L)).inv ≫ e.R.map (cIi c L).inv := by
  rw [Iso.inv_comp_eq, cIi_hom, cI_comp, ← CompI_hom, ← cIi_hom c L]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.map_hom_inv_id, Category.comp_id]

/-- Restricting a realization-induced arrow along a further cube. -/
lemma pbH_phi (c : CubeMap S T) (e : CubeMap T T') {L : PicardGroupoid S.X}
    {N' : PicardGroupoid T.X} (σ : (P c.t).obj L ⟶ N') (ρ : T.C.obj N' ≅ c.R.obj D) :
    pbH c e ((cIi c L).inv ≫ T.C.map σ ≫ ρ.hom) =
      (cIi (comp e c) L).inv ≫ T'.C.map (pcI e.t c.t L ≫ (P e.t).map σ) ≫
        (pb c e ρ).hom := by
  rw [pbH, pb_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← cIi_comp_inv_assoc, cIa_nat_assoc]

/-- Comparisons of equal cubes agree through the equality-induced arrows. -/
lemma cIi_congr {c c' : CubeMap S T} (h : c = c') (L : PicardGroupoid S.X) :
    (cIi c L).inv ≫ T.C.map (eqToHom (congrArg (fun c : CubeMap S T ↦ (P c.t).obj L) h)) =
      eqToHom (congrArg (fun c : CubeMap S T ↦ c.R.obj (S.C.obj L)) h) ≫ (cIi c' L).inv := by
  subst h
  simp

end PullbackOfArrows

end Langlands.AlgebraicGeometry.Picard.SquareGluingDescent
