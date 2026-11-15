import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreProofSteps

/-! # Points of a scheme representing a base change

Let `π : S' ⟶ S` and let `q' : X' ⟶ S'` represent the base change `F ×_S S'` of a presheaf `F`
on `Over S`. A morphism `a : T ⟶ X'` from an `S`-scheme `T`, compatible with the structure
morphisms, gives the element `pt a ∈ F(T)`: the pullback along `a` of the universal element.
This file records how these elements behave. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent

variable {S S' : Scheme.{u}} {π : S' ⟶ S} {F : (Over S)ᵒᵖ ⥤ Type v} {X' : Scheme.{u}}
  {q' : X' ⟶ S'} (e : (baseChange π F).RepresentableBy (Over.mk q'))

/-- The universal element of `F(X' ⟶ S' ⟶ S)`. -/
def univ : F.obj (op ((Over.map π).obj (Over.mk q'))) :=
  e.homEquiv (𝟙 (Over.mk q'))

/-- The element of `F(T)` given by a morphism `a : T ⟶ X'` with `a ≫ q' ≫ π = T ⟶ S`. -/
def pt (T : Over S) (a : T.left ⟶ X') (ha : a ≫ q' ≫ π = T.hom) : F.obj (op T) :=
  F.map (Over.homMk a ha : T ⟶ (Over.map π).obj (Over.mk q')).op (univ e)

lemma pt_congr {T : Over S} {a b : T.left ⟶ X'} (hab : a = b) (ha : a ≫ q' ≫ π = T.hom)
    (hb : b ≫ q' ≫ π = T.hom) : pt e T a ha = pt e T b hb := by
  subst hab
  rfl

lemma map_univ {T : Over S} (g : T ⟶ (Over.map π).obj (Over.mk q')) :
    F.map g.op (univ e) = pt e T g.left (Over.w g) := by
  unfold pt
  congr

lemma pt_comp {T₁ T₂ : Over S} (f : T₁ ⟶ T₂) (a : T₂.left ⟶ X') (ha : a ≫ q' ≫ π = T₂.hom) :
    F.map f.op (pt e T₂ a ha) = pt e T₁ (f.left ≫ a) (by rw [Category.assoc, ha, Over.w f]) := by
  unfold pt
  rw [← Functor.map_comp_apply, ← op_comp]
  congr

lemma homEquiv_eq_pt {T' : Over S'} (h : T' ⟶ Over.mk q') :
    e.homEquiv h = pt e ((Over.map π).obj T') h.left
      (by rw [Over.map_obj_hom, ← Over.w h, Category.assoc]; rfl) := by
  have : e.homEquiv h = e.homEquiv (h ≫ 𝟙 _) := by rw [Category.comp_id]
  rw [this, e.homEquiv_comp]
  exact map_univ e ((Over.map π).map h)

/-- Two morphisms to `X'` over the same morphism to `S'` with the same element of `F` are
equal. -/
lemma pt_inj {T : Over S} {a b : T.left ⟶ X'} (ha : a ≫ q' ≫ π = T.hom)
    (hb : b ≫ q' ≫ π = T.hom) (hq : a ≫ q' = b ≫ q') (h : pt e T a ha = pt e T b hb) :
    a = b := by
  let T' : Over S' := Over.mk (a ≫ q')
  let φ : (Over.map π).obj T' ⟶ T := Over.homMk (𝟙 T.left)
    (by simp [T', ha])
  have ka := homEquiv_eq_pt e (Over.homMk a rfl : T' ⟶ Over.mk q')
  have kb := homEquiv_eq_pt e (Over.homMk b hq.symm : T' ⟶ Over.mk q')
  have ea : pt e ((Over.map π).obj T') a (by rw [← Category.assoc]; rfl) =
      F.map φ.op (pt e T a ha) := by
    rw [pt_comp]
    exact pt_congr e (Category.id_comp _).symm _ _
  have eb : pt e ((Over.map π).obj T') b
      (by rw [← Category.assoc, hq.symm]; rfl) = F.map φ.op (pt e T b hb) := by
    rw [pt_comp]
    exact pt_congr e (Category.id_comp _).symm _ _
  have hk : (Over.homMk a rfl : T' ⟶ Over.mk q') = Over.homMk b hq.symm := by
    apply e.homEquiv.injective
    rw [ka, kb]
    simp only [Over.homMk_left]
    rw [ea, eb, h]
  exact congrArg CommaMorphism.left hk

/-- Every element of `F(T)` over a morphism `c : T ⟶ S'` lifting `T ⟶ S` comes from a
morphism `T ⟶ X'` over `c`. -/
lemma exists_pt (T : Over S) (c : T.left ⟶ S') (hc : c ≫ π = T.hom) (v : F.obj (op T)) :
    ∃ (a : T.left ⟶ X') (hac : a ≫ q' = c),
      pt e T a (by rw [← Category.assoc, hac, hc]) = v := by
  let T' : Over S' := Over.mk c
  let φ : (Over.map π).obj T' ⟶ T := Over.homMk (𝟙 T.left) (by simp [T', hc])
  let ψ : T ⟶ (Over.map π).obj T' := Over.homMk (𝟙 T.left) (by simp [T', hc])
  let h : T' ⟶ Over.mk q' := e.homEquiv.symm (F.map φ.op v)
  have hw : h.left ≫ q' = c := Over.w h
  refine ⟨h.left, hw, ?_⟩
  have k := homEquiv_eq_pt e h
  rw [show e.homEquiv h = F.map φ.op v from e.homEquiv.apply_symm_apply _] at k
  have k' := congrArg (F.map ψ.op) k
  rw [← Functor.map_comp_apply, ← op_comp, pt_comp] at k'
  have hψφ : ψ ≫ φ = 𝟙 T := by ext; simp [φ, ψ]
  rw [hψφ, op_id, Functor.map_id_apply] at k'
  rw [k']
  exact pt_congr e (Category.id_comp _).symm _ _

/-- The pullback `X' ×_S S'`, with its structure morphism through the second factor. -/
abbrev prodOver (q' : X' ⟶ S') (π : S' ⟶ S) : Over S :=
  Over.mk (pullback.snd (q' ≫ π) π ≫ π)

lemma fst_comp_eq (q' : X' ⟶ S') (π : S' ⟶ S) :
    pullback.fst (q' ≫ π) π ≫ q' ≫ π = (prodOver q' π).hom :=
  pullback.condition

/-- The morphism `σ̃ : X' ×_S S' ⟶ X'` over the second projection with
`pt σ̃ = pt (first projection)`: it identifies two points of `X'` with the same image in `F`. -/
theorem exists_sigma :
    ∃ (σ : pullback (q' ≫ π) π ⟶ X') (hσ : σ ≫ q' = pullback.snd (q' ≫ π) π),
      pt e (prodOver q' π) σ (by rw [← Category.assoc, hσ]; rfl) =
        pt e (prodOver q' π) (pullback.fst (q' ≫ π) π) (fst_comp_eq q' π) :=
  exists_pt e (prodOver q' π) (pullback.snd (q' ≫ π) π) rfl _

end Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent
