/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorSectionRepresentation
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.TorsorNormalizedGraphEvaluation

/-! # Ordinary locally constant evaluation on a torsor

Source: Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R; sites.tex, Example
constant-sheaf and Tags 04TR and 04TS. Fixed-cover adaptation to arbitrary modules.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry
open Etale

set_option backward.isDefEq.respectTransparency false in
/-- Naturality evaluates a locally presented section at its constant label. -/
private theorem evaluation_of_local_presentation
    {V : Scheme.{u}} (ℓ : ℕ) {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (β : ∀ W : V.Etaleᵒᵖ, F.obj.obj W →ₗ[ULift.{u + 1} (ZMod ℓ)]
      LocallyConstant (c.sectionSpace W.unop) (F.obj.obj (op c.sectionObject)))
    (hβ : ∀ (W W' : V.Etaleᵒᵖ) (f : W ⟶ W') (s : F.obj.obj W)
        (x : c.sectionSpace W'.unop),
      β W' (F.obj.map f s) x = β W s (c.sectionRestriction f.unop x))
    (hΔ : ∀ (s : F.obj.obj (op c.sectionObject)) (y : c.P),
      β (op c.sectionObject) s
        (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) (by simp) y) = s)
    (W : V.Etaleᵒᵖ) (s : F.obj.obj W)
    (T : V.Etale) (p : T ⟶ W.unop) (q : T ⟶ c.sectionObject) (y : T.left)
    (a : F.obj.obj (op c.sectionObject))
    (hs : F.obj.map p.op s = F.obj.map q.op a) :
    β W s (pullback.lift p.left q.left
      ((MorphismProperty.Over.w p).trans (MorphismProperty.Over.w q).symm) y) = a := by
  let d : T.left ⟶ c.sectionSpace T :=
    pullback.lift (𝟙 _) q.left (by simpa using (MorphismProperty.Over.w q).symm)
  have hp : d ≫ c.sectionRestriction p =
      pullback.lift p.left q.left
        ((MorphismProperty.Over.w p).trans (MorphismProperty.Over.w q).symm) := by
    apply pullback.hom_ext <;>
      simp only [d, Scheme.GaloisCover.sectionRestriction, Scheme.GaloisCover.sectionObject,
        Scheme.Etale.mk, MorphismProperty.Over.mk, pullback.map,
        pullback.lift_fst_assoc, pullback.lift_fst,
        pullback.lift_snd, Category.id_comp, Category.comp_id, Category.assoc]
  have hq : d ≫ c.sectionRestriction q =
      q.left ≫ pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) (by simp) := by
    apply pullback.hom_ext <;>
      simp only [d, Scheme.GaloisCover.sectionRestriction, Scheme.GaloisCover.sectionObject,
        Scheme.Etale.mk, MorphismProperty.Over.mk, pullback.map,
        pullback.lift_fst_assoc, pullback.lift_fst,
        pullback.lift_snd, Category.id_comp, Category.comp_id, Category.assoc]
  calc
    _ = β (op T) (F.obj.map p.op s) (d y) := by
      rw [hβ]
      change β W s _ = β W s ((d ≫ c.sectionRestriction p) y)
      rw [hp]
      rfl
    _ = β (op T) (F.obj.map q.op a) (d y) := by rw [hs]
    _ = a := by
      rw [hβ]
      change β (op c.sectionObject) a ((d ≫ c.sectionRestriction q) y) = a
      rw [hq, Scheme.Hom.comp_apply]
      exact hΔ a (q.left y)

set_option backward.isDefEq.respectTransparency false in
/-- A natural ordinary evaluation normalized on the diagonal is deck-equivariant.
Source: Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R; sites.tex, Example
constant-sheaf and Tags 04TR and 04TS. Fixed-cover adaptation to arbitrary modules.
(blueprint: lem-weil-pbc-torsor-ordinary-evaluation-equivariant)

Proof: The constant trivialization and connectedness of Y identify the restricted
sheaf with the locally constant function sheaf valued in F(Y), with restriction of
a global section a corresponding to the constant function a. Put U=W times_V Y,
with projections p to W and q to Y, and restrict s to t=p*s. Around any point x of
U choose an etale neighbourhood T on which t=q*a for some a in F(Y). On the graph
of q:T to Y, naturality of beta along q and diagonal normalization give value a;
naturality along p then gives beta_W(s)(x)=a. Etale covers are surjective on points,
so such neighbourhoods determine all the values of beta. At the translated point
g*x, use the same T with its Y-map changed from q to g*q. The same section t is now
the restriction of b=F(g inverse)(a), since (g*q)*b=q*a. Naturality and diagonal
normalization therefore give beta_W(s)(g*x)=b. This is exactly the action in
sectionRepresentation, whose scalar restriction does not change underlying values.
This argument uses only local constant presentations of sections, not uniqueness of
a chosen trivialization or any equivariance assumption on beta. Empty objects give
a vacuous assertion; zero coefficients and the identity torsor obey the same formula. -/
theorem Scheme.GaloisCover.ordinarySectionEvaluation_equivariant
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    (h : Nonempty ((c.π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj A))
    (β : ∀ W : V.Etaleᵒᵖ, F.obj.obj W →ₗ[ULift.{u + 1} (ZMod ℓ)]
      LocallyConstant (c.sectionSpace W.unop) (F.obj.obj (op c.sectionObject)))
    (hβ : ∀ (W W' : V.Etaleᵒᵖ) (f : W ⟶ W') (s : F.obj.obj W)
        (x : c.sectionSpace W'.unop),
      β W' (F.obj.map f s) x = β W s (c.sectionRestriction f.unop x))
    (hΔ : ∀ (s : F.obj.obj (op c.sectionObject)) (y : c.P),
      β (op c.sectionObject) s
        (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) (by simp) y) = s) :
    ∀ (W : V.Etaleᵒᵖ) (s : F.obj.obj W) (g : P) (x : c.sectionSpace W.unop),
      β W s (c.sectionAction W.unop g x) =
        (c.sectionRepresentation ℓ F).ρ g (β W s x) := by
  intro W s g x
  have := c.etale
  let U : V.Etale := Etale.mk (pullback.fst W.unop.hom c.π ≫ W.unop.hom)
  let pU : U ⟶ W.unop :=
    MorphismProperty.Over.homMk (pullback.fst W.unop.hom c.π) rfl
  let qU : U ⟶ c.sectionObject :=
    MorphismProperty.Over.homMk (pullback.snd W.unop.hom c.π) pullback.condition.symm
  let t := F.obj.map pU.op s
  let dU : U.left ⟶ c.sectionSpace U :=
    pullback.lift (𝟙 _) qU.left (by simpa using (MorphismProperty.Over.w qU).symm)
  let f : LocallyConstant U.left (F.obj.obj (op c.sectionObject)) :=
    LocallyConstant.comap dU.base.hom (β (op U) t)
  let O : U.left.Opens := ⟨{z | f z = f x}, f.isLocallyConstant.isOpen_fiber _⟩
  let T : V.Etale := Etale.mk (O.ι ≫ U.hom)
  let i : T ⟶ U := MorphismProperty.Over.homMk O.ι rfl
  let p : T ⟶ W.unop := i ≫ pU
  let q : T ⟶ c.sectionObject := i ≫ qU
  let y : T.left := ⟨x, rfl⟩
  let a : F.obj.obj (op c.sectionObject) := f x
  have hx : pullback.lift p.left q.left
      ((MorphismProperty.Over.w p).trans (MorphismProperty.Over.w q).symm) y = x := by
    have hm : pullback.lift p.left q.left
        ((MorphismProperty.Over.w p).trans (MorphismProperty.Over.w q).symm) = O.ι := by
      apply pullback.hom_ext <;>
        simp only [Scheme.GaloisCover.sectionObject, Scheme.Etale.mk,
          MorphismProperty.Over.mk, pullback.lift_fst, pullback.lift_snd]
      all_goals rfl
    rw [hm]
    rfl
  have hs : F.obj.map p.op s = F.obj.map q.op a := by
    apply (c.ordinaryGraphEvaluation_bijective ℓ P F A h β hβ hΔ (op T) q).1
    apply LocallyConstant.ext
    intro z
    let d : T.left ⟶ c.sectionSpace T :=
      pullback.lift (𝟙 _) q.left (by simpa using (MorphismProperty.Over.w q).symm)
    change β (op T) (F.obj.map p.op s) (d z) =
      β (op T) (F.obj.map q.op a) (d z)
    have hm : d ≫ c.sectionRestriction i = O.ι ≫ dU := by
      apply pullback.hom_ext <;>
        simp only [d, Scheme.GaloisCover.sectionRestriction, dU, q, i,
          pullback.map, pullback.lift_fst_assoc, pullback.lift_fst,
          pullback.lift_snd, Category.assoc, Category.id_comp, Category.comp_id]
      all_goals rfl
    have hleft : β (op T) (F.obj.map p.op s) (d z) = a := by
      change β (op T) (F.obj.map (pU.op ≫ i.op) s) (d z) = a
      rw [CategoryTheory.Functor.map_comp, ModuleCat.comp_apply, hβ]
      change β (op U) t ((d ≫ c.sectionRestriction i) z) = a
      rw [hm, Scheme.Hom.comp_apply]
      exact z.property
    have hright : β (op T) (F.obj.map q.op a) (d z) = a := by
      exact evaluation_of_local_presentation ℓ c F β hβ hΔ (op T)
        (F.obj.map q.op a) T (𝟙 T) q z a (by simp)
    exact hleft.trans hright.symm
  have ha : β W s x = a := by
    rw [← hx]
    exact evaluation_of_local_presentation ℓ c F β hβ hΔ W s T p q y a hs
  let q' : T ⟶ c.sectionObject := q ≫ c.sectionDeck g
  let b : F.obj.obj (op c.sectionObject) := F.obj.map (c.sectionDeck g⁻¹).op a
  have hd : c.sectionDeck g ≫ c.sectionDeck g⁻¹ = 𝟙 _ := by
    apply Scheme.EtaleTorsor.etaleHom_ext
    change c.smul ⟨g⟩ ≫ c.smul ⟨g⁻¹⟩ = 𝟙 _
    rw [← c.mul_smul]
    change c.smul ((⟨g⟩ : ULift.{u + 1} P)⁻¹ * ⟨g⟩) = 𝟙 _
    rw [inv_mul_cancel, c.one_smul]
  have hs' : F.obj.map p.op s = F.obj.map q'.op b := by
    rw [hs]
    dsimp [q', b]
    rw [Functor.map_comp]
    change F.obj.map q.op a =
      F.obj.map q.op (F.obj.map (c.sectionDeck g).op
        (F.obj.map (c.sectionDeck g⁻¹).op a))
    have hm : (c.sectionDeck g⁻¹).op ≫ (c.sectionDeck g).op = 𝟙 _ := by
      rw [← op_comp, hd, op_id]
    have he : F.obj.map (c.sectionDeck g).op
        (F.obj.map (c.sectionDeck g⁻¹).op a) = a := by
      rw [← ModuleCat.comp_apply, ← Functor.map_comp, hm, CategoryTheory.Functor.map_id]
      rfl
    rw [he]
  have hx' : pullback.lift p.left q'.left
      ((MorphismProperty.Over.w p).trans (MorphismProperty.Over.w q').symm) y =
      c.sectionAction W.unop g x := by
    have hm : pullback.lift p.left q'.left
        ((MorphismProperty.Over.w p).trans (MorphismProperty.Over.w q').symm) =
        pullback.lift p.left q.left
          ((MorphismProperty.Over.w p).trans (MorphismProperty.Over.w q).symm) ≫
          c.sectionAction W.unop g := by
      apply pullback.hom_ext <;>
        simp [Scheme.GaloisCover.sectionAction, q', Scheme.GaloisCover.sectionDeck,
          Scheme.GaloisCover.sectionObject, Scheme.Etale.mk, MorphismProperty.Over.mk]
      rfl
    rw [hm, Scheme.Hom.comp_apply, hx]
    rfl
  rw [← hx']
  rw [evaluation_of_local_presentation ℓ c F β hβ hΔ W s T p q' y b hs', ha]
  rfl

end AlgebraicGeometry
