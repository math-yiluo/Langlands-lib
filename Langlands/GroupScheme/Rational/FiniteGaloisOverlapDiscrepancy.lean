import Langlands.GroupScheme.Rational.FiniteGaloisCocycleValues
import Langlands.GroupScheme.Rational.InnerDiscrepancyOverlap

/-! # Inner discrepancies on finite Galois covers from Galois-pair values -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Cocycle

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Each actual component of the double cover is the corresponding Galois pair. -/
theorem finiteGaloisComponent_eq_galoisPair (i : Fin (Module.finrank K L)) :
    Descent.finiteGaloisComponent K L i =
      (galoisPair (Descent.galoisIndexEquiv K L i)).left := by
  apply pullback.hom_ext
  · rw [Descent.finiteGaloisComponent_fst]
    exact (congrArg (fun f => f.left) (galoisPair_fst (Descent.galoisIndexEquiv K L i))).symm
  · rw [Descent.finiteGaloisComponent_snd]
    exact (congrArg (fun f => f.left) (galoisPair_snd (Descent.galoisIndexEquiv K L i))).symm

/-- Maps out of the double cover times any scheme agree once they agree on all test
points whose cover coordinate factors through a Galois pair. -/
theorem galoisPair_ext_tensor {Y Z : Over (Spec (CommRingCat.of K))}
    {h₁ h₂ : (ringTest K L ⊗ ringTest K L) ⊗ Y ⟶ Z}
    (h : ∀ (σ : L ≃ₐ[K] L) {V : Over (Spec (CommRingCat.of K))}
      (s : V ⟶ ringTest K L) (y : V ⟶ Y),
      CartesianMonoidalCategory.lift (s ≫ galoisPair σ) y ≫ h₁ =
        CartesianMonoidalCategory.lift (s ≫ galoisPair σ) y ≫ h₂) :
    h₁ = h₂ := by
  let f := (fst (ringTest K L ⊗ ringTest K L) Y).left
  let c := Descent.finiteGaloisComponent K L
  have : IsIso (Sigma.desc (fun i => pullback.fst f (c i))) :=
    FinitaryPreExtensive.isIso_sigmaDesc_fst c f inferInstance
  apply Over.OverMorphism.ext
  refine (cancel_epi (Sigma.desc (fun i => pullback.fst f (c i)))).1 ?_
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc_assoc]
  let σ := Descent.galoisIndexEquiv K L i
  have hi : c i = (galoisPair σ).left := finiteGaloisComponent_eq_galoisPair i
  let V : Over (Spec (CommRingCat.of K)) :=
    Over.mk (pullback.fst f (c i) ≫ ((ringTest K L ⊗ ringTest K L) ⊗ Y).hom)
  let t : V ⟶ (ringTest K L ⊗ ringTest K L) ⊗ Y := Over.homMk (pullback.fst f (c i)) rfl
  let s : V ⟶ ringTest K L := Over.homMk (pullback.snd f (c i)) (by
    change pullback.snd f (c i) ≫ (ringTest K L).hom =
      pullback.fst f (c i) ≫ ((ringTest K L ⊗ ringTest K L) ⊗ Y).hom
    rw [← Over.w (fst (ringTest K L ⊗ ringTest K L) Y), ← Category.assoc,
      pullback.condition, Category.assoc, hi, Over.w (galoisPair σ)])
  have ht : t = CartesianMonoidalCategory.lift (s ≫ galoisPair σ) (t ≫ snd _ _) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      apply Over.OverMorphism.ext
      change pullback.fst f (c i) ≫ f = pullback.snd f (c i) ≫ (galoisPair σ).left
      rw [pullback.condition, hi]
    · rw [lift_snd]
  have hσ := congrArg (fun m => m.left) (h σ s (t ≫ snd _ _))
  rw [← ht] at hσ
  exact hσ

/-- The inverse of the actual component decomposition of the double overlap. -/
def galoisComponentInv :
    Descent.Overlap (Descent.fieldMap K L) ⟶
      ∐ fun _ : Fin (Module.finrank K L) => Spec (CommRingCat.of L) :=
  inv (Sigma.desc (Descent.finiteGaloisComponent K L))

@[reassoc (attr := simp)]
theorem finiteGaloisComponent_comp_galoisComponentInv (i : Fin (Module.finrank K L)) :
    Descent.finiteGaloisComponent K L i ≫ galoisComponentInv =
      Sigma.ι (fun _ : Fin (Module.finrank K L) => Spec (CommRingCat.of L)) i := by
  rw [galoisComponentInv, ← Sigma.ι_comp_desc (Descent.finiteGaloisComponent K L) i,
    Category.assoc, IsIso.hom_inv_id, Category.comp_id]

@[reassoc (attr := simp)]
theorem desc_comp_galoisComponentInv :
    Sigma.desc (Descent.finiteGaloisComponent K L) ≫ galoisComponentInv = 𝟙 _ := by
  rw [galoisComponentInv, IsIso.hom_inv_id]

@[reassoc (attr := simp)]
theorem galoisComponentInv_comp_desc :
    galoisComponentInv ≫ Sigma.desc (Descent.finiteGaloisComponent K L) = 𝟙 _ := by
  rw [galoisComponentInv, IsIso.inv_hom_id]

/-- Assemble a morphism out of the double cover from prescribed Galois-pair values. -/
def galoisPairDesc {W : Over (Spec (CommRingCat.of K))}
    (x : (L ≃ₐ[K] L) → (ringTest K L ⟶ W)) : ringTest K L ⊗ ringTest K L ⟶ W :=
  Over.homMk (galoisComponentInv ≫
      Sigma.desc (fun i => (x (Descent.galoisIndexEquiv K L i)).left)) (by
    change galoisComponentInv ≫ Sigma.desc (fun i => (x (Descent.galoisIndexEquiv K L i)).left) ≫
        W.hom = (ringTest K L ⊗ ringTest K L).hom
    rw [← cancel_epi (Sigma.desc (Descent.finiteGaloisComponent K L)),
      desc_comp_galoisComponentInv_assoc]
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc_assoc, finiteGaloisComponent_eq_galoisPair i]
    exact (Over.w (x (Descent.galoisIndexEquiv K L i))).trans
      (Over.w (galoisPair (Descent.galoisIndexEquiv K L i))).symm)

/-- The assembled morphism has the prescribed value on every Galois pair. -/
@[reassoc (attr := simp)]
theorem galoisPair_comp_galoisPairDesc {W : Over (Spec (CommRingCat.of K))}
    (x : (L ≃ₐ[K] L) → (ringTest K L ⟶ W)) (σ : L ≃ₐ[K] L) :
    galoisPair σ ≫ galoisPairDesc x = x σ := by
  obtain ⟨i, rfl⟩ := (Descent.galoisIndexEquiv K L).surjective σ
  apply Over.OverMorphism.ext
  change (galoisPair (Descent.galoisIndexEquiv K L i)).left ≫ galoisComponentInv ≫
      Sigma.desc (fun j => (x (Descent.galoisIndexEquiv K L j)).left) = _
  rw [← finiteGaloisComponent_eq_galoisPair i, finiteGaloisComponent_comp_galoisComponentInv_assoc,
    Sigma.ι_comp_desc]

end Cocycle

namespace LocalGroupIso

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  {G H A : GroupScheme (Spec (CommRingCat.of K))}
  (e : LocalGroupIso G H (ringTest K L)) (a : AutomorphicAction A G)

/-- On a finite Galois cover, the universal overlap equation follows from its
restrictions to the Galois pairs `(1, σ)`. -/
theorem hasOverlapDiscrepancy_of_galois (δ : ringTest K L ⊗ ringTest K L ⟶ A.X)
    (h : ∀ (σ : L ≃ₐ[K] L) {V : Over (Spec (CommRingCat.of K))}
      (s : V ⟶ ringTest K L) (g : V ⟶ G.X),
      e.toFun s (a.act (s ≫ Cocycle.galoisPair σ ≫ δ) g) =
        e.toFun (s ≫ ringTestMap K σ.toAlgHom) g) :
    e.HasOverlapDiscrepancy a δ := by
  apply Cocycle.galoisPair_ext_tensor
  intro σ V s y
  have hσ := h σ s y
  simp only [← e.naturality, a.naturality, ← Category.assoc,
    lift_fst, lift_snd]
  simpa only [Category.assoc, Cocycle.galoisPair_fst, Cocycle.galoisPair_snd,
    Category.comp_id] using hσ

/-- Galois-pair values satisfying the discrepancy equations give all-test inner
discrepancy. -/
theorem hasInnerDiscrepancy_of_galois (x : (L ≃ₐ[K] L) → (ringTest K L ⟶ A.X))
    (h : ∀ (σ : L ≃ₐ[K] L) {V : Over (Spec (CommRingCat.of K))}
      (s : V ⟶ ringTest K L) (g : V ⟶ G.X),
      e.toFun s (a.act (s ≫ x σ) g) = e.toFun (s ≫ ringTestMap K σ.toAlgHom) g) :
    e.HasInnerDiscrepancy a :=
  e.hasInnerDiscrepancy_of_overlap a
    (e.hasOverlapDiscrepancy_of_galois a (Cocycle.galoisPairDesc x) (fun σ {_} s g => by
      rw [Cocycle.galoisPair_comp_galoisPairDesc]
      exact h σ s g))

end LocalGroupIso

end Langlands.GroupScheme
