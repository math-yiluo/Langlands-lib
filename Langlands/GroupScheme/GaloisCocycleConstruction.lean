import Langlands.GroupScheme.GaloisCocycle
import Mathlib.AlgebraicGeometry.Gluing

/-! # Construction of natural cocycles from finite Galois coefficients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisCocycle

set_option backward.isDefEq.respectTransparency false

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {G : GroupScheme (Spec (CommRingCat.of k))}

private abbrev overlap (k L : Type u) [Field k] [Field L] [Algebra k L] :
    Over (Spec (CommRingCat.of k)) :=
  Over.mk (Descent.fst (Descent.fieldMap k L) ≫ Descent.fieldMap k L)

private def pair {Z : Over (Spec (CommRingCat.of k))} (a b : Z ⟶ cover k L) :
    Z ⟶ overlap k L :=
  Over.homMk (pullback.lift a.left b.left (a.w.trans b.w.symm)) (by
    change pullback.lift a.left b.left _ ≫ Descent.fst (Descent.fieldMap k L) ≫
      Descent.fieldMap k L = Z.hom
    rw [pullback.lift_fst_assoc]
    exact a.w)

private theorem pair_comp {Z W : Over (Spec (CommRingCat.of k))}
    (t : W ⟶ Z) (a b : Z ⟶ cover k L) :
    pair (t ≫ a) (t ≫ b) = t ≫ pair a b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;> simp [pair]

variable [FiniteDimensional k L] [IsGalois k L]

private abbrev componentObjects (k L : Type u) [Field k] [Field L] [Algebra k L] :
    Fin (Module.finrank k L) → Scheme.{u} :=
  fun _ => Spec (CommRingCat.of L)

private abbrev componentMap : (∐ componentObjects k L) ⟶ (overlap k L).left :=
  Sigma.desc (Descent.finiteGaloisComponent k L)

private instance : IsIso (componentMap (k := k) (L := L)) :=
  Descent.finiteGaloisComponent_isIso_desc k L

@[reassoc]
private theorem i_comp_componentMap (i : Fin (Module.finrank k L)) :
    Sigma.ι (componentObjects k L) i ≫ componentMap = Descent.finiteGaloisComponent k L i :=
  Sigma.ι_comp_desc _ _

private theorem pair_translated {Z : Over (Spec (CommRingCat.of k))}
    (a : Z ⟶ cover k L) (i : Fin (Module.finrank k L)) :
    (pair a (a ≫ arrow k L (Descent.galoisIndexEquiv k L i))).left =
      a.left ≫ Descent.finiteGaloisComponent k L i := by
  apply pullback.hom_ext
  · rw [show (pair a (a ≫ arrow k L (Descent.galoisIndexEquiv k L i))).left ≫
        Descent.fst (Descent.fieldMap k L) = a.left from pullback.lift_fst _ _ _,
      Category.assoc, Descent.finiteGaloisComponent_fst]
    exact (Category.comp_id (a.left : Z.left ⟶ Spec (CommRingCat.of L))).symm
  · rw [show (pair a (a ≫ arrow k L (Descent.galoisIndexEquiv k L i))).left ≫
        Descent.snd (Descent.fieldMap k L) =
        (a ≫ arrow k L (Descent.galoisIndexEquiv k L i)).left from pullback.lift_snd _ _ _,
      Category.assoc, Descent.finiteGaloisComponent_snd]
    rfl

private def overlapValue (c : (L ≃ₐ[k] L) → G.affinePoints (CommAlgCat.of k L)) :
    overlap k L ⟶ G.X :=
  Over.homMk (inv (componentMap (k := k) (L := L)) ≫
    Sigma.desc (fun i => (c (Descent.galoisIndexEquiv k L i)).left)) (by
      apply (cancel_epi (componentMap (k := k) (L := L))).mp
      apply Sigma.hom_ext
      intro i
      rw [Category.assoc, IsIso.hom_inv_id_assoc, Sigma.ι_comp_desc_assoc, i_comp_componentMap_assoc]
      change (c (Descent.galoisIndexEquiv k L i)).left ≫ G.X.hom =
        Descent.finiteGaloisComponent k L i ≫ (overlap k L).hom
      exact (c (Descent.galoisIndexEquiv k L i)).w.trans (by
        change Descent.fieldMap k L = Descent.finiteGaloisComponent k L i ≫
          Descent.fst (Descent.fieldMap k L) ≫ Descent.fieldMap k L
        rw [Descent.finiteGaloisComponent_fst_assoc]))

private theorem pair_value (c : (L ≃ₐ[k] L) → G.affinePoints (CommAlgCat.of k L))
    {Z : Over (Spec (CommRingCat.of k))} (a : Z ⟶ cover k L) (σ : L ≃ₐ[k] L) :
    pair a (a ≫ arrow k L σ) ≫ overlapValue c = a ≫ c σ := by
  let i := (Descent.galoisIndexEquiv k L).symm σ
  have hi : Descent.galoisIndexEquiv k L i = σ := (Descent.galoisIndexEquiv k L).apply_symm_apply σ
  rw [← hi]
  apply Over.OverMorphism.ext
  change (pair a _).left ≫ (overlapValue c).left = a.left ≫ (c _).left
  rw [pair_translated]
  have h : Descent.finiteGaloisComponent k L i ≫
      inv (componentMap (k := k) (L := L)) = Sigma.ι (componentObjects k L) i := by
    apply (cancel_mono (componentMap (k := k) (L := L))).mp
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact (i_comp_componentMap i).symm
  change (a.left ≫ Descent.finiteGaloisComponent k L i) ≫
    inv (componentMap (k := k) (L := L)) ≫
      Sigma.desc (fun j => (c (Descent.galoisIndexEquiv k L j)).left) = _
  rw [Category.assoc, ← Category.assoc (Descent.finiteGaloisComponent k L i), h,
    Sigma.ι_comp_desc]

private theorem hom_ext_of_translated_pair {Z Y : Over (Spec (CommRingCat.of k))}
    (a b : Z ⟶ cover k L) (f g : Z ⟶ Y)
    (h : ∀ {W : Over (Spec (CommRingCat.of k))} (t : W ⟶ Z) (σ : L ≃ₐ[k] L),
      t ≫ b = (t ≫ a) ≫ arrow k L σ → t ≫ f = t ≫ g) : f = g := by
  let q := (pair a b).left ≫ inv (componentMap (k := k) (L := L))
  let 𝒱 := sigmaOpenCover (componentObjects k L)
  let 𝒰 : Z.left.OpenCover := 𝒱.pullback₁ q
  apply Over.OverMorphism.ext
  apply 𝒰.hom_ext
  intro i
  let t : Over.mk (𝒰.f i ≫ Z.hom) ⟶ Z := Over.homMk (𝒰.f i)
  let s := 𝒱.pullbackHom q i
  have hp : t.left ≫ (pair a b).left = s ≫ Descent.finiteGaloisComponent k L i := by
    have hq := (𝒱.pullbackHom_map q i).symm
    change t.left ≫ q = s ≫ Sigma.ι (componentObjects k L) i at hq
    have hd := congrArg (fun m => m ≫ componentMap (k := k) (L := L)) hq
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, q, i_comp_componentMap]
      using hd
  have ha : t.left ≫ a.left = s := by
    have hf := congrArg (fun f => f ≫ Descent.fst (Descent.fieldMap k L)) hp
    simp only [Category.assoc, show (pair a b).left ≫ Descent.fst (Descent.fieldMap k L) =
      a.left from pullback.lift_fst _ _ _, Descent.finiteGaloisComponent_fst] at hf
    exact hf.trans (Category.comp_id s)
  have hb : t ≫ b = (t ≫ a) ≫ arrow k L (Descent.galoisIndexEquiv k L i) := by
    apply Over.OverMorphism.ext
    change t.left ≫ b.left = (t.left ≫ a.left) ≫ _
    rw [ha]
    change t.left ≫ (b.left : Z.left ⟶ Spec (CommRingCat.of L)) =
      s ≫ Spec.map (CommRingCat.ofHom (Descent.galoisIndexEquiv k L i).toRingHom)
    have hs := congrArg (fun f => f ≫ Descent.snd (Descent.fieldMap k L)) hp
    simpa only [Category.assoc, show (pair a b).left ≫ Descent.snd (Descent.fieldMap k L) =
      b.left from pullback.lift_snd _ _ _, Descent.finiteGaloisComponent_snd]
      using hs
  exact congrArg (fun m => m.left) (h t _ hb)

/-- Crossed cocycle coefficients determine a natural cocycle on the actual finite Galois cover. -/
def ofValues (c : (L ≃ₐ[k] L) → G.affinePoints (CommAlgCat.of k L))
    (hc : ∀ σ τ, c (σ * τ) = c σ * GaloisPoint.conjugate k L G σ (c τ)) :
    Cocycle G (cover k L) where
  toFun a b := pair a b ≫ overlapValue c
  naturality t a b := by rw [pair_comp, Category.assoc]
  cocycle a b e := by
    apply hom_ext_of_translated_pair a b
    intro W t σ hs
    simp only [← Category.assoc, ← pair_comp, MonObj.comp_mul]
    apply hom_ext_of_translated_pair (t ≫ b) (t ≫ e)
    intro V r τ ht
    simp only [← Category.assoc, ← pair_comp, MonObj.comp_mul]
    have hs' : r ≫ t ≫ b = (r ≫ t ≫ a) ≫ arrow k L σ := by
      rw [hs, Category.assoc r (t ≫ a)]
    rw [Category.assoc r t, Category.assoc r t, Category.assoc r t, ht, hs']
    let z := r ≫ t ≫ a
    change pair z ((z ≫ arrow k L σ) ≫ arrow k L τ) ≫ overlapValue c =
      (pair z (z ≫ arrow k L σ) ≫ overlapValue c) *
        (pair (z ≫ arrow k L σ) ((z ≫ arrow k L σ) ≫ arrow k L τ) ≫ overlapValue c)
    rw [pair_value c (z ≫ arrow k L σ) τ, pair_value c z σ,
      Category.assoc z (arrow k L σ) (arrow k L τ), ← arrow_mul, pair_value, hc,
      MonObj.comp_mul]
    change (z ≫ c σ) * (z ≫ arrow k L σ ≫ c τ) =
      (z ≫ c σ) * ((z ≫ arrow k L σ) ≫ c τ)
    rw [Category.assoc z]

@[simp] theorem value_ofValues (c : (L ≃ₐ[k] L) → G.affinePoints (CommAlgCat.of k L))
    (hc : ∀ σ τ, c (σ * τ) = c σ * GaloisPoint.conjugate k L G σ (c τ))
    (σ : L ≃ₐ[k] L) : value (ofValues c hc) σ = c σ := by
  change pair (𝟙 _) (arrow k L σ) ≫ overlapValue c = c σ
  simpa only [Category.id_comp] using pair_value c (𝟙 (cover k L)) σ

end Langlands.GroupScheme.GaloisCocycle
