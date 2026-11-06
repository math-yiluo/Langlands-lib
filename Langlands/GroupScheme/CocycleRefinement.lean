import Langlands.GroupScheme.TorsorCocycle
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Refinement and fpqc reflection of cocycle triviality -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

variable {S : Scheme.{u}} {G : GroupScheme S} {U V W : Over S}

/-- Restrict a natural cocycle along a morphism of its cover. -/
def refine (ξ : Cocycle G U) (r : V ⟶ U) : Cocycle G V where
  toFun a b := ξ.toFun (a ≫ r) (b ≫ r)
  naturality t a b := by
    simpa only [Category.assoc] using ξ.naturality t (a ≫ r) (b ≫ r)
  cocycle a b c := ξ.cocycle (a ≫ r) (b ≫ r) (c ≫ r)

@[simp] theorem refine_toFun (ξ : Cocycle G U) (r : V ⟶ U)
    {Z : Over S} (a b : Z ⟶ V) :
    (ξ.refine r).toFun a b = ξ.toFun (a ≫ r) (b ≫ r) := rfl

/-- A cocycle has unit value on the diagonal. -/
@[simp] theorem toFun_self (ξ : Cocycle G U) {Z : Over S} (a : Z ⟶ U) :
    ξ.toFun a a = 1 := by
  have h := congrArg (fun g => (ξ.toFun a a)⁻¹ * g) (ξ.cocycle a a a)
  simpa only [inv_mul_cancel, inv_mul_cancel_left] using h.symm

/-- A coboundary remains a coboundary after every refinement. -/
theorem IsTrivial.refine {ξ : Cocycle G U} (hξ : ξ.IsTrivial) (r : V ⟶ U) :
    (ξ.refine r).IsTrivial := by
  obtain ⟨f, hf⟩ := hξ
  exact ⟨r ≫ f, fun a b => by
    simpa only [refine_toFun, Category.assoc] using hf (a ≫ r) (b ≫ r)⟩

/-- Naturality determines every value from the universal pair of cover points. -/
theorem toFun_eq_of_universal_eq (ξ ζ : Cocycle G U)
    (h : ξ.toFun (fst U U) (snd U U) = ζ.toFun (fst U U) (snd U U))
    {Z : Over S} (a b : Z ⟶ U) : ξ.toFun a b = ζ.toFun a b := by
  have hh := congrArg (fun f => CartesianMonoidalCategory.lift a b ≫ f) h
  simpa only [← ξ.naturality, ← ζ.naturality, lift_fst, lift_snd] using hh

/-- A trivializing cochain on an effective refinement descends to the old cover.
Epimorphy of the product refinement then reflects its coboundary equation. -/
theorem IsTrivial.of_refine {ξ : Cocycle G U} (r : V ⟶ U)
    [EffectiveEpi r.left] [Epi (r ⊗ₘ r).left]
    (hξ : (ξ.refine r).IsTrivial) : ξ.IsTrivial := by
  obtain ⟨f, hf⟩ := hξ
  have hrel {Z : Over S} (a b : Z ⟶ V) (hab : a ≫ r = b ≫ r) :
      a ≫ f = b ≫ f := by
    have hh := hf a b
    change ξ.toFun (a ≫ r) (b ≫ r) = (a ≫ f) * (b ≫ f)⁻¹ at hh
    rw [hab, toFun_self] at hh
    exact mul_inv_eq_one.mp hh.symm
  let d : U.left ⟶ G.X.left :=
    EffectiveEpi.desc r.left f.left (fun {Z} a b hab => by
      have hb : b ≫ V.hom = a ≫ V.hom := by
        rw [← Over.w r, ← Category.assoc, ← Category.assoc, hab]
      let a₀ : Over.mk (a ≫ V.hom) ⟶ V := Over.homMk a rfl
      let b₀ : Over.mk (a ≫ V.hom) ⟶ V := Over.homMk b hb
      exact congrArg (fun e => e.left)
        (hrel a₀ b₀ (Over.OverMorphism.ext hab)))
  have hd : r.left ≫ d = f.left := EffectiveEpi.fac _ _ _
  let g : U ⟶ G.X := Over.homMk d (by
    apply (cancel_epi r.left).mp
    rw [← Category.assoc, hd, Over.w f, Over.w r])
  have hg : r ≫ g = f := Over.OverMorphism.ext hd
  refine ⟨g, ?_⟩
  apply toFun_eq_of_universal_eq ξ (coboundary g)
  apply Over.OverMorphism.ext
  apply (cancel_epi (r ⊗ₘ r).left).mp
  have hh := hf (fst V V) (snd V V)
  change ξ.toFun (fst V V ≫ r) (snd V V ≫ r) =
    (fst V V ≫ f) * (snd V V ≫ f)⁻¹ at hh
  have hcover : (r ⊗ₘ r) ≫ ξ.toFun (fst U U) (snd U U) =
      (r ⊗ₘ r) ≫ (coboundary g).toFun (fst U U) (snd U U) := by
    rw [← ξ.naturality, ← (coboundary g).naturality]
    simp only [tensorHom_fst, tensorHom_snd, coboundary, Category.assoc, hg]
    exact hh
  exact congrArg (fun e => e.left) hcover

private abbrev fpqcProperty : MorphismProperty Scheme.{u} :=
  @QuasiCompact ⊓ (@Flat ⊓ @Surjective)

set_option backward.isDefEq.respectTransparency false in
/-- Products of fpqc refinements are effective epimorphisms. -/
theorem effectiveEpi_tensorHom (r : V ⟶ U)
    [QuasiCompact r.left] [Flat r.left] [Surjective r.left] :
    EffectiveEpi (r ⊗ₘ r).left := by
  have hp : fpqcProperty (r ⊗ₘ r).left :=
    MorphismProperty.pullbackMap (P := fpqcProperty)
      ⟨inferInstance, inferInstance, inferInstance⟩
      ⟨inferInstance, inferInstance, inferInstance⟩
      (Over.w r).symm (Over.w r).symm
  let : QuasiCompact (r ⊗ₘ r).left := hp.1
  let : Flat (r ⊗ₘ r).left := hp.2.1
  let : Surjective (r ⊗ₘ r).left := hp.2.2
  infer_instance

/-- Triviality of actual natural cocycles is invariant under fpqc refinement. -/
theorem isTrivial_refine_iff (ξ : Cocycle G U) (r : V ⟶ U)
    [QuasiCompact r.left] [Flat r.left] [Surjective r.left] :
    (ξ.refine r).IsTrivial ↔ ξ.IsTrivial := by
  have := effectiveEpi_tensorHom r
  exact ⟨fun h => h.of_refine r, fun h => h.refine r⟩

end Langlands.GroupScheme.Cocycle
