import Mathlib.AlgebraicGeometry.Gluing
import Langlands.AlgebraicGeometry.QuasiSeparatedTestIsoDetectionStatement
import Mathlib.CategoryTheory.Comma.Over.Basic

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Langlands.AlgebraicGeometry

private theorem left_cancel_of_quasiSeparated_tests
    (S : Scheme.{u}) (P Q : Over S) (f : P ⟶ Q)
    (H : ∀ (T : Over S) [QuasiSeparatedSpace T.left],
      Function.Bijective (fun (g : T ⟶ P) => g ≫ f))
    (W : Scheme.{u}) (a b : W ⟶ P.left)
    (hab : a ≫ f.left = b ≫ f.left) : a = b := by
  have habS : a ≫ P.hom = b ≫ P.hom := by
    rw [← Over.w f, ← Category.assoc, hab, Category.assoc]
  apply W.affineCover.hom_ext a b
  intro i
  let T : Over S := Over.mk (W.affineCover.f i ≫ a ≫ P.hom)
  have : QuasiSeparatedSpace T.left := by
    change QuasiSeparatedSpace (W.affineCover.X i)
    infer_instance
  let ai : T ⟶ P := Over.homMk (W.affineCover.f i ≫ a)
  let bi : T ⟶ P := Over.homMk (W.affineCover.f i ≫ b) (by
    dsimp [T]
    simpa only [Category.assoc] using congrArg (fun k => W.affineCover.f i ≫ k) habS.symm)
  have hcomp : ai ≫ f = bi ≫ f := by
    apply Over.OverMorphism.ext
    change (W.affineCover.f i ≫ a) ≫ f.left =
      (W.affineCover.f i ≫ b) ≫ f.left
    simpa only [Category.assoc] using congrArg (fun k => W.affineCover.f i ≫ k) hab
  exact congrArg (fun k : T ⟶ P => k.left) ((H T).1 hcomp)

/-- Quasi-separated tests detect isomorphisms of schemes over an arbitrary base.
The proof lifts affine charts and glues a two-sided inverse.
Adapted from Worker 535's affine-cover argument. -/
theorem quasiSeparatedTestIsoDetection :
    QuasiSeparatedTestIsoDetectionStatement.{u} := by
  intro S P Q f H
  classical
  have : Mono f.left :=
    ⟨fun a b hab => left_cancel_of_quasiSeparated_tests S P Q f H _ a b hab⟩
  let U := Q.left.affineCover
  have hsurj (i : U.I₀) :
      ∃ g : Over.mk (U.f i ≫ Q.hom) ⟶ P,
        g ≫ f = Over.homMk (U.f i) := by
    have : QuasiSeparatedSpace (Over.mk (U.f i ≫ Q.hom)).left := by
      change QuasiSeparatedSpace (Q.left.affineCover.X i)
      infer_instance
    exact (H (Over.mk (U.f i ≫ Q.hom))).2 (Over.homMk (U.f i))
  choose lifts hlifts using hsurj
  have hlifts_left (i : U.I₀) : (lifts i).left ≫ f.left = U.f i :=
    congrArg (fun k => k.left) (hlifts i)
  have hcompat (i j : U.I₀) :
      pullback.fst (U.f i) (U.f j) ≫ (lifts i).left =
        pullback.snd (U.f i) (U.f j) ≫ (lifts j).left := by
    apply (cancel_mono f.left).1
    simpa only [Category.assoc, hlifts_left] using
      (pullback.condition (f := U.f i) (g := U.f j))
  let g : Q.left ⟶ P.left := U.glueMorphisms (fun i => (lifts i).left) hcompat
  have hgf : g ≫ f.left = 𝟙 Q.left := by
    apply U.hom_ext
    intro i
    simpa only [Category.assoc, g, Scheme.Cover.ι_glueMorphisms_assoc,
      Category.comp_id] using hlifts_left i
  have hfg : f.left ≫ g = 𝟙 P.left := by
    apply (cancel_mono f.left).1
    simp only [Category.assoc, hgf, Category.comp_id, Category.id_comp]
  let e : P.left ≅ Q.left :=
    { hom := f.left
      inv := g
      hom_inv_id := hfg
      inv_hom_id := hgf }
  have : IsIso ((Over.forget S).map f) := by
    change IsIso f.left
    exact e.isIso_hom
  exact isIso_of_reflects_iso f (Over.forget S)

end Langlands.AlgebraicGeometry
