import Langlands.AlgebraicGeometry.Picard.AffineFamilyDescent
import Langlands.AlgebraicGeometry.Picard.ProperLineBundleIsomOfHom
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation

/-! # Descent of specified actual Picard isomorphisms over affine bases -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- Every specified section over an affine algebra base comes from a finitely
 generated subalgebra containing any prescribed finite set of coefficients. -/
def HasAffineSubalgebraSectionDescent
    (F : AlgebraicSpace.Presheaf (Spec (CommRingCat.of R))) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A]
    (x : F.obj (op (affineBase R A))) (s : Finset A),
    ∃ B : Subalgebra R A, B.FG ∧ (↑s : Set A) ⊆ B ∧
      ∃ y : F.obj (op (affineBase R B)), F.map (affineSubalgebraMap B).op y = x

/-- A specified point of a scheme locally of finite presentation over an affine
 base factors through a finitely generated subalgebra, with exact equality. -/
theorem exists_affinePoint_subalgebra (I : Over (Spec (CommRingCat.of R)))
    [LocallyOfFinitePresentation I.hom] (p : affineBase R A ⟶ I) (s : Finset A) :
    ∃ B : Subalgebra R A, B.FG ∧ (↑s : Set A) ⊆ B ∧
      ∃ p₀ : affineBase R B ⟶ I, affineSubalgebraMap B ≫ p₀ = p := by
  let S := Spec (CommRingCat.of R)
  let a := (affineBase R A).hom
  let g : pullback (𝟙 S) a ⟶ pullback I.hom a :=
    pullback.lift (pullback.snd (𝟙 S) a ≫ p.left) (pullback.snd (𝟙 S) a)
      (by rw [Category.assoc, Over.w p])
  obtain ⟨B, hB, hs, g₀, hg₀, hg⟩ :=
    exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (𝟙 S) I.hom g (pullback.lift_snd _ _ _) s
  let b := (affineBase R B).hom
  let j := (affineSubalgebraMap B).left
  have hj : j ≫ b = a := Over.w (affineSubalgebraMap B)
  let i : (affineBase R B).left ⟶ pullback (𝟙 S) b :=
    pullback.lift b (𝟙 _) (by simp)
  let p₀ : affineBase R B ⟶ I := Over.homMk
    (i ≫ g₀ ≫ pullback.fst I.hom b) (by
      calc
        (i ≫ g₀ ≫ pullback.fst I.hom b) ≫ I.hom =
            i ≫ (g₀ ≫ pullback.snd I.hom b) ≫ b := by
          simp only [Category.assoc, pullback.condition]
        _ = i ≫ pullback.snd (𝟙 S) b ≫ b :=
          congrArg (fun k ↦ i ≫ k ≫ b) hg₀
        _ = b := by simp only [i, pullback.lift_snd_assoc, Category.id_comp])
  let q₁ : pullback (𝟙 S) a ⟶ pullback (𝟙 S) b :=
    pullback.lift (pullback.fst (𝟙 S) a) (pullback.snd (𝟙 S) a ≫ j)
      (by rw [Category.assoc, hj, pullback.condition])
  let q₂ : pullback I.hom a ⟶ pullback I.hom b :=
    pullback.lift (pullback.fst I.hom a) (pullback.snd I.hom a ≫ j)
      (by rw [Category.assoc, hj, pullback.condition])
  have h := hg q₁ q₂ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  let iA : (affineBase R A).left ⟶ pullback (𝟙 S) a :=
    pullback.lift a (𝟙 _) (by simp)
  have hi : iA ≫ q₁ = j ≫ i := by
    apply pullback.hom_ext <;>
      dsimp only [iA, q₁, i] <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc,
        Category.id_comp, Category.comp_id]
    exact hj.symm
  refine ⟨B, hB, hs, p₀, ?_⟩
  apply Over.OverMorphism.ext
  change j ≫ i ≫ g₀ ≫ pullback.fst I.hom b = p.left
  calc
    j ≫ i ≫ g₀ ≫ pullback.fst I.hom b =
        iA ≫ (q₁ ≫ g₀) ≫ pullback.fst I.hom b := by
      rw [← Category.assoc j i, ← hi]
      simp only [Category.assoc]
    _ = iA ≫ (g ≫ q₂) ≫ pullback.fst I.hom b := by rw [h]
    _ = p.left := by
      simp only [g, q₂, iA, Category.assoc, pullback.lift_fst,
        pullback.lift_snd_assoc, Category.id_comp]

/-- Affine finite-presentation representation descends each specified section,
 not only the assertion that a section exists. -/
theorem hasAffineSubalgebraSectionDescent_of_representable
    {F : AlgebraicSpace.Presheaf (Spec (CommRingCat.of R))}
    (hF : AlgebraicSpace.IsAffineFinitePresentationRepresentable F) :
    HasAffineSubalgebraSectionDescent F := by
  obtain ⟨I, ⟨e⟩, _, hI⟩ := hF
  intro A _ _ x s
  let p : affineBase R A ⟶ I := (e.inv.app (op (affineBase R A)) x).down
  obtain ⟨B, hB, hs, p₀, hp₀⟩ := exists_affinePoint_subalgebra I p s
  refine ⟨B, hB, hs, e.hom.app (op (affineBase R B)) (ULift.up p₀), ?_⟩
  have he := congrArg
    (fun k : ((AlgebraicSpace.schemeYoneda (Spec (CommRingCat.of R))).obj I).obj
        (op (affineBase R B)) ⟶ F.obj (op (affineBase R A)) ↦ k (ULift.up.{u+1} p₀))
    (e.hom.naturality (affineSubalgebraMap B).op)
  change e.hom.app _ (ULift.up.{u+1} (affineSubalgebraMap B ≫ p₀)) =
    F.map (affineSubalgebraMap B).op (e.hom.app _ (ULift.up.{u+1} p₀)) at he
  refine he.symm.trans ?_
  rw [hp₀]
  exact ConcreteCategory.congr_hom (e.inv_hom_id_app _) x

namespace PicardGroupoid

/-- Focused line-bundle Isom representability yields descent of every specified
 actual isomorphism on each affine test base, retaining its restriction map. -/
theorem affineIsomSectionDescent_of_isomRepresentability
    (h : ProperLineBundleIsomRepresentabilityStatement.{u})
    {S X : Scheme.{u}} (f : X ⟶ S) (hf : IsProper f) (hflat : Flat f)
    (hfp : LocallyOfFinitePresentation f) (t : Spec (CommRingCat.of R) ⟶ S)
    (L M : PicardGroupoid ((relativeSpace f).obj (Over.mk t))) :
    HasAffineSubalgebraSectionDescent (relativeIsomPresheaf f L M) :=
  hasAffineSubalgebraSectionDescent_of_representable
    (h S X f hf hflat hfp (Over.mk t) L M)

/-- The focused line-bundle Hom premise already suffices for descent of a
 specified actual line-bundle isomorphism over an affine algebra base. -/
theorem affineIsomSectionDescent_of_homRepresentability
    (h : ProperLineBundleHomRepresentabilityStatement.{u})
    {S X : Scheme.{u}} (f : X ⟶ S) (hf : IsProper f) (hflat : Flat f)
    (hfp : LocallyOfFinitePresentation f) (t : Spec (CommRingCat.of R) ⟶ S)
    (L M : PicardGroupoid ((relativeSpace f).obj (Over.mk t))) :
    HasAffineSubalgebraSectionDescent (relativeIsomPresheaf f L M) :=
  affineIsomSectionDescent_of_isomRepresentability
    (properLineBundleIsomRepresentability_of_hom h) f hf hflat hfp t L M

end PicardGroupoid

end Langlands.AlgebraicGeometry.Picard
