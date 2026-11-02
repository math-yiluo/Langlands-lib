import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiGluingGeneral
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Over

/-! # The Zariski sheaf of general relative rigidified classes -/

universe v u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

/-- An open cover of a test scheme, regarded as an actual family in the slice. -/
def openCoverOver {S : Scheme.{u}} (T : Over S) (𝒰 : T.left.OpenCover.{u}) :
    PreZeroHypercover.{u} T where
  I₀ := 𝒰.I₀
  X i := Over.mk (𝒰.f i ≫ T.hom)
  f i := Over.homMk (𝒰.f i)

/-- Unique gluing for actual open covers gives the sheaf condition on the big Zariski slice. -/
lemma isSheaf_zariski_over_of_openCover {S : Scheme.{u}} (P : (Over S)ᵒᵖ ⥤ Type v)
    (hP : ∀ (T : Over S) (𝒰 : T.left.OpenCover.{u}),
      Presieve.IsSheafFor P (openCoverOver T 𝒰).presieve₀) :
    Presieve.IsSheaf (Scheme.zariskiTopology.over S) P := by
  intro T R hR
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hR
  have hle : (openCoverOver T 𝒰).presieve₀ ≤ R := by
    rintro _ _ ⟨i⟩
    exact (Sieve.overEquiv_iff R (𝒰.f i)).mp (h𝒰 _ _ ⟨i⟩)
  apply Presieve.isSheafFor_subsieve_aux P ((Sieve.generate_le_iff (openCoverOver T 𝒰).presieve₀ R).mpr hle)
    ((Presieve.isSheafFor_iff_generate (openCoverOver T 𝒰).presieve₀).mp (hP T 𝒰))
  intro U g _ x t₁ t₂ ht₁ ht₂
  apply (hP U (𝒰.pullback₁ g.left)).isSeparatedFor.ext
  rintro _ _ ⟨i⟩
  have hm : (Sieve.generate (openCoverOver T 𝒰).presieve₀).pullback g
      ((openCoverOver U (𝒰.pullback₁ g.left)).f i) := by
    let a : (openCoverOver U (𝒰.pullback₁ g.left)).X i ⟶ (openCoverOver T 𝒰).X i :=
      Over.homMk (𝒰.pullbackHom g.left i) (by
        dsimp [openCoverOver]
        rw [← Category.assoc, 𝒰.pullbackHom_map, Category.assoc, Over.w g])
    refine ⟨_, a, (openCoverOver T 𝒰).f i, ⟨i⟩, ?_⟩
    ext
    exact 𝒰.pullbackHom_map g.left i
  exact (ht₁ _ hm).trans (ht₂ _ hm).symm

namespace RigidifiedLineBundle

open Langlands.SchemeModule.RigidifiedModule

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S)

/-- Relative rigidified classes are a Zariski sheaf when relative isomorphisms are unique. -/
lemma classPresheaf_isSheaf_zariski_of_unique
    (unique : ∀ (T : Over S) (L M : relative f ε section_eq T), Subsingleton (L ≅ M)) :
    Presieve.IsSheaf (Scheme.zariskiTopology.over S)
      (classPresheaf pullbackCoherence f ε section_eq) := by
  apply isSheaf_zariski_over_of_openCover
  intro T 𝒰
  apply (Presieve.isSheafFor_arrows_iff _ _).mpr
  intro q hq
  have hpair : ∀ i j,
      classesPullback f ε section_eq
        (Over.homMk (pullback.fst (𝒰.f i) (𝒰.f j)) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f i ≫ T.hom)) (q i) =
      classesPullback f ε section_eq
        (Over.homMk (pullback.snd (𝒰.f i) (𝒰.f j))
            (by simp [pullback.condition_assoc]) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f j ≫ T.hom)) (q j) := by
    intro i j
    exact hq i j _ _ _ (by ext; exact pullback.condition)
  obtain ⟨q₀, hq₀⟩ := classes_zariskiGluing_of_unique f ε section_eq unique T 𝒰 q hpair
  refine ⟨q₀, hq₀, fun q' hq' ↦ ?_⟩
  exact classes_zariskiSeparated_of_unique f ε section_eq unique T 𝒰 q' q₀
    (fun i ↦ (hq' i).trans (hq₀ i).symm)

end RigidifiedLineBundle
end Langlands.AlgebraicGeometry.Picard
