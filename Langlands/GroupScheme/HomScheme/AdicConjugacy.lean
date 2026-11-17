import Langlands.GroupScheme.HomScheme.AdicSystem
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent

/-! # Algebraizing compatible conjugating points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AdicAffinePoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HomScheme

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- Conjugation by a constant family is the base change of global conjugation. -/
theorem conjugationFamily_constantPoint (f : H ⟶ G)
    (g : Over.mk (𝟙 S) ⟶ G.X) (T : Over S) :
    conjugationFamily f (G.constantPoint g T) =
      (baseChange T.hom).map (f ≫ (G.innerIso g).hom) := by
  have hp : RelativeLevi.pulledBackPoint G T (G.constantPoint g T) =
      baseChangeBasePoint T.hom G g := by
    apply (baseChangeBasePointsEquiv T.hom G).injective
    rw [RelativeLevi.baseChangeBasePointsEquiv_pulledBackPoint]
    exact ((baseChangeBasePointsEquiv T.hom G).apply_symm_apply _).symm
  rw [conjugationFamily, hp, Functor.map_comp, baseChange_innerIso_hom]

/-- The identity point acts trivially on each relative Hom family. -/
@[simp]
theorem conjugationFamily_one (f : H ⟶ G) (T : Over S) :
    conjugationFamily f (1 : T ⟶ G.X) = (baseChange T.hom).map f := by
  change (baseChange T.hom).map f ≫
    (((baseChange T.hom).obj G).innerIso
      (RelativeLevi.pulledBackPointHom G T 1)).hom = _
  rw [map_one, innerIso_one_hom, Category.comp_id]

namespace Adic

variable {A : Type u} [CommRing A] (I : Ideal A)
    {H G : GroupScheme (Spec (CommRingCat.of A))}

/-- Compatible actual conjugating points on the adic thickenings, starting at the unit. -/
structure ConjugatorSystem (f f' : H ⟶ G) where
  point (n : ℕ) : Over.mk (quotientMap I n) ⟶ G.X
  compatible (n : ℕ) : transitionOver I n ≫ point (n + 1) = point n
  initial : point 0 = 1
  conjugates (n : ℕ) :
    (baseChange (quotientMap I n)).map f' = conjugationFamily f (point n)

/-- Compatible conjugating points algebraize, and injectivity of adic Hom restriction
turns their formal conjugacy into actual conjugacy over the complete ring. -/
theorem exists_conjugator_of_compatible_points [IsAdicComplete I A]
    [IsAffineHom G.X.hom]
    (hinj : Function.Injective (System.restrict I H G))
    (f f' : H ⟶ G)
    (g : ∀ n : ℕ, Over.mk (quotientMap I n) ⟶ G.X)
    (hg : ∀ n : ℕ, transitionOver I n ≫ g (n + 1) = g n)
    (hg₀ : g 0 = 1)
    (hconj : ∀ n : ℕ,
      (baseChange (quotientMap I n)).map f' = conjugationFamily f (g n)) :
    ∃ q : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ G.X,
      G.constantPoint q (Over.mk (quotientMap I 0)) = 1 ∧
        f' = f ≫ (G.innerIso q).hom := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨q, hq, -⟩ := existsUnique_over_adic_lift I g hg
  refine ⟨q, ?_, ?_⟩
  · change reduction I 0 ≫ q = 1
    rw [hq 0, hg₀]
  · apply hinj
    apply System.ext
    intro n
    change (baseChange (quotientMap I n)).map f' =
      (baseChange (quotientMap I n)).map (f ≫ (G.innerIso q).hom)
    calc
      _ = conjugationFamily f (g n) := hconj n
      _ = conjugationFamily f (G.constantPoint q (Over.mk (quotientMap I n))) :=
        congrArg (conjugationFamily f) (hq n).symm
      _ = _ := conjugationFamily_constantPoint f q _

/-- A compatible system of conjugators gives a global conjugator when Hom restriction is
injective. -/
theorem ConjugatorSystem.exists_global [IsAdicComplete I A] [IsAffineHom G.X.hom]
    (hinj : Function.Injective (System.restrict I H G))
    {f f' : H ⟶ G} (s : ConjugatorSystem I f f') :
    ∃ q : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ G.X,
      G.constantPoint q (Over.mk (quotientMap I 0)) = 1 ∧
        f' = f ≫ (G.innerIso q).hom :=
  exists_conjugator_of_compatible_points I hinj f f'
    s.point s.compatible s.initial s.conjugates

/-- Extending every conjugator by one level suffices to obtain a global conjugator
reducing to the identity. -/
theorem exists_conjugator_of_step_lifting [IsAdicComplete I A] [IsAffineHom G.X.hom]
    (hinj : Function.Injective (System.restrict I H G))
    (f f' : H ⟶ G)
    (h₀ : (baseChange (quotientMap I 0)).map f =
      (baseChange (quotientMap I 0)).map f')
    (hstep : ∀ (n : ℕ) (g : Over.mk (quotientMap I n) ⟶ G.X),
      (baseChange (quotientMap I n)).map f' = conjugationFamily f g →
      ∃ g' : Over.mk (quotientMap I (n + 1)) ⟶ G.X,
        transitionOver I n ≫ g' = g ∧
          (baseChange (quotientMap I (n + 1))).map f' = conjugationFamily f g') :
    ∃ q : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ G.X,
      G.constantPoint q (Over.mk (quotientMap I 0)) = 1 ∧
        f' = f ≫ (G.innerIso q).hom := by
  let C (n : ℕ) := { g : Over.mk (quotientMap I n) ⟶ G.X //
    (baseChange (quotientMap I n)).map f' = conjugationFamily f g }
  let c₀ : C 0 := ⟨1, by
    rw [conjugationFamily_one]
    exact h₀.symm⟩
  let c : ∀ n, C n := Nat.rec (motive := C) c₀ (fun n g ↦
    ⟨(hstep n g.val g.property).choose, (hstep n g.val g.property).choose_spec.2⟩)
  apply exists_conjugator_of_compatible_points I hinj f f' (fun n ↦ (c n).val)
  · intro n
    exact (hstep n (c n).val (c n).property).choose_spec.1
  · rfl
  · exact fun n ↦ (c n).property

end Adic

end Langlands.GroupScheme.HomScheme
