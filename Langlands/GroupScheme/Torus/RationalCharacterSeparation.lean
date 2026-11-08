import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.Rational.GeometricPointHom
import Langlands.GroupScheme.Torus.RationalDensity
import Langlands.GroupScheme.Torus.Integral

/-! # Rational points separate characters of a split base change -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.RationalCharacterSeparation

/-- Morphisms out of a reduced scheme that agree over a separated morphism are equal once
they agree after composing with a family of morphisms whose images have dense union. -/
theorem ext_of_dense_iUnion_range {X Y Z : Scheme.{u}} [IsReduced X] {f g : X ⟶ Y}
    (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s) {J : Type*} {W : J → Scheme.{u}}
    (p : ∀ a, W a ⟶ X) (hp : Dense (⋃ a, Set.range (p a)))
    (hfg : ∀ a, p a ≫ f = p a ≫ g) : f = g := by
  have : IsDominant (equalizer.ι f g) := by
    refine ⟨hp.mono ?_⟩
    rintro x ⟨_, ⟨a, rfl⟩, w, rfl⟩
    exact ⟨equalizer.lift (p a) (hfg a) w, by rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]⟩
  exact ext_of_isDominant_of_isSeparated s h (equalizer.ι f g) (equalizer.condition f g)

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- The extended rational points of `G` separate the characters of its base change to `L`:
two characters of the base change agreeing on every extended rational point are equal. -/
def SeparatesBaseChangeCharacters : Prop :=
  ∀ ψ ψ' : rationalCharacters (GaloisPointComparison.baseChanged k L G),
    (∀ z : rationalPoints G,
      rationalCharacterEval ψ (GaloisPointComparison.rationalExtend k L G z) =
        rationalCharacterEval ψ' (GaloisPointComparison.rationalExtend k L G z)) → ψ = ψ'

/-- Extending a rational point to `L` is the canonical pullback section. -/
theorem rationalExtend_eq_geometricRationalPointHom (z : rationalPoints G) :
    GaloisPointComparison.rationalExtend k L G z = geometricRationalPointHom (K := L) G z := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [GaloisPointComparison.rationalExtend_fst]
    exact (baseChangeSectionHom_fst _ G z).symm
  · have h1 := Over.w (GaloisPointComparison.rationalExtend k L G z)
    have h2 := Over.w (geometricRationalPointHom (K := L) G z)
    exact h1.trans h2.symm

/-- If `G` has dense rational points, their extensions are dense in the base change. -/
theorem dense_iUnion_range_rationalExtend (hG : HasDenseRationalPoints k G.X) :
    Dense (⋃ z : rationalPoints G,
      Set.range (GaloisPointComparison.rationalExtend k L G z).left) := by
  simp only [rationalExtend_eq_geometricRationalPointHom]
  exact dense_geometricRationalPointHom G hG

/-- **Rational points separate characters of the base change.** If `G` has dense rational
points and its base change to `L` is reduced, then two characters of the base change that
agree on all extended rational points of `G` are equal. -/
theorem rationalCharacters_ext [IsReduced (GaloisPointComparison.baseChanged k L G).X.left]
    (hG : HasDenseRationalPoints k G.X)
    {ψ ψ' : rationalCharacters (GaloisPointComparison.baseChanged k L G)}
    (h : ∀ z : rationalPoints G,
      rationalCharacterEval ψ (GaloisPointComparison.rationalExtend k L G z) =
        rationalCharacterEval ψ' (GaloisPointComparison.rationalExtend k L G z)) :
    ψ = ψ' := by
  have hpt : ∀ z : rationalPoints G,
      GaloisPointComparison.rationalExtend k L G z ≫ ψ.toMul.hom.hom =
        GaloisPointComparison.rationalExtend k L G z ≫ ψ'.toMul.hom.hom := fun z =>
    (Gm.affinePointsEquiv _).injective (h z)
  have hleft : ψ.toMul.hom.hom.left = ψ'.toMul.hom.hom.left :=
    ext_of_dense_iUnion_range (GroupScheme.Gm (Spec (CommRingCat.of L))).X.hom
      ((Over.w ψ.toMul.hom.hom).trans (Over.w ψ'.toMul.hom.hom).symm)
      (fun z => (GaloisPointComparison.rationalExtend k L G z).left)
      (dense_iUnion_range_rationalExtend k L G hG)
      (fun z => congrArg (fun q => q.left) (hpt z))
  have hhom : ψ.toMul = ψ'.toMul := by
    apply Grp.hom_ext
    exact Over.OverMorphism.ext hleft
  exact congrArg Additive.ofMul hhom

/-- **Separation for tori.** Let `k` be infinite and `L / k` finite Galois, and suppose the
base change of `G` to `L` is a split torus. Then characters of the base change are determined
by their values on the extended rational points of `G`. -/
theorem rationalCharacters_ext_of_isSplitTorus [Infinite k] [FiniteDimensional k L]
    [IsGalois k L] (hT : IsSplitTorus (GaloisPointComparison.baseChanged k L G))
    {ψ ψ' : rationalCharacters (GaloisPointComparison.baseChanged k L G)}
    (h : ∀ z : rationalPoints G,
      rationalCharacterEval ψ (GaloisPointComparison.rationalExtend k L G z) =
        rationalCharacterEval ψ' (GaloisPointComparison.rationalExtend k L G z)) :
    ψ = ψ' := by
  have : IsIntegral (GaloisPointComparison.baseChanged k L G).X.left := hT.isIntegral
  exact rationalCharacters_ext k L G
    (TorusDensity.dense_rationalPoints_of_isSplitTorus_baseChange G hT) h

/-- Dense rational points and a reduced base change give `SeparatesBaseChangeCharacters`. -/
theorem separatesBaseChangeCharacters
    [IsReduced (GaloisPointComparison.baseChanged k L G).X.left]
    (hG : HasDenseRationalPoints k G.X) : SeparatesBaseChangeCharacters k L G :=
  fun _ _ h => rationalCharacters_ext k L G hG h

/-- A torus split by a finite Galois extension of an infinite field satisfies
`SeparatesBaseChangeCharacters`. -/
theorem separatesBaseChangeCharacters_of_isSplitTorus [Infinite k] [FiniteDimensional k L]
    [IsGalois k L] (hT : IsSplitTorus (GaloisPointComparison.baseChanged k L G)) :
    SeparatesBaseChangeCharacters k L G :=
  fun _ _ h => rationalCharacters_ext_of_isSplitTorus k L G hT h

end Langlands.GroupScheme.RationalCharacterSeparation
