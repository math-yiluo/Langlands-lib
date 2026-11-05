import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.CentralIsogeny.TorusCentralizerReflection
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Rational.Characters

/-! # Actual normalizer lifting through a central cover and a monomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Commutation of a maximal split torus with its conjugate already implies
that the conjugating point normalizes that torus. -/
theorem IsMaximalSplitTorus.mem_normalizerPoints_of_commute_conjugate
    {C : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom C.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ C} (hi : IsMaximalSplitTorus i) (c : rationalPoints C)
    (hab : ∀ (U : Over (Spec (CommRingCat.of k)))
      (x y : U ⟶ T.X),
      Commute (x ≫ (i ≫ (C.innerIso c).hom).hom.hom) (y ≫ i.hom.hom)) :
    c ∈ normalizerPoints i := by
  obtain ⟨b, hb⟩ := hi.exists_factor_of_commute hi.1.1 (i ≫ (C.innerIso c).hom) hab
  have : IsIso b := (hi.comp_iso (C.innerIso c)).2 T i hi.1 b hb
  let e : T ≅ T :=
    { hom := Additive.ofMul (asIso b).hom
      inv := Additive.ofMul (asIso b).inv
      hom_inv_id := congrArg Additive.ofMul (asIso b).hom_inv_id
      inv_hom_id := congrArg Additive.ofMul (asIso b).inv_hom_id }
  exact ⟨e, hb.symm⟩

namespace DerivedCoverNormalizerLift

variable {C D G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom C.X.hom]
  {T S : CommGroupScheme (Spec (CommRingCat.of k))}
  (π : C ⟶ D) (d : D ⟶ G) [Mono d.hom.hom.left]
  (hπ : IsCentralIsogeny π)
  (i : T.toGrp ⟶ C) (hi : IsMaximalSplitTorus i)
  (j : S.toGrp ⟶ G) (t : T ⟶ S)
  (h : i ≫ π ≫ d = CommGroupScheme.groupHom t ≫ j)

include h hπ hi

/-- Any chosen cover point whose image normalizes the target commutative
subgroup normalizes the source maximal split torus. -/
theorem mem_normalizerPoints (c : rationalPoints C)
    (hc : rationalPoints.map (π ≫ d) c ∈ normalizerPoints j) :
    c ∈ normalizerPoints i := by
  obtain ⟨σ, hσ⟩ := hc
  let a := i ≫ (C.innerIso c).hom
  have ha : a ≫ π ≫ d = CommGroupScheme.groupHom (t ≫ σ.hom) ≫ j := by
    calc
      _ = i ≫ (π ≫ d) ≫ (G.innerIso (rationalPoints.map (π ≫ d) c)).hom := by
        dsimp only [a]
        rw [Category.assoc, Category.assoc, innerIso_hom_comp]
        rfl
      _ = CommGroupScheme.groupHom t ≫ j ≫
          (G.innerIso (rationalPoints.map (π ≫ d) c)).hom := by
        rw [← Category.assoc, h, Category.assoc]
      _ = _ := by
        rw [hσ]
        rfl
  have hcomm : ∀ (U : Over (Spec (CommRingCat.of k)))
      (x : U ⟶ T.X) (y : U ⟶ T.X),
      Commute (x ≫ a.hom.hom) (y ≫ i.hom.hom) := by
    intro U x y
    have hcent : (x ≫ a.hom.hom) ≫ π.hom.hom ∈
        (torusCentralizer (i ≫ π)).carrier U := by
      intro V v z
      apply (commute_iff_eq _ _).mpr
      let : Mono d.hom.hom := Over.mono_of_mono_left _
      apply (cancel_mono d.hom.hom).mp
      have hcS : Commute
          ((v ≫ x) ≫ (CommGroupScheme.groupHom (t ≫ σ.hom)).hom.hom)
          (z ≫ (CommGroupScheme.groupHom t).hom.hom) := Commute.all _ _
      have he := congrArg (fun w : V ⟶ S.X => w ≫ j.hom.hom) hcS.eq
      simpa only [MonObj.mul_comp, Category.assoc, ← Grp.comp_hom_hom, ha, h] using he
    have hcT := (hπ.mem_torusCentralizer_iff hi.1.1.isTorus i (x ≫ a.hom.hom)).mp hcent
    simpa only [Category.id_comp] using hcT U (𝟙 U) y
  exact hi.mem_normalizerPoints_of_commute_conjugate c hcomm

/-- The inverse image of the target normalizer maps into the actual source
normalizer by retaining each chosen cover point. -/
def normalizerPointsHom :
    (normalizerPoints j).comap (rationalPoints.map (π ≫ d)) →* normalizerPoints i where
  toFun c := ⟨c.val, mem_normalizerPoints π d hπ i hi j t h c.val c.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem normalizerPointsHom_apply
    (c : (normalizerPoints j).comap (rationalPoints.map (π ≫ d))) :
    (normalizerPointsHom π d hπ i hi j t h c : rationalPoints C) = c.val := rfl

/-- A target normalizer point in the actual rational-point image has a lift
in the actual source normalizer. -/
theorem exists_normalizer_lift (n : normalizerPoints j)
    (hn : n.val ∈ (rationalPoints.map (π ≫ d)).range) :
    ∃ c : normalizerPoints i, rationalPoints.map (π ≫ d) c.val = n.val := by
  obtain ⟨c, hc⟩ := hn
  have hcn : rationalPoints.map (π ≫ d) c ∈ normalizerPoints j := hc.symm ▸ n.property
  exact ⟨⟨c, mem_normalizerPoints π d hπ i hi j t h c hcn⟩, hc⟩

end DerivedCoverNormalizerLift

end Langlands.GroupScheme
