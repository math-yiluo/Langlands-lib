import Langlands.Geometry.Building.IntegerCentralizer

/-! # Independence of integer-valued V 6 from the centralizer representative -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits

namespace Langlands.Geometry.Building.IntegerValuation

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [IsAffineHom G.X.hom]
  {v : Valuation k (WithZero (Multiplicative ℤ))}

/-- Full integer-valued V 6 depends on the actual centralizer functor, rather than
on its chosen representing group scheme and inclusion. -/
theorem IsCentralizerCompatible.changeCentralizer
    {φ : RootFunctionFamily S G} {C E : CentralizerDatum i}
    (hφ : IsCentralizerCompatible v i C.j C.s C.bijective φ) :
    IsCentralizerCompatible v i E.j E.s E.bijective φ := by
  let e : C.Z ≅ E.Z := C.isRepresentedBy.isoOfIsRepresentedBy E.isRepresentedBy
  have hj : e.hom ≫ E.j = C.j :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ E.isRepresentedBy
  have hs : C.s ≫ e.hom = E.s := by
    apply E.isRepresentedBy.hom_ext
    rw [Category.assoc, hj, C.comp_eq, E.comp_eq]
  have heval : ∀ χ : rationalCharacters E.Z,
      Cartan.characterRestriction C.s (characterRestrict e.hom χ) =
        Cartan.characterRestriction E.s χ := by
    intro χ
    change C.s ≫ e.hom ≫ χ.toMul = E.s ≫ χ.toMul
    rw [← Category.assoc, hs]
  have htrans : ∀ z : rationalPoints C.Z,
      (centralizerTranslation v C.s C.bijective z).toAdd =
        (centralizerTranslation v E.s E.bijective (rationalPoints.map e.hom z)).toAdd := by
    intro z
    apply E.bijective.injective
    apply AddMonoidHom.ext
    intro χ
    change eval S (Cartan.characterRestriction E.s χ)
        (centralizerTranslation v C.s C.bijective z).toAdd =
      eval S (Cartan.characterRestriction E.s χ)
        (centralizerTranslation v E.s E.bijective (rationalPoints.map e.hom z)).toAdd
    conv_lhs => rw [← heval χ]
    rw [eval_centralizerTranslation, eval_centralizerTranslation,
      rationalCharacterEval_characterRestrict]
  have hmap : ∀ z : rationalPoints C.Z,
      rationalPoints.map E.j (rationalPoints.map e.hom z) = rationalPoints.map C.j z := by
    intro z
    simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f : C.Z ⟶ G => z ≫ f.hom.hom) hj
  intro a ha z g hg
  obtain ⟨z, rfl⟩ := (isoPointsEquiv e (Over.mk (𝟙 _))).surjective z
  change φ a ((rationalPoints.map E.j (rationalPoints.map e.hom z))⁻¹ * g *
      rationalPoints.map E.j (rationalPoints.map e.hom z)) =
    φ a g + ((eval S a
      (centralizerTranslation v E.s E.bijective (rationalPoints.map e.hom z)).toAdd : ℝ) :
        WithTop ℝ)
  rw [hmap, ← htrans]
  exact hφ a ha z g hg

variable [Mono i.hom.hom.left]

/-- The class-level full V 6 condition is independent of the chosen representative
of the same actual centralizer. -/
theorem IsOmegaCompatible.changeCentralizer
    {D : KPApartmentData i (order v)} {C E : CentralizerDatum i}
    (hD : IsOmegaCompatible v D C) : IsOmegaCompatible v D E := by
  intro φ hφ
  exact (hD φ hφ).changeCentralizer

end Langlands.Geometry.Building.IntegerValuation
