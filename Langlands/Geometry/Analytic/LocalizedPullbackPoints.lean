import Langlands.Geometry.Analytic.FibreProductPoints
import Langlands.Geometry.Analytic.FibreProductLocalizedLimit

/-! # Underlying point lifting for localized pullbacks -/

noncomputable section

universe u

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A localized square has point lifting if every pair with equal images
comes from some point of its upper-left object. This condition asserts
neither uniqueness nor any topological universal property. -/
def HasPointLifting
    {P A B C : LocalizedCategory.{u, u, u} (K := K)}
    (p : P ⟶ A) (q : P ⟶ B) (f : A ⟶ C) (g : B ⟶ C) : Prop :=
  ∀ (x : localizedSpaceFunctor.obj A) (y : localizedSpaceFunctor.obj B),
    localizedSpaceFunctor.map f x = localizedSpaceFunctor.map g y →
      ∃ z : localizedSpaceFunctor.obj P,
        localizedSpaceFunctor.map p z = x ∧ localizedSpaceFunctor.map q z = y

/-- Compatible points lift to the actual small fibre-product cone. -/
theorem exists_smallFibreProduct_point
    {A B C : SaturatedAtlasPresentation.{u, u, u} K} (f : A ⟶ C) (g : B ⟶ C)
    (x : A.presentation.space) (y : B.presentation.space)
    (hxy : f.baseMap x = g.baseMap y) :
    ∃ z : (smallFibreProduct f g).presentation.space,
      (smallFibreProductFst f g).baseMap z = x ∧
      (smallFibreProductSnd f g).baseMap z = y := by
  obtain ⟨z, hz₁, hz₂⟩ := FibreProduct.exists_point
    (geometricCompatibleMap f) (geometricCompatibleMap g)
    A.hasAllLocalDomains B.hasAllLocalDomains x y hxy
  refine ⟨FibreProduct.smallSpaceHomeomorph (geometricCompatibleMap f)
    (geometricCompatibleMap g) A.hasAllLocalDomains B.hasAllLocalDomains
    C.hasAllLocalDomains z, ?_, ?_⟩
  · change FibreProduct.fst (geometricCompatibleMap f) (geometricCompatibleMap g)
      ((FibreProduct.smallSpaceHomeomorph (geometricCompatibleMap f)
        (geometricCompatibleMap g) A.hasAllLocalDomains B.hasAllLocalDomains
        C.hasAllLocalDomains).symm
          (FibreProduct.smallSpaceHomeomorph (geometricCompatibleMap f)
            (geometricCompatibleMap g) A.hasAllLocalDomains B.hasAllLocalDomains
            C.hasAllLocalDomains z)) = x
    rw [Homeomorph.symm_apply_apply]
    exact hz₁
  · change FibreProduct.snd (geometricCompatibleMap f) (geometricCompatibleMap g)
      ((FibreProduct.smallSpaceHomeomorph (geometricCompatibleMap f)
        (geometricCompatibleMap g) A.hasAllLocalDomains B.hasAllLocalDomains
        C.hasAllLocalDomains).symm
          (FibreProduct.smallSpaceHomeomorph (geometricCompatibleMap f)
            (geometricCompatibleMap g) A.hasAllLocalDomains B.hasAllLocalDomains
            C.hasAllLocalDomains z)) = y
    rw [Homeomorph.symm_apply_apply]
    exact hz₂

/-- The underlying points of a localized pullback of strong arrows lift all
compatible pairs. -/
theorem exists_point_of_isPullback_strong
    {A B C : SaturatedAtlasPresentation.{u, u, u} K}
    {P : LocalizedCategory.{u, u, u} (K := K)}
    (p : P ⟶ localizationFunctor.obj A) (q : P ⟶ localizationFunctor.obj B)
    (f : A ⟶ C) (g : B ⟶ C)
    (h : IsPullback p q (localizationFunctor.map f) (localizationFunctor.map g))
    (x : A.presentation.space) (y : B.presentation.space)
    (hxy : f.baseMap x = g.baseMap y) :
    ∃ z : localizedSpaceFunctor.obj P,
      localizedSpaceFunctor.map p z = x ∧ localizedSpaceFunctor.map q z = y := by
  obtain ⟨z, hz₁, hz₂⟩ := exists_smallFibreProduct_point f g x y hxy
  obtain ⟨l, hl₁, hl₂⟩ := h.exists_lift
    (localizationFunctor.map (smallFibreProductFst f g))
    (localizationFunctor.map (smallFibreProductSnd f g)) (by
      rw [← Functor.map_comp, ← Functor.map_comp, smallFibreProduct_condition])
  refine ⟨localizedSpaceFunctor.map l z, ?_, ?_⟩
  · have hz := congrArg
      (fun (k : localizationFunctor.obj (smallFibreProduct f g) ⟶
          localizationFunctor.obj A) => localizedSpaceFunctor.map k
        (z : localizedSpaceFunctor.obj
          (localizationFunctor.obj (smallFibreProduct f g)))) hl₁
    rw [Functor.map_comp, localizedSpaceFunctor_map] at hz
    exact hz.trans hz₁
  · have hz := congrArg
      (fun (k : localizationFunctor.obj (smallFibreProduct f g) ⟶
          localizationFunctor.obj B) => localizedSpaceFunctor.map k
        (z : localizedSpaceFunctor.obj
          (localizationFunctor.obj (smallFibreProduct f g)))) hl₂
    rw [Functor.map_comp, localizedSpaceFunctor_map] at hz
    exact hz.trans hz₂

/-- Every categorical pullback in the equal-universe localization lifts all
compatible underlying points. -/
theorem exists_point_of_isPullback
    {P A B C : LocalizedCategory.{u, u, u} (K := K)}
    (p : P ⟶ A) (q : P ⟶ B) (f : A ⟶ C) (g : B ⟶ C)
    (h : IsPullback p q f g)
    (x : localizedSpaceFunctor.obj A) (y : localizedSpaceFunctor.obj B)
    (hxy : localizedSpaceFunctor.map f x = localizedSpaceFunctor.map g y) :
    ∃ z : localizedSpaceFunctor.obj P,
      localizedSpaceFunctor.map p z = x ∧ localizedSpaceFunctor.map q z = y := by
  obtain ⟨A₀, hA⟩ := localizedObjectEquiv.surjective A
  obtain ⟨B₀, hB⟩ := localizedObjectEquiv.surjective B
  obtain ⟨C₀, hC⟩ := localizedObjectEquiv.surjective C
  change localizationFunctor.obj A₀ = A at hA
  change localizationFunctor.obj B₀ = B at hB
  change localizationFunctor.obj C₀ = C at hC
  subst A B C
  obtain ⟨φ, rfl⟩ := exists_localizedRightFraction f
  obtain ⟨ψ, rfl⟩ := exists_localizedRightFraction g
  have hxy' : φ.f.baseMap (φ.hs.inverseBaseMap x) =
      ψ.f.baseMap (ψ.hs.inverseBaseMap y) := by
    rw [localizedSpaceFunctor_map_rightFraction,
      localizedSpaceFunctor_map_rightFraction] at hxy
    exact hxy
  obtain ⟨z, hz₁, hz₂⟩ := exists_smallFibreProduct_point φ.f ψ.f
    (φ.hs.inverseBaseMap x) (ψ.hs.inverseBaseMap y) hxy'
  let a := localizationFunctor.map (smallFibreProductFst φ.f ψ.f) ≫
    localizationFunctor.map φ.s
  let b := localizationFunctor.map (smallFibreProductSnd φ.f ψ.f) ≫
    localizationFunctor.map ψ.s
  have hab : a ≫ localizedRightFraction φ = b ≫ localizedRightFraction ψ := by
    dsimp only [a, b]
    rw [Category.assoc, localizationFunctor_map_s_comp_localizedRightFraction,
      Category.assoc, localizationFunctor_map_s_comp_localizedRightFraction,
      ← Functor.map_comp, ← Functor.map_comp, smallFibreProduct_condition]
  obtain ⟨l, hl₁, hl₂⟩ := h.exists_lift a b hab
  refine ⟨localizedSpaceFunctor.map l z, ?_, ?_⟩
  · have hz := congrArg
      (fun (k : localizationFunctor.obj (smallFibreProduct φ.f ψ.f) ⟶
          localizationFunctor.obj A₀) => localizedSpaceFunctor.map k
        (z : localizedSpaceFunctor.obj
          (localizationFunctor.obj (smallFibreProduct φ.f ψ.f)))) hl₁
    dsimp only [a] at hz
    rw [Functor.map_comp, Functor.map_comp,
      localizedSpaceFunctor_map, localizedSpaceFunctor_map] at hz
    change localizedSpaceFunctor.map p (localizedSpaceFunctor.map l z) =
      φ.s.baseMap ((smallFibreProductFst φ.f ψ.f).baseMap z) at hz
    rw [hz₁] at hz
    exact hz.trans (φ.hs.1.homeomorph.apply_symm_apply x)
  · have hz := congrArg
      (fun (k : localizationFunctor.obj (smallFibreProduct φ.f ψ.f) ⟶
          localizationFunctor.obj B₀) => localizedSpaceFunctor.map k
        (z : localizedSpaceFunctor.obj
          (localizationFunctor.obj (smallFibreProduct φ.f ψ.f)))) hl₂
    dsimp only [b] at hz
    rw [Functor.map_comp, Functor.map_comp,
      localizedSpaceFunctor_map, localizedSpaceFunctor_map] at hz
    change localizedSpaceFunctor.map q (localizedSpaceFunctor.map l z) =
      ψ.s.baseMap ((smallFibreProductSnd φ.f ψ.f).baseMap z) at hz
    rw [hz₂] at hz
    exact hz.trans (ψ.hs.1.homeomorph.apply_symm_apply y)

/-- Categorical pullbacks have the underlying point-lifting property. -/
theorem hasPointLifting_of_isPullback
    {P A B C : LocalizedCategory.{u, u, u} (K := K)}
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (h : IsPullback p q f g) : HasPointLifting p q f g :=
  exists_point_of_isPullback p q f g h

end Langlands.Analytic.SaturatedAtlasPresentation
