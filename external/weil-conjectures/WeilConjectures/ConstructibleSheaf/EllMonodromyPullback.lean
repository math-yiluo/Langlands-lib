/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.GaloisCoverPullback
public import WeilConjectures.ConstructibleSheaf.EllMonodromy
public import WeilConjectures.ConstructibleSheaf.Pullback

/-!
# Pullback of complexes with finite `ℓ`-group monodromy

The pullback `f^* E` along any morphism of schemes `f : V ⟶ U` of a complex `E` with finite
`ℓ`-group monodromy has finite `ℓ`-group monodromy
(`AlgebraicGeometry.Etale.HasFiniteEllMonodromy.upperStar'`): homology commutes with the exact
functor `f^*`, so boundedness and finite local constancy are preserved, and the base change
`P ×_U V` of a Galois cover `P ⟶ U` trivializing the homology sheaves of `E` is a Galois cover
with the same group trivializing the homology sheaves of `f^* E`, since `(P ×_U V ⟶ V)^* f^*` is
`(P ×_U V ⟶ P)^* (P ⟶ U)^*` and pullbacks of constant sheaves are constant.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The pullback of a complex with finite `ℓ`-group monodromy has finite `ℓ`-group monodromy. -/
lemma HasFiniteEllMonodromy.upperStar' {ℓ : ℕ} {U V : Scheme.{u}} (f : V ⟶ U)
    {E : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hE : HasFiniteEllMonodromy ℓ E) :
    HasFiniteEllMonodromy ℓ (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E) := by
  obtain ⟨⟨a, b, ha, hb⟩, hc⟩ := hE
  let e (n : ℤ) :
      ((f)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.homologyFunctor _ n).obj E) ≅
      (DerivedCategory.homologyFunctor _ n).obj
        (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E) :=
    (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n).app E
  refine ⟨⟨a, b, ?_, ?_⟩, fun n ↦ ?_⟩
  · rw [DerivedCategory.isGE_iff] at ha ⊢
    exact fun i hi ↦ (((f)^*[ModuleCat.{u + 1} Λ]).map_isZero (ha i hi)).of_iso (e i).symm
  · rw [DerivedCategory.isLE_iff] at hb ⊢
    exact fun i hi ↦ (((f)^*[ModuleCat.{u + 1} Λ]).map_isZero (hb i hi)).of_iso (e i).symm
  · obtain ⟨G, _, _, hG, c, M, hM, ⟨i⟩⟩ := hc n
    set H := (DerivedCategory.homologyFunctor _ n).obj E
    refine ⟨G, inferInstance, inferInstance, hG, c.pullback f, M, hM, ⟨?_⟩⟩
    exact ((pullback.snd c.π f)^*[ModuleCat.{u + 1} Λ]).mapIso (e n).symm ≪≫
      ((upperStarComp _ (pullback.snd c.π f) f).app H).symm ≪≫
      eqToIso (congrArg (fun m ↦ ((m)^*[ModuleCat.{u + 1} Λ]).obj H) pullback.condition.symm) ≪≫
      (upperStarComp _ (pullback.fst c.π f) c.π).app H ≪≫
      ((pullback.fst c.π f)^*[ModuleCat.{u + 1} Λ]).mapIso i ≪≫
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) (pullback.fst c.π f)).app M

end AlgebraicGeometry.Etale
