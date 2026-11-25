/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
import WeilConjectures.AlgebraicGeometry.Modules.LocalInvertibleMinorBlock
import WeilConjectures.AlgebraicGeometry.Modules.ComplementaryBlockVanishes
import Mathlib.CategoryTheory.Preadditive.Biproducts

@[expose] public section

universe u
open CategoryTheory Limits SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

/-- The local normal form in the nonempty open-subscheme case. -/
theorem exists_local_normal_form_of_constantRank_nonempty
    {Y Z : Scheme.{u}} [IsReduced Y] [Nonempty Z] {M N : Y.Modules} {m n : ℕ}
    (eM : M ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin m)))
    (eN : N ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin n)))
    (φ : M ⟶ N) (j : Z ⟶ Y) [IsOpenImmersion j] (a : ℕ)
    (hrank : ∀ z : Z, ∃ (R : CommRingCat.{u}) (_ : IsField R) (g : Spec R ⟶ Y),
      Set.range g.base = {j.base z} ∧
      ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).map g.appTop).rank = a) :
    ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
      ∃ (eS : ((Modules.pullback j).obj M).restrict U.ι ≅
          free (ULift.{u} (Fin (m - a))) ⊞ free (ULift.{u} (Fin a)))
        (eT : ((Modules.pullback j).obj N).restrict U.ι ≅
          free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (n - a)))),
        (restrictFunctor U.ι).map ((Modules.pullback j).map φ) =
          eS.hom ≫ biprod.snd ≫ biprod.inl ≫ eT.inv := by
  classical
  intro z
  obtain ⟨R, hR, g, hpoint, hRank⟩ := hrank z
  let := hR.toField
  obtain ⟨x⟩ : Nonempty (Spec R) := inferInstance
  have hx : g.base x = j.base z := by
    have hx' : g.base x ∈ Set.range g.base := ⟨x, rfl⟩
    simpa only [hpoint, Set.mem_singleton_iff] using hx'
  obtain ⟨rows, cols, hminor⟩ :=
    (le_rank_map_appTop_iff (isField_Γ_Spec hR) g x
      (freeMatrix (eM.inv ≫ φ ≫ eN.hom)) a).mp (le_of_eq hRank.symm)
  rw [hx] at hminor
  obtain ⟨U, hzU, eS, eT, hblock⟩ :=
    exists_local_invertible_minor_block eM eN φ j a z rows cols hminor
  let ψ := (restrictFunctor U.ι).map ((Modules.pullback j).map φ)
  let F := eS.inv ≫ ψ ≫ eT.hom
  let f := biprod.inl ≫ F ≫ biprod.fst
  have : IsIso f := by
    simpa only [f, F, ψ, Category.assoc] using hblock
  obtain ⟨L, Q, δ, hdiag⟩ := Biprod.gaussian F
  let eS' := eS ≪≫ L.symm
  let eT' := eT ≪≫ Q
  have hform : ψ = eS'.hom ≫ biprod.map f δ ≫ eT'.inv := by
    rw [← hdiag]
    simp [eS', eT', F, Category.assoc]
  have hδ : δ = 0 := complementary_block_eq_zero_of_rank_le eM eN φ j a U
    (fun w _ => by
      obtain ⟨K, hK, k, hk, hr⟩ := hrank w
      exact ⟨K, hK, k, hk, le_of_eq hr⟩) eS' eT' f δ hform
  let B := biprod.mapIso (asIso f)
    (Iso.refl (free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (m - a)))))
  let C := biprod.braiding (free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin a)))
    (free (ULift.{u} (Fin (m - a))))
  refine ⟨U, hzU, eS' ≪≫ B ≪≫ C, eT', ?_⟩
  change ψ = _
  rw [hform, hδ]
  have hmap : biprod.map f (0 : free (R := U.toScheme.ringCatSheaf)
      (ULift.{u} (Fin (m - a))) ⟶ free (ULift.{u} (Fin (n - a)))) =
      B.hom ≫ C.hom ≫ biprod.snd ≫ biprod.inl := by
    apply biprod.hom_ext <;> simp [B, C]
  simp only [Iso.trans_hom, Category.assoc]
  rw [hmap]
  simp only [Category.assoc]

end AlgebraicGeometry.Scheme.Modules
