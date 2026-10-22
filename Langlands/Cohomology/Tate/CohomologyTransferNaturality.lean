import Langlands.Cohomology.Tate.CohomologyTransfer
import Langlands.Cohomology.Tate.CochainComparison

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R G : Type u} [CommRing R] [Group G]

/-- The standard-resolution coordinates commute with coefficient maps. -/
lemma cochainsIsoStandard_hom_postcomp {A B : Rep.{u} R G}
    (f : A ⟶ B) (n : ℕ) (c : (Fin n → G) → A) :
    (cochainsIsoStandard B).hom.f n
        ((groupCohomology.cochainsMap (MonoidHom.id G) f).f n c) =
      (cochainsIsoStandard A).hom.f n c ≫ f := by
  have hf :
      (Rep.freeLiftLEquiv R G (Fin n → G) B).symm (fun g => f.hom (c g)) =
        (Rep.freeLiftLEquiv R G (Fin n → G) A).symm c ≫ f := by
    apply Rep.free_ext
    intro g
    simp [Rep.freeLiftLEquiv, Representation.freeLiftLEquiv, Rep.homEquiv,
      Representation.freeLift_single_single]
  change (Rep.barComplex.isoStandardComplex R G).inv.f n ≫
      (Rep.freeLiftLEquiv R G (Fin n → G) B).symm (fun g => f.hom (c g)) =
    ((Rep.barComplex.isoStandardComplex R G).inv.f n ≫
      (Rep.freeLiftLEquiv R G (Fin n → G) A).symm c) ≫ f
  rw [hf, Category.assoc]

/-- The inverse coordinate comparison also commutes with coefficient maps. -/
lemma cochainsIsoStandard_inv_postcomp {A B : Rep.{u} R G}
    (f : A ⟶ B) (n : ℕ) (c : (Rep.standardComplex R G).X n ⟶ A) :
    (cochainsIsoStandard B).inv.f n (c ≫ f) =
      (groupCohomology.cochainsMap (MonoidHom.id G) f).f n
        ((cochainsIsoStandard A).inv.f n c) := by
  apply (ModuleCat.mono_iff_injective ((cochainsIsoStandard B).hom.f n)).mp inferInstance
  rw [cochainsIsoStandard_hom_postcomp]
  have hA := ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
    (cochainsIsoStandard A)).toLinearEquiv.apply_symm_apply c
  have hB := ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
    (cochainsIsoStandard B)).toLinearEquiv.apply_symm_apply (c ≫ f)
  change (cochainsIsoStandard A).hom.f n ((cochainsIsoStandard A).inv.f n c) = c at hA
  change (cochainsIsoStandard B).hom.f n
    ((cochainsIsoStandard B).inv.f n (c ≫ f)) = c ≫ f at hB
  rw [hA, hB]

variable (H : Subgroup G) [Fintype (G ⧸ H)]

/-- Ordinary corestriction is natural before passage to cohomology. -/
theorem ordinaryCorestrictionCochainMap_naturality {A B : Rep.{u} R G}
    (f : A ⟶ B) :
    groupCohomology.cochainsMap (MonoidHom.id H) ((Rep.resFunctor H.subtype).map f) ≫
        ordinaryCorestrictionCochainMap H B =
      ordinaryCorestrictionCochainMap H A ≫
        groupCohomology.cochainsMap (MonoidHom.id G) f := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change (cochainsIsoStandard B).inv.f n
      (homTransfer H ((Rep.standardComplex R G).X n) B
        (standardCosetComparisonComponent H n ≫
          (cochainsIsoStandard (Rep.res H.subtype B)).hom.f n
            ((groupCohomology.cochainsMap (MonoidHom.id H)
              ((Rep.resFunctor H.subtype).map f)).f n c))) =
    (groupCohomology.cochainsMap (MonoidHom.id G) f).f n
      ((cochainsIsoStandard A).inv.f n
        (homTransfer H ((Rep.standardComplex R G).X n) A
          (standardCosetComparisonComponent H n ≫
            (cochainsIsoStandard (Rep.res H.subtype A)).hom.f n c)))
  rw [cochainsIsoStandard_hom_postcomp, ← Category.assoc,
    homTransfer_postcomp, cochainsIsoStandard_inv_postcomp]

/-- Naturality of the independently constructed ordinary cohomological transfer. -/
theorem ordinaryCohomologyCorestriction_naturality {A B : Rep.{u} R G}
    (f : A ⟶ B) (n : ℕ) :
    groupCohomology.map (MonoidHom.id H) ((Rep.resFunctor H.subtype).map f) n ≫
        ordinaryCohomologyCorestriction H B n =
      ordinaryCohomologyCorestriction H A n ≫
        groupCohomology.map (MonoidHom.id G) f n := by
  simpa only [HomologicalComplex.homologyMap_comp,
    ordinaryCohomologyCorestriction, groupCohomology.map] using
      congrArg (fun c => HomologicalComplex.homologyMap c n)
        (ordinaryCorestrictionCochainMap_naturality H f)

variable [Fintype G]

/-- Extend the ordinary cochain transfer to the actual Tate complex by zero below degree zero. -/
def transferCochainsToTate (A : Rep.{u} R G) :
    zeroSpliceComplex (Rep.res H.subtype A) ⟶ tateComplex A :=
  CochainComplex.ConnectData.map _ _ 0 (ordinaryCorestrictionCochainMap H A)
    (by simp [zeroSpliceConnectData])

lemma transferCochainsToTate_homology (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    HomologicalComplex.homologyMap (transferCochainsToTate H A) n =
      ((zeroSpliceConnectData (Rep.res H.subtype A)).homologyIsoPos n n rfl).hom ≫
        ordinaryCohomologyCorestriction H A n ≫
          ((TateCohomology.isoGroupCohomology n).app A).inv :=
  CochainComplex.ConnectData.homologyMap_map_of_eq_succ _ _ _ _ _ n _ rfl

lemma transferCochainsToTate_naturality {A B : Rep.{u} R G} (f : A ⟶ B) :
    transferCochainsToTate H A ≫ tateComplex.map f =
      zeroSpliceMap ((Rep.resFunctor H.subtype).map f) ≫ transferCochainsToTate H B := by
  ext i : 1
  cases i with
  | ofNat n =>
    exact (congrArg (fun m => m.f n)
      (ordinaryCorestrictionCochainMap_naturality H f)).symm
  | negSucc n =>
    change (0 : _ ⟶ _) ≫ _ = _ ≫ (0 : _ ⟶ _)
    simp

def transferCochainsToTateSequence (S : ShortComplex (Rep.{u} R G)) :
    (S.map (Rep.resFunctor H.subtype)).map zeroSpliceFunctor ⟶
      S.map (tateComplexFunctor R G) where
  τ₁ := transferCochainsToTate H S.X₁
  τ₂ := transferCochainsToTate H S.X₂
  τ₃ := transferCochainsToTate H S.X₃
  comm₁₂ := transferCochainsToTate_naturality H S.f
  comm₂₃ := transferCochainsToTate_naturality H S.g

/-- The ordinary transfer comparison commutes with the actual connecting maps. -/
lemma transferCochainsToTate_delta (S : ShortComplex (Rep.{u} R G))
    (hS : S.ShortExact) (n : ℤ) :
    (zeroSplice_shortExact (hS.map_of_exact (Rep.resFunctor H.subtype))).δ
        n (n + 1) rfl ≫
        HomologicalComplex.homologyMap (transferCochainsToTate H S.X₁) (n + 1) =
      HomologicalComplex.homologyMap (transferCochainsToTate H S.X₃) n ≫
        TateCohomology.δ hS n :=
  HomologicalComplex.HomologySequence.δ_naturality
    (transferCochainsToTateSequence H S)
    (zeroSplice_shortExact (hS.map_of_exact (Rep.resFunctor H.subtype)))
    (TateCohomology.map_tateComplexFunctor_shortExact hS) n (n + 1) rfl

end Langlands.Tate
