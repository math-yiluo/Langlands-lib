/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyFilteredColimit
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison

/-!
# The `n`-torsion subsheaves of an étale sheaf and its cohomology

For a sheaf `F` of abelian groups on the small étale site of a scheme and a positive integer
`n`, the `n`-torsion subsheaf is `F[n] = ker (n : F ⟶ F)` (`AlgebraicGeometry.Scheme.torsionBy`).
A torsion sheaf is the filtered colimit of its subsheaves `F[n]`
(`AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf`), and on a quasi-compact quasi-separated
scheme étale cohomology commutes with this colimit. Hence statements about the cohomology of
torsion sheaves reduce to sheaves killed by a positive integer.

## Main definitions

- `AlgebraicGeometry.Scheme.torsionBy`: the `n`-torsion subsheaf `F[n]`.

## Main statements

- `AlgebraicGeometry.Scheme.subsingleton_sheafH_of_forall_torsionBy`: `Hᵠ(X, F) = 0` for a
  torsion sheaf `F` on a qcqs scheme as soon as `Hᵠ(X, F[n]) = 0` for every `n`.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_of_forall_torsionBy`: the pullback
  `Hᵠ(X, F) ⟶ Hᵠ(Y, u^* F)` along a morphism of qcqs schemes is bijective for a torsion
  sheaf `F` as soon as it is bijective for every `F[n]`.

## References

- Stacks Project, Lemma 59.51.7 (cohomology and filtered colimits),
  <https://stacks.math.columbia.edu/tag/03Q6>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-- The **`n`-torsion subsheaf** `F[n] = ker (n : F ⟶ F)` of a sheaf `F` of abelian groups on the
small étale site of `T`, for a positive integer `n`. -/
noncomputable abbrev torsionBy {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ+) :
    Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel ((n : ℕ) • 𝟙 F)

/-- The `n`-torsion subsheaf `F[n]` is killed by `n`. -/
theorem torsionBy_nsmul_id {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ+) :
    (n : ℕ) • 𝟙 (torsionBy F n) = 0 := by
  rw [← cancel_mono (kernel.ι ((n : ℕ) • 𝟙 F)), zero_comp, Preadditive.nsmul_comp,
    Category.id_comp, ← Category.comp_id (kernel.ι _), ← Preadditive.comp_nsmul,
    kernel.condition]

private theorem isFiltered_dvdOrder : IsFiltered PNat.DvdOrder := by
  have : Nonempty PNat.DvdOrder := ⟨⟨1, Nat.one_pos⟩⟩
  have : IsDirectedOrder PNat.DvdOrder := ⟨fun n m ↦
    ⟨⟨n.val * m.val, Nat.mul_pos n.val_pos m.val_pos⟩,
      dvd_mul_right n.val m.val, dvd_mul_left m.val n.val⟩⟩
  infer_instance

/-- The diagram `n ↦ F[n]` over the positive integers ordered by divisibility. -/
private noncomputable def torsionDiagram {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    PNat.DvdOrder ⥤ Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} where
  obj n := kernel (n.val • 𝟙 F)
  map {n m} hnm := kernel.lift (m.val • 𝟙 F) (kernel.ι (n.val • 𝟙 F))
    (torsionKernelTransition_condition F n m hnm.down.down)
  map_id n := torsionKernelTransition_id F n
  map_comp hnm hmk :=
    (torsionKernelTransition_comp F _ _ _ hnm.down.down hmk.down.down).symm

/-- The cocone of the kernel inclusions `F[n] ⟶ F`. -/
private noncomputable def torsionCocone {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) : Cocone (torsionDiagram F) where
  pt := F
  ι := { app n := kernel.ι (n.val • 𝟙 F)
         naturality := by intro n m hnm; simp [torsionDiagram] }

/-- A torsion sheaf is the colimit of its `n`-torsion subsheaves. -/
private noncomputable def isColimitTorsionCocone {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : IsTorsionAbelianSheaf F) :
    IsColimit (torsionCocone F) :=
  have : IsIso ((colimit.isColimit (torsionDiagram F)).desc (torsionCocone F)) := hF
  (colimit.isColimit _).ofPointIso

/-- On a qcqs scheme, `Hᵠ` preserves colimits of diagrams indexed by `PNat.DvdOrder`. -/
private noncomputable def isColimitMapCoconeFunctorH (Z : Scheme.{u}) [CompactSpace Z]
    [QuasiSeparatedSpace Z] (q : ℕ)
    {K : PNat.DvdOrder ⥤ Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {t : Cocone K} (ht : IsColimit t) :
    IsColimit ((Sheaf.functorH Z.smallEtaleTopology q).mapCocone t) :=
  have := isFiltered_dvdOrder
  let R := DerivedCategory.singleFunctor
    (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} Z (q : ℤ)
  let e : AsSmall.{u} PNat.DvdOrder ≌ PNat.DvdOrder := (AsSmall.equiv).symm
  have : IsFiltered (AsSmall.{u} PNat.DvdOrder) := IsFiltered.of_equivalence e.symm
  have hR' : IsColimit (R.mapCocone (t.whisker e.functor)) :=
    (etaleCohomology_isColimit_of_isFiltered Z (ht.whiskerEquivalence e) q).some
  IsColimit.mapCoconeEquiv (nonempty_sheafH_extDerivedIso Z q).some.symm
    (IsColimit.ofWhiskerEquivalence e hR')

/-- **Vanishing of the cohomology of a torsion sheaf from its `n`-torsion subsheaves.** Let `X`
be a quasi-compact quasi-separated scheme and `F` a torsion abelian sheaf on `X_ét`. If
`Hᵠ(X, F[n]) = 0` for every positive integer `n`, then `Hᵠ(X, F) = 0`. -/
theorem subsingleton_sheafH_of_forall_torsionBy {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionAbelianSheaf F) (q : ℕ)
    (h : ∀ n : ℕ+, Subsingleton (Sheaf.H (torsionBy F n) q)) :
    Subsingleton (Sheaf.H F q) := by
  have hc := isColimitMapCoconeFunctorH X q (isColimitTorsionCocone F hF)
  have hz : IsZero ((Sheaf.functorH X.smallEtaleTopology q).obj F) := by
    rw [IsZero.iff_id_eq_zero]
    refine hc.hom_ext fun n ↦ ?_
    have : Subsingleton ((torsionDiagram F ⋙ Sheaf.functorH X.smallEtaleTopology q).obj n) :=
      h n.toPNat
    exact (AddCommGrpCat.isZero_of_subsingleton _).eq_of_src _ _
  exact AddCommGrpCat.isZero_iff_subsingleton.mp hz

end Scheme

namespace Etale

/-- **Bijectivity of pullback on the cohomology of a torsion sheaf from its `n`-torsion
subsheaves.** Let `u : Y ⟶ X` be a morphism of quasi-compact quasi-separated schemes and `F` a
torsion abelian sheaf on `X_ét`. If the pullback `Hᵠ(X, F[n]) ⟶ Hᵠ(Y, u^* F[n])` is bijective
for every positive integer `n`, then so is `Hᵠ(X, F) ⟶ Hᵠ(Y, u^* F)`. -/
theorem bijective_cohomologyMap_of_forall_torsionBy {X Y : Scheme.{u}} (u : Y ⟶ X)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Scheme.IsTorsionAbelianSheaf F) (q : ℕ)
    (h : ∀ n : ℕ+, Function.Bijective (cohomologyMap u (Scheme.torsionBy F n) q)) :
    Function.Bijective (cohomologyMap u F q) := by
  let D := Scheme.torsionDiagram F
  let c := Scheme.torsionCocone F
  have hc : IsColimit c := Scheme.isColimitTorsionCocone F hF
  let L := Sheaf.functorH X.smallEtaleTopology q
  let L' := (u)^*[AddCommGrpCat.{u + 1}] ⋙ Sheaf.functorH Y.smallEtaleTopology q
  have : PreservesColimit D L :=
    preservesColimit_of_preserves_colimit_cocone hc (Scheme.isColimitMapCoconeFunctorH X q hc)
  have hc' : IsColimit (((u)^*[AddCommGrpCat.{u + 1}]).mapCocone c) :=
    isColimitOfPreserves _ hc
  have : PreservesColimit D L' :=
    preservesColimit_of_preserves_colimit_cocone hc (Scheme.isColimitMapCoconeFunctorH Y q hc')
  let α : L ⟶ L' :=
    { app G := AddCommGrpCat.ofHom (cohomologyMap u G q)
      naturality G G' φ := by
        ext x
        exact cohomologyMap_map u q φ x }
  have : ∀ n, IsIso ((Functor.whiskerLeft D α).app n) := fun n ↦
    (ConcreteCategory.isIso_iff_bijective _).2 (h n.toPNat)
  have : IsIso (Functor.whiskerLeft D α) := NatIso.isIso_of_isIso_app _
  have : IsIso (α.app c.pt) := isIso_app_coconePt_of_preservesColimit D α c hc
  exact ConcreteCategory.bijective_of_isIso (α.app c.pt)

end Etale

end AlgebraicGeometry
