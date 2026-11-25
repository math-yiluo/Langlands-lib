/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyFilteredColimit
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Passage from positive-integer annihilated sheaves to torsion sheaves.
Source: Stacks Project, Tag 0A4B, proof, filtered-colimit reduction, transposed to
global cohomology using Tag 03Q5 (the constant-scheme case of Theorem 09YQ).
See https://stacks.math.columbia.edu/tag/0A4B and
https://stacks.math.columbia.edu/tag/03Q5.
(blueprint: lem-weil-pbc-pullback-iso-torsion-colimit)

Proof: Index the kernels F[n] of multiplication by positive n by divisibility.
This is a nonempty filtered poset: 1 is an object and nm bounds n and m. The
kernel equation and cancellation of its inclusion show n times its identity is
zero. The torsion hypothesis says the cocone of these inclusions with vertex F
is a colimit cocone. Inverse image preserves it, since it is a left adjoint.
Cohomology on each qcqs scheme preserves these filtered colimit cocones (Tag
03Q5); the natural Ext-to-derived comparison gives the same fact for Sheaf.H.
Naturality of cohomologyMap makes the stagewise pullback maps a natural
transformation between the cohomology diagrams. The bounded-torsion hypothesis
makes every component bijective. Their inverses also commute with transitions,
by composing the naturality square with the inverse maps. Thus the induced
map of colimits is invertible. Naturality with the kernel inclusions identifies
that map with cohomologyMap u F q, so the latter is bijective for every q.
This also covers F = 0 and q = 0. -/
theorem pullback_cohomology_bijective_of_torsion_colimit
    {X Y : Scheme.{u}} (u : Y ⟶ X)
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (hbounded : ∀ (n : ℕ), 0 < n →
      ∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
        n • 𝟙 G = 0 → ∀ (q : ℕ),
          Function.Bijective (cohomologyMap u G q))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Scheme.IsTorsionAbelianSheaf F) :
    ∀ (q : ℕ), Function.Bijective (cohomologyMap u F q) := by
  classical
  have : Nonempty PNat.DvdOrder := ⟨⟨1, Nat.one_pos⟩⟩
  have : IsDirectedOrder PNat.DvdOrder := ⟨fun n m ↦
    ⟨⟨n.val * m.val, Nat.mul_pos n.val_pos m.val_pos⟩,
      dvd_mul_right n.val m.val, dvd_mul_left m.val n.val⟩⟩
  have : IsFiltered PNat.DvdOrder := inferInstance
  let D : PNat.DvdOrder ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    { obj := fun n ↦ kernel (n.val • 𝟙 F)
      map := fun {n m} hnm ↦ kernel.lift (m.val • 𝟙 F) (kernel.ι (n.val • 𝟙 F))
        (Scheme.torsionKernelTransition_condition F n m hnm.down.down)
      map_id := fun n ↦ Scheme.torsionKernelTransition_id F n
      map_comp := fun hnm hmk ↦
        (Scheme.torsionKernelTransition_comp F _ _ _ hnm.down.down hmk.down.down).symm }
  let c : Cocone D :=
    { pt := F
      ι := { app := fun n ↦ kernel.ι (n.val • 𝟙 F)
             naturality := by intro n m hnm; simp [D] } }
  have : IsIso (colimit.desc D c) := hF
  have : IsIso ((colimit.isColimit D).desc c) := by
    change IsIso (colimit.desc D c)
    infer_instance
  have hc : IsColimit c := (colimit.isColimit D).ofPointIso
  intro q
  let L := Sheaf.functorH X.smallEtaleTopology q
  let L' := (u)^*[AddCommGrpCat.{u + 1}] ⋙ Sheaf.functorH Y.smallEtaleTopology q
  have hH (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z]
      {K : PNat.DvdOrder ⥤ Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}}
      {t : Cocone K} (ht : IsColimit t) :
      IsColimit ((Sheaf.functorH Z.smallEtaleTopology q).mapCocone t) := by
    let R := DerivedCategory.singleFunctor
      (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} Z (q : ℤ)
    let e : AsSmall.{u} PNat.DvdOrder ≌ PNat.DvdOrder :=
      (AsSmall.equiv).symm
    have : IsFiltered (AsSmall.{u} PNat.DvdOrder) :=
      IsFiltered.of_equivalence e.symm
    have hR' : IsColimit (R.mapCocone (t.whisker e.functor)) :=
      (Scheme.etaleCohomology_isColimit_of_isFiltered Z (ht.whiskerEquivalence e) q).some
    have hR : IsColimit (R.mapCocone t) :=
      IsColimit.ofWhiskerEquivalence e hR'
    exact IsColimit.mapCoconeEquiv (Scheme.nonempty_sheafH_extDerivedIso Z q).some.symm hR
  have : PreservesColimit D L := preservesColimit_of_preserves_colimit_cocone hc (hH X hc)
  have hc' : IsColimit (((u)^*[AddCommGrpCat.{u + 1}]).mapCocone c) :=
    isColimitOfPreserves _ hc
  have : PreservesColimit D L' :=
    preservesColimit_of_preserves_colimit_cocone hc (hH Y hc')
  let α : L ⟶ L' :=
    { app := fun G ↦ AddCommGrpCat.ofHom (cohomologyMap u G q)
      naturality := by
        intro G G' φ
        ext x
        exact cohomologyMap_map u q φ x }
  have : ∀ n, IsIso ((Functor.whiskerLeft D α).app n) := by
    intro n
    apply (ConcreteCategory.isIso_iff_bijective _).2
    apply hbounded n.val n.val_pos (D.obj n) ?_ q
    change n.val • 𝟙 (kernel (n.val • 𝟙 F)) = 0
    rw [← cancel_mono (kernel.ι (n.val • 𝟙 F)), zero_comp, Preadditive.nsmul_comp,
      Category.id_comp, ← Category.comp_id (kernel.ι _), ← Preadditive.comp_nsmul,
      kernel.condition]
  have : IsIso (Functor.whiskerLeft D α) := NatIso.isIso_of_isIso_app _
  have : IsIso (α.app c.pt) := isIso_app_coconePt_of_preservesColimit D α c hc
  exact ConcreteCategory.bijective_of_isIso (α.app c.pt)

end AlgebraicGeometry.Etale
