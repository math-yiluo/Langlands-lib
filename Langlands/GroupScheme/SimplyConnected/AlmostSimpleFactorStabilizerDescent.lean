import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescent
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorStabilizer
import Langlands.GroupScheme.GaloisPointTowerBaseChange
import Langlands.GroupScheme.SimplyConnected.AlgebraicExtensionReflection
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties

/-! # An actual selected factor over its finite separable stabilizer field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    (D : SimplyConnectedAlmostSimpleProduct
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
    [IsGalois k L] [IsAffineHom G.X.hom]
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom]

/-- The actual selected factor descends to its stabilizer's fixed field, with
its original inclusion recovered through the standard tower comparison. -/
def factorStabilizerDescent (i : D.Index) :
    Σ H : GroupScheme (Spec (CommRingCat.of (D.factorStabilizerField i))),
      Σ j : H ⟶ (GroupScheme.baseChange
          (algebraBaseMap k (D.factorStabilizerField i))).obj G,
        {r : (GroupScheme.baseChange
            (algebraBaseMap (D.factorStabilizerField i) L)).obj H ≅ D.factor i //
          IsAffine H.X.left ∧ IsClosedSubgroup j ∧
            (GroupScheme.baseChange (algebraBaseMap (D.factorStabilizerField i) L)).map j =
              r.hom ≫ (D.inclusion i ≫
                (GaloisPointComparison.towerBaseChangeIso k (D.factorStabilizerField i) L G).inv)} := by
  apply D.factorDescentOfFixes i
    (GaloisPointComparison.towerBaseChangeIso k (D.factorStabilizerField i) L G)
  · exact GaloisPointComparison.towerBaseChangeIso_hom_fst
      k (D.factorStabilizerField i) L G
  · intro σ
    apply (D.fixes_factorStabilizerField_iff i (σ.restrictScalars k)).mp
    intro x hx
    exact σ.commutes (⟨x, hx⟩ : D.factorStabilizerField i)

/-- Simple connectedness reflects from the recovered actual factor. -/
theorem isSimplyConnected_factorStabilizerDescent (i : D.Index) :
    IsSimplyConnected (D.factorStabilizerDescent i).1 := by
  apply IsSimplyConnected.of_algebraicExtension (K := L)
  exact (D.isSimplyConnected i).of_iso (D.factorStabilizerDescent i).2.2.1

/-- The descended factor's actual inclusion is normal on every test scheme. -/
theorem isNormal_factorStabilizerDescent (i : D.Index) :
    (SubgroupFunctor.range (D.factorStabilizerDescent i).2.1).IsNormal := by
  let d := D.factorStabilizerDescent i
  let b := algebraBaseMap (D.factorStabilizerField i) L
  let e := GaloisPointComparison.towerBaseChangeIso k (D.factorStabilizerField i) L G
  let : Surjective b := (fieldExtension_fpqc (D.factorStabilizerField i) L).1
  let : Flat b := (fieldExtension_fpqc (D.factorStabilizerField i) L).2.1
  let : QuasiCompact b := (fieldExtension_fpqc (D.factorStabilizerField i) L).2.2
  let : IsClosedImmersion d.2.1.hom.hom.left := d.2.2.2.2.1
  let : Mono d.2.1.hom.hom := Over.mono_of_mono_left _
  apply SubgroupFunctor.isNormal_range_of_baseChange b d.2.1
  rw [← SubgroupFunctor.range_baseChangeHom, d.2.2.2.2.2,
    SubgroupFunctor.range_iso_comp]
  change (SubgroupFunctor.range (D.inclusion i ≫ e.symm.hom)).IsNormal
  rw [SubgroupFunctor.range_comp_iso]
  exact (D.isNormal_range_inclusion i).comap e.hom

end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct
