import Langlands.GroupScheme.SplitExistence.OppositeFactorPairs
import Langlands.GroupScheme.SplitExistence.RootDatumOf

/-! # Simple rank-one maps on Chevalley rational points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base} {D : ChevalleyData P b} {k : Type u} [Field k]

namespace ChevGroup

variable (G : D.ChevGroup k)

local notation "S" => Spec (CommRingCat.of k)
local notation "U" => Over.mk (𝟙 S)

private abbrev sectionsRing (k : Type u) [Field k] : CommRingCat.{u} :=
  Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)

private abbrev toSections (k : Type u) [Field k] : k →+* sectionsRing k :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

private def pointMatrix : rationalPoints G.H →* GL (Fin D.n) (sectionsRing k) :=
  (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) U).toMonoidHom.comp
    (rationalPoints.map G.i)

private theorem pointMatrix_injective : Function.Injective G.pointMatrix := by
  intro p q h
  exact G.mono_i.right_cancellation p q
    ((GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) U).injective h)

/-- The torus point whose character values are the corresponding powers of `a` under `j∨`. -/
def corootPt (j : J) (a : kˣ) : rationalPoints G.H :=
  G.torusPt (corootCharRing (P := P) j (Units.map (toSections k).toMonoidHom a))

/-- The torus point is evaluation of the actual coroot of the split torus in the Chevalley
group, followed by the torus inclusion. -/
theorem corootPt_eq_eval [Module.Finite ℤ X] [Module.Free ℤ X] (j : J) (a : kˣ) :
    G.corootPt j a = (Gm.affinePointsEquiv (𝟙 S)).symm a ≫
      (CommGroupScheme.groupHom ((chevDatum k P).coroot j)).hom.hom ≫ G.t.hom.hom := by
  rw [corootPt, torusPt, chevDatum_coroot, ← Category.assoc]
  congr 1
  apply (torusPointsEquiv k U).injective
  rw [MulEquiv.apply_symm_apply]
  apply MonoidHom.ext
  intro x
  let ν := cocharEquiv k P (P.coroot j)
  let χ := charOf k (Multiplicative.toAdd x)
  let z := (Gm.affinePointsEquiv (𝟙 S)).symm a
  have hz : Gm.pointsEquiv S U z = Units.map (toSections k).toMonoidHom a := by
    change Gm.pointsEquiv S U ((Gm.pointsEquiv S U).symm
      ((Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv).symm a)) =
        _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have h : ν ≫ χ = (gmEndEquiv k).symm (P.toLinearMap (Multiplicative.toAdd x) (P.coroot j)) := by
    apply (gmEndEquiv k).injective
    rw [AddEquiv.apply_symm_apply, ← latticePairing_apply, latticePairing_charOf_cocharEquiv]
  change (Units.map (toSections k).toMonoidHom a) ^
    P.toLinearMap (Multiplicative.toAdd x) (P.coroot j) = _
  rw [← hz]
  change Gm.pointsEquiv S U z ^ P.toLinearMap (Multiplicative.toAdd x) (P.coroot j) =
    torusPointsEquiv k U (z ≫ (CommGroupScheme.groupHom ν).hom.hom)
      (Multiplicative.ofAdd (Multiplicative.toAdd x))
  rw [← gmPoints_charOf, Category.assoc, ← Grp.comp_hom_hom]
  change _ = Gm.pointsEquiv S U (z ≫ (CommGroupScheme.groupHom (ν ≫ χ)).hom.hom)
  rw [h, gmEndEquiv_symm_comp, map_zpow]

theorem corootPt_mem_centralizerPoints (j : J) (a : kˣ) :
    G.corootPt j a ∈ centralizerPoints G.t :=
  G.torusPt_mem_centralizerPoints _

theorem corootPt_mul (j : J) (a c : kˣ) :
    G.corootPt j (a * c) = G.corootPt j a * G.corootPt j c := by
  let f := Units.map (toSections k).toMonoidHom
  have h : corootCharRing (P := P) j (f (a * c)) =
      corootCharRing (P := P) j (f a) * corootCharRing (P := P) j (f c) := by
    apply MonoidHom.ext
    intro x
    simp [corootCharRing, mul_zpow]
  unfold corootPt torusPt
  rw [h, map_mul, MonObj.mul_comp]

theorem corootPt_opposite (j : J) (a : kˣ) :
    G.corootPt (P.reflectionPerm j j) a = G.corootPt j a⁻¹ := by
  unfold corootPt
  congr 1
  apply MonoidHom.ext
  intro x
  simp [corootCharRing, RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply_self]

private def simpleMatrix (i : b.support) :
    SpecialLinearGroup (Fin 2) k →* GL (Fin D.n) (sectionsRing k) :=
  (D.φ i (sectionsRing k)).comp (SpecialLinearGroup.map (toSections k))

private theorem simpleMatrix_upper (i : b.support) (t : k) :
    simpleMatrix (D := D) i (sl2Upper t) = G.pointMatrix (G.rootPt i t) := by
  have h : (sl2Upper t).map (toSections k) = sl2Upper (toSections k t) := by
    apply Subtype.ext
    ext p q
    change toSections k (!![1, t; 0, 1] p q) = !![1, toSections k t; 0, 1] p q
    fin_cases p <;> fin_cases q <;> simp
  change D.φ i _ ((sl2Upper t).map (toSections k)) = _
  rw [h, D.φ_sl2Upper_ring]
  exact (G.pointsEquiv_rootPt i t).symm

private theorem simpleMatrix_lower (i : b.support) (t : k) :
    simpleMatrix (D := D) i (sl2Lower t) =
      G.pointMatrix (G.rootPt (P.reflectionPerm i i) t) := by
  have h : (sl2Lower t).map (toSections k) = sl2Lower (toSections k t) := by
    apply Subtype.ext
    ext p q
    change toSections k (!![1, 0; t, 1] p q) = !![1, 0; toSections k t, 1] p q
    fin_cases p <;> fin_cases q <;> simp
  change D.φ i _ ((sl2Lower t).map (toSections k)) = _
  rw [h, D.φ_sl2Lower_ring]
  exact (G.pointsEquiv_rootPt (P.reflectionPerm i i) t).symm

private theorem simpleMatrix_mem_range (i : b.support) (g : SpecialLinearGroup (Fin 2) k) :
    simpleMatrix (D := D) i g ∈ G.pointMatrix.range := by
  refine Matrix.SL2.transvection_induction
    (fun g => simpleMatrix (D := D) i g ∈ G.pointMatrix.range) ?_ ?_ g
  · intro p q hpq t
    fin_cases p
    · obtain rfl : q = 1 := by fin_cases q <;> tauto
      have h : SpecialLinearGroup.transvection hpq t = sl2Upper t := by
        apply Subtype.ext
        ext p q
        fin_cases p <;> fin_cases q <;> simp [SpecialLinearGroup.transvection_coe, sl2Upper]
      rw [h, G.simpleMatrix_upper]
      exact ⟨_, rfl⟩
    · obtain rfl : q = 0 := by fin_cases q <;> tauto
      have h : SpecialLinearGroup.transvection hpq t = sl2Lower t := by
        apply Subtype.ext
        ext p q
        fin_cases p <;> fin_cases q <;> simp [SpecialLinearGroup.transvection_coe, sl2Lower]
      rw [h, G.simpleMatrix_lower]
      exact ⟨_, rfl⟩
  · intro g h hg hh
    rw [map_mul]
    exact G.pointMatrix.range.mul_mem hg hh

/-- The simple Chevalley `SL₂(k)` homomorphism, with codomain the rational points of the
represented Chevalley group. -/
def simpleRankOne (i : b.support) : SpecialLinearGroup (Fin 2) k →* rationalPoints G.H :=
  (MonoidHom.ofInjective G.pointMatrix_injective).symm.toMonoidHom.comp
    ((simpleMatrix (D := D) i).codRestrict G.pointMatrix.range (G.simpleMatrix_mem_range i))

theorem pointsEquiv_simpleRankOne (i : b.support) (g : SpecialLinearGroup (Fin 2) k) :
    GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) U
      (G.simpleRankOne i g ≫ G.i.hom.hom) = D.φ i _ (g.map (toSections k)) :=
  MonoidHom.apply_ofInjective_symm G.pointMatrix_injective _

theorem simpleRankOne_upper (i : b.support) (t : k) :
    G.simpleRankOne i (sl2Upper t) = G.rootPt i t :=
  G.pointMatrix_injective ((G.pointsEquiv_simpleRankOne i _).trans (G.simpleMatrix_upper i t))

theorem simpleRankOne_lower (i : b.support) (t : k) :
    G.simpleRankOne i (sl2Lower t) = G.rootPt (P.reflectionPerm i i) t :=
  G.pointMatrix_injective ((G.pointsEquiv_simpleRankOne i _).trans (G.simpleMatrix_lower i t))

theorem simpleRankOne_diag (i : b.support) (a : kˣ) :
    G.simpleRankOne i (sl2Diag a) = G.corootPt i a := by
  apply G.pointMatrix_injective
  change GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) U
    (G.simpleRankOne i (sl2Diag a) ≫ G.i.hom.hom) =
      GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) U (G.corootPt i a ≫ G.i.hom.hom)
  rw [pointsEquiv_simpleRankOne, corootPt, pointsEquiv_torusPt]
  have h : (sl2Diag a).map (toSections k) = sl2Diag (Units.map (toSections k).toMonoidHom a) := by
    apply Subtype.ext
    ext p q
    change toSections k (!![(a : k), 0; 0, ((a⁻¹ : kˣ) : k)] p q) =
      !![toSections k (a : k), 0; 0, toSections k ((a⁻¹ : kˣ) : k)] p q
    fin_cases p <;> fin_cases q <;> simp
  rw [h, D.φ_sl2Diag_ring]

theorem simpleRankOne_weyl (i : b.support) :
    G.simpleRankOne i sl2Weyl = G.weylPoint i := by
  apply G.pointMatrix_injective
  change GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) U
    (G.simpleRankOne i sl2Weyl ≫ G.i.hom.hom) =
      GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) U (G.weylPoint i ≫ G.i.hom.hom)
  rw [pointsEquiv_simpleRankOne, pointsEquiv_weylPoint]
  congr 1
  apply Subtype.ext
  ext p q
  change toSections k ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) p q) = !![0, 1; -1, 0] p q
  fin_cases p <;> fin_cases q <;> simp

end ChevGroup

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
