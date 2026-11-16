import Langlands.GroupScheme.Reductive.CorootQuotientKernel
import Langlands.GroupScheme.Reductive.AffinePinnedModel
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Reductive.RelativeDerivedKernel
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.KernelSquareTransport

/-! # Geometric kernels of supplied coroot quotient homomorphisms -/

noncomputable section
universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeDerived

variable {I J : Type u} [Fintype I] [DecidableEq I]
  {R R' : CommRingCat.{u}}

/-- The actual coroot projection commutes with canonical base-change comparisons. -/
theorem corootProjection_baseChange_square
    (b : Spec R' ⟶ Spec R) (P : RootDatum J (I → ℤ) (I → ℤ)) :
    (GroupScheme.baseChange b).map (corootProjection R P) ≫
        (Diagonalizable.baseChangeIso b (cocenterLattice P)).hom =
      (splitTorus.baseChangeIso b I).hom ≫ corootProjection R' P := by
  apply hom_ext_points
  intro U x
  apply (Diagonalizable.characterPointsEquiv R' (cocenterLattice P) U).injective
  apply MonoidHom.ext
  intro m
  simp only [Grp.comp_hom_hom, ← Category.assoc,
    Diagonalizable.characterPointsEquiv_baseChangeIso_hom]
  change Diagonalizable.characterPointsEquiv R (cocenterLattice P)
      ((Over.map b).obj U)
      (GroupScheme.baseChangePointsEquiv b _ U
        (x ≫ ((GroupScheme.baseChange b).map (corootProjection R P)).hom.hom))
        (.ofAdd m.toAdd) =
    Diagonalizable.characterPointsEquiv R' (cocenterLattice P) U
      ((x ≫ (splitTorus.baseChangeIso b I).hom.hom.hom) ≫
        (corootProjection R' P).hom.hom) (.ofAdd m.toAdd)
  rw [GroupScheme.baseChangePointsEquiv_comp, corootProjection_points,
    corootProjection_points, splitTorus.pointsEquiv_baseChangeIso_hom]
  rfl

/-- Normalizing the source and target leaves the coordinate projection unchanged. -/
theorem corootProjection_baseChange
    (b : Spec R' ⟶ Spec R) (P : RootDatum J (I → ℤ) (I → ℤ)) :
    (splitTorus.baseChangeIso b I).inv ≫
        (GroupScheme.baseChange b).map (corootProjection R P) ≫
        (Diagonalizable.baseChangeIso b (cocenterLattice P)).hom =
      corootProjection R' P := by
  rw [corootProjection_baseChange_square]
  simp

/-- Pull back a supplied quotient and identify its target with the same lattice
on the new coefficient ring. -/
def corootQuotientBaseChangeHom
    (b : Spec R' ⟶ Spec R) (P : RootDatum J (I → ℤ) (I → ℤ))
    {G : GroupScheme (Spec R)} (q : G ⟶ (corootQuotient R P).toGrp) :
    (GroupScheme.baseChange b).obj G ⟶ (corootQuotient R' P).toGrp :=
  (GroupScheme.baseChange b).map q ≫
    (Diagonalizable.baseChangeIso b (cocenterLattice P)).hom

/-- The prescribed restriction survives normalization of both pulled-back tori. -/
theorem corootQuotientBaseChangeHom_restrict
    (b : Spec R' ⟶ Spec R) (P : RootDatum J (I → ℤ) (I → ℤ))
    {G : GroupScheme (Spec R)} (t : splitTorus (Spec R) I ⟶ G)
    (q : G ⟶ (corootQuotient R P).toGrp)
    (hq : t ≫ q = corootProjection R P) :
    ((splitTorus.baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map t) ≫
        corootQuotientBaseChangeHom b P q = corootProjection R' P := by
  have h := corootProjection_baseChange b P
  rw [← hq, Functor.map_comp] at h
  simpa only [corootQuotientBaseChangeHom, Category.assoc] using h

/-- The comparison with the full kernel of the normalized pulled-back map. -/
def corootQuotientKernelBaseChangeIso
    (b : Spec R' ⟶ Spec R) (P : RootDatum J (I → ℤ) (I → ℤ))
    {G : GroupScheme (Spec R)} (q : G ⟶ (corootQuotient R P).toGrp) :
    (GroupScheme.baseChange b).obj (kernel q) ≅
      kernel (corootQuotientBaseChangeHom b P q) :=
  kernelBaseChangeIso b q ≪≫
    kernelSquareIso ((GroupScheme.baseChange b).map q)
      (corootQuotientBaseChangeHom b P q) (Iso.refl _)
      (Diagonalizable.baseChangeIso b (cocenterLattice P)) (by
        simp [corootQuotientBaseChangeHom])

omit [Fintype I] [DecidableEq I] in
/-- The normalized full kernel over any supplied field algebra is semisimple. -/
theorem isSemisimple_corootQuotientBaseChangeKernel
    (M : AffinePinnedModel.{u}) [DecidableEq M.coordinates]
    (q : M.group ⟶ (corootQuotient (CommRingCat.of M.ring) M.rootDatum).toGrp)
    (hq : M.inclusion ≫ q = corootProjection (CommRingCat.of M.ring) M.rootDatum)
    (k : Type u) [Field k] [Algebra M.ring k] :
    IsSemisimple (kernel
      (corootQuotientBaseChangeHom (algebraBaseMap M.ring k) M.rootDatum q)) := by
  classical
  let : Smooth M.group.X.hom := M.reductive.smooth
  let : IsAffineHom
      ((GroupScheme.baseChange (algebraBaseMap M.ring k)).obj M.group).X.hom :=
    inferInstanceAs (IsAffineHom
      (CategoryTheory.Limits.pullback.snd M.group.X.hom (algebraBaseMap M.ring k)))
  have ht := splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise
    M.coordinates M.group M.inclusion M.maximal k
  let : IsClosedImmersion
      (splitTorus.baseChangeHom (K := k) M.group M.coordinates M.inclusion).hom.hom.left :=
    ht.2.1
  exact isSemisimple_kernel_of_corootProjection
    (splitTorus.baseChangeHom (K := k) M.group M.coordinates M.inclusion) M.rootDatum
    (M.reductive.isConnectedReductive_baseChange (algebraBaseMap M.ring k))
    ht (M.fibrewiseRootDatum.field k)
    (corootQuotientBaseChangeHom (algebraBaseMap M.ring k) M.rootDatum q)
    (corootQuotientBaseChangeHom_restrict
      (algebraBaseMap M.ring k) M.rootDatum M.inclusion q hq)

omit [Fintype I] [DecidableEq I] in
/-- Every actual field-valued fibre of the full supplied kernel is semisimple. -/
theorem isSemisimple_corootQuotientKernel_fieldPoint
    (M : AffinePinnedModel.{u}) [DecidableEq M.coordinates]
    (q : M.group ⟶ (corootQuotient (CommRingCat.of M.ring) M.rootDatum).toGrp)
    (hq : M.inclusion ≫ q = corootProjection (CommRingCat.of M.ring) M.rootDatum)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ M.base) :
    IsSemisimple ((GroupScheme.baseChange b).obj (kernel q)) := by
  let : Algebra M.ring k := (Spec.preimage b).hom.toAlgebra
  have hb : algebraBaseMap M.ring k = b := Spec.map_preimage b
  have h := isSemisimple_corootQuotientBaseChangeKernel M q hq k
  rw [hb] at h
  exact h.of_iso (corootQuotientKernelBaseChangeIso b M.rootDatum q)

omit [Fintype I] [DecidableEq I] in
/-- In particular every full kernel of the geometric-fibre homomorphism is
semisimple, with no smoothness or surjectivity premise on the supplied map. -/
theorem isSemisimple_corootQuotient_geometricKernel
    (M : AffinePinnedModel.{u}) [DecidableEq M.coordinates]
    (q : M.group ⟶ (corootQuotient (CommRingCat.of M.ring) M.rootDatum).toGrp)
    (hq : M.inclusion ≫ q = corootProjection (CommRingCat.of M.ring) M.rootDatum)
    (s : M.base) :
    IsSemisimple (kernel ((GroupScheme.baseChange (geometricPoint M.base s)).map q)) :=
  (isSemisimple_corootQuotientKernel_fieldPoint M q hq (geometricPoint M.base s)).of_iso
    (kernelBaseChangeIso (geometricPoint M.base s) q).symm

end Langlands.GroupScheme.RelativeDerived
