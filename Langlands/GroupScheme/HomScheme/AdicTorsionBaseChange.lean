import Langlands.GroupScheme.HomScheme.AdicDiagonalizableSeparation
import Langlands.GroupScheme.HomScheme.AdicSystemBaseChange
import Langlands.GroupScheme.HomScheme.AdicTorsionRestriction

/-! # Scalar extension of algebraized torsion restrictions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.AdicAffinePoints

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme

private theorem flatten_comp {S T : Scheme.{u}} (b : T ⟶ S) (V : Over T)
    {K H G : GroupScheme S}
    (a : RelativeHom ((baseChange b).obj K) ((baseChange b).obj H) V)
    (f : RelativeHom ((baseChange b).obj H) ((baseChange b).obj G) V) :
    flatten b V (a ≫ f) = flatten b V a ≫ flatten b V f := by
  simp only [flatten, Category.assoc, Iso.hom_inv_id_assoc]

namespace Adic.System

variable {A B : Type u} [CommRing A] [CommRing B] {I : Ideal A}
variable {K H G : GroupScheme (Spec (CommRingCat.of A))}

/-- Scalar extension of a formal Hom system commutes with precomposition. -/
theorem pull_precompose (φ : A →+* B) (s : System I H G) (a : K ⟶ H) :
    (s.precompose a).pull φ = (s.pull φ).precompose
      ((baseChange (Spec.map (CommRingCat.ofHom φ))).map a) := by
  apply System.ext
  intro n
  let b := Spec.map (CommRingCat.ofHom φ)
  let V := Over.mk (quotientMap (I.map φ) n)
  let c := quotientOver φ I n
  apply (flattenEquiv b V).injective
  change flatten b V (((s.precompose a).pull φ).hom n) =
    flatten b V ((baseChange V.hom).map ((baseChange b).map a) ≫ (s.pull φ).hom n)
  rw [flatten_pull_hom, flatten_comp, flatten_baseChange, flatten_pull_hom]
  have ha := Descent.pullHom_comp c.left c.w c.w c.w
    ((baseChange (quotientMap I n)).map a) (s.hom n)
  change evaluate c ((baseChange (quotientMap I n)).map a ≫ s.hom n) =
    evaluate c ((baseChange (quotientMap I n)).map a) ≫ evaluate c (s.hom n) at ha
  exact ha.trans (congrArg (· ≫ evaluate c (s.hom n))
    ((evaluate_baseChange c a).trans (evaluate_baseChange
      (Over.homMk V.hom rfl : (Over.map b).obj V ⟶ Over.mk b) a).symm))

variable [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]

/-- An algebraization of a pulled system agrees on finite restrictions
whenever equality over the changed base is detected by the quotient systems. -/
theorem baseChange_finiteRestriction [IsFinite K.X.hom]
    (s : System (maximalIdeal A) H G) (a : K ⟶ H) (φ : A →+* B)
    (f : (baseChange (Spec.map (CommRingCat.ofHom φ))).obj H ⟶
      (baseChange (Spec.map (CommRingCat.ofHom φ))).obj G)
    (hf : System.restrict ((maximalIdeal A).map φ) _ _ f = s.pull φ)
    (hi : Function.Injective (System.restrict ((maximalIdeal A).map φ)
      ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj K)
      ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj G))) :
    (baseChange (Spec.map (CommRingCat.ofHom φ))).map (s.finiteRestriction a) =
      (baseChange (Spec.map (CommRingCat.ofHom φ))).map a ≫ f := by
  have h : System.restrict (maximalIdeal A) K G (s.finiteRestriction a) = s.precompose a :=
    System.ext (s.finiteRestriction_reduce a)
  apply hi
  rw [← pull_restrict, h, pull_precompose, ← hf]
  apply System.ext
  intro n
  exact (Functor.map_comp _ _ _).symm

end Adic.System

namespace Adic

open Diagonalizable FiniteCharacterSeparation

variable {A B : Type u} [CommRing A] [CommRing B]
/-- The quotient character lattice for positive split-torus torsion is finite. -/
theorem isFinite_splitTorsion (L : Type u) [Fintype L] (n : ℕ) (hn : 0 < n) :
    IsFinite (groupScheme (CommRingCat.of A) ((L → ℤ) ⧸ TorsionDensity.multiples (L → ℤ) n)).X.hom := by
  let : AddGroup.FG (L → ℤ) := Module.Finite.iff_addGroup_fg.mp inferInstance
  let : Finite ((L → ℤ) ⧸ TorsionDensity.multiples (L → ℤ) n) := finite_quotient hn.ne'
  infer_instance

variable [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]
variable {G : GroupScheme (Spec (CommRingCat.of A))}

/-- The actual restriction of a formal split-torus homomorphism to positive torsion. -/
def System.splitTorsionHom (L : Type u) [Fintype L]
    (s : System (maximalIdeal A) (groupScheme (CommRingCat.of A) (L → ℤ)).toGrp G)
    (n : ℕ) (hn : 0 < n) :
    (groupScheme (CommRingCat.of A) ((L → ℤ) ⧸ TorsionDensity.multiples (L → ℤ) n)).toGrp ⟶ G :=
  letI : IsFinite (groupScheme (CommRingCat.of A) ((L → ℤ) ⧸ TorsionDensity.multiples (L → ℤ) n)).X.hom :=
    isFinite_splitTorsion L n hn
  s.finiteRestriction (splitTorsionRestriction (CommRingCat.of A) L n)

/-- The actual torsion restriction reduces to the prescribed map at every level. -/
theorem System.splitTorsionHom_reduce (L : Type u) [Fintype L]
    (s : System (maximalIdeal A) (groupScheme (CommRingCat.of A) (L → ℤ)).toGrp G)
    (n : ℕ) (hn : 0 < n) (d : ℕ) :
    (baseChange (quotientMap (maximalIdeal A) d)).map (s.splitTorsionHom L n hn) =
      (baseChange (quotientMap (maximalIdeal A) d)).map
        (splitTorsionRestriction (CommRingCat.of A) L n) ≫ s.hom d := by
  let := isFinite_splitTorsion (A := A) L n hn
  exact s.finiteRestriction_reduce _ d

/-- An algebraization over an adically separated ring realizes the pulled-back
algebraized torsion restrictions of the original system. -/
theorem System.baseChange_splitTorsionHom [IsSeparated G.X.hom] (L : Type u) [Fintype L]
    (s : System (maximalIdeal A) (groupScheme (CommRingCat.of A) (L → ℤ)).toGrp G)
    (φ : A →+* B) [IsHausdorff ((maximalIdeal A).map φ) B]
    (f : (baseChange (Spec.map (CommRingCat.ofHom φ))).obj
      (groupScheme (CommRingCat.of A) (L → ℤ)).toGrp ⟶
      (baseChange (Spec.map (CommRingCat.ofHom φ))).obj G)
    (hf : System.restrict ((maximalIdeal A).map φ) _ _ f = s.pull φ)
    (n : ℕ) (hn : 0 < n) :
    (baseChange (Spec.map (CommRingCat.ofHom φ))).map (s.splitTorsionHom L n hn) =
      (baseChange (Spec.map (CommRingCat.ofHom φ))).map
        (splitTorsionRestriction (CommRingCat.of A) L n) ≫ f := by
  let := isFinite_splitTorsion (A := A) L n hn
  apply s.baseChange_finiteRestriction _ φ f hf
  let b := Spec.map (CommRingCat.ofHom φ)
  let : IsSeparated ((baseChange b).obj G).X.hom := by
    change IsSeparated (pullback.snd G.X.hom b)
    infer_instance
  exact diagonalizableAdicInjectivity_of_iso _ (baseChangeIso b ((L → ℤ) ⧸ TorsionDensity.multiples (L → ℤ) n)).symm

end Adic

end Langlands.GroupScheme.HomScheme
