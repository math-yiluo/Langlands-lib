import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeFinite
import Langlands.GroupScheme.Torus.DiagonalizableTorsion
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeNormalizerSmooth
import Langlands.GroupScheme.Reductive.Basic
import Langlands.AbelianScheme.TorsionFunctor
import Langlands.AlgebraicGeometry.Morphisms.FppfLocalAtTarget
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricRank
import Mathlib.Algebra.MonoidAlgebra.Module

/-! # Finite flat torsion of relative multiplicative-type groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- Isomorphic commutative group schemes have isomorphic integer torsion. -/
def torsionMapIso {S : Scheme.{u}} {G H : GroupScheme S}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (e : G ≅ H) (n : ℤ) :
    torsion G n ≅ torsion H n where
  hom := torsionMap e.hom n
  inv := torsionMap e.inv n
  hom_inv_id := by rw [← torsionMap_comp, e.hom_inv_id, torsionMap_id]
  inv_hom_id := by rw [← torsionMap_comp, e.inv_hom_id, torsionMap_id]

namespace Diagonalizable

/-- Every diagonalizable group is flat over its coefficient ring. -/
theorem flat_groupScheme (R : CommRingCat.{u}) (M : Type u) [AddCommGroup M] :
    Flat (groupScheme R M).X.hom := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R M))))
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

end Diagonalizable

namespace RelativeMultiplicativeType

variable (S : Scheme.{u}) (M : Type u) [AddCommGroup M]

/-- The relative diagonalizable model retains the full quotient character group
in its scheme-theoretic torsion. -/
def diagonalizableTorsionIso (n : ℕ) :
    torsion (diagonalizable S M) (n : ℤ) ≅
      diagonalizable S (Diagonalizable.torsionCharacters M n) :=
  (torsionBaseChangeIso (Gm.toSpecZ S)
    (Diagonalizable.groupScheme (CommRingCat.of (ULift.{u} ℤ)) M).toGrp (n : ℤ)).symm ≪≫
      (GroupScheme.baseChange (Gm.toSpecZ S)).mapIso
        (Diagonalizable.torsionIso (CommRingCat.of (ULift.{u} ℤ)) M n)

variable {S} {H : GroupScheme S} [IsCommMonObj H.X]

/-- Positive torsion of a diagonalizable group is finite, flat and locally of
finite presentation, including in the residue characteristics dividing `n`. -/
theorem IsDiagonalizable.torsion_geometry (hH : IsDiagonalizable H)
    (n : ℕ) (hn : 0 < n) :
    IsFinite (torsion H (n : ℤ)).X.hom ∧
      Flat (torsion H (n : ℤ)).X.hom ∧
        LocallyOfFinitePresentation (torsion H (n : ℤ)).X.hom := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  obtain ⟨M, hM, hfg, ⟨e⟩⟩ := hH
  let E := torsionMapIso e (n : ℤ) ≪≫ diagonalizableTorsionIso S M n
  have : Finite (Diagonalizable.torsionCharacters M n) :=
    FiniteCharacterSeparation.finite_quotient hn.ne'
  have := isFinite_diagonalizable S (Diagonalizable.torsionCharacters M n)
  have := flat_diagonalizable S (Diagonalizable.torsionCharacters M n)
  have := locallyOfFinitePresentation_diagonalizable S (Diagonalizable.torsionCharacters M n)
  rw [← Over.w E.hom.hom.hom]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Positive torsion of a relative group of multiplicative type is finite flat
and locally of finite presentation over the entire base. -/
theorem IsMultiplicativeType.torsion_geometry (hH : IsMultiplicativeType H)
    (n : ℕ) (hn : 0 < n) :
    IsFinite (torsion H (n : ℤ)).X.hom ∧
      Flat (torsion H (n : ℤ)).X.hom ∧
        LocallyOfFinitePresentation (torsion H (n : ℤ)).X.hom := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  obtain ⟨𝒰, h𝒰⟩ := hH
  let P : MorphismProperty Scheme.{u} := @IsFinite ⊓ (@Flat ⊓ @LocallyOfFinitePresentation)
  have : P.IsLocalAtTarget Scheme.fppfPrecoverage :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage P
  let 𝒱 : Scheme.Cover Scheme.fppfPrecoverage S := 𝒰
  change P (torsion H (n : ℤ)).X.hom
  apply MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒱
  intro i
  let E := torsionBaseChangeIso (𝒰.f i) H (n : ℤ)
  change P ((GroupScheme.baseChange (𝒰.f i)).obj (torsion H (n : ℤ))).X.hom
  rw [← Over.w E.hom.hom.hom, P.cancel_left_of_respectsIso]
  exact (h𝒰 i).torsion_geometry n hn

end RelativeMultiplicativeType

/-- Whenever the actual torsion scheme is finite flat, its geometric coordinate
dimension is its native rank at the base point. -/
theorem geometricTorsionFinrank_eq {S : Scheme.{u}} (H : GroupScheme S)
    [IsCommMonObj H.X] (n : ℤ)
    [IsFinite (torsion H n).X.hom] [Flat (torsion H n).X.hom] (s : S) :
    let := Langlands.AlgebraicGeometry.FiniteEtale.coordinateAlgebra
      (torsion (geometricFiber H s) n).X.hom
    Module.finrank (AlgebraicClosure (S.residueField s))
      Γ((torsion (geometricFiber H s) n).X.left, ⊤) =
        (torsion H n).X.hom.finrank s := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  let b := geometricPoint S s
  let E := torsionBaseChangeIso b H n
  have : IsFinite (torsion (geometricFiber H s) n).X.hom := by
    rw [← Over.w E.inv.hom.hom]
    change IsFinite (E.inv.hom.hom.left ≫ pullback.snd _ _)
    infer_instance
  have : Flat (torsion (geometricFiber H s) n).X.hom := by
    rw [← Over.w E.inv.hom.hom]
    change Flat (E.inv.hom.hom.left ≫ pullback.snd _ _)
    infer_instance
  let x := IsLocalRing.closedPoint (AlgebraicClosure (S.residueField s))
  let := Langlands.AlgebraicGeometry.FiniteEtale.coordinateAlgebra
    (torsion (geometricFiber H s) n).X.hom
  calc
    _ = (torsion (geometricFiber H s) n).X.hom.finrank x :=
      (Langlands.AlgebraicGeometry.FiniteEtale.homFinrank_eq_coordinateFinrank
        (torsion (geometricFiber H s) n).X.hom x).symm
    _ = ((GroupScheme.baseChange b).obj (torsion H n)).X.hom.finrank x := by
      have hE := Scheme.Hom.finrank_comp_left_of_isIso E.hom.hom.hom.left
        (torsion (geometricFiber H s) n).X.hom
      rw [Over.w E.hom.hom.hom] at hE
      exact (congrFun hE x).symm
    _ = (torsion H n).X.hom.finrank (b x) :=
      Scheme.Hom.finrank_pullback_snd (torsion H n).X.hom b x
    _ = (torsion H n).X.hom.finrank s := by
      congr 1
      change S.fromSpecResidueField s _ = s
      exact Scheme.fromSpecResidueField_apply _ _

/-- The orders of all positive geometric torsion levels of a relative group of
multiplicative type are locally constant in exactly the fibral criterion's
coordinate-dimension sense. -/
theorem RelativeMultiplicativeType.IsMultiplicativeType.isLocallyConstant_torsionFinrank
    {S : Scheme.{u}} {H : GroupScheme S} [IsCommMonObj H.X]
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H) (n : ℕ) (hn : 0 < n) :
    IsLocallyConstant fun s : S =>
      let := Langlands.AlgebraicGeometry.FiniteEtale.coordinateAlgebra
        (torsion (geometricFiber H s) (n : ℤ)).X.hom
      Module.finrank (AlgebraicClosure (S.residueField s))
        Γ((torsion (geometricFiber H s) (n : ℤ)).X.left, ⊤) := by
  obtain ⟨hf, hflat, hfp⟩ := hH.torsion_geometry n hn
  let := hf
  let := hflat
  let := hfp
  have hEq : (fun s : S =>
      let := Langlands.AlgebraicGeometry.FiniteEtale.coordinateAlgebra
        (torsion (geometricFiber H s) (n : ℤ)).X.hom
      Module.finrank (AlgebraicClosure (S.residueField s))
        Γ((torsion (geometricFiber H s) (n : ℤ)).X.left, ⊤)) =
      (torsion H (n : ℤ)).X.hom.finrank :=
    funext (geometricTorsionFinrank_eq H (n : ℤ))
  rw [hEq]
  exact (torsion H (n : ℤ)).X.hom.isLocallyConstant_finrank

end Langlands.GroupScheme
