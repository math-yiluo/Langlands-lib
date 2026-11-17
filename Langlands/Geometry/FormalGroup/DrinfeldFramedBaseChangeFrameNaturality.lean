import Langlands.Geometry.FormalGroup.DrinfeldFramedBaseChangeCanonicalSquare

/-! # Residue-identity naturality of the fixed-frame base-change comparison -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A B : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
  (R := κ) π}
variable {X Y : DrinfeldFramedAtlas Φ A}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The residue-forced identity frame comparison has complete identity coordinate series. -/
theorem globalFrameIso_hom_coordinates (e : X.residueMap = Y.residueMap) :
    (globalFrameIso e).hom.val.toHom.toCoordinateMap = CoordinateMap.id := by
  cases X
  cases Y
  cases e
  rfl

/-- The same actual identity-frame map retains its full series on every coefficient test. -/
theorem globalFrameIso_map_hom_coordinates (e : X.residueMap = Y.residueMap)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj) :
    ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C)).hom.val.toHom.toCoordinateMap =
        CoordinateMap.id := by
  change (globalFrameIso e).hom.val.toHom.toCoordinateMap.map
    (algebraMap ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C) = _
  rw [globalFrameIso_hom_coordinates e]
  exact CoordinateMap.map_id _

/-- Equal stored residue maps remain equal after the actual quotient scalar map. -/
theorem baseChange_residue_eq (e : X.residueMap = Y.residueMap) (f : A ⟶ B) :
    (X.baseChange f).residueMap = (Y.baseChange f).residueMap :=
  congrArg (fun ψ => (Nilp.reducedScalarMap 𝒪[K] f).comp ψ) e

/-- The residue-forced identity frame map on the new test algebra. -/
def baseChangeNewResidueFrameTestIso (e : X.residueMap = Y.residueMap) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj) :=
  (globalFrameIso (baseChange_residue_eq e f)).map (IsScalarTower.toAlgHom 𝒪[K]
    ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj C)

/-- Transport of the same original identity frame map to an equal test scalar structure retains identity series. -/
theorem globalFrameIso_map_reAlgebra_hom_coordinates (e : X.residueMap = Y.residueMap)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (β : Algebra 𝒪[K] C) (d : coefficientAlgebra (O := 𝒪[K]) C = β) :
    (letI := β;
      ((letI := coefficientAlgebra (O := 𝒪[K]) C;
        (globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K]
          ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C)).reAlgebra β d).hom.val.toHom.toCoordinateMap) = CoordinateMap.id := by
  cases d
  exact globalFrameIso_map_hom_coordinates e C

/-- The original residue-forced identity frame map on the restricted test, with the actual new scalars. -/
def baseChangeResidueFrameTestIso (e : X.residueMap = Y.residueMap) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj) :=
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let T := restrictCoefficientAlgebra φ C
  let γ : Algebra 𝒪[K] C := coefficientAlgebra (O := 𝒪[K]) C
  let eC := BasicAtlas.coefficientAlgebra_comp_transport (BasicAtlas.coefficientTest φ) C _
    (BasicAtlas.coefficientAlgebraAlong_eq φ)
  (letI := coefficientAlgebra (O := 𝒪[K]) T;
    ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj T)).reAlgebra γ eC)

set_option backward.isDefEq.respectTransparency false in
/-- The transported original identity-frame map has complete identity series. -/
theorem baseChangeResidueFrameTestIso_hom_coordinates (e : X.residueMap = Y.residueMap)
    (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj) :
    (letI := coefficientAlgebra (O := 𝒪[K]) C;
      (ModuleLaw.OrderAction.Iso.hom (O := 𝒪[K]) (R := C)
        (baseChangeResidueFrameTestIso e f C)).val.toHom.toCoordinateMap) = CoordinateMap.id := by
  exact globalFrameIso_map_reAlgebra_hom_coordinates e
    (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C) _
    (BasicAtlas.coefficientAlgebra_comp_transport
      (BasicAtlas.coefficientTest (Nilp.reducedScalarMap 𝒪[K] f)) C _
      (BasicAtlas.coefficientAlgebraAlong_eq (Nilp.reducedScalarMap 𝒪[K] f)))

set_option backward.isDefEq.respectTransparency false in
/-- The direct fixed-frame test comparison commutes with the residue-forced actual identity maps. -/
theorem baseChangeGlobalFrameTestIso_residue_natural (e : X.residueMap = Y.residueMap)
    (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj) :
    (letI := coefficientAlgebra (O := 𝒪[K]) C;
      ModuleLaw.OrderAction.Iso.trans (O := 𝒪[K]) (R := C)
          (baseChangeNewResidueFrameTestIso e f C) (Y.baseChangeGlobalFrameTestIso f C) =
        ModuleLaw.OrderAction.Iso.trans (O := 𝒪[K]) (R := C)
          (X.baseChangeGlobalFrameTestIso f C) (baseChangeResidueFrameTestIso e f C)) := by
  let _ := coefficientAlgebra (O := 𝒪[K]) C
  let n := baseChangeNewResidueFrameTestIso e f C
  let y := Y.baseChangeGlobalFrameTestIso f C
  let x := X.baseChangeGlobalFrameTestIso f C
  let o := baseChangeResidueFrameTestIso e f C
  have hn : n.hom.val.toHom.toCoordinateMap = CoordinateMap.id :=
    globalFrameIso_map_hom_coordinates (baseChange_residue_eq e f) C
  have hy : y.hom.val.toHom.toCoordinateMap = CoordinateMap.id :=
    Y.baseChangeGlobalFrameTestIso_hom_coordinates f C
  have hx : x.hom.val.toHom.toCoordinateMap = CoordinateMap.id :=
    X.baseChangeGlobalFrameTestIso_hom_coordinates f C
  have ho : (ModuleLaw.OrderAction.Iso.hom (O := 𝒪[K]) (R := C) o).val.toHom.toCoordinateMap =
      CoordinateMap.id :=
    baseChangeResidueFrameTestIso_hom_coordinates e f C
  apply ModuleLaw.OrderAction.Iso.ext_hom
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  exact (ModuleLaw.OrderAction.Iso.trans_hom_coordinates_id n y hn hy).trans
    (ModuleLaw.OrderAction.Iso.trans_hom_coordinates_id x o hx ho).symm

/-- The four actual full-order rational fixed-frame maps, with their proved residue naturality square. -/
def baseChangeResidueFrameSquare (e : X.residueMap = Y.residueMap) (f : A ⟶ B)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj B).obj) :=
  letI := coefficientAlgebra (O := 𝒪[K]) C
  let n := baseChangeNewResidueFrameTestIso e f C
  let y := Y.baseChangeGlobalFrameTestIso f C
  let x := X.baseChangeGlobalFrameTestIso f C
  let o := baseChangeResidueFrameTestIso e f C
  ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare.mk
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K) n)
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K) y)
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K) x)
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K) o)
    ((ModuleLaw.OrderAction.QuasiIsogeny.ofIso_trans n y).symm.trans
      ((congrArg (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (O := 𝒪[K]) (R := C) (F := K))
        (baseChangeGlobalFrameTestIso_residue_natural e f C)).trans
          (ModuleLaw.OrderAction.QuasiIsogeny.ofIso_trans x o)))

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
