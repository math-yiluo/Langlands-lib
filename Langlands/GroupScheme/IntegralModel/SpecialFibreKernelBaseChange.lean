import Langlands.GroupScheme.IntegralModel.BaseChangeCoefficientHom
import Langlands.GroupScheme.IntegralModelReduction
import Langlands.GroupScheme.KernelSquareTransport
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Special-fibre kernels under local coefficient extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.IntegralModel

section Square

variable {S T U V : Scheme.{u}}
  (b : T ⟶ S) (c : V ⟶ T) (d : U ⟶ S) (e : V ⟶ U)
  (h : c ≫ b = e ≫ d) (G : GroupScheme S)

private def coefficientFibreSquareIso :
    (GroupScheme.baseChange c).obj ((GroupScheme.baseChange b).obj G) ≅
      (GroupScheme.baseChange e).obj ((GroupScheme.baseChange d).obj G) :=
  (baseChangeCompIso b c G).symm ≪≫
    eqToIso (congrArg (fun f => (GroupScheme.baseChange f).obj G) h) ≪≫
      baseChangeCompIso d e G

private theorem coefficientFibreSquareIso_naturality
    {H : GroupScheme S} (f : G ⟶ H) :
    (GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map f) ≫
        (coefficientFibreSquareIso b c d e h H).hom =
      (coefficientFibreSquareIso b c d e h G).hom ≫
        (GroupScheme.baseChange e).map ((GroupScheme.baseChange d).map f) := by
  have heq {q q' : V ⟶ S} (hq : q = q') :
      (GroupScheme.baseChange q).map f ≫
          (eqToIso (congrArg (fun k => (GroupScheme.baseChange k).obj H) hq)).hom =
        (eqToIso (congrArg (fun k => (GroupScheme.baseChange k).obj G) hq)).hom ≫
          (GroupScheme.baseChange q').map f := by
    subst q'
    simp
  have hinv : (GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map f) ≫
        (baseChangeCompIso b c H).inv =
      (baseChangeCompIso b c G).inv ≫ (GroupScheme.baseChange (c ≫ b)).map f :=
    ((Functor.mapGrpNatIso (Over.pullbackComp c b)) ≪≫
      Functor.mapGrpCompIso).inv.naturality f
  have hhom : (GroupScheme.baseChange (e ≫ d)).map f ≫
        (baseChangeCompIso d e H).hom =
      (baseChangeCompIso d e G).hom ≫
        (GroupScheme.baseChange e).map ((GroupScheme.baseChange d).map f) :=
    ((Functor.mapGrpNatIso (Over.pullbackComp e d)) ≪≫
      Functor.mapGrpCompIso).hom.naturality f
  unfold coefficientFibreSquareIso
  simp only [Iso.trans_hom, Iso.symm_hom]
  simp only [← Category.assoc]
  rw [hinv]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ (baseChangeCompIso d e H).hom, heq h,
    Category.assoc, hhom]

end Square

section Coefficients

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  [IsLocalRing A] [IsLocalHom (algebraMap R A)]

omit [IsDomain R] [IsFractionRing R K] [IsDomain A] [IsFractionRing A L] in
/-- The actual residue maps and a local coefficient extension form a square. -/
theorem residueCoefficientSquare :
    Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A) ≫
        residueBaseMap R =
      residueBaseMap A ≫ Spec.algebraMap R A := by
  unfold residueBaseMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- Extending the special fibre by the induced residue-field extension agrees
with taking the special fibre of the model with extended coefficients. -/
def specialFibreBaseChangeIso :
    (GroupScheme.baseChange
      (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))).obj
        M.specialFibre ≅ (M.baseChange A L).specialFibre :=
  coefficientFibreSquareIso (residueBaseMap R)
    (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))
    (Spec.algebraMap R A) (residueBaseMap A)
    (residueCoefficientSquare (R := R) A) M.group

variable {M} {N : IntegralModel R K H} {f : G ⟶ H} (φ : M.Hom N f)

/-- The special-fibre comparison commutes with every compatible model map. -/
theorem Hom.specialFibreBaseChangeIso_naturality :
    (GroupScheme.baseChange
        (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))).map
          φ.specialFibreMap ≫ (N.specialFibreBaseChangeIso A L).hom =
      (M.specialFibreBaseChangeIso A L).hom ≫
        (φ.baseChangeCoefficients A L).specialFibreMap :=
  coefficientFibreSquareIso_naturality _ _ _ _ _ _ φ.hom

/-- The residue extension of the full scheme-theoretic kernel is the full
special-fibre kernel after local coefficient extension. -/
def Hom.specialFibreKernelBaseChangeIso :
    (GroupScheme.baseChange
      (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))).obj
        (kernel φ.specialFibreMap) ≅
      kernel (φ.baseChangeCoefficients A L).specialFibreMap :=
  kernelBaseChangeIso _ φ.specialFibreMap ≪≫
    kernelSquareIso _ _ (M.specialFibreBaseChangeIso A L) (N.specialFibreBaseChangeIso A L)
      (φ.specialFibreBaseChangeIso_naturality A L).symm

/-- All three geometric kernel properties reflect along a local extension of
integral coefficients, with no finiteness hypothesis on the residue extension. -/
theorem Hom.specialFibreKernel_properties_of_baseChange
    (hφ : Smooth (kernel (φ.baseChangeCoefficients A L).specialFibreMap).X.hom ∧
      ConnectedSpace (kernel (φ.baseChangeCoefficients A L).specialFibreMap).X.left ∧
        IsUnipotent (kernel (φ.baseChangeCoefficients A L).specialFibreMap)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) := by
  let b := Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)
  have hb := fieldExtension_fpqc (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)
  let : Surjective b := hb.1
  let : Flat b := hb.2.1
  let : QuasiCompact b := hb.2.2
  have h := smooth_connected_unipotent_of_groupIso
    (φ.specialFibreKernelBaseChangeIso A L) hφ
  let : IsAffineHom M.specialFibre.X.hom := by
    change IsAffineHom (pullback.snd M.group.X.hom (residueBaseMap R))
    infer_instance
  let : IsAffineHom N.specialFibre.X.hom := by
    change IsAffineHom (pullback.snd N.group.X.hom (residueBaseMap R))
    infer_instance
  let : IsAffineHom (kernel φ.specialFibreMap).X.hom := by
    rw [← (kernelι φ.specialFibreMap).hom.hom.w]
    infer_instance
  exact ⟨smooth_of_baseChange b _ h.1, connectedSpace_of_baseChange b _ h.2.1,
    h.2.2.of_baseChange⟩

end Coefficients

end Langlands.GroupScheme.IntegralModel
