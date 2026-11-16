import Langlands.GroupScheme.Torus.CommutativeReductive
import Langlands.GroupScheme.Torus.RelativeCommutative
import Langlands.GroupScheme.Torus.RelativeReductive
import Langlands.GroupScheme.Torus.BaseChange

/-! # Fppf descent of relative tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {T : GroupScheme S}

/-- Commutativity of an actual group scheme descends along an fppf base cover. -/
theorem isCommMonObj_of_fppfCover
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (hT : ∀ i, IsCommMonObj ((baseChange (𝒰.f i)).obj T).X) :
    IsCommMonObj T.X := by
  apply (isCommMonObj_iff_isMulCommutative _).2
  intro U
  refine ⟨⟨fun x y => ?_⟩⟩
  apply Over.OverMorphism.ext
  apply (𝒰.pullback₁ U.hom).hom_ext
  intro i
  let V : Over (𝒰.X i) := Over.mk (pullback.snd U.hom (𝒰.f i))
  let a : (Over.map (𝒰.f i)).obj V ⟶ U :=
    Over.homMk (pullback.fst U.hom (𝒰.f i)) pullback.condition
  let e := baseChangePointsEquiv (𝒰.f i) T V
  let : IsCommMonObj ((baseChange (𝒰.f i)).obj T).X := hT i
  have h : (e.symm (a ≫ x)) * (e.symm (a ≫ y)) =
      (e.symm (a ≫ y)) * (e.symm (a ≫ x)) := mul_comm _ _
  have he := congrArg e h
  simp only [map_mul, MulEquiv.apply_symm_apply] at he
  exact congrArg (fun z => z.left)
    ((MonObj.comp_mul a x y).trans (he.trans (MonObj.comp_mul a y x).symm))

namespace RelativeTorus

private theorem isTorus_residueFiber_of_fppfCover
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (hT : ∀ i, IsTorus ((baseChange (𝒰.f i)).obj T)) (s : S) :
    _root_.Langlands.GroupScheme.IsTorus
      ((baseChange (S.fromSpecResidueField s)).obj T) := by
  have : Scheme.JointlySurjective Scheme.fppfPrecoverage.{u} :=
    inferInstanceAs (Scheme.JointlySurjective
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)))
  obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq s
  let a := S.fromSpecResidueField ((𝒰.f i) x)
  let c := Spec.map ((𝒰.f i).residueFieldMap x)
  let : Algebra (S.residueField ((𝒰.f i) x) : Type u)
      ((𝒰.X i).residueField x : Type u) :=
    ((𝒰.f i).residueFieldMap x).hom.toAlgebra
  apply _root_.Langlands.GroupScheme.IsTorus.of_baseChange
    (k := (S.residueField ((𝒰.f i) x) : Type u))
    (K := ((𝒰.X i).residueField x : Type u))
    (T := (baseChange a).obj T)
  change _root_.Langlands.GroupScheme.IsTorus
    ((baseChange c).obj ((baseChange a).obj T))
  apply _root_.Langlands.GroupScheme.IsTorus.of_iso (baseChangeCompIso a c T).symm
  rw [show c ≫ a = (𝒰.X i).fromSpecResidueField x ≫ 𝒰.f i from
    (𝒰.f i).SpecMap_residueFieldMap_fromSpecResidueField x]
  exact (IsTorus.of_iso
    (baseChangeCompIso (𝒰.f i) ((𝒰.X i).fromSpecResidueField x) T)
    ((hT i).baseChange ((𝒰.X i).fromSpecResidueField x))).isTorus

/-- Being an étale form of a finite split torus descends along every fppf base cover. -/
theorem IsTorus.of_fppfCover
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (hT : ∀ i, IsTorus ((GroupScheme.baseChange (𝒰.f i)).obj T)) : IsTorus T := by
  have hcomm : IsCommMonObj T.X :=
    isCommMonObj_of_fppfCover 𝒰 fun i => (hT i).isCommMonObj
  have hsmooth : Smooth T.X.hom := by
    have : MorphismProperty.IsLocalAtTarget (@Smooth : MorphismProperty Scheme.{u})
        Scheme.fppfPrecoverage :=
      Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _
    exact MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒰 fun i => (hT i).smooth
  have haffine : IsAffineHom T.X.hom := by
    have : MorphismProperty.IsLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u})
        Scheme.fppfPrecoverage :=
      Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _
    exact MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒰 fun i => (hT i).isAffineHom
  have hred : IsReductive T := by
    refine ⟨hsmooth, haffine, fun s => ?_⟩
    have hres := (isTorus_residueFiber_of_fppfCover 𝒰 hT s).isRelativeTorus
    have hgeom := IsTorus.of_iso
      (baseChangeCompIso (S.fromSpecResidueField s)
        (toAlgebraicClosure (S.residueField s)) T)
      (hres.baseChange (toAlgebraicClosure (S.residueField s)))
    exact hgeom.isConnectedReductive.isPseudoReductive
  exact relativeTorus_of_commutative_reductive
    ({ T with comm := hcomm } : CommGroupScheme S) hred

end RelativeTorus

/-- Relative-torus status is local for fppf covering families of any base scheme. -/
def FppfRelativeTorusDescentStatement : Prop :=
  ∀ (S : Scheme.{u}) (T : GroupScheme S)
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S),
    (∀ i, RelativeTorus.IsTorus ((baseChange (𝒰.f i)).obj T)) →
      RelativeTorus.IsTorus T

/-- Fppf descent of relative tori holds in every universe. -/
theorem fppfRelativeTorusDescent : FppfRelativeTorusDescentStatement.{u} :=
  fun _ _ 𝒰 hT => RelativeTorus.IsTorus.of_fppfCover 𝒰 hT

end Langlands.GroupScheme
