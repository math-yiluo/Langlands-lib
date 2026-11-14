import Langlands.GroupScheme.IntegralModel.KernelCentralizer
import Langlands.GroupScheme.Rational.RootKernelIdentityTorus
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Torus.HenselianSplitRank

/-! # The integral torus in a full character-kernel centralizer component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- A split torus has geometrically connected fibres over any base scheme. -/
theorem IsSplitTorus.geometricallyConnected {S : Scheme.{u}} {T : GroupScheme S}
    (hT : IsSplitTorus T) : GeometricallyConnected T.X.hom :=
  ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun _K _ b =>
    (hT.baseChange b).connectedSpace⟩

namespace IntegralModel.KernelCentralizerData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {M : IntegralModel R K G}
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    {i : T.toGrp ⟶ M.group} {a : characterLattice T}
    (D : KernelCentralizerData M i a)

/-- The actual split integral torus map factors through the relative
identity component of its full character-kernel centralizer. -/
def torus (hT : IsSplitTorus T.toGrp) : T.toGrp ⟶ D.componentGroup := by
  have := hT.geometricallyConnected
  exact Classical.choose (D.isRelativeComponent.exists_hom_lift
    (RelativeRoot.kernelCentralizerTorus i a D.fullHom D.fullRepresents))

@[reassoc]
theorem torus_comp_componentHom (hT : IsSplitTorus T.toGrp) :
    D.torus hT ≫ D.componentHom =
      RelativeRoot.kernelCentralizerTorus i a D.fullHom D.fullRepresents := by
  have := hT.geometricallyConnected
  exact Classical.choose_spec (D.isRelativeComponent.exists_hom_lift
    (RelativeRoot.kernelCentralizerTorus i a D.fullHom D.fullRepresents))

/-- The torus factor retains the original integral ambient map. -/
@[reassoc]
theorem torus_comp_ambient (hT : IsSplitTorus T.toGrp) :
    D.torus hT ≫ (D.componentHom ≫ D.fullHom) = i := by
  rw [← Category.assoc, torus_comp_componentHom,
    RelativeRoot.kernelCentralizerTorus_comp]

/-- A closed integral torus stays closed in the relative component. -/
theorem torus_isClosed (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i) :
    IsClosedSubgroup (D.torus hT) := by
  apply D.isRelativeComponent.isClosedSubgroup_of_comp
  rw [torus_comp_componentHom]
  exact IsClosedSubgroup.of_comp D.fullClosed
    (by rwa [RelativeRoot.kernelCentralizerTorus_comp])

variable {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))

local instance : Smooth ((baseChange b).obj D.fullGroup).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd D.fullGroup.X.hom b))

local instance : IsAffineHom ((baseChange b).obj D.fullGroup).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd D.fullGroup.X.hom b))

local instance : GeometricallyConnected ((baseChange b).obj D.componentGroup).X.hom :=
  inferInstanceAs (GeometricallyConnected
    (CategoryTheory.Limits.pullback.snd D.componentGroup.X.hom b))

/-- At every field-valued base point the relative component is the ordinary
identity component of the full centralizer fibre. -/
def fibreIso :
    (baseChange b).obj D.componentGroup ≅
      identityComponent ((baseChange b).obj D.fullGroup) :=
  (RelativeIdentityComponent.smoothBaseChange _ D.fullGroup D.fullSmooth
    D.componentGroup D.componentHom D.isRelativeComponent _ b).identityComponentIso

@[reassoc]
theorem fibreIso_hom_comp :
    (D.fibreIso b).hom ≫ identityComponentι ((baseChange b).obj D.fullGroup) =
      (baseChange b).map D.componentHom :=
  (RelativeIdentityComponent.smoothBaseChange _ D.fullGroup D.fullSmooth
    D.componentGroup D.componentHom D.isRelativeComponent _ b).identityComponentIso_hom_comp

/-- The full fibre represents the centralizer of the entire base-changed
scheme-theoretic character kernel. -/
theorem fullFibreRepresents :
    (RelativeRoot.kernelCentralizer ((baseChange b).map i)
      (characterLattice.baseChange b T a)).IsRepresentedBy
        ((baseChange b).map D.fullHom) :=
  RelativeRoot.kernelCentralizer_isRepresentedBy_baseChange b i a D.fullRepresents

/-- Under the canonical component-fibre isomorphism, the base-changed
integral torus is the canonical torus in the ordinary kernel-centralizer
identity component, with the original base-changed ambient inclusion. -/
theorem torus_fibreIso (hT : IsSplitTorus T.toGrp) :
    (baseChange b).map (D.torus hT) ≫ (D.fibreIso b).hom =
      RelativeRoot.kernelCentralizerIdentityTorus
        (T := (CommGroupScheme.baseChange b).obj T)
        (G := (baseChange b).obj M.group) (C := (baseChange b).obj D.fullGroup)
        ((baseChange b).map i)
        (hT.baseChange b) (characterLattice.baseChange b T a)
        ((baseChange b).map D.fullHom) (D.fullFibreRepresents b) := by
  apply IdentityComponent.hom_ext_of_isOpenImmersion
    (identityComponentι ((baseChange b).obj D.fullGroup))
  rw [Category.assoc, fibreIso_hom_comp,
    RelativeRoot.kernelCentralizerIdentityTorus_comp]
  apply (D.fullFibreRepresents b).hom_ext
  rw [Category.assoc, RelativeRoot.kernelCentralizerTorus_comp]
  simpa only [Functor.map_comp] using
    congrArg (fun f => (baseChange b).map f) (D.torus_comp_ambient hT)

/-- A maximal ambient split torus in any field fibre stays maximal in the
actual fibre of the integral centralizer component. -/
theorem torus_fibre_isMaximal (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange b).obj T) ((baseChange b).map i)) :
    IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange b).obj T)
      ((baseChange b).map (D.torus hT)) := by
  apply (IsMaximalSplitTorus.comp_iso_iff _ (D.fibreIso b)).mp
  rw [torus_fibreIso]
  exact hi.kernelCentralizerIdentityTorus (characterLattice.baseChange b T a)
    ((baseChange b).map D.fullHom) (D.fullFibreRepresents b)
    (D.fullClosed.baseChange b)

omit b in
/-- Over a Henselian domain, generic maximality of a closed split ambient
torus implies maximality of its residue fibre in the actual integral
centralizer component. -/
theorem torus_residue_isMaximal [HenselianLocalRing R] [Algebra R k]
    [Smooth M.group.X.hom] (hk : Function.Surjective (algebraMap R k))
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsClosedSubgroup i)
    (hiK : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T)
      ((baseChange (Spec.algebraMap R K)).map i)) :
    IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T)
      ((baseChange (Spec.algebraMap R k)).map (D.torus hT)) := by
  apply D.torus_fibre_isMaximal (Spec.algebraMap R k) hT
  exact isMaximalSplitTorus_residue_of_generic hk M.group
    (hG.of_iso M.genericIso) T hT i hi hiK

end IntegralModel.KernelCentralizerData
end Langlands.GroupScheme
