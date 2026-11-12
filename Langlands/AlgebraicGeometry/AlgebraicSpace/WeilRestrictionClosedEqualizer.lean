import Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionEqualizerGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.QuasiAffineWeilRestrictionComparison
import Langlands.AlgebraicGeometry.PointTopology.WeilRestrictionClosedImmersionProof

/-! # Closed equality loci under finite locally free restriction of scalars -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace
namespace WeilRestrictionDiagonalGeometry

open PointTopology
set_option backward.isDefEq.respectTransparency false

/-- Any monomorphic representative of an equality locus inherits the diagonal property. -/
theorem property_of_mono_representsEqualizer {S : Scheme.{u}} {F : Presheaf S}
    {P : MorphismProperty Scheme.{u}}
    (hF : (P.inverseImage (Over.forget S)).relative (schemeYoneda S) (diag F))
    {U Z : Over S} {ι : Z ⟶ U} [Mono ι.left] {x y : F.obj (op U)}
    (hι : RepresentsEqualizer ι x y) : P ι.left := by
  have : Mono ι := (Over.forget S).mono_of_mono_map (inferInstance : Mono ι.left)
  let α : (schemeYoneda S).obj U ⟶ F := uliftYonedaEquiv.symm x
  let β : (schemeYoneda S).obj U ⟶ F := uliftYonedaEquiv.symm y
  have w : (schemeYoneda S).map ι ≫ α = (schemeYoneda S).map ι ≫ β := by
    apply uliftYonedaEquiv.injective
    have e₁ := uliftYonedaEquiv_naturality α ι.op
    have e₂ := uliftYonedaEquiv_naturality β ι.op
    simp only [Quiver.Hom.unop_op] at e₁ e₂
    rw [← e₁, ← e₂]
    simpa [α, β] using (hι ι).1 ⟨𝟙 _, by simp⟩
  have hc := RepresentsEqualizer.isLimitFork α β (by simpa [α, β] using hι) w
  exact hF.property (prod.lift α β) _ ι (isPullback_diag_of_isLimit_fork hc)

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

/-- The affine Weil restriction preserves a terminal scheme. -/
def affineWeilRestriction_isTerminal
    (U : Over (Spec (CommRingCat.of B))) [IsAffine U.left]
    [LocallyOfFiniteType U.hom] (hU : IsTerminal U) :
    IsTerminal (affineWeilRestriction A B U) := by
  apply IsTerminal.ofUniqueHom
    (fun T => (affineWeilRestrictionTestEquiv A B U T).symm (hU.from _))
  intro T f
  apply (affineWeilRestrictionTestEquiv A B U T).injective
  rw [Equiv.apply_symm_apply]
  exact hU.hom_ext _ _

/-- A closed subscheme of the affine upper base has closed affine Weil restriction. -/
theorem affineWeilRestriction_hom_isClosedImmersion
    (Y : Over (Spec (CommRingCat.of B))) [IsAffine Y.left]
    [LocallyOfFiniteType Y.hom] [AlgebraicGeometry.IsClosedImmersion Y.hom] :
    AlgebraicGeometry.IsClosedImmersion (affineWeilRestriction A B Y).hom := by
  let U : Over (Spec (CommRingCat.of B)) := Over.mk (𝟙 _)
  have : IsAffine U.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))
  have : LocallyOfFiniteType U.hom := inferInstanceAs (LocallyOfFiniteType (𝟙 _))
  let e := (affineWeilRestriction_isTerminal A B U Over.mkIdTerminal).uniqueUpToIso
    Over.mkIdTerminal
  have he : (affineWeilRestriction A B U).hom = e.hom.left := by
    simpa using (Over.w e.hom).symm
  have : IsIso (affineWeilRestriction A B U).hom := by
    rw [he]
    exact (Over.forget _).map_isIso e.hom
  let f : Y ⟶ U := Over.homMk Y.hom (by simp [U])
  have : AlgebraicGeometry.IsClosedImmersion f.left := inferInstanceAs
    (AlgebraicGeometry.IsClosedImmersion Y.hom)
  have : AlgebraicGeometry.IsClosedImmersion (affineWeilRestrictionMap A B f).left :=
    affineWeilRestrictionMap_isClosedImmersion A B f
  rw [← Over.w (affineWeilRestrictionMap A B f)]
  infer_instance

/-- The quasi-affine representing scheme of a closed upper-base scheme is closed. -/
theorem quasiAffineWeilRestriction_hom_isClosedImmersion
    (Y : Over (Spec (CommRingCat.of B))) [Y.left.IsQuasiAffine]
    [LocallyOfFiniteType Y.hom] [AlgebraicGeometry.IsClosedImmersion Y.hom] :
    AlgebraicGeometry.IsClosedImmersion (affineChartWeilRestriction A B Y).hom := by
  have : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  let e : affineChartWeilRestriction A B Y ≅ affineWeilRestriction A B Y :=
    (ULiftYoneda.fullyFaithful _).preimageIso
      (quasiAffineWeilRestrictionPresheafIso A B Y ≪≫
        (affineWeilRestrictionPresheafIso A B Y).symm)
  have := affineWeilRestriction_hom_isClosedImmersion A B Y
  rw [← Over.w e.hom]
  infer_instance

end WeilRestrictionDiagonalGeometry
end Langlands.AlgebraicGeometry.AlgebraicSpace
