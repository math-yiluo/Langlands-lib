import Langlands.GroupScheme.Torus.GeometricHomMaximal
import Langlands.GroupScheme.Absolute.ParabolicMaximalTorusProof
import Langlands.GroupScheme.Rational.ParabolicConnectedConjugacy
import Langlands.GroupScheme.RelativeLevi.ParabolicSourceGeometry
import Langlands.GroupScheme.RelativeLevi.ParabolicClosedProof
import Langlands.GroupScheme.Torus.FieldPointMaximality

/-! # Ambient maximality of maximal tori in parabolic subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- Every maximal torus of a parabolic in a connected reductive group is
maximal in the ambient group, with the same torus source. -/
theorem IsMaximalTorus.comp_parabolic
    {k : Type u} [Field k]
    {G P : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {t : T.toGrp ⟶ P} (ht : IsMaximalTorus t)
    (i : P ⟶ G) (hi : IsParabolicSubgroup i) (hG : IsConnectedReductive G) :
    IsMaximalTorus (t ≫ i) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : Smooth P.X.hom := hi.smooth
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  let : IsAffineHom P.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let : ConnectedSpace P.X.left := hi.connectedSpace
  apply ht.comp_of_common_geometric_maximalTorus (K := AlgebraicClosure k) i
  let b := algebraBaseMap k (AlgebraicClosure k)
  let F := baseChange b
  have hGK : IsConnectedReductive (F.obj G) :=
    connectedReductiveFieldExtensionStatement k (AlgebraicClosure k) G hG
  have hiK : IsParabolicSubgroup (F.map i) :=
    parabolicFieldExtensionStatement k (AlgebraicClosure k) G hG P i hi
  obtain ⟨T₀, j, f, hj, hf⟩ :=
    parabolicMaximalTorus (AlgebraicClosure k) (F.obj G) hGK (F.obj P) (F.map i) hiK
  refine ⟨T₀, f, ?_, ?_⟩
  · exact IsMaximalTorus.of_comp hiK.isClosedSubgroup (hf.symm ▸ hj)
  · rwa [hf]

/-- Fibrewise maximality in a relative parabolic implies fibrewise maximality
in the ambient reductive group. -/
theorem IsFibrewiseMaximalTorus.comp_relativeParabolic
    {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    {t : T.toGrp ⟶ P} (ht : IsFibrewiseMaximalTorus t)
    (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i) (hG : IsReductive G) :
    IsFibrewiseMaximalTorus (t ≫ i) := by
  intro s
  rw [Functor.map_comp]
  exact (ht s).comp_parabolic ((baseChange (S.fromSpecResidueField s)).map i)
    (hi.residueFiber s) (hG.isConnectedReductive_residueFiber s)

/-- The actual composite torus inclusion, with closedness and ambient
fibrewise maximality. -/
def RelativeLevi.parabolicAmbientMaximalTorus
    {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    {t : T.toGrp ⟶ P} (ht : IsFibrewiseMaximalTorus t) (hc : IsClosedSubgroup t)
    (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i) (hG : IsReductive G) :
    {a : T.toGrp ⟶ G // IsClosedSubgroup a ∧ IsFibrewiseMaximalTorus a} :=
  ⟨t ≫ i, hc.comp (relativeParabolicClosed S G P i hG hi),
    ht.comp_relativeParabolic i hi hG⟩

@[simp]
theorem RelativeLevi.parabolicAmbientMaximalTorus_val
    {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    {t : T.toGrp ⟶ P} (ht : IsFibrewiseMaximalTorus t) (hc : IsClosedSubgroup t)
    (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i) (hG : IsReductive G) :
    (RelativeLevi.parabolicAmbientMaximalTorus ht hc i hi hG).val = t ≫ i := rfl

end Langlands.GroupScheme
