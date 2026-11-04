import Langlands.GroupScheme.Dynamic.UnipotentStructure
import Langlands.GroupScheme.Dynamic.UnipotentTorusAction
import Langlands.GroupScheme.Rational.TorusUnipotenceProof

/-! # Dynamic geometric radicals from reductivity of the centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section Unipotence

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)

/-- A representative of the actual identity-limit subgroup of a smooth affine
group over a field is unipotent. -/
theorem isUnipotent_unipotentRepresentative
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : (unipotent χ).IsRepresentedBy j) : IsUnipotent H := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact isUnipotent_of_torusActionUnipotence χ RelativeRoot.torusActionUnipotence
    hj (Affine.isClosedSubgroup_of_isRepresentedBy_unipotent χ hj)

end Unipotence

section GeometricStructure

variable {k : Type u} [Field k]
    {G Z P U : GroupScheme (Spec (CommRingCat.of k))}
    [hGaff : IsAffineHom G.X.hom] [hGsm : Smooth G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (z : Z ⟶ G) (p : P ⟶ G) (r : U ⟶ P)
    (hP : (parabolic χ).IsRepresentedBy p)
    (hU : (unipotent χ).IsRepresentedBy (r ≫ p))
    (hz : (centralizer χ).IsRepresentedBy z)

include χ z p hP hU hz hGaff hGsm

/-- For a smooth affine ambient group, connected reductivity of the dynamic
centralizer implies the full geometric radical predicate. -/
theorem isGeometricUnipotentRadical_of_centralizer
    (hZ : IsConnectedReductive Z) : IsGeometricUnipotentRadical r := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hpc := Affine.isClosedSubgroup_of_isRepresentedBy_parabolic χ hP
  have hj := Affine.isClosedSubgroup_of_isRepresentedBy_unipotent χ hU
  have hzc := Affine.isClosedSubgroup_of_isRepresentedBy_centralizer χ hz
  have hrc : IsClosedSubgroup r := IsClosedSubgroup.of_comp hpc hj
  have hsm : Smooth U.X.hom := (dynamicSmooth k G χ U (r ≫ p)).2.2 hU
  have hc : ConnectedSpace U.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G χ hU
  have hu : IsUnipotent U := isUnipotent_unipotentRepresentative χ hU
  have hn := range_unipotentRepresentative_isNormal χ p r hP hU
  let b := toAlgebraicClosure k
  let B := GroupScheme.baseChange b
  let : IsAffineHom (B.obj G).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  let : Smooth (B.obj G).X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have hUb : (unipotent (baseChangeCocharacter b χ)).IsRepresentedBy
      (B.map (r ≫ p)) := by
    rw [unipotent_baseChange]
    exact hU.baseChange b
  have hcg : ConnectedSpace (B.obj U).X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent
      (B.obj G) (baseChangeCocharacter b χ) hUb
  have hug : IsUnipotent (B.obj U) :=
    isUnipotent_unipotentRepresentative (baseChangeCocharacter b χ) hUb
  exact isGeometricUnipotentRadical_of_reductive_centralizer χ z p r
    hP hpc hU hz hzc hZ hrc hsm hc hu hn hcg hug

end GeometricStructure

end Langlands.GroupScheme.Dynamic

namespace Langlands.GroupScheme

/-- The full universal dynamic-radical target follows from the separately
owned universal dynamic-centralizer reductivity target. -/
def DynamicGeometricUnipotentRadicalFromCentralizerStatement : Prop :=
  DynamicCentralizerReductiveStatement.{u} →
    DynamicGeometricUnipotentRadicalStatement.{u}

/-- Unipotence is discharged by the published torus-action theorem, leaving
only connected reductivity of dynamic centralizers as an explicit input. -/
theorem dynamicGeometricUnipotentRadical_of_centralizer :
    DynamicGeometricUnipotentRadicalFromCentralizerStatement.{u} := by
  intro hcentralizer k _ G hG χ P U p r hP hU
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact Dynamic.isGeometricUnipotentRadical_of_centralizer
    χ (Dynamic.Affine.centralizerHom χ) p r hP hU
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)
    (hcentralizer k G hG χ _ (Dynamic.Affine.centralizerHom χ)
      (Dynamic.Affine.isClosedSubgroup_centralizerHom χ)
      (Dynamic.Affine.isRepresentedBy_centralizerHom χ))

end Langlands.GroupScheme
