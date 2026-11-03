import Langlands.GroupScheme.Derived.SplitTorusTransport
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.Derived.ConnectednessProof
import Langlands.GroupScheme.Derived.NormalityTransfer
import Langlands.GroupScheme.Derived.CenterReduction

/-! # Assembly reductions for semisimplicity of the actual derived subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IsDerivedSubgroup

section BaseChange

variable {k : Type u} [Field k]
  {G D : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {d : D ⟶ G}
  {S' : Scheme.{u}} (b : S' ⟶ Spec (CommRingCat.of k)) [IsAffineHom b]
  {E : GroupScheme S'} {e : E ⟶ (GroupScheme.baseChange b).obj G}

/-- Compare the base change of any actual derived subgroup with an independently chosen
actual derived subgroup after an affine base change from a field. -/
def baseChangeIso (hd : IsDerivedSubgroup d) (he : IsDerivedSubgroup e) :
    (GroupScheme.baseChange b).obj D ≅ E :=
  (hd.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b G)).iso he

/-- The comparison commutes with the two actual inclusions into the base-changed group. -/
@[reassoc]
theorem baseChangeIso_hom_comp (hd : IsDerivedSubgroup d) (he : IsDerivedSubgroup e) :
    (hd.baseChangeIso b he).hom ≫ e = (GroupScheme.baseChange b).map d :=
  (hd.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b G)).iso_hom_comp he

end BaseChange

section FiniteCenter

variable {k : Type u} [Field k]
  {G D Z E : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffine G.X.left] {d : D ⟶ G}

/-- An epimorphic central product and a finite ambient-centre preimage in one actual derived
subgroup give a finite full centre in every actual derived subgroup. -/
theorem hasFiniteCenter_of_centralProduct
    (hd : IsDerivedSubgroup d) (i : Z ⟶ G) (e : E ⟶ G)
    (hi : IsCentral i) (he : IsDerivedSubgroup e) [Epi (subgroupProductMap i e)]
    (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ E)
    (hcc : IsClosedSubgroup c) (hc : SubgroupFunctor.range c = (center G).comap e)
    (hfin : IsFinite C.X.hom) : HasFiniteCenter D :=
  HasFiniteCenter.of_iso (hd.iso he)
    (hasFiniteCenter_of_finite_center_preimage_of_epi_subgroupProductMap
      i hi e he.1 C c hcc hc hfin)

end FiniteCenter

section Geometric

variable {k : Type u} [Field k]
  {G D : GroupScheme (Spec (CommRingCat.of k))} {d : D ⟶ G}
  {Z E : GroupScheme (Spec (CommRingCat.of (AlgebraicClosure k)))}
  (i : Z ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj G)
  (e : E ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj G)

/-- A central product chosen over the algebraic closure transfers the geometric unipotent
radical condition to any supplied actual derived subgroup over the ground field. -/
theorem hasTrivialGeometricUnipotentRadical_of_centralProduct
    (hG : IsConnectedReductive G) (hd : IsDerivedSubgroup d)
    (hi : IsCentral i) (he : IsDerivedSubgroup e) [Epi (subgroupProductMap i e)] :
    HasTrivialUnipotentRadical
      ((GroupScheme.baseChange (toAlgebraicClosure k)).obj D) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _))
  let : IsAffine ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.left :=
    isAffine_of_isAffineHom
      ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom
  exact HasTrivialUnipotentRadical.of_iso (hd.baseChangeIso (toAlgebraicClosure k) he)
    (HasTrivialUnipotentRadical.of_isCentral_of_epi_subgroupProductMap
      i e hi he.1 hG.hasTrivialGeometricUnipotentRadical)

/-- Smoothness and an actual central product over the algebraic closure suffice for connected
reductivity of a supplied actual derived subgroup; connectedness and affineness follow from
the published derived-subgroup results. -/
theorem isConnectedReductive_of_geometricCentralProduct
    (hG : IsConnectedReductive G) (hd : IsDerivedSubgroup d)
    (hs : Smooth D.X.hom) (hi : IsCentral i) (he : IsDerivedSubgroup e)
    [Epi (subgroupProductMap i e)] : IsConnectedReductive D := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  exact ⟨hs, hd.1.isAffineHom,
    derivedSubgroupConnectedness k G D d hd hG.connectedSpace,
    hd.hasTrivialGeometricUnipotentRadical_of_centralProduct i e hG hi he⟩

end Geometric

end Langlands.GroupScheme.IsDerivedSubgroup
