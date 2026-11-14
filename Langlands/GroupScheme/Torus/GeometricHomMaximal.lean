import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Descent.ClosedSubgroups

/-! # Maximal tori through homomorphisms with a common geometric maximal torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Conjugacy

variable {k : Type u} [Field k]
  {H Q : GroupScheme (Spec (CommRingCat.of k))}
  {T S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- One source maximal torus which remains maximal under a homomorphism
certifies the same property for all source maximal tori, if they are conjugate. -/
theorem MaximalToriAreConjugate.isMaximalTorus_comp_of_common
    (hH : MaximalToriAreConjugate H) (q : H ⟶ Q)
    {i : T.toGrp ⟶ H} (hi : IsMaximalTorus i)
    (s : S.toGrp ⟶ H) (hs : IsMaximalTorus s)
    (hsq : IsMaximalTorus (s ≫ q)) : IsMaximalTorus (i ≫ q) :=
  ((hH T S i s hi hs).postcomp q).isMaximalTorus_iff.mpr hsq

end Conjugacy

section Geometric

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
  {H Q : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
  [IsAffineHom Q.X.hom]

/-- A common maximal torus after an algebraically closed field extension
ensures that every original-field maximal torus maps with its same source to a
maximal torus. The ambient homomorphism need not be closed or surjective. -/
theorem IsMaximalTorus.comp_of_common_geometric_maximalTorus
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ H} (hi : IsMaximalTorus i) (q : H ⟶ Q)
    (hcommon :
      ∃ (S : CommGroupScheme (Spec (CommRingCat.of K)))
        (s : S.toGrp ⟶ (baseChange (algebraBaseMap k K)).obj H),
        IsMaximalTorus s ∧
          IsMaximalTorus (s ≫ (baseChange (algebraBaseMap k K)).map q)) :
    IsMaximalTorus (i ≫ q) := by
  let b := algebraBaseMap k K
  let bc := baseChange b
  let TK := (CommGroupScheme.baseChange b).obj T
  let : Smooth (bc.obj H).X.hom := by
    change Smooth (pullback.snd H.X.hom b)
    infer_instance
  let : IsAffineHom (bc.obj H).X.hom := by
    change IsAffineHom (pullback.snd H.X.hom b)
    infer_instance
  let : ConnectedSpace (bc.obj H).X.left :=
    H.connectedSpace_baseChange_of_smooth_affine b
  have hconj : MaximalToriAreConjugate (bc.obj H) := by
    intro S S' s s' hs hs'
    exact (subgroupConjugate_iff_exists_commGroupSchemeIso s s').mpr
      (maximalTorusConjugacy K (bc.obj H) S S' s s' hs hs')
  have hiK : IsMaximalTorus (T := TK) (bc.map i) :=
    (maximalTorusBaseChange k K H T i hi.1 hi.2.1).mp hi
  obtain ⟨S, s, hs, hsq⟩ := hcommon
  have hgeom : IsMaximalTorus (T := TK) (bc.map (i ≫ q)) := by
    rw [bc.map_comp]
    exact hconj.isMaximalTorus_comp_of_common (bc.map q) hiK s hs hsq
  let : Flat b := (fieldExtension_fpqc k K).2.1
  let : Surjective b := (fieldExtension_fpqc k K).1
  let : IsClosedImmersion i.hom.hom.left := hi.2.1
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom i.hom.hom.left
  let : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have hclosed : IsClosedSubgroup (i ≫ q) :=
    IsClosedSubgroup.of_baseChange_of_isAffine b hgeom.2.1
  exact IsMaximalTorus.of_baseChange hclosed hgeom

/-- A common geometric maximal torus gives an original-field maximal torus
whose composite with the prescribed homomorphism is still maximal. -/
theorem exists_maximalTorus_comp_of_common_geometric_maximalTorus
    (q : H ⟶ Q)
    (hcommon :
      ∃ (S : CommGroupScheme (Spec (CommRingCat.of K)))
        (s : S.toGrp ⟶ (baseChange (algebraBaseMap k K)).obj H),
        IsMaximalTorus s ∧
          IsMaximalTorus (s ≫ (baseChange (algebraBaseMap k K)).map q)) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ H),
      IsMaximalTorus i ∧ IsMaximalTorus (i ≫ q) := by
  obtain ⟨T, i, hi⟩ := maximalTorusExistence k H
  exact ⟨T, i, hi, hi.comp_of_common_geometric_maximalTorus q hcommon⟩

end Geometric

/-- Preservation of maximal tori by an arbitrary homomorphism from a smooth
connected affine group, certified by one common geometric maximal torus. -/
def CommonGeometricMaximalTorusHomStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
    (H Q : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    [IsAffineHom Q.X.hom] (q : H ⟶ Q),
    (∃ (S : CommGroupScheme (Spec (CommRingCat.of K)))
      (s : S.toGrp ⟶ (baseChange (algebraBaseMap k K)).obj H),
      IsMaximalTorus s ∧
        IsMaximalTorus (s ≫ (baseChange (algebraBaseMap k K)).map q)) →
      (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ H),
        IsMaximalTorus i → IsMaximalTorus (i ≫ q)) ∧
      (∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ H),
        IsMaximalTorus i ∧ IsMaximalTorus (i ≫ q))

/-- The common geometric torus suffices by published maximal-torus conjugacy,
field-extension preservation and reflection, and original-field existence. -/
theorem commonGeometricMaximalTorusHom :
    CommonGeometricMaximalTorusHomStatement.{u} := by
  intro k K _ _ _ _ H Q _ _ _ _ q hcommon
  exact ⟨fun T i hi => hi.comp_of_common_geometric_maximalTorus q hcommon,
    exists_maximalTorus_comp_of_common_geometric_maximalTorus q hcommon⟩

end Langlands.GroupScheme
