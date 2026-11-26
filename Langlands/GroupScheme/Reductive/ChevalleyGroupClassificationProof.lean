import Langlands.GroupScheme.Reductive.ChevalleyGroupClassificationStatement
import Langlands.GroupScheme.Reductive.PidSplitRootDatum
import Langlands.GroupScheme.Reductive.AffineSplitIsomorphismTheoremStatement
import Langlands.GroupScheme.Reductive.AffineSplitIsomorphismTheoremProof
import Langlands.GroupScheme.Reductive.RootDatumFieldComparison
import Langlands.GroupScheme.Torus.IntegerSplitStatement
import Langlands.GroupScheme.Torus.IntegerSplitProof
import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport
import Langlands.LinearAlgebra.LiftedIntegerLinearEquiv

/-! # Chevalley groups over the integers are split and classified by one fibre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The lifted integers form a domain. -/
local instance liftedIntIsDomain : IsDomain (ULift.{u} ℤ) :=
  MulEquiv.isDomain ℤ (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv

/-- The lifted integers form a principal ideal ring. -/
local instance liftedIntIsPrincipalIdealRing : IsPrincipalIdealRing (ULift.{u} ℤ) :=
  IsPrincipalIdealRing.of_surjective
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm.toRingHom
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm.surjective

/-- **Chevalley groups over `ℤ` are split.** Let `t : T ⟶ G` be a homomorphism
from a torus `T` over `Spec ℤ` to a reductive group `G` over `Spec ℤ` that is a
maximal torus on every residue-field fibre. Then `T` is isomorphic to a
coordinate split torus `𝔾_m^I`, one full root datum on the coordinate lattices
`ℤ^I` is the root datum on every field fibre, and every root space is a free
module of rank one over `ℤ`. -/
theorem integerReductive_split
    (G : GroupScheme (Spec (CommRingCat.of (ULift.{u} ℤ)))) (hG : IsReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of (ULift.{u} ℤ)))) (t : T.toGrp ⟶ G)
    (hT : RelativeTorus.IsTorus T.toGrp) (hm : IsFibrewiseMaximalTorus t) :
    ∃ (I : Type u) (_ : Fintype I)
      (e : splitTorus (Spec (CommRingCat.of (ULift.{u} ℤ))) I ≅ T.toGrp)
      (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
      haveI := hG.isAffineHom
      IsFibrewiseRootDatumOf I G (e.hom ≫ t) P ∧
        ∀ α : J, Nonempty (splitTorus.exponentWeightSpace I G (e.hom ≫ t)
          (P.root α) ≃ₗ[CommRingCat.of (ULift.{u} ℤ)] CommRingCat.of (ULift.{u} ℤ)) := by
  classical
  let := hG.isAffineHom
  obtain ⟨I, hI, ⟨e⟩⟩ := integerTorusSplit T.toGrp hT
  let : Fintype I := Fintype.ofFinite I
  have hi : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of (ULift.{u} ℤ))) I)
      (e.inv ≫ t) :=
    hm.iso_comp (T' := splitTorus.commGroupScheme _ I) e.symm
  obtain ⟨J, P, hP⟩ := exists_fibrewiseRootDatum_of_isDomain I G hG (e.inv ≫ t) hi
  refine ⟨I, inferInstance, e.symm, J, P, hP, fun α => ?_⟩
  obtain ⟨eR⟩ := pidRootWeightSpace_nonempty_linearEquiv G hG I (e.inv ≫ t) hi P hP α
  exact ⟨Langlands.LinearAlgebra.liftedIntLinearEquivOfAddEquiv
    (@LinearEquiv.toAddEquiv (ULift.{u} ℤ) (ULift.{u} ℤ) _ _ _ _ _ _ _ _ _ _
      (splitTorus.exponentWeightSpace I G (e.inv ≫ t) (P.root α)).module _ eR)⟩

/-- **Chevalley groups over `ℤ`** (Conrad, *Reductive group schemes* (2014),
p.230 and Proposition 6.4.1): every Chevalley group is split, and two Chevalley
groups are isomorphic over `ℤ` if and only if they are isomorphic over a given
field `k`. -/
theorem chevalleyGroupClassification : ChevalleyGroupClassificationStatement.{u} := by
  classical
  refine ⟨fun G hG T t hT _ hm => integerReductive_split G hG T t hT hm, ?_⟩
  intro G H hGChev hHChev k _ _
  obtain ⟨hG, T, t, hT, htc, htm⟩ := hGChev
  obtain ⟨hH, T', t', hT', ht'c, ht'm⟩ := hHChev
  let := hG.isAffineHom
  let := hG.smooth
  let := hH.isAffineHom
  let := hH.smooth
  obtain ⟨I, hI, e, J, P, hP, hL⟩ := integerReductive_split G hG T t hT htm
  obtain ⟨I', hI', e', J', Q, hQ, hL'⟩ := integerReductive_split H hH T' t' hT' ht'm
  let i := e.hom ≫ t
  let j := e'.hom ≫ t'
  have hi : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i :=
    htm.iso_comp (T := T) (T' := splitTorus.commGroupScheme _ I) e
  have hj : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j :=
    ht'm.iso_comp (T := T') (T' := splitTorus.commGroupScheme _ I') e'
  constructor
  · rintro ⟨f⟩
    exact ⟨(GroupScheme.baseChange (algebraBaseMap (ULift.{u} ℤ) k)).mapIso f⟩
  · rintro ⟨f⟩
    obtain ⟨ef⟩ := nonempty_rootDatumEquiv_of_iso
      (hG.isConnectedReductive_algebraMap k) (hH.isConnectedReductive_algebraMap k)
      (isSplitTorus_splitTorus I) (isSplitTorus_splitTorus I')
      (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hi k)
      (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I' H j hj k)
      f (hP.field k) (hQ.field k)
    let ePQ := CoordinateRootDatum.equivOfFieldRealizationEquiv k P Q ef
    obtain ⟨φ, -, -, -⟩ := affineSplitIsomorphismTheorem (ULift.{u} ℤ) G H hG hH I I' i j
      J J' P Q (htc.iso_comp e) hi hP
      (fun α => (hL α).map fun eR =>
        @Langlands.LinearAlgebra.liftedIntLinearEquivOfAddEquiv _ _ _ _
          (splitTorus.exponentWeightSpace I G i (P.root α)).module _
          (@LinearEquiv.toAddEquiv (ULift.{u} ℤ) (ULift.{u} ℤ) _ _ _ _ _ _ _ _ _ _
            ULift.module _ eR))
      (ht'c.iso_comp e') hj hQ
      (fun α => (hL' α).map fun eR =>
        @Langlands.LinearAlgebra.liftedIntLinearEquivOfAddEquiv _ _ _ _
          (splitTorus.exponentWeightSpace I' H j (Q.root α)).module _
          (@LinearEquiv.toAddEquiv (ULift.{u} ℤ) (ULift.{u} ℤ) _ _ _ _ _ _ _ _ _ _
            ULift.module _ eR))
      ePQ.symm
    exact ⟨φ⟩

end Langlands.GroupScheme
