import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.SplitRootDatumNeighbourhood
import Langlands.GroupScheme.Reductive.LocalSplitRootWeightFreeness
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Full root data and root lines over principal ideal domains -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

local instance fieldFibreAffine {R : Type u} [CommRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    {k : Type u} [Field k] [Algebra R k] :
    IsAffineHom ((baseChange (algebraBaseMap R k)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R k)))

/-- The full coordinate root datum of a fibrewise maximal split torus is
constant over the spectrum of a domain. -/
theorem exists_fibrewiseRootDatum_of_isDomain
    {R : Type u} [CommRing R] [IsDomain R]
    (I : Type u) [Fintype I]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i) :
    haveI := hG.isAffineHom
    ∃ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
      IsFibrewiseRootDatumOf I G i P := by
  classical
  let := hG.isAffineHom
  let := hG.smooth
  let S := Spec (CommRingCat.of R)
  let η := genericPoint S
  obtain ⟨J, hJ, P, U, hred, hU, hηU, -, hUP⟩ :=
    exists_open_coordinateRootDatum I G hG i hmax η
  let k := S.residueField η
  let φ := Spec.preimage (S.fromSpecResidueField η)
  let : Algebra R k := φ.hom.toAlgebra
  have hb : algebraBaseMap R k = S.fromSpecResidueField η := Spec.map_preimage _
  have hp : (algebraBaseMap R k) (IsLocalRing.closedPoint k) = η := by
    rw [hb]
    exact Scheme.fromSpecResidueField_apply _ _
  have hPk := hUP k (hp.symm ▸ hηU)
  refine ⟨J, P, hJ, hred, ?_⟩
  intro l _ _
  let s := (algebraBaseMap R l) (IsLocalRing.closedPoint l)
  obtain ⟨J', hJ', Q, V, -, hV, hsV, -, hVQ⟩ :=
    exists_open_coordinateRootDatum I G hG i hmax s
  have hηV : η ∈ V :=
    ((genericPoint_spec S).mem_open_set_iff hV).mpr ⟨s, Set.mem_univ _, hsV⟩
  have hQk := hVQ k (hp.symm ▸ hηV)
  have hQl := hVQ l hsV
  have hclosed := (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax k).2.1
  let e := Langlands.LinearAlgebra.rootDatumEquivOfFiniteOrderReflections Q P
    (CoordinateRootDatum.pairing_eq_of_fields I G i k Q k P hQk hPk)
    (CoordinateRootDatum.rootRange_eq_of_weightRanks I G i k Q k P hQk hPk
      (fun _ => rfl))
    (fun j' j _ => LocalSplitCorootTransport.isOfFinOrder_mul_of_isRealizedAt
      I G i k hclosed
      (LocalSplitCorootTransport.isRealizedAt_reflection I G i k Q hQk j')
      (LocalSplitCorootTransport.isRealizedAt_reflection I G i k P hPk j))
  exact CoordinateRootDatum.isRootDatumOf_of_identityEquiv l hQl e rfl rfl

/-- Each actual root weight module over a principal ideal domain is free
of rank one over that same ring. -/
theorem pidRootWeightSpace_nonempty_linearEquiv
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
    (hG : IsReductive G)
    (I : Type u) [Fintype I]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hi : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J) :
    Nonempty (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R]
      CommRingCat.of R) := by
  classical
  let := hG.smooth
  let W := splitTorus.exponentWeightSpace I G i (P.root α)
  let : Module.Finite R W := splitTorus.finite_exponentWeightSpace I G i (P.root α)
  let : Module.Projective R W := splitTorus.projective_exponentWeightSpace I G i (P.root α)
  let : Module.Flat R W := Module.Flat.of_projective
  let : Module.IsTorsionFree R W := Module.Flat.isTorsionFree
  let : Module.Free R W := Module.free_of_finite_type_torsion_free'
  let s := genericPoint (Spec (CommRingCat.of R))
  let k := (Spec (CommRingCat.of R)).residueField s
  let φ := Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)
  let : Algebra R k := φ.hom.toAlgebra
  let GK := (baseChange (algebraBaseMap R k)).obj G
  let iK := splitTorus.baseChangeHom (K := k) G I i
  have hGK : IsConnectedReductive GK :=
    hG.isConnectedReductive_baseChange (algebraBaseMap R k)
  have hiK : IsMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) iK :=
    splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hi k
  have hroot : splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (P.root α) ∈
      roots iK :=
    (hP.mem_roots_iff k (P.root α)).mpr ⟨α, rfl⟩
  obtain ⟨e⟩ := splitRootLieLine k GK hGK
    (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
    (isSplitTorus_splitTorus I) iK hiK _ hroot
  have hdim : Module.finrank k (splitTorus.exponentWeightSpace I GK iK (P.root α)) = 1 := by
    rw [splitTorus.exponentWeightSpace_eq_weightSpace_exponentCharacter]
    rw [← e.finrank_eq]
    exact Module.finrank_self k
  have hdimR : Module.finrank R W = 1 := by
    calc
      Module.finrank R W = Module.finrank k (k ⊗[R] W) :=
        Module.finrank_baseChange.symm
      _ = Module.finrank k (splitTorus.exponentWeightSpace I GK iK (P.root α)) :=
        (splitTorus.exponentWeightBaseChangeEquiv (K := k) G I i (P.root α)).finrank_eq
      _ = 1 := hdim
  obtain ⟨eR⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hdimR
  exact ⟨eR.symm⟩

/-- A chosen trivialization of an actual root weight module over the
original principal ideal domain. -/
def pidRootWeightSpaceEquiv
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
    (hG : IsReductive G)
    (I : Type u) [Fintype I]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hi : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J) :
    splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R]
      CommRingCat.of R :=
  Classical.choice (pidRootWeightSpace_nonempty_linearEquiv G hG I i hi P hP α)

end Langlands.GroupScheme
