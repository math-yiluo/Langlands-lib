import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeightedSynthesis
import Langlands.Representation.Plancherel.DynamicOppositeFullLeviContinuation
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Actual orbit packet data for the full Levi -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.Plancherel.DynamicOppositeCanonicalScalar

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  rationalWeightsIsAffine rationalWeightsTopology
  rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  {p : SemistandardSpectralIndex i} {hG : IsConnectedReductive G}
  (r : CocharacterPresentation hG p)
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom r.cocharacter ≫ i

open DynamicOppositeStandardIntertwining in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- At the full Levi, the source-normalized packet data at the specified
compact have constant continuations and irreducibility on the whole torus. -/
def OrbitPacketData.ofFullLevi (hM : RationalSemistandard.levi p = ⊤) :
    OrbitPacketData r π := by
  have hχ : DynamicOppositeStandardIntertwining.levi χ = ⊤ :=
    (congrArg (fun M : SubgroupFunctor G => M.carrier (Over.mk (𝟙 _))) r.levi_eq).trans hM
  have hP : DynamicOppositeStandardIntertwining.parabolic χ = ⊤ :=
    (DynamicOppositeStandardIntertwining.decomposition χ).parabolic_eq_top_of_levi_eq_top hχ
  have hQ : oppositeParabolic χ = ⊤ :=
    (oppositeDecomposition χ).parabolic_eq_top_of_levi_eq_top hχ
  let hPK (g : rationalPoints G) : ∃ x : DynamicOppositeStandardIntertwining.parabolic χ, ∃ k : K,
      g = (x : rationalPoints G) * (k : rationalPoints G) :=
    ⟨⟨g, hP.symm ▸ Subgroup.mem_top g⟩, 1, (mul_one g).symm⟩
  let hQK (g : rationalPoints G) : ∃ x : oppositeParabolic χ, ∃ k : K,
      g = (x : rationalPoints G) * (k : rationalPoints G) :=
    ⟨⟨g, hQ.symm ▸ Subgroup.mem_top g⟩, 1, (mul_one g).symm⟩
  let A := SmoothRep.pullback r.literalLeviHomeomorph π.obj
  have hA : A.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff π.obj.representation r.literalLeviHomeomorph).mpr
      π.property.1
  let hR := relativeRootReflectionExistence.{u}
  let hC := centralSplitTorusCharacter.{u}
  let forward := forwardContinuationOfLeviEqTop χ K hK A hR hC hG hPK hQK hχ
  let reverse := reverseContinuationOfLeviEqTop χ K hK A hR hC hG hPK hQK hχ
  let full : Set (unramifiedCharacters (normCharacters χ)) := Set.univ
  have hopen : IsOpen full := isOpen_univ
  have hne : full.Nonempty := ⟨1, Set.mem_univ _⟩
  have hf : full ⊆ forwardFullDomainRegion χ K hK A :=
    fun z _ => mem_forwardFullDomainRegion_of_levi_eq_top χ K hK A hχ z
  have hr : full ⊆ reverseFullDomainRegion χ K hK A :=
    fun z _ => mem_reverseFullDomainRegion_of_levi_eq_top χ K hK A hχ z
  have hirr (z : unramifiedCharacters (normCharacters χ)) (_ : z ∈ full) :
      (UnramifiedLeviInduction (DynamicOppositeStandardIntertwining.decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible :=
    unramifiedLeviInduction_isIrreducible_of_levi_eq_top χ A hG hχ hA z
  exact
    { reflection := hR
      centralCharacters := hC
      compact := K
      isCompact := hK
      factorization := hPK
      oppositeFactorization := hQK
      forward := forward
      reverse := reverse
      forwardDomain := full
      forwardOpen := hopen
      forwardNonempty := hne
      forwardContained := hf
      reverseDomain := full
      reverseOpen := hopen
      reverseNonempty := hne
      reverseContained := hr
      irreducibleDomain := full
      irreducibleOpen := hopen
      irreducibleNonempty := hne
      irreducible := hirr
      inverseRegular := rationalFunctionUnitaryRegular_inv_of_levi_eq_top
        i r.cocharacter hR hC hG K hK hPK hQK A forward reverse
        hopen hne hf hopen hne hr hopen hne hirr hχ }

end Langlands.HarishChandraSchwartz.RationalSemistandard
