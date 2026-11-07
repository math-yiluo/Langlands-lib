import Langlands.Representation.Geometric.NativeJacquetSupportAdmissibility
import Langlands.Representation.Geometric.RepresentedGeometricLemmaTargetInduction
import Langlands.Representation.Aubert.General.RationalPointSecondCountable
import Langlands.GroupScheme.Rational.ParabolicRootRadicals

/-! Exact dynamic-output fixed modules from actual finite orbit geometry. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct NNReal

namespace Langlands.GroupScheme.ParabolicRootPresentation

universe u

variable {F : Type u} [Field F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P N : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

include r in
/-- Any supplied geometric radical gives the actual multiplication isomorphism
with the original Levi; no new multiplication premise is needed. -/
theorem isIso_subgroupMultiplication_of_radical [Smooth G.X.hom] {n : N ⟶ P}
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n) :
    IsIso (subgroupMultiplication l n) := by
  let χ := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p
  have hP : (Dynamic.parabolic χ).IsRepresentedBy p :=
    ⟨r.isCompatible.parabolic.isClosedSubgroup.mono_overHom,
      r.parabolic_eq_splitComponentCocharacter⟩
  have hM : (Dynamic.centralizer χ).IsRepresentedBy (l ≫ p) :=
    ⟨(r.isCompatible.levi.isClosedSubgroup.comp
      r.isCompatible.parabolic.isClosedSubgroup).mono_overHom,
      r.levi_eq_splitComponentCocharacter⟩
  have hN : (Dynamic.unipotent χ).IsRepresentedBy (n ≫ p) :=
    ⟨(hn.1.isClosedSubgroup.comp r.isCompatible.parabolic.isClosedSubgroup).mono_overHom,
      r.range_comp_radical_eq hn⟩
  exact Dynamic.isIso_subgroupMultiplication hP hM hN l n rfl rfl

end Langlands.GroupScheme.ParabolicRootPresentation

namespace Langlands.Plancherel.UnramifiedNormalized

universe uL uI uG uV

variable {L : Type uL} [Group L] [TopologicalSpace L]
  {I : Type uI} (ν : I → (L →* ℝ≥0ˣ))
  {Γ : Type uG} [Group Γ] [TopologicalSpace Γ]
  [LocallyCompactSpace Γ] [NonarchimedeanGroup Γ]
  {V : Type uV} [AddCommGroup V] [Module (unramifiedRegularFunctions ν) V]

/-- Equality of the original radical and Levi subgroups transports admissibility
of the same normalized native quotient, including its exact half character. -/
theorem isAdmissible_jacquetRepresentation_of_subgroup_eq
    (ρ : Representation (unramifiedRegularFunctions ν) Γ V)
    {U M U' M' : Subgroup Γ} (hU : IsClosed (U : Set Γ))
    (hMU : M ≤ Subgroup.normalizer U) (hU' : IsClosed (U' : Set Γ))
    (hM'U' : M' ≤ Subgroup.normalizer U') (eU : U = U') (eM : M = M')
    (hρ : IsAdmissible (jacquetRepresentation ν ρ U M hU hMU)) :
    IsAdmissible (jacquetRepresentation ν ρ U' M' hU' hM'U') := by
  subst U'
  subst M'
  exact hρ

end Langlands.Plancherel.UnramifiedNormalized

namespace Langlands.Plancherel.RationalNormalized

open GroupScheme Aubert.General.RepresentedParabolic Induction
open Langlands.AlgebraicGeometry.PointTopology

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P N : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance geometryFiniteAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance geometryFinitePointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance geometryFiniteFieldT2 : T2Space F := BruhatTits.localField_t2Space F

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : N ⟶ P} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))
  {Q L U : GroupScheme (Spec (CommRingCat.of F))}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {nQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hnQ : LeviSubgroup.IsGeometricUnipotentRadical nQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ nQ)}
  {E : Type uV} [AddCommGroup E] [Module ℂ E]

local instance geometryFiniteRegularCommRing : CommRing (RegularAlgebra r) :=
  Subalgebra.toCommRing _
local instance geometryFiniteRegularAlgebra : Algebra ℂ (RegularAlgebra r) :=
  Subalgebra.algebra _
local instance geometryFiniteTensorAddCommGroup :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.addCommGroup
local instance geometryFiniteTensorModule :
    Module (RegularAlgebra r) (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.leftModule

/-- Actual finite ordered geometry for the source and represented output.
This record contains geometric data and original quotient compactness, with no
coefficient representation or finiteness assertion. -/
structure NativeJacquetFiniteOrbitGeometry where
  length : ℕ
  ordering : Geometric.OrderedDoubleCosets (pointImage p) (pointImage q) length
  intersection : ∀ i : Fin length, GeometricLemmaIntersectionDatum p l n
    r.isCompatible.parabolic hn r.isCompatible.levi
    (r.isIso_subgroupMultiplication_of_radical hn)
    q lQ nQ hq hnQ hlQ hmulQ (ordering.representative i)⁻¹
  realization : ∀ i : Fin length, (intersection i).DynamicRealization
  quotient_compact : ∀ i : Fin length, letI := leviPointTopology lQ hlQ;
    CompactSpace (LeftQuotient (pointImage (intersection i).q'))

set_option maxHeartbeats 800000 in
/-- The exact output action in the finiteness statement is admissible under
actual finite ordered orbit geometry and compactness of the original target
intersection parabolic quotients. -/
theorem outputJacquet_isAdmissible_of_geometry
    [CompactSpace (LeftQuotient (pointImage p))]
    (hG : IsConnectedReductive G) (hproj : Continuous h.projection)
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E)
    (hσ : IsAdmissible σ) (hcusp : IsSupercuspidal r σ)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hL : SubgroupFunctor.range (lQ ≫ q) = Dynamic.centralizer χ)
    (hN : SubgroupFunctor.range (nQ ≫ q) = Dynamic.unipotent χ)
    {m : ℕ} (t : Geometric.OrderedDoubleCosets (pointImage p) (pointImage q) m)
    (D : ∀ i : Fin m, GeometricLemmaIntersectionDatum p l n
      r.isCompatible.parabolic hn r.isCompatible.levi
      (r.isIso_subgroupMultiplication_of_radical hn)
      q lQ nQ hq hnQ hlQ hmulQ (t.representative i)⁻¹)
    (R : ∀ i : Fin m, (D i).DynamicRealization)
    (hcompact : ∀ i : Fin m, letI := leviPointTopology lQ hlQ;
      CompactSpace (LeftQuotient (pointImage (D i).q'))) :
    IsAdmissible (R := RegularAlgebra r) (outputJacquetRepresentation r h hU σ χ) := by
  let : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  let : SecondCountableTopology (rationalPoints G) :=
    Aubert.General.RationalPointFamily.reductiveRationalPoint_secondCountable F G hG
  let : SigmaCompactSpace (rationalPoints G) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have hK : ∀ i : Fin m, CompactSpace (LeftQuotient
      (Subgroup.comap
        (Subgroup.inclusion (Aubert.General.IsSemidirectDecomposition.levi_le
          (isSemidirectDecomposition_pointImage q lQ nQ hq.isClosedSubgroup hnQ hmulQ)))
        (D i).compactComparisonSaturation)) := by
    intro i
    rw [(D i).compactComparisonSaturation_comap_section]
    exact (D i).targetIntersectionQuotient_compactSpace (hcompact i)
  have hadm := universalNativeJacquet_isAdmissible r h hU hn
    (r.isIso_subgroupMultiplication_of_radical hn) hproj σ hσ hcusp t D R hK
  have eN : pointImage (nQ ≫ q) =
      BruhatTits.DynamicUnipotentContainment.unipotentPoints χ := by
    rw [pointImage_eq_range_carrier, hN]
  have eL : pointImage (lQ ≫ q) = outputLeviPoints χ := by
    rw [pointImage_eq_range_carrier, hL]
  exact UnramifiedNormalized.isAdmissible_jacquetRepresentation_of_subgroup_eq
    (parabolicLeviRationalNormCharacters r) (inducedRepresentation r h hU σ)
    (isClosed_pointImage_comp q nQ hq.isClosedSubgroup hnQ.1.isClosedSubgroup)
    (pointImage_le_normalizer q lQ nQ hnQ)
    (BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints χ)
    (Aubert.General.dynamic_isSemidirectDecomposition χ
      (Over.mk (𝟙 (Spec (CommRingCat.of F))))).levi_le_normalizer eN eL hadm

set_option maxHeartbeats 800000 in
/-- Finite generation of the unchanged compact-open fixed module, over the
complete rational-norm coefficient algebra, follows from actual orbit geometry. -/
theorem outputJacquet_fixedModule_finite_of_geometry
    [CompactSpace (LeftQuotient (pointImage p))]
    (hG : IsConnectedReductive G) (hproj : Continuous h.projection)
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E)
    (hσ : IsAdmissible σ) (hcusp : IsSupercuspidal r σ)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hL : SubgroupFunctor.range (lQ ≫ q) = Dynamic.centralizer χ)
    (hN : SubgroupFunctor.range (nQ ≫ q) = Dynamic.unipotent χ)
    {m : ℕ} (t : Geometric.OrderedDoubleCosets (pointImage p) (pointImage q) m)
    (D : ∀ i : Fin m, GeometricLemmaIntersectionDatum p l n
      r.isCompatible.parabolic hn r.isCompatible.levi
      (r.isIso_subgroupMultiplication_of_radical hn)
      q lQ nQ hq hnQ hlQ hmulQ (t.representative i)⁻¹)
    (R : ∀ i : Fin m, (D i).DynamicRealization)
    (hcompact : ∀ i : Fin m, letI := leviPointTopology lQ hlQ;
      CompactSpace (LeftQuotient (pointImage (D i).q')))
    (J : OpenSubgroup (outputLeviPoints χ)) :
    Module.Finite (RegularAlgebra r)
      (fixedVectors (outputJacquetRepresentation r h hU σ χ) J.toSubgroup) :=
  (outputJacquet_isAdmissible_of_geometry r hn h hU hG hproj σ hσ hcusp
    χ hL hN t D R hcompact).2 J

end Langlands.Plancherel.RationalNormalized
