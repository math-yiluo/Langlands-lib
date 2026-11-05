import Langlands.Representation.Plancherel.CompactIntertwiningParameterContinuity
import Langlands.Representation.Plancherel.RationalUnramifiedVectorCancellation
import Langlands.Representation.Plancherel.UnramifiedOperatorTransport
import Langlands.Representation.Plancherel.ParabolicPointIntertwiningRegion

/-! # Scalar tests and local domination for actual compact standard operators -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Topology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily

universe u uG uI uV uW uJ

section CompactTests

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (K : OpenSubgroup G)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

/-- Evaluate a compact section at a compact point, then apply a smooth
functional of the original inducing representation. -/
def compactPictureScalarTests (j : K × Langlands.SmoothDual A.representation) :
    CompactInductionPicture h K A →ₗ[ℂ] ℂ where
  toFun f := j.2.val (eval _ _ f j.1)
  map_add' _ _ := j.2.val.map_add _ _
  map_smul' c _ := j.2.val.map_smul c _

/-- Closedness of the actual Levi supplies smooth-dual separation of these
point evaluations. No topology on the compact-picture carrier is used. -/
theorem compactPictureScalarTests_separates (hM : IsClosed (M : Set G))
    (f g : CompactInductionPicture h K A)
    (hfg : ∀ j, compactPictureScalarTests h K A j f =
      compactPictureScalarTests h K A j g) : f = g := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  apply smoothBidual_injective_of_compact_cofinal (compactCofinal hM)
    A.representation A.property
  apply Subtype.ext
  apply LinearMap.ext
  intro ℓ
  exact hfg (k, ℓ)

end CompactTests

section CompactContinuity

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  (U' : Subgroup G)
  [MeasurableSpace (QuotientSpace (U := U) U')]
  (qν : Measure (QuotientSpace (U := U) U'))

/-- Every fixed compact section, compact point and original smooth functional
has an integrable bound uniform in a neighborhood of each parameter in Ω. -/
def CompactIntegralLocallyDominatedOn (Ω : Set (unramifiedCharacters ν)) : Prop :=
  ∀ (f : CompactInductionPicture h K A) (k : K)
    (ℓ : Langlands.SmoothDual A.representation) (χ₀ : Ω),
    ∃ bound : QuotientSpace (U := U) U' → ℝ,
      Integrable bound qν ∧
      ∀ᶠ χ : Ω in 𝓝 χ₀, ∀ᵐ q ∂qν,
        ‖ℓ.val (unramifiedCompactIntegrand h hU hδ K hP hK hPK ν hν hr A U'
          f k χ.val q)‖ ≤ bound q

variable {P' : Subgroup G}
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  (hδ' : IsUnimodularModulus U' hU') (hP' : IsClosed (P' : Set G))
  (hP'K : ∀ g : G, ∃ p : P', ∃ k : K, g = (p : G) * (k : G))
  (hr' : Continuous h'.projection)
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [BorelSpace (QuotientSpace (U := U) U')] [T2Space G]
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI qν)
  (hM : IsClosed (M : Set G)) (hsq : SquaredModulusCompatibility h hU h' hU')

/-- Full convergence and explicit local domination imply continuity under
the separating scalar tests of the actual target compact picture. -/
theorem standardCompactOperator_isWeaklyContinuousOn_of_dominated
    [FirstCountableTopology (unramifiedCharacters ν)]
    (Ω : Set (unramifiedCharacters ν))
    (hfull : ∀ χ : Ω, domain h hU U'
      (A.twist χ.val.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ.val)) qν = ⊤)
    (hdom : CompactIntegralLocallyDominatedOn h hU hδ K hP hK hPK ν hν hr A U' qν Ω)
    (f : CompactInductionPicture h K A) :
    IsWeaklyContinuousOn (compactPictureScalarTests h' K A)
      (fun χ : Ω => standardCompactOperator h hU hδ K hP hK hPK ν hν hr
        h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq χ.val A (hfull χ) f) := by
  rintro ⟨k, ℓ⟩
  apply continuous_iff_continuousAt.mpr
  intro χ₀
  obtain ⟨bound, hint, hbound⟩ := hdom f k ℓ χ₀
  exact continuousAt_standardCompactOperator_scalar_of_dominated h hU hδ K hP hK hPK
    ν hν hr A h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq
    (fun χ : Ω => χ.val) continuous_subtype_val.continuousAt hfull f k ℓ hbound hint

end CompactContinuity

section ActualTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (H : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints H)]
  (hp : Continuous (rationalValuationImageProjection H))
  (hH : GroupScheme.IsConnectedReductive H)

include hp hH in
/-- The full actual character space is first countable, by its existing
matching finite complex-torus homeomorphism. -/
theorem firstCountableTopology_rationalUnramifiedCharacters :
    FirstCountableTopology
      (unramifiedCharacters (fun ψ => (rationalNormCharacters H ψ).toMul)) := by
  have : FirstCountableTopology ℂˣ := Units.isEmbedding_val₀.firstCountableTopology
  let e := (rationalImageUnramifiedContinuousEquiv H hp).symm.trans
    (rationalReductiveImageCharacterCoordinates H hH)
  exact e.toHomeomorph.isEmbedding.firstCountableTopology

variable (hdiv : RationalUnramifiedLocalHypersurfaceDivisibilityStatement.{u})
  {L : Type uG} [Group L] [TopologicalSpace L]
  (e : GroupScheme.rationalPoints H ≃ₜ* L)

include hp hH in
/-- First countability transports to the pulled-back full rational norm family. -/
theorem firstCountableTopology_transportedRationalUnramifiedCharacters :
    FirstCountableTopology (unramifiedCharacters
      (fun ψ => (rationalNormCharacters H ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)) := by
  have := firstCountableTopology_rationalUnramifiedCharacters H hp hH
  exact (unramifiedCharactersHomeomorph e
    (fun ψ => (rationalNormCharacters H ψ).toMul)).symm.toHomeomorph.isEmbedding.firstCountableTopology

include hp hH hdiv in
/-- Conditional weak cancellation on an arbitrary open subset of the characters
of a point group isomorphic to the actual rational points. The same transported
denominator is chosen before every source vector. -/
theorem transported_isRationalOperatorOn_of_weak_continuity
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W] {J : Type uJ}
    (tests : J → W →ₗ[ℂ] ℂ)
    (hsep : ∀ x y : W, (∀ j, tests j x = tests j y) → x = y)
    {Ω : Set (unramifiedCharacters
      (fun ψ => (rationalNormCharacters H ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom))}
    (hΩ : IsOpen Ω)
    (b : unramifiedRegularFunctions
      (fun ψ => (rationalNormCharacters H ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom))
    (hb : b ≠ 0) (T : Ω → V →ₗ[ℂ] W)
    (hcont : ∀ v, IsWeaklyContinuousOn tests (fun χ => T χ v))
    (hpoly : IsPolynomialOperatorOn Ω (fun χ => b.val χ.val • T χ)) :
    IsRationalOperatorOn Ω T := by
  apply (isRationalOperatorOn_transport_iff e
    (fun ψ => (rationalNormCharacters H ψ).toMul) Ω T).mp
  refine rationalUnramified_isRationalOperatorOn_of_weak_continuity H hp hH hdiv tests hsep
    (show IsOpen ((unramifiedCharactersHomeomorph e
        (fun ψ => (rationalNormCharacters H ψ).toMul)) ⁻¹' Ω) from
      hΩ.preimage (unramifiedCharactersHomeomorph e
        (fun ψ => (rationalNormCharacters H ψ).toMul)).continuous)
    ((unramifiedRegularFunctionsEquiv e (fun ψ => (rationalNormCharacters H ψ).toMul)).symm b)
    ((map_ne_zero_iff _ (AlgEquiv.injective _)).mpr hb) _ ?_ ?_
  · intro v j
    exact (hcont v j).comp
      (((unramifiedCharactersHomeomorph e
        (fun ψ => (rationalNormCharacters H ψ).toMul)).continuous.comp
          continuous_subtype_val).subtype_mk _)
  · simpa only [unramifiedRegularFunctionsEquiv_symm_apply,
      unramifiedParameterPreimageEquiv_apply] using
        (isPolynomialOperatorOn_transport_iff e (fun ψ => (rationalNormCharacters H ψ).toMul) Ω
          (fun χ => b.val χ.val • T χ)).mpr hpoly

end ActualTopology

section LiteralLevi

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)
  (hdiv : RationalUnramifiedLocalHypersurfaceDivisibilityStatement.{u})

local instance compactWeakRegularityAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance compactWeakRegularityAmbientPointTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance compactWeakRegularityLeviPointTopology :
    TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X

include r in
/-- The full rational norm family on the literal Levi point subgroup has a
first-countable character space. -/
theorem firstCountableTopology_parabolicLeviUnramifiedCharacters :
    FirstCountableTopology
      (unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :=
  firstCountableTopology_transportedRationalUnramifiedCharacters M
    (continuous_rationalValuationImageProjection M) r.isCompatible.levi.isConnectedReductive
    (parabolicLeviPointHomeomorph r)

include r hdiv in
/-- Conditional weak cancellation for the full rational norm family on the
literal Levi point subgroup, on an arbitrary open parameter subset. -/
theorem parabolicLevi_isRationalOperatorOn_of_weak_continuity
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W] {J : Type uJ}
    (tests : J → W →ₗ[ℂ] ℂ)
    (hsep : ∀ x y : W, (∀ j, tests j x = tests j y) → x = y)
    {Ω : Set (unramifiedCharacters (parabolicLeviRationalNormCharacters r))}
    (hΩ : IsOpen Ω)
    (b : unramifiedRegularFunctions (parabolicLeviRationalNormCharacters r))
    (hb : b ≠ 0) (T : Ω → V →ₗ[ℂ] W)
    (hcont : ∀ v, IsWeaklyContinuousOn tests (fun χ => T χ v))
    (hpoly : IsPolynomialOperatorOn Ω (fun χ => b.val χ.val • T χ)) :
    IsRationalOperatorOn Ω T :=
  transported_isRationalOperatorOn_of_weak_continuity M
    (continuous_rationalValuationImageProjection M) r.isCompatible.levi.isConnectedReductive
    hdiv (parabolicLeviPointHomeomorph r) tests hsep hΩ b hb T hcont hpoly

section Compact

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [T2Space (rationalPoints G)]
  {Ppt Upt P'pt U'pt : Subgroup (rationalPoints G)}
  (h : IsSemidirectDecomposition Ppt (parabolicLeviPointSubgroup p l) Upt)
  (hU : IsClosed (Upt : Set (rationalPoints G))) (hδ : IsUnimodularModulus Upt hU)
  (K : OpenSubgroup (rationalPoints G)) (hP : IsClosed (Ppt : Set (rationalPoints G)))
  (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : ∀ g : rationalPoints G, ∃ p : Ppt, ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (hr : Continuous h.projection)
  (h' : IsSemidirectDecomposition P'pt (parabolicLeviPointSubgroup p l) U'pt)
  (hU' : IsClosed (U'pt : Set (rationalPoints G))) (hδ' : IsUnimodularModulus U'pt hU')
  (hP' : IsClosed (P'pt : Set (rationalPoints G)))
  (hP'K : ∀ g : rationalPoints G, ∃ p : P'pt, ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (hr' : Continuous h'.projection)
  [MeasurableSpace U'pt] [BorelSpace U'pt]
  [MeasurableSpace (Upt.subgroupOf U'pt)] [BorelSpace (Upt.subgroupOf U'pt)]
  [MeasurableSpace (QuotientSpace (U := Upt) U'pt)]
  [BorelSpace (QuotientSpace (U := Upt) U'pt)]
  (qν : Measure (QuotientSpace (U := Upt) U'pt))
  (μU' : Measure U'pt) (μI : Measure (Upt.subgroupOf U'pt))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hqν : QuotientIntegration.IsCompatible (Upt.subgroupOf U'pt) μU' μI qν)
  (hsq : SquaredModulusCompatibility h hU h' hU')

include hdiv in
/-- Conditional on local hypersurface divisibility, local integrable domination
on an open subset and one nonzero regular numerator for the whole actual
compact standard operator give the literal compact rationality predicate. -/
theorem parabolicLevi_standardCompactRationalOn_of_dominated
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    {Ω : Set (unramifiedCharacters (parabolicLeviRationalNormCharacters r))}
    (hΩ : IsOpen Ω)
    (hfull : ∀ χ : Ω, domain h hU U'pt
      (π.twist χ.val.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters r) χ.val)) qν = ⊤)
    (hdom : CompactIntegralLocallyDominatedOn h hU hδ K hP hK hPK
      (parabolicLeviRationalNormCharacters r) (continuous_parabolicLeviRationalNormCharacters r)
      hr π U'pt qν Ω)
    (b : unramifiedRegularFunctions (parabolicLeviRationalNormCharacters r)) (hb : b ≠ 0)
    (hpoly : IsPolynomialOperatorOn Ω (fun χ => b.val χ.val •
      standardCompactOperator h hU hδ K hP hK hPK (parabolicLeviRationalNormCharacters r)
        (continuous_parabolicLeviRationalNormCharacters r) hr h' hU' hδ' hP' hP'K hr'
        qν μU' μI hqν (isClosed_parabolicLeviPointSubgroup r) hsq χ.val π (hfull χ))) :
    StandardCompactRationalOn h hU hδ K hP hK hPK (parabolicLeviRationalNormCharacters r)
      (continuous_parabolicLeviRationalNormCharacters r) hr h' hU' hδ' hP' hP'K hr'
      qν μU' μI hqν (isClosed_parabolicLeviPointSubgroup r) hsq Ω π hfull := by
  have := firstCountableTopology_parabolicLeviUnramifiedCharacters r
  exact parabolicLevi_isRationalOperatorOn_of_weak_continuity r hdiv
    (compactPictureScalarTests h' K π)
    (compactPictureScalarTests_separates h' K π (isClosed_parabolicLeviPointSubgroup r))
    hΩ b hb _
    (standardCompactOperator_isWeaklyContinuousOn_of_dominated h hU hδ K hP hK hPK
      (parabolicLeviRationalNormCharacters r) (continuous_parabolicLeviRationalNormCharacters r)
      hr π U'pt qν h' hU' hδ' hP' hP'K hr' μU' μI hqν
      (isClosed_parabolicLeviPointSubgroup r) hsq Ω hfull hdom)
    hpoly

end Compact

end LiteralLevi

end Langlands.Plancherel
