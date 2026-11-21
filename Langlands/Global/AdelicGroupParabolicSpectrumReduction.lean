import Langlands.Global.AdelicSpectralDecompositionReduction
import Langlands.Global.AdelicEisensteinRationalCosets
import Langlands.Global.AdelicEisensteinImaginaryContinuation
import Langlands.Global.AdelicLogSection
import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.GroupScheme.Rational.FullParabolicLevi
import Langlands.GroupScheme.Rational.ParabolicCharacterLattice

/-! # The packets of the whole group: reduction to square-integrable automorphic forms

For a presented standard parabolic `p : P → G` that is an isomorphism, the wave packets of
`IsRelativeWavePacket` are exactly the finite linear combinations of elements of Lapid's `A²_P`
(Lapid 2011, §2, p.311). So `parabolicSpectrum` is the closed span of these combinations, and
`GroupParabolicSpectrumStatement` follows from `GroupSquareIntegrableFormSpectrumStatement`,
Lapid's density of `A²_G` in `L²_disc(A_G G(F) \ G(𝔸))`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Roots

variable {F : Type} [Field F] [NumberField F] {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G P M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
/-- For a full presented parabolic, the split component `A ⊆ M ≅ G` is central in `G`. -/
theorem _root_.Langlands.GroupScheme.ParabolicRootPresentation.isCentral_of_isIso
    (r : ParabolicRootPresentation p l a) [IsIso p] (hG : IsConnectedReductive G) :
    IsCentral (a ≫ l ≫ p) := by
  have := r.isCompatible.levi.isIso_of_isIso_parabolic (p := p) hG
  exact r.isCompatible.splitComponent.isCentralSplitTorus.isCentral.comp_iso (asIso (l ≫ p))

omit [NumberField F] in
/-- For a full presented parabolic, no root of `A` occurs in the unipotent radical, so every
complex parameter is regular. -/
theorem _root_.Langlands.GroupScheme.ParabolicRootPresentation.unipotentRoots_eq_empty_of_isIso
    (r : ParabolicRootPresentation p l a) [IsIso p] (hG : IsConnectedReductive G) :
    r.unipotentRoots = ∅ := by
  have hc : IsCentral (CommGroupScheme.groupHom r.data.f ≫ r.data.i) := by
    rw [r.isCompatible.factor_comp]
    exact r.isCentral_of_isIso hG
  have hA : IsSplitTorus A.toGrp := r.isCompatible.splitComponent.1.1.1
  ext α
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨h0, χ, hχ, rfl⟩
  exact h0 (root_restrict_eq_zero_of_isCentral r.data.i r.data.f hA hc hχ.1)

end Roots

namespace AdelicGroupPoints

section Eisenstein

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
  {K : Subgroup (AdelicGroupPoints F G)}

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- If `p` is an isomorphism, every principal rational point of `G` is the image of one of `P`. -/
theorem map_rational_inv_of_isIso [IsIso p] (w : RationalGroupPoints F G) :
    map F P G p (rational F P (G.affinePointsTarget (inv p) (CommAlgCat.of F F) w)) =
      rational F G w := by
  have h := DFunLike.congr_fun (rational_naturality F G (inv p)) w
  simp only [MonoidHom.comp_apply] at h
  rw [h]
  simp only [map_apply, GroupScheme.affinePointsTarget_apply, Category.assoc,
    ← Grp.comp_hom_hom, IsIso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- If `p` is an isomorphism, `P(F) \ G(F)` has at most one point. -/
theorem subsingleton_parabolicRationalCosets_of_isIso [IsIso p] :
    Subsingleton (ParabolicRationalCosets F p) := by
  refine ⟨fun c d => ?_⟩
  induction c using Quotient.inductionOn with | h x => ?_
  induction d using Quotient.inductionOn with | h y => ?_
  refine Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)
  obtain ⟨w, hw⟩ := (y * x⁻¹).2
  rw [parabolicRationalSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  exact ⟨_, ⟨_, rfl⟩, (map_rational_inv_of_isIso w).trans hw⟩

/-- The Eisenstein series of a full parabolic has one term: for `φ` left invariant under
`U(𝔸) M(F)`, `E(g, φ, λ) = φ(g) m_P(g)^λ`. -/
theorem IsIwasawaCompact.eisensteinSeries_of_isIso (hK : IsIwasawaCompact p K) [IsIso p]
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (hl : IsRationalLeviSubgroup l) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.eisensteinSeries φ lam g = φ g * hK.heightPower lam g := by
  have := subsingleton_parabolicRationalCosets_of_isIso (F := F) (p := p)
  let c₀ : ParabolicRationalCosets F p := Quotient.mk _ 1
  rw [IsIwasawaCompact.eisensteinSeries,
    tsum_eq_single c₀ (fun c hc => (hc (Subsingleton.elim c c₀)).elim),
    hK.eisensteinTerm_eq_of_representative hφ hl hU lam g c₀ 1 rfl]
  simp [IsIwasawaCompact.parameterTwist]

/-- At `λ = 0` the Eisenstein series of a full parabolic is the function itself. -/
theorem IsIwasawaCompact.eisensteinSeries_zero_of_isIso (hK : IsIwasawaCompact p K) [IsIso p]
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (hl : IsRationalLeviSubgroup l) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (g : AdelicGroupPoints F G) :
    hK.eisensteinSeries φ 0 g = φ g := by
  rw [hK.eisensteinSeries_of_isIso hφ hl hU]
  simp [IsIwasawaCompact.heightPower]

/-- The Eisenstein series of a full parabolic is entire in linear coordinates. -/
theorem IsIwasawaCompact.isMeromorphicInCoordinatesOn_eisensteinSeries_of_isIso
    (hK : IsIwasawaCompact p K) [IsIso p] [FiniteDimensional ℂ (ComplexCharacterParameter F P)]
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (hl : IsRationalLeviSubgroup l) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (g : AdelicGroupPoints F G) :
    IsMeromorphicInCoordinatesOn (fun lam => hK.eisensteinSeries φ lam g) Set.univ := by
  refine ⟨inferInstance, fun n e => ?_⟩
  let L : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun s => complexParameterPairing F P (e s) (hK.height g)
      map_add' := fun x y => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun c x => by
        simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hfun : (fun lam => hK.eisensteinSeries φ lam g) ∘ e =
      fun s => φ g * Complex.exp (L s) := by
    funext s
    simp only [Function.comp_apply, hK.eisensteinSeries_of_isIso hφ hl hU,
      IsIwasawaCompact.heightPower]
    rfl
  have hL : Differentiable ℂ L := by
    simpa using (LinearMap.toContinuousLinearMap L).differentiable
  have hdiff : Differentiable ℂ (fun s => φ g * Complex.exp (L s)) :=
    (differentiable_const _).mul hL.cexp
  have hhol : ∀ W : Set (Fin n → ℂ),
      IsHolomorphicOn 𝓘(ℂ, Fin n → ℂ) (fun s => φ g * Complex.exp (L s)) W := fun W q =>
    mdifferentiableOn_iff_differentiableOn.2 (q.differentiable.comp hdiff).differentiableOn
  rw [hfun, Set.preimage_univ]
  exact ⟨isOpen_univ, dense_univ, hhol _, fun s₀ => ⟨Set.univ, isOpen_univ, isConnected_univ,
    Set.mem_univ _, fun _ => 1, fun s => φ g * Complex.exp (L s), mdifferentiableOn_const,
    ⟨s₀, Set.mem_univ _, one_ne_zero⟩, hhol _, fun s _ => one_smul ℂ _⟩⟩

end Eisenstein

end AdelicGroupPoints

section Parameters

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
/-- The real pairing `X^*(P) ⊗ ℝ × Hom(X^*(P), ℝ) → ℝ` is nondegenerate on the left when
`X^*(P)` is free: the coordinates of `w` in a base-changed basis are pairings with the dual
basis. -/
theorem realParameterPairing_left_eq_zero {P : GroupScheme (Spec (CommRingCat.of F))}
    [Module.Free ℤ (rationalCharacters P)] (w : RealCharacterParameter F P)
    (h : ∀ H : RealCharacterDual F P, realParameterPairing F P w H = 0) : w = 0 := by
  classical
  let b := Module.Free.chooseBasis ℤ (rationalCharacters P)
  let b' := b.baseChange ℝ
  let dual : Module.Free.ChooseBasisIndex ℤ (rationalCharacters P) → RealCharacterDual F P :=
    fun i => (Int.castAddHom ℝ).comp (b.coord i).toAddMonoidHom
  have hrepr : ∀ (i : Module.Free.ChooseBasisIndex ℤ (rationalCharacters P))
      (z : RealCharacterParameter F P), realParameterPairing F P z (dual i) = b'.repr z i := by
    intro i z
    induction z using TensorProduct.inductionOn with
    | tmul t χ =>
      rw [realParameterPairing_tmul, Module.Basis.baseChange_repr_tmul]
      change t * ((b.coord i χ : ℤ) : ℝ) = b.repr χ i • t
      rw [Module.Basis.coord_apply, zsmul_eq_mul, mul_comm]
    | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, map_add, Finsupp.add_apply]
  apply b'.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply, ← hrepr]
  exact h _

variable {G P M : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

omit [IsAffineHom G.X.hom] [IsAffine P.X.left] in
/-- If `p` is an isomorphism, `H_P` maps the points of `P(𝔸)` lying over `A_G` onto
`Hom(X^*(P), ℝ)`: the split centre already realizes every real functional. -/
theorem exists_characterLog_of_isIso [IsIso p] (hG : IsConnectedReductive G)
    (H : RealCharacterDual F P) :
    ∃ x : AdelicGroupPoints F P,
      map F P G p x ∈ RestrictionSplitCentre.canonicalSubgroup F G ∧ characterLog F P x = H := by
  obtain ⟨I, hI, ⟨e⟩⟩ := (RestrictionSplitCentre.isSplitComponent_canonicalComponent F G).1.1.1
  have := Fintype.ofFinite I
  have := RestrictionSplitCentre.canonical_finiteIndex F G hG
  have hi := RestrictionSplitCentre.canonical_characterRestrict_injective F G
    centralSplitTorusCharacter hG
  let y := PositiveRealTorus.logSection F G (RestrictionSplitCentre.canonicalTorus F G)
    (RestrictionSplitCentre.canonicalComponent F G) hi I e
    (Multiplicative.ofAdd (realCharacterDualMap F P G p H))
  have hy : characterLog F G y = realCharacterDualMap F P G p H :=
    congrArg Multiplicative.toAdd (PositiveRealTorus.characterLogHom_logSection F G _ _ hi I e _)
  have hmap : map F P G p (map F G P (inv p) y) = y := by
    simp only [map_apply, GroupScheme.affinePointsTarget_apply, Category.assoc,
      ← Grp.comp_hom_hom, IsIso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  refine ⟨map F G P (inv p) y, ?_, ?_⟩
  · rw [hmap, RestrictionSplitCentre.canonicalSubgroup_eq_imageSubgroup,
      ← PositiveRealTorus.logSection_range F G _ _ hi I e]
    exact ⟨_, rfl⟩
  · rw [characterLog_map, hy]
    apply AddMonoidHom.ext
    intro χ
    change H (characterRestrict p (characterRestrict (inv p) χ)) = H χ
    rw [← AddMonoidHom.comp_apply (characterRestrict p), ← characterRestrict_comp,
      IsIso.hom_inv_id, characterRestrict_id, AddMonoidHom.id_apply]

/-- For a full presented parabolic, `(𝔞_M^G)^* = 0`. -/
theorem relativeParameterSpace_eq_bot_of_isIso (r : ParabolicRootPresentation p l a) [IsIso p]
    (hG : IsConnectedReductive G) : relativeParameterSpace (F := F) p = ⊥ := by
  have := (r.rationalCharacters_free_finite hG).1
  refine (Submodule.eq_bot_iff _).mpr fun w hw => realParameterPairing_left_eq_zero w fun H => ?_
  obtain ⟨x, hx, rfl⟩ := exists_characterLog_of_isIso (p := p) hG H
  have h := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hw x) hx
  rwa [LinearMap.mem_ker, LinearMap.flip_apply] at h

theorem subsingleton_relativeParameterSpace_of_isIso (r : ParabolicRootPresentation p l a)
    [IsIso p] (hG : IsConnectedReductive G) :
    Subsingleton (relativeParameterSpace (F := F) p) :=
  ⟨fun x y => Subtype.ext (by
    have hb := (Submodule.eq_bot_iff _).mp (relativeParameterSpace_eq_bot_of_isIso r hG)
    rw [hb x x.2, hb y y.2])⟩

end Parameters

/-- Integration against `spectralMeasure 0`, the unit mass on the one-point space `ℝ⁰`. -/
theorem integral_spectralMeasure_zero (f : (Fin 0 → ℝ) → ℂ) :
    ∫ x, f x ∂(spectralMeasure 0) = f 0 := by
  have hf : f = fun _ => f 0 := funext fun x => congrArg f (Subsingleton.elim x 0)
  rw [hf, integral_const]
  simp [spectralMeasure, Measure.real, Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]

section Spectrum

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]

/-- The closure in `L²([G])` of the span of the classes `y ↦ ∑ j, c j · v j (y.out)` of finite
linear combinations of elements `v j` of Lapid's `A²_P` (`IsSquareIntegrableInducedForm`).
For `P = G` these are the square-integrable automorphic forms on `[G]`. -/
def squareIntegrableFormSpectrum (K : Subgroup (AdelicGroupPoints F G))
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (p : P ⟶ G) (iU : U ⟶ P) (l : M ⟶ P) :
    Submodule ℂ (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)) :=
  (Submodule.span ℂ {f : Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G) |
    ∃ (k : ℕ) (v : Fin k → AdelicGroupPoints F G → ℂ) (c : Fin k → ℂ),
      (∀ j, IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l (v j)) ∧
        f =ᵐ[RestrictionSplitCentre.canonicalMeasure F G]
          fun y => ∑ j, c j * v j y.out}).topologicalClosure

variable [IsAffineHom G.X.hom] [IsAffine U.X.left] {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  {K : Subgroup (AdelicGroupPoints F G)}

omit [IsAffine U.X.left] in
/-- For a full presented parabolic, the wave packets are exactly the finite linear combinations
of elements of `A²_P`, so `L²_P([G])` is `squareIntegrableFormSpectrum`. -/
theorem parabolicSpectrum_eq_squareIntegrableFormSpectrum_of_isIso (hK : IsIwasawaCompact p K)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (hG : IsConnectedReductive G) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) [IsIso p] :
    parabolicSpectrum hK rho hsmooth hcalc iU l r hA hT =
      squareIntegrableFormSpectrum K hK.isCompact rho hsmooth hcalc p iU l := by
  have hl : IsRationalLeviSubgroup l := r.isCompatible.levi
  have := subsingleton_relativeParameterSpace_of_isIso (F := F) r hG
  have hzero : ∀ {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] relativeParameterSpace (F := F) p) (x : Fin n → ℝ),
      imaginaryParameter F P (e x : RealCharacterParameter F P) = 0 := by
    intro n e x
    rw [Subsingleton.elim (e x) 0, Submodule.coe_zero, map_zero]
  refine congrArg (fun s => (Submodule.span ℂ s).topologicalClosure) (Set.ext fun f => ?_)
  constructor
  · rintro ⟨Θ, ⟨n, e, k, v, c, E, D, hv, -, -, -, hreg, rfl⟩, hf⟩
    have hn : n = 0 := by
      have h1 := e.finrank_eq
      rwa [Module.finrank_fin_fun, Module.finrank_zero_of_subsingleton] at h1
    subst hn
    have hE : ∀ j lam, E j lam = hK.eisensteinSeries (v j) lam := by
      intro j lam
      obtain ⟨R, hR⟩ := hreg j
      exact hR lam fun α hα => by simp [r.unipotentRoots_eq_empty_of_isIso hG] at hα
    refine ⟨k, v, fun j => c j 0, hv, hf.trans (Filter.Eventually.of_forall fun y => ?_)⟩
    change ∫ x, ∑ j, c j x * E j (imaginaryParameter F P (e x : RealCharacterParameter F P))
      y.out ∂(spectralMeasure 0) = ∑ j, c j 0 * v j y.out
    rw [integral_spectralMeasure_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hzero, hE, hK.eisensteinSeries_zero_of_isIso (hv j).1.1 hl hU]
  · rintro ⟨k, v, c, hv, hf⟩
    have := finiteDimensional_complexCharacterParameter r hG
    let e : (Fin 0 → ℝ) ≃ₗ[ℝ] relativeParameterSpace (F := F) p := LinearEquiv.ofSubsingleton _ _
    refine ⟨fun g => ∑ j, c j * v j g, ⟨0, e, k, v, fun j _ => c j,
      fun j => hK.eisensteinSeries (v j), Set.univ, hv,
      fun j => ⟨contDiff_const, (Set.toFinite _).isCompact⟩, Set.subset_univ _,
      fun j g => hK.isMeromorphicInCoordinatesOn_eisensteinSeries_of_isIso (hv j).1.1 hl hU g,
      fun j => ⟨0, fun _ _ => rfl⟩, ?_⟩, hf⟩
    funext g
    rw [integral_spectralMeasure_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hzero]
    show _ = c j * hK.eisensteinSeries (v j) 0 g
    rw [hK.eisensteinSeries_zero_of_isIso (hv j).1.1 hl hU]

end Spectrum

section Statement

/-- Lapid's density of `A²_G` in the discrete spectrum (Lapid 2011, §2, p.311, for `P = G`:
"we can view `A²_P` as a dense subspace of `Ind_{P(𝔸)}^{G(𝔸)} L²_disc(A_M M \ M(𝔸))`").
For a presented parabolic `p : P → G` of a connected reductive group that is an isomorphism,
the closure in `L²([G])` of the span of the classes of finite linear combinations of elements of
`A²_P` is the discrete spectrum `discreteSpectrum F G hG`. -/
def GroupSquareIntegrableFormSpectrumStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G)
    (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (P M U : GroupScheme (Spec (CommRingCat.of F)))
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
      (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
      (a : A.toGrp ⟶ M), ParabolicRootPresentation p l a →
      haveI : LocallyOfFiniteType P.X.hom :=
        IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
      LeviSubgroup.IsGeometricUnipotentRadical iU →
      ∀ hK : IsIwasawaCompact p K, IsIso p →
        squareIntegrableFormSpectrum K hK.isCompact rho hsmooth hcalc p iU l =
          discreteSpectrum F G hG

end Statement

/-- `GroupParabolicSpectrumStatement` from Lapid's density of `A²_G` in `L²_disc([G])`. -/
theorem groupParabolicSpectrum_of_squareIntegrableFormSpectrum
    (h : GroupSquareIntegrableFormSpectrumStatement) : GroupParabolicSpectrumStatement := by
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho P₀ _ p₀ _ hP₀ hK₀ P M U A _ _ _ _ p _
    iU l a r _ _ _ hA hT h₀ hU hK hp
  have := hp
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  rw [parabolicSpectrum_eq_squareIntegrableFormSpectrum_of_isIso hK rho hsmooth hcalc r hA hT hG hU]
  exact h F G hG K rho hsmooth hcalc hKmax hrho P M U A p iU l a r hU hK hp

end Langlands.Global
