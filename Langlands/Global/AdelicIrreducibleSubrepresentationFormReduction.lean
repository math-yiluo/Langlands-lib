import Langlands.Global.AdelicGroupDiscreteSpectrumReduction
import Langlands.Global.AdelicIntertwiningLeviQuotient
import Langlands.GroupScheme.Lie.AdjointDeterminantReductiveProof
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.Global.AdelicL2FiniteVectorDensity

/-! # Irreducible subrepresentations of `L²([G])`: reduction to the automorphy of `K`-finite vectors

`IrreducibleSubrepresentationFormSpectrumStatement` (module
`Langlands.Global.AdelicGroupDiscreteSpectrumReduction`) asks that every irreducible closed
invariant subspace `V` of `L²([G])` lie in `squareIntegrableFormSpectrum` for a presented
parabolic `p : P → G` that is an isomorphism. This module reduces it to one proposition on `[G]`
that does not mention the parabolic data,
`IrreducibleSubrepresentationFiniteVectorAutomorphyStatement`. This is the assertion underlying
Getz–Hahn 2024, Theorem 6.6.4, for automorphic forms in the smoothness convention of
Borel–Jacquet 1979, §§4.1–4.2: if `V` is irreducible, each vector of `V` that is `K_∞`-finite
and fixed by an open subgroup of `G(𝔸_f)` is the class of an automorphic form on
`G(F) \ G(𝔸)` that is left invariant under `A_G`.

The density of these vectors in `V` is `subset_closure_canonicalL2FiniteVectors` (module
`Langlands.Global.AdelicL2FiniteVectorDensity`). The comparison proved here,
`isSquareIntegrableInducedForm_of_isIso`, shows that for an isomorphism `p` every `A_G`-invariant
automorphic form on `G(F) \ G(𝔸)` whose class lies in `L²([G])` belongs to Lapid's `A²_P`
(`IsSquareIntegrableInducedForm`). The theorem
`irreducibleSubrepresentationFormSpectrum_of_finiteVectorAutomorphy` derives
`IrreducibleSubrepresentationFormSpectrumStatement` from the proposition. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

section Comparison

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {p : P ⟶ G} {iU : U ⟶ P} {l : M ⟶ P}

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] in
/-- The geometric unipotent radical of a connected reductive group has trivial adelic image. -/
theorem map_eq_one_of_isGeometricUnipotentRadical (hP : IsConnectedReductive P)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (n : AdelicGroupPoints F U) :
    map F U P iU n = 1 := by
  have hrad : SubgroupFunctor.range iU = ⊥ :=
    hP.hasTrivialUnipotentRadical U iU hU.1.isClosedSubgroup hU.1.smooth hU.1.connectedSpace
      hU.1.isUnipotent hU.1.isNormal
  have hmem : n ≫ iU.hom.hom ∈ (SubgroupFunctor.range iU).carrier _ :=
    SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
  rw [hrad] at hmem
  exact hmem

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] in
/-- For a presented parabolic that is an isomorphism onto a connected reductive group, the
subgroup `U(𝔸) M(F)` lies in `G(F)`. -/
theorem parabolicQuotientSubgroup_le_rationalSubgroup_of_isIso [IsIso p]
    (hG : IsConnectedReductive G) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) :
    parabolicQuotientSubgroup F p iU l ≤ rationalSubgroup F G := by
  have hP : IsConnectedReductive P := hG.of_iso (asIso p)
  refine sup_le ?_ ?_
  · rintro _ ⟨n, rfl⟩
    have h1 : map F U G (iU ≫ p) n = 1 := by
      rw [InducedInnerProductIntegrable.map_comp_apply,
        map_eq_one_of_isGeometricUnipotentRadical hP hU n, map_one]
    change map F U G (iU ≫ p) n ∈ rationalSubgroup F G
    rw [h1]
    exact (rationalSubgroup F G).one_mem
  · rintro _ ⟨q, rfl⟩
    exact ⟨M.affinePointsTarget (l ≫ p) (CommAlgCat.of F F) q,
      DFunLike.congr_fun (rational_naturality F M (l ≫ p)) q⟩

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine M.X.left]
  [LocallyOfFiniteType M.X.hom] in
/-- The modulus parameter `2ρ_P` of a connected reductive `P` is zero. -/
theorem modulusParameter_eq_zero (hP : IsConnectedReductive P) :
    modulusParameter F P = 0 := by
  rw [modulusParameter, Lie.connectedReductiveAdjointDeterminant F P hP,
    TensorProduct.tmul_zero]

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine M.X.left]
  [LocallyOfFiniteType M.X.hom] in
/-- The parameter `ρ_P` of a connected reductive `P` is zero. -/
theorem halfModulusParameter_eq_zero (hP : IsConnectedReductive P) :
    halfModulusParameter F P = 0 := by
  rw [halfModulusParameter, Lie.connectedReductiveAdjointDeterminant F P hP,
    TensorProduct.tmul_zero]

/-- For a presented parabolic that is an isomorphism onto a connected reductive group, the
`A^n_P` condition holds for every function left invariant under `A_G`: the image of `A_M` is
`A_G`, and `δ_P = 1`. -/
theorem isSplitComponentEquivariant_of_isIso [IsIso p] (hG : IsConnectedReductive G)
    (hl : IsRationalLeviSubgroup l) {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (RestrictionSplitCentre.canonicalSubgroup F G) φ) :
    IsSplitComponentEquivariant p l φ := by
  have hP : IsConnectedReductive P := hG.of_iso (asIso p)
  let e : M ≅ G := hl.isoOfIsIsoParabolic (p := p) hG
  intro x hx g
  rw [halfModulusParameter_eq_zero hP, InducedInnerProductIntegrable.parameterPower_zero, one_mul,
    ← InducedInnerProductIntegrable.map_comp_apply]
  exact hφ _ (RestrictionSplitCentre.map_mem_canonicalSubgroup e hx) g

/-- For a presented parabolic that is an isomorphism onto a connected reductive group, the
Iwasawa form of the integrability condition of `A²_P` holds for every continuous function that
is left invariant under `A_G G(F)` and whose class lies in `L²([G])`. -/
theorem integrable_iwasawa_of_isIso [IsIso p] (hG : IsConnectedReductive G)
    (hl : IsRationalLeviSubgroup l) {K : Subgroup (AdelicGroupPoints F G)}
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) {φ : AdelicGroupPoints F G → ℂ}
    (hφc : Continuous φ)
    (hφ : IsLeftInvariantUnder F G (RestrictionSplitCentre.canonicalRationalSubgroup F G) φ)
    (hL2 : MemLp (fun y : RestrictionSplitCentre.CanonicalQuotient F G => φ y.out) 2
      (RestrictionSplitCentre.canonicalMeasure F G)) :
    Integrable (fun x : K × RestrictionSplitCentre.CanonicalQuotient F M =>
        ‖parameterPower F P (-modulusParameter F P) (map F M P l x.2.out)‖ *
          ‖φ (map F P G p (map F M P l x.2.out) * (x.1 : AdelicGroupPoints F G))‖ ^ 2)
      ((compactHaarProbability F G K hKc).prod
        (RestrictionSplitCentre.canonicalMeasure F M)) := by
  have hP : IsConnectedReductive P := hG.of_iso (asIso p)
  have hM : IsConnectedReductive M := hG.of_iso (hl.isoOfIsIsoParabolic (p := p) hG)
  let e : M ≅ G := hl.isoOfIsIsoParabolic (p := p) hG
  set κ := compactHaarProbability F G K hKc with hκ
  set μM := RestrictionSplitCentre.canonicalMeasure F M with hμM
  set μG := RestrictionSplitCentre.canonicalMeasure F G with hμG
  have hmod : ∀ m : AdelicGroupPoints F M,
      ‖parameterPower F P (-modulusParameter F P) (map F M P l m)‖ = 1 := by
    intro m
    rw [modulusParameter_eq_zero hP, neg_zero, InducedInnerProductIntegrable.parameterPower_zero,
      norm_one]
  let W : K → AdelicGroupPoints F M → ℝ := fun k m =>
    ‖φ (map F M G e.hom m * (k : AdelicGroupPoints F G))‖ ^ 2
  have hfun : (fun x : K × RestrictionSplitCentre.CanonicalQuotient F M =>
      ‖parameterPower F P (-modulusParameter F P) (map F M P l x.2.out)‖ *
        ‖φ (map F P G p (map F M P l x.2.out) * (x.1 : AdelicGroupPoints F G))‖ ^ 2) =
      fun x => W x.1 x.2.out := by
    funext x
    rw [hmod, one_mul, ← InducedInnerProductIntegrable.map_comp_apply]
    rfl
  rw [hfun]
  have := RestrictionSplitCentre.canonicalQuotient_borelSpace F M
    centralSplitTorusCharacter.{0} hM
  have hWc : Continuous (fun z : K × AdelicGroupPoints F M => W z.1 z.2) :=
    (hφc.comp (((map F M G e.hom).continuous.comp continuous_snd).mul
      (continuous_subtype_val.comp continuous_fst))).norm.pow 2
  have hWinv : ∀ k : K, ∀ g₀ ∈ RestrictionSplitCentre.canonicalRationalSubgroup F M, ∀ m,
      W k (g₀ * m) = W k m := by
    intro k g₀ hg₀ m
    simp only [W]
    rw [map_mul, mul_assoc,
      hφ _ (RestrictionSplitCentre.map_mem_canonicalRationalSubgroup e hg₀)]
  have hcont : Continuous (fun z : K × RestrictionSplitCentre.CanonicalQuotient F M =>
      W z.1 z.2.out) :=
    LeftCosetSpace.continuous_out_of_invariant _ W hWc hWinv
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  show ∫⁻ z, ‖W z.1 z.2.out‖ₑ ∂(κ.prod μM) < ∞
  have : SFinite μM := by
    rw [hμM, RestrictionSplitCentre.canonicalMeasure, RestrictionSplitCentre.quotientHaarMeasure,
      normOneRationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure,
      LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.quotientMeasure]
    infer_instance
  rw [lintegral_prod _ hcont.measurable.enorm.aemeasurable]
  -- The finite square integral of the class.
  set C : ℝ≥0∞ := ∫⁻ z, ‖φ z.out‖ₑ ^ 2 ∂μG with hC
  have hCfin : C < ∞ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hL2
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using h
  obtain ⟨s, -, hmap⟩ := RestrictionSplitCentre.map_canonicalMeasure e
  have hinv' : ∀ k : AdelicGroupPoints F G,
      ∀ g₀ ∈ RestrictionSplitCentre.canonicalRationalSubgroup F G, ∀ m : AdelicGroupPoints F G,
        ‖φ (g₀ * m * k)‖ₑ ^ 2 = ‖φ (m * k)‖ₑ ^ 2 := by
    intro k g₀ hg₀ m
    rw [mul_assoc, hφ g₀ hg₀]
  have hinner : ∀ k : K, ∫⁻ y, ‖W k y.out‖ₑ ∂μM = (s : ℝ≥0∞) * C := by
    intro k
    let Hk : RestrictionSplitCentre.CanonicalQuotient F G → ℝ≥0∞ := fun z =>
      ‖φ (z.out * (k : AdelicGroupPoints F G))‖ₑ ^ 2
    have hHk : Measurable Hk :=
      LeftCosetSpace.measurable_out_of_invariant _
        ((hφc.comp (continuous_id.mul continuous_const)).measurable.enorm.pow_const 2)
        (hinv' k)
    have hpt : ∀ y : RestrictionSplitCentre.CanonicalQuotient F M,
        ‖W k y.out‖ₑ = Hk (RestrictionSplitCentre.canonicalQuotientMap e y) := by
      intro y
      induction y using Quotient.inductionOn with
      | _ m =>
        have h1 : W k (LeftCosetSpace.mk _ m).out = W k m :=
          LeftCosetSpace.out_mk_of_invariant _ (W k) (hWinv k) m
        have h2 : Hk (RestrictionSplitCentre.canonicalQuotientMap e (LeftCosetSpace.mk _ m)) =
            ‖φ (map F M G e.hom m * (k : AdelicGroupPoints F G))‖ₑ ^ 2 :=
          LeftCosetSpace.out_mk_of_invariant _
            (fun g => ‖φ (g * (k : AdelicGroupPoints F G))‖ₑ ^ 2) (hinv' k) _
        change ‖W k (LeftCosetSpace.mk _ m).out‖ₑ =
          Hk (RestrictionSplitCentre.canonicalQuotientMap e (LeftCosetSpace.mk _ m))
        rw [h1, h2]
        simp only [W, enorm_pow, enorm_norm]
    have htrans : ∫⁻ z, Hk z ∂μG = C := by
      have hT := RestrictionSplitCentre.canonicalMeasure_rightInvariant F G
        centralSplitTorusCharacter.{0} hG (k : AdelicGroupPoints F G)
      have hH1 : Measurable (fun z : RestrictionSplitCentre.CanonicalQuotient F G =>
          ‖φ z.out‖ₑ ^ 2) :=
        LeftCosetSpace.measurable_out_of_invariant _ (hφc.measurable.enorm.pow_const 2)
          (fun g₀ hg₀ m => by rw [hφ g₀ hg₀])
      rw [hC, ← hT.lintegral_comp hH1]
      refine lintegral_congr fun z => ?_
      induction z using Quotient.inductionOn with
      | _ m =>
        have h1 : Hk (LeftCosetSpace.mk _ m) = ‖φ (m * (k : AdelicGroupPoints F G))‖ₑ ^ 2 :=
          LeftCosetSpace.out_mk_of_invariant _
            (fun g => ‖φ (g * (k : AdelicGroupPoints F G))‖ₑ ^ 2) (hinv' k) m
        have h2 : (fun z : RestrictionSplitCentre.CanonicalQuotient F G => ‖φ z.out‖ₑ ^ 2)
            (LeftCosetSpace.mk _ (m * (k : AdelicGroupPoints F G))) =
              ‖φ (m * (k : AdelicGroupPoints F G))‖ₑ ^ 2 :=
          LeftCosetSpace.out_mk_of_invariant _ (fun g => ‖φ g‖ₑ ^ 2)
            (fun g₀ hg₀ m => by rw [hφ g₀ hg₀]) _
        change Hk (LeftCosetSpace.mk _ m) = (fun z : RestrictionSplitCentre.CanonicalQuotient F G =>
          ‖φ z.out‖ₑ ^ 2) (LeftCosetSpace.mk _ (m * (k : AdelicGroupPoints F G)))
        rw [h1, h2]
    rw [lintegral_congr hpt, ← lintegral_map hHk
      (RestrictionSplitCentre.measurable_canonicalQuotientMap e), hmap,
      lintegral_smul_measure, htrans]
    rfl
  rw [lintegral_congr hinner, lintegral_const, measure_univ, mul_one]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hCfin

/-- **Comparison for a full parabolic.** For a presented parabolic `p` that is an isomorphism onto
a connected reductive group, every automorphic form on `G(F) \ G(𝔸)` (for `K_∞` and `rho`) that
is left invariant under `A_G` and whose class lies in `L²([G])` belongs to Lapid's `A²_P`. -/
theorem isSquareIntegrableInducedForm_of_isIso [IsIso p] (hl : IsRationalLeviSubgroup l)
    (hG : IsConnectedReductive G) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    {K : Subgroup (AdelicGroupPoints F G)} (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
    {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
    {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth} {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ)
    (hA : IsLeftInvariantUnder F G (RestrictionSplitCentre.canonicalSubgroup F G) φ)
    (hL2 : MemLp (fun y : RestrictionSplitCentre.CanonicalQuotient F G => φ y.out) 2
      (RestrictionSplitCentre.canonicalMeasure F G)) :
    IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l φ := by
  have hinv : IsLeftInvariantUnder F G (RestrictionSplitCentre.canonicalRationalSubgroup F G) φ :=
    LeftCosetSpace.invariant_sup (RestrictionSplitCentre.canonicalSubgroup F G) φ hA hφ.1
  exact ⟨⟨fun x hx g =>
      hφ.1 x (parabolicQuotientSubgroup_le_rationalSubgroup_of_isIso hG hU hx) g, hφ.2⟩,
    isSplitComponentEquivariant_of_isIso hG hl hA,
    integrable_iwasawa_of_isIso hG hl hKc hφ.2.1.1 hinv hL2⟩

end Comparison

/-- **Automorphy of the `K`-finite vectors of a discrete summand.** This is the number-field
assertion about representatives that underlies Getz–Hahn 2024, Theorem 6.6.4 (p.172), stated
for automorphic forms in the smoothness and finite-level convention of Borel–Jacquet 1979,
§§4.1–4.2: continuity, smooth archimedean slices and right invariance under one open subgroup
of `G(𝔸_f)`, as `IsAutomorphicFunctionOn` asks. Getz–Hahn's space `A_{A_G}` is built from the
algebraic tensor product of their (6.1) and Definition 6.3.3. That space is strictly smaller,
since all archimedean slices of its elements lie in one finite-dimensional space (see the note
`notes/automorphic/getz-hahn-literal-tensor-boundary.md`). For a disconnected `K_∞` the
`𝔷`-finiteness uses the adjoint invariance of the centre of the enveloping algebra instead of
the printed Corollary 4.6.3.

Let `G` be a connected reductive group over a number field `F`, `K` a maximal compact subgroup
of `G(𝔸)`, `rho` a closed embedding of `G` into `GL_N` and `V` an irreducible subrepresentation
of the right regular representation of `G(𝔸)` on `L²([G])`. Every vector `w` of `V` that is
`K_∞`-finite and fixed by an open subgroup of `G(𝔸_f)` is the class of a function `φ` on `G(𝔸)`
that is an automorphic form on `G(F) \ G(𝔸)` (`IsAutomorphicFunctionOn` for
`K_∞ = K.comap (ofInfinite F G)` and `rho`) and is left invariant under `A_G`. -/
def IrreducibleSubrepresentationFiniteVectorAutomorphyStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G)
    (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ V : Submodule ℂ (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)),
      Langlands.Analysis.IsIrreducibleSubrepresentation
        (RestrictionSplitCentre.canonicalL2RightAction F G centralSplitTorusCharacter.{0} hG) V →
      ∀ w ∈ V, IsCanonicalL2FiniteVector hG K w →
        ∃ φ : AdelicGroupPoints F G → ℂ,
          IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
              (K.comap (ofInfinite F G).toMonoidHom) rho φ ∧
            IsLeftInvariantUnder F G (RestrictionSplitCentre.canonicalSubgroup F G) φ ∧
            w =ᵐ[RestrictionSplitCentre.canonicalMeasure F G] fun y => φ y.out

/-- The automorphy of the `K`-finite vectors of the irreducible subrepresentations of `L²([G])`
implies `IrreducibleSubrepresentationFormSpectrumStatement`; the density of the `K`-finite vectors
is `subset_closure_canonicalL2FiniteVectors`. -/
theorem irreducibleSubrepresentationFormSpectrum_of_finiteVectorAutomorphy
    (hA : IrreducibleSubrepresentationFiniteVectorAutomorphyStatement) :
    IrreducibleSubrepresentationFormSpectrumStatement := by
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho P M U A _ _ _ _ p _ iU l a r hU hK hp
    V hV
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  intro v hv
  have hsub := subset_closure_canonicalL2FiniteVectors hG hKmax.1 hV.1 hV.2.2.1 hv
  show v ∈ (squareIntegrableFormSpectrum K hK.isCompact rho hsmooth hcalc p iU l :
    Set (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)))
  rw [squareIntegrableFormSpectrum, Submodule.topologicalClosure_coe]
  refine closure_mono ?_ hsub
  rintro w ⟨hwV, hwfin⟩
  obtain ⟨φ, hφ, hφA, hwφ⟩ := hA F G hG K rho hsmooth hcalc hKmax hrho V hV w hwV hwfin
  have hL2 : MemLp (fun y : RestrictionSplitCentre.CanonicalQuotient F G => φ y.out) 2
      (RestrictionSplitCentre.canonicalMeasure F G) :=
    (Lp.memLp w).ae_eq hwφ
  refine Submodule.subset_span ⟨1, fun _ => φ, fun _ => 1, fun _ =>
    isSquareIntegrableInducedForm_of_isIso r.isCompatible.levi hG hU hK.isCompact hφ hφA hL2, ?_⟩
  filter_upwards [hwφ] with y hy
  simp [hy]

end Langlands.Global
