import Langlands.Global.AdelicEisensteinCuspidalTestIntertwiningReduction
import Langlands.Global.CuspidalTestExpansion.Reduction
import Langlands.Global.AdelicConstantTermAutomorphyProof
import Langlands.Global.AdelicLeviCuspFormRapidDecayProof

/-! # The tested constant-term formula (6.18) for standard parabolics

`Langlands.Global.eisensteinCuspidalTestIntertwiningExpansion` proves
`EisensteinCuspidalTestIntertwiningExpansionStatement` (Bernstein–Lapid, §6.10, (6.17)–(6.18),
tested by the pairings of (6.8)). In the range of convergence the constant term along `P_J` of
`E(φ, λ)` is the sum over the minimal double coset representatives `v ∈ W_J \ W / W_I` of the
coset series of the intertwining integrals of the Bruhat pieces (the theorem
`eisensteinConstantTerm_of_convergence_of_unfolding`). The tests against cusp forms on `M_J` of
the pieces with proper target vanish (`NestedLeviParabolic.properPiece_pairing`); a piece with
full target is its own coset series and is the intertwining integral of `C_{I_v} φ` from
`P_{I_v}` to `P_J`, which the constant term along `P_J` fixes. The three lemmas of the namespace
`StandardParabolicFamily` treat the pieces with full target. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj BigOperators

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

attribute [local instance] StandardParabolicFamily.isClosedImmersion_p

variable {I J I₁ J₁ : StandardIndex F G fam.i fam.ν} {n : normalizerPoints fam.i}

/-- A Bruhat piece with full target `P_J` presents an element of `W(P_{I₁}, P_J)`: its Levi
conjugation `M_J → M_{I₁}` and the projection of its target onto `M_J`, a retraction of the
Levi. -/
theorem fullPiece_weylData (pc : StandardBruhatPiece fam I J I₁ J₁ n) (hJ₁ : J = J₁) :
    ∃ (c : fam.M J ⟶ fam.M I₁) (π : fam.P J ⟶ fam.M J),
      fam.l J ≫ π = 𝟙 (fam.M J) ∧
        IsWeylConjugation (fam.p I₁) (fam.l I₁) (fam.p J) (fam.l J) n.val c := by
  subst hJ₁
  exact ⟨pc.conjugation, pc.target.projection, pc.target.section_projection, pc.weylLevi⟩

/-- For a Bruhat piece with full target `P_J`, the intertwining integral of the piece is the
intertwining integral of `C_{I₁} φ` from `P_{I₁}` to `P_J`, written with the standard maps of
`P_{I₁}` and `U_J`. -/
theorem fullPiece_intertwiningIntegral_eq (pc : StandardBruhatPiece fam I J I₁ J₁ n)
    (hJ₁ : J = J₁) {K : Subgroup (AdelicGroupPoints F G)}
    (hK₁ : IsIwasawaCompact (pc.source.inclusion ≫ fam.p I) K)
    (hK₂ : IsIwasawaCompact (fam.p I₁) K) (φ : AdelicGroupPoints F G → ℂ)
    (lam : ComplexCharacterParameter F (fam.P I)) :
    hK₁.intertwiningIntegral (fam.iU I₁) (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J) n.val
        (subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ)
        (parameterRestrict pc.source.inclusion lam) =
      hK₂.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n.val (fam.constantTerm I₁ φ)
        (parameterRestrict pc.source.inclusion lam) := by
  subst hJ₁
  have hincl := pc.source.inclusion_comp
  have hCT : subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ =
      fam.constantTerm I₁ φ := subgroupConstantTerm_congr_hom (by rw [hincl]) φ
  have ej : fam.iU J ≫ pc.target.inclusion ≫ fam.p J = fam.iU J ≫ fam.p J := by
    rw [pc.target.inclusion_comp]
  rw [hCT]
  exact (intertwining_congr_hom hincl ej hK₁ hK₂ (fam.iU I₁) n.val (fam.constantTerm I₁ φ)
    (parameterRestrict pc.source.inclusion lam)).1

/-- The intertwining integral into `P_J` of a function left invariant under `U_{I₁}(𝔸)` is left
invariant under `U_J(𝔸)`, so the constant term along `P_J` fixes it. -/
theorem constantTerm_intertwiningIntegral {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (fam.p I₁) K) (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I₁) (fam.iU I₁)) φ)
    (lam : ComplexCharacterParameter F (fam.P I₁)) :
    fam.constantTerm J (hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) w φ lam) =
      hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) w φ lam := by
  have hVr := (fam.isUnipotentRadical J).1
  have : IsAffineHom (fam.U J).X.hom := IsClosedSubgroup.isAffineHom hVr.isClosedSubgroup
  have : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G
      (SubgroupFunctor.range (fam.iU J ≫ fam.p J))) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (fam.iU J ≫ fam.p J)
      hVr.smooth hVr.connectedSpace hVr.isUnipotent
  refine fam.constantTerm_eq_self_of_unipotent_invariant J ?_
  rintro _ ⟨y, rfl⟩ g
  exact hK.intertwiningIntegral_adelicPoints_mul (fam.iU I₁) (fam.iU J ≫ fam.p J) w
    (fam.isUnipotentRadical I₁).1.isUnipotent hφ lam ⟨_, ⟨y, rfl⟩⟩ g

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions
  Langlands.Aubert.General.RationalPointFamily RealTorusSpace Langlands.Group.RelativeWeylIndexing

attribute [local instance] StandardParabolicFamily.isClosedImmersion_p

set_option maxHeartbeats 4000000 in
/-- **The tested constant-term formula** (Bernstein–Lapid, §6.10, (6.17)–(6.18), tested by the
pairings of (6.8)): `EisensteinCuspidalTestIntertwiningExpansionStatement`. The terms are the
minimal double coset representatives `v ∈ W_J \ W / W_I` whose Bruhat piece has full target
`P_J`; for such `v` the source is `P_{I_v}`, the inducing function is `C_{I_v} φ` and the term is
the intertwining integral `[M(v, λ|) C_{I_v} φ]_{vλ}`. -/
theorem eisensteinCuspidalTestIntertwiningExpansion :
    EisensteinCuspidalTestIntertwiningExpansionStatement.{u} := by
  have hGLU : GeometricLemmaUnfoldingStatement.{u} := geometricLemmaUnfolding
  intro F _ _ G _ _ _ fam _ _ K h₀ hKmax hKlevi N d rho hsmooth hrho I φ hφ J
  classical
  let hK := fam.isIwasawaCompact_of_minimal h₀ I
  let r := fam.rootPresentation I
  let hA := (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
  let hT := fam.maximalSplit.isSplitSubtorus.1
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  -- the Coxeter system of the relative Weyl group and the Bruhat data
  obtain ⟨-, hSfin, CM, cs, hcs⟩ := relativeWeylCoxeter F G fam.connectedReductive fam.T fam.i
    fam.maximalSplit fam.ν fam.generic
  let PI := fam.simpleRootsOfIndex I
  let PJ := fam.simpleRootsOfIndex J
  have hPI : rootSet fam.i fam.ν PI = I.val :=
    congrArg Subtype.val (fam.indexOfSimpleRoots_simpleRootsOfIndex I)
  have hPJ : rootSet fam.i fam.ν PJ = J.val :=
    congrArg Subtype.val (fam.indexOfSimpleRoots_simpleRootsOfIndex J)
  obtain ⟨lift, hlift, -, hreps⟩ :=
    fam.exists_standardBruhatRepresentatives cs PI PJ I J 1 hcs hPI hPJ
  let Wm := {v : relativeWeylGroup fam.i // IsMinimal cs PJ PI v}
  let Iv : Wm → StandardIndex F G fam.i fam.ν :=
    fun v => fam.indexOfSimpleRoots (intersectionSubset cs PJ PI v.val)
  let Jv : Wm → StandardIndex F G fam.i fam.ν :=
    fun v => fam.indexOfSimpleRoots (intersectionSubset cs PI PJ v.val⁻¹)
  have hpiece : ∀ v : Wm, Nonempty (StandardParabolicFamily.StandardBruhatPiece fam I J (Iv v)
      (Jv v) (lift v)) := by
    intro v
    have hv : (QuotientGroup.mk (lift v) : relativeWeylGroup fam.i) = v.val := hlift v
    have hmin : IsMinimal cs PJ PI (QuotientGroup.mk (lift v) : relativeWeylGroup fam.i) := by
      rw [hv]; exact v.property
    have h := fam.standardBruhatPiece (lift v) cs PI PJ hcs hmin
    rw [fam.indexOfSimpleRoots_simpleRootsOfIndex I, fam.indexOfSimpleRoots_simpleRootsOfIndex J]
      at h
    simp only [hv] at h
    exact h
  let piece := fun v : Wm => (hpiece v).some
  have instF : ∀ v : Wm,
      IsClosedImmersion ((piece v).source.inclusion ≫ fam.p I).hom.hom.left := fun v => by
    rw [(piece v).source.inclusion_comp]
    exact (fam.isCompatible (Iv v)).parabolic.isClosedSubgroup
  have instFU : ∀ v : Wm, IsClosedImmersion
      (fam.iU (Iv v) ≫ (piece v).source.inclusion ≫ fam.p I).hom.hom.left := fun v => by
    rw [(piece v).source.inclusion_comp]
    exact fam.closedU (Iv v)
  have instGV : ∀ v : Wm, IsClosedImmersion
      (fam.iU (Jv v) ≫ (piece v).target.inclusion ≫ fam.p J).hom.hom.left := fun v => by
    rw [(piece v).target.inclusion_comp]
    exact fam.closedU (Jv v)
  have hK0' : IsIwasawaCompact (fam.p (fam.indexOfSimpleRoots ∅)) K := by
    have h0 : fam.indexOfSimpleRoots ∅ = ⟨∅, Set.empty_subset _⟩ :=
      Subtype.ext (rootSet_empty fam.i fam.ν)
    rw [h0]
    exact h₀
  -- the constant-term formula (6.17) in the range of convergence
  have hconst := eisensteinConstantTerm_of_convergence_of_unfolding eisensteinAbsoluteConvergence
    hGLU F G (fam.P I) (fam.M I) (fam.U I) (fam.P J) (fam.U J) (fam.A I) (fam.p I) (fam.iU I)
    (fam.l I) (fam.a I) r hA hT (fam.p J) (fam.iU J) Wm (fun v => (lift v).val)
    (fun v => fam.P (Iv v)) (fun v => fam.U (Iv v)) (fun v => fam.P (Jv v)) (fun v => fam.U (Jv v))
    (fun v => (piece v).source.inclusion) (fun v => fam.iU (Iv v))
    (fun v => (piece v).target.inclusion) (fun v => fam.iU (Jv v))
    fam.connectedReductive (fam.isUnipotentRadical I) (fam.isCompatible J).parabolic
    (fam.isUnipotentRadical J) hreps
    (fun v => by rw [(piece v).source.inclusion_comp]; exact (fam.isCompatible (Iv v)).parabolic)
    (fun v => fam.isUnipotentRadical (Iv v))
    (fun v => by rw [(piece v).target.inclusion_comp]; exact (fam.isCompatible (Jv v)).parabolic)
    (fun v => fam.isUnipotentRadical (Jv v)) (fun v => (piece v).geometry) K hK
    (fun v => ((piece v).iwasawa K hK0').1) rho hsmooth
    (adelicDifferentialCommutator_of_smooth F G hsmooth) φ hKmax hrho hφ
  obtain ⟨R₀, hR₀⟩ := hconst
  have hIv_le : ∀ v : Wm, Iv v ≤ I := fun v => by
    have h := (fam.indexOfSimpleRoots_le _ _).mpr (intersectionSubset_subset cs PJ PI v.val)
    rwa [fam.indexOfSimpleRoots_simpleRootsOfIndex] at h
  have hAutv : ∀ v : Wm,
      fam.IsAutomorphicOn hsmooth Kinf rho (Iv v) (fam.constantTerm (Iv v) φ) := fun v => constantTermAutomorphy F G fam Kinf rho hsmooth hrho I (Iv v) (hIv_le v) φ hφ
  -- the terms: the representatives whose Bruhat piece has full target
  let FullV := {v : Wm // J = Jv v}
  have hdata := fun v : FullV => fam.fullPiece_weylData (piece v.1) v.2
  choose cv πv hπv hWv using hdata
  let e := Fintype.equivFin FullV
  -- the pieces and their coset series
  let Pint : ComplexCharacterParameter F (fam.P I) → Wm → AdelicGroupPoints F G → ℂ :=
    fun lam v =>
      ((piece v).iwasawa K hK0').1.intertwiningIntegral (fam.iU (Iv v))
        (fam.iU (Jv v) ≫ (piece v).target.inclusion ≫ fam.p J) (lift v).val
        (subgroupConstantTerm F (fam.iU (Iv v) ≫ (piece v).source.inclusion ≫ fam.p I) φ)
        (parameterRestrict (piece v).source.inclusion lam)
  let S : ComplexCharacterParameter F (fam.P I) → Wm → AdelicGroupPoints F G → ℂ :=
    fun lam v y =>
      ∑' c : RelativeRationalCosets F ((piece v).target.inclusion ≫ fam.p J) (fam.p J),
        Pint lam v ((c.out : AdelicGroupPoints F G) * y)
  suffices key : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
      ∀ ψ, fam.IsLeviCuspForm Kinf rho J ψ → ∀ g,
        (∀ v, Integrable (fam.leviPairingIntegrand J (S lam v) g ψ)
          (normOneRationalQuotientHaarMeasure F (fam.M J))) ∧
        (∀ v, ¬ J = Jv v → fam.leviPairing J (S lam v) g ψ = 0) ∧
        (∀ v : FullV, S lam v.1 = Pint lam v.1) by
    obtain ⟨R, hR⟩ := key
    refine ⟨Fintype.card FullV, fun t => Iv (e.symm t).1,
      fun t => (piece (e.symm t).1).source.inclusion, fun t => lift (e.symm t).1,
      fun t => cv (e.symm t), fun t => πv (e.symm t),
      fun t => fam.constantTerm (Iv (e.symm t).1) φ,
      fun t => (piece (e.symm t).1).source.inclusion_comp, fun t => hWv (e.symm t),
      fun t => hπv (e.symm t), fun t α hα => ?_, fun t => hAutv (e.symm t).1,
      max R R₀, fun lam hlam ψ hψ g => ?_⟩
    · -- positivity of the minimal representatives on the simple roots of `I`
      rw [show (QuotientGroup.mk (lift (e.symm t).1) : relativeWeylGroup fam.i) =
        (e.symm t).1.val from hlift _]
      have hα' : α ∈ rootSet fam.i fam.ν PI := by rw [hPI]; exact hα
      obtain ⟨a, ha, rfl⟩ := hα'
      have hlen := ((minimalityLengthCriterion_proof cs PJ PI _).mp (e.symm t).1.2).2 a ha
      exact (hcs.2.2.1 _ a).mp hlen
    · obtain ⟨hSint, hProper, hFull⟩ := hR lam
        (ParabolicRootPresentation.IsRegularParameter.mono r hA hT (le_max_left R R₀) hlam) ψ hψ g
      have hCE : fam.constantTerm J (hK.eisensteinSeries φ lam) = ∑ v, S lam v := by
        funext y
        rw [Finset.sum_apply]
        exact (hR₀ lam (ParabolicRootPresentation.IsRegularParameter.mono r hA hT
          (le_max_right R R₀) hlam) y).2.2
      have h0 : ∑ v : {v : Wm // ¬ J = Jv v}, fam.leviPairing J (S lam v.1) g ψ = 0 :=
        Finset.sum_eq_zero (fun v _ => hProper v.1 v.2)
      rw [hCE, fam.leviPairing_finsetSum_of_integrable J Finset.univ (S lam) ψ g
        (fun v _ => hSint v),
        ← Fintype.sum_subtype_add_sum_subtype (fun v : Wm => J = Jv v)
          (fun v => fam.leviPairing J (S lam v) g ψ), h0, add_zero,
        ← Equiv.sum_comp e.symm (fun v : FullV => fam.leviPairing J (S lam v.1) g ψ)]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hinv : IsLeftInvariantUnder F G
          (parabolicUnipotentImage F (fam.p (Iv (e.symm t).1)) (fam.iU (Iv (e.symm t).1)))
          (fam.constantTerm (Iv (e.symm t).1) φ) := by
        rintro _ ⟨y, rfl⟩ x
        exact (hAutv (e.symm t).1).1 _ (Subgroup.mem_sup_left ⟨y, rfl⟩) x
      rw [hFull, fam.constantTerm_intertwiningIntegral _ _ hinv]
      exact congrArg (fun f => fam.leviPairing J f g ψ)
        (fam.fullPiece_intertwiningIntegral_eq (piece (e.symm t).1) (e.symm t).2
          ((piece (e.symm t).1).iwasawa K hK0').1 _ φ lam)
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · -- rank zero: `G(𝔸)` is a point, every standard index is the empty one, so every piece has
    -- full target, and every pairing integrand is integrable
    subst hN0
    have hsub : Subsingleton (AdelicGroupPoints F G) :=
      ⟨fun _ _ => (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective
        (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩
    have hratsub : Subsingleton (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) :=
      ⟨fun a b => ((rational_injective F G).comp
        (Langlands.GroupScheme.GaloisPointComparison.rationalCoeffEquiv F G).injective)
        (Subsingleton.elim _ _)⟩
    have hWsub : ∀ a b : relativeWeylGroup fam.i, a = b := by
      intro a b
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [Subsingleton.elim x y]
    have hempty : IsEmpty (SimpleRoot fam.i fam.ν) := ⟨fun a => by
      have h := cs.length_simple a
      rw [hWsub (cs.simple a) 1, cs.length_one] at h
      exact zero_ne_one h⟩
    have hidx : ∀ A B : StandardIndex F G fam.i fam.ν, A = B := fun A B =>
      Subtype.ext (Set.ext fun α =>
        ⟨fun h => (hempty.false ⟨α, A.2 h⟩).elim, fun h => (hempty.false ⟨α, B.2 h⟩).elim⟩)
    have hint0 : ∀ (f : AdelicGroupPoints F G → ℂ) (test : AdelicGroupPoints F (fam.M J) → ℂ)
        (g : AdelicGroupPoints F G), Integrable (fam.leviPairingIntegrand J f g test)
          (normOneRationalQuotientHaarMeasure F (fam.M J)) := by
      intro f test g
      have hcJ := fam.isCompatible J
      have hjc : IsClosedSubgroup (fam.l J ≫ fam.p J) :=
        hcJ.levi.isClosedSubgroup.comp hcJ.parabolic.isClosedSubgroup
      have : IsClosedImmersion (fam.l J ≫ fam.p J).hom.hom.left := hjc
      have : IsAffine (fam.M J).X.left := isAffine_of_isAffineHom (fam.l J ≫ fam.p J).hom.hom.left
      have hMsub : Subsingleton (AdelicGroupPoints F (fam.M J)) :=
        ⟨fun a b => (isClosedEmbedding_map F (fam.M J) G (fam.l J ≫ fam.p J)).injective
          (Subsingleton.elim _ _)⟩
      have hQsub : Subsingleton (NormOneRationalQuotient F (fam.M J)) := ⟨fun a b => by
        obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective _ a
        obtain ⟨y, rfl⟩ := LeftCosetSpace.mk_surjective _ b
        rw [Subsingleton.elim x y]⟩
      have hconst : fam.leviPairingIntegrand J f g test =
          fun _ => fam.leviPairingIntegrand J f g test (LeftCosetSpace.mk _ 1) :=
        funext fun q => congrArg _ (Subsingleton.elim q _)
      rw [hconst]
      exact integrable_const _
    refine ⟨R₀, fun lam _ ψ _ g => ⟨fun v => hint0 _ _ _, fun v hv => (hv (hidx _ _)).elim,
      fun v => funext fun y => ?_⟩⟩
    exact fam.fullPiece_series (piece v.1).target v.2 (Pint lam v.1)
      (fun x _ z => by rw [Subsingleton.elim (x * z) z]) y
  · -- positive rank: the majorant of the Eisenstein series, the rapid decay of cusp forms, and
    -- the vanishing of the tests of the pieces with proper target
    have hφc : Continuous φ := hφ.2.1.1
    have hφinv := hφ.1
    have hφgrowth := hφ.2.2.2.2
    obtain ⟨R₁, hmaj⟩ := eisensteinGlobalMajorant F G (fam.P I) (fam.M I) (fam.U I) (fam.A I)
      (fam.p I) (fam.iU I) (fam.l I) (fam.a I) r hA hT fam.connectedReductive
      (fam.isUnipotentRadical I) hK rho hN hrho φ hφinv hφgrowth
    have hJv_le : ∀ v : Wm, Jv v ≤ J := fun v => by
      have h := (fam.indexOfSimpleRoots_le _ _).mpr (intersectionSubset_subset cs PI PJ v.val⁻¹)
      rwa [fam.indexOfSimpleRoots_simpleRootsOfIndex] at h
    refine ⟨R₁, fun lam hlam ψ hψ g => ?_⟩
    obtain ⟨b, dd, hb, hb0, hdd, hbound⟩ := hmaj lam hlam
    have hPP := fun v : Wm => fam.pieceIntegral_properties hGLU (piece v) hK
      ((piece v).iwasawa K hK0').1 rho hN hφc hφinv lam b dd hb hb0 hdd hbound
    obtain ⟨B, hB0, hBdecay⟩ :=
      leviCuspFormRapidDecay F G fam K hKmax h₀ hKlevi rho hN hrho J ψ hψ dd hdd
    have htc : Continuous ψ := hψ.1.2.1.1
    have hti : IsLeftInvariantUnder F (fam.M J) (rationalSubgroup F (fam.M J)) ψ := hψ.1.1
    -- pieces with full target
    have hdomFull : ∀ v : FullV, Pint lam v.1 ∈ fam.leviPairingDomain J ψ := by
      intro v g'
      obtain ⟨C, hC, hCb⟩ := (hPP v.1).2.2.2.1
      have hle : rationalImage F (fam.l J ≫ fam.p J) ≤
          rationalImage F ((piece v.1).target.inclusion ≫ fam.p J) := by
        refine (rationalImage_comp_le (fam.l J) (fam.p J)).trans
          (rationalImage_le_of_range_le _ _ ?_)
        rw [(piece v.1).target.inclusion_comp, ← v.2]
      exact StandardParabolicFamily.weightedLeviPairingIntegrability fam J rho hN (Pint lam v.1)
        (hPP v.1).2.2.1 (fun z hz x => (hPP v.1).2.2.2.2 z (hle hz) x) C dd hC hdd hCb ψ htc hti
        ⟨B, hB0, hBdecay⟩ g'
    have hS_full : ∀ v : FullV, S lam v.1 = Pint lam v.1 := fun v => funext fun y =>
      fam.fullPiece_series (piece v.1).target v.2 (Pint lam v.1) (hPP v.1).2.2.2.2 y
    -- pieces with proper target
    have hΦc : Continuous (hK.parameterTwist φ lam) := hK.continuous_parameterTwist hφc lam
    have hΦP := (fam.parameterTwist_isLeftInvariant hK hφinv lam).2
    have hVn : (SubgroupFunctor.range (fam.iU J)).IsNormal := (fam.isUnipotentRadical J).1.isNormal
    have hcpt := fam.compactSpace_radicalRationalQuotient J
    obtain ⟨Cabs, hCabs0, hCabs⟩ := eisensteinBruhatAbsoluteBound (fam.p I) (fam.p J) (fam.iU J)
      (fun v : Wm => (lift v).val)
      (fun v => rationalImage F ((piece v).target.inclusion ≫ fam.p J)) rho hN hreps
      (fun v => (piece v).geometry.rationalImage_right) hVn hcpt (hK.parameterTwist φ lam) hΦc
      hΦP b dd hb hb0 hdd hbound
    have hAbs : ∀ v : Wm, ∀ y, ∑' c : RelativeRationalCosets F
        ((piece v).target.inclusion ≫ fam.p J) (fam.p J),
        ‖Pint lam v ((c.out : AdelicGroupPoints F G) * y)‖ₑ ≤
          ENNReal.ofReal (Cabs * RepresentationGrowth.adelicHeight F G rho y ^ dd) := by
      intro v y
      refine (ENNReal.tsum_le_tsum fun c => ?_).trans (hCabs y v)
      have h1 : Pint lam v ((c.out : AdelicGroupPoints F G) * y) =
          stabilizerIntegral (fam.p I) (fam.p J) (fam.iU J) (innerAdelicPoint F G (lift v).val)
            (hK.parameterTwist φ lam) ((c.out : AdelicGroupPoints F G) * y) := (hPP v).2.1 _
      rw [h1]
      exact enorm_integral_le_lintegral_enorm _
    have hCTinv : ∀ v : Wm, IsLeftInvariantUnder F G
        (parabolicUnipotentImage F (fam.p (Iv v)) (fam.iU (Iv v)))
        (fam.constantTerm (Iv v) φ) := by
      intro v
      rintro _ ⟨y, rfl⟩ x
      exact (hAutv v).1 _ (Subgroup.mem_sup_left ⟨y, rfl⟩) x
    have hProper : ∀ v : Wm, ¬ (J = Jv v) →
        Integrable (fam.leviPairingIntegrand J (S lam v) g ψ)
          (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
        fam.leviPairing J (S lam v) g ψ = 0 := by
      intro v hv
      have hlt : Jv v < J := lt_of_le_of_ne (hJv_le v) (Ne.symm hv)
      exact (piece v).target.properPiece_pairing hlt rho hN Kinf (Pint lam v) (hPP v).2.2.1
        (hPP v).2.2.2.2 (fun u hu y => fam.pieceIntegral_radical_invariant (piece v)
          ((piece v).iwasawa K hK0').1 φ (hCTinv v) lam u hu y)
        Cabs dd hCabs0 hdd (hAbs v) ψ hψ B hBdecay g
    refine ⟨fun v => ?_, fun v hv => (hProper v hv).2, hS_full⟩
    by_cases hv : J = Jv v
    · rw [hS_full ⟨v, hv⟩]
      exact hdomFull ⟨v, hv⟩ g
    · exact (hProper v hv).1

end Langlands.Global
