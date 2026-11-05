import Langlands.Geometry.Building.IwahoriWeylQuotientLemmas
import Langlands.Geometry.Building.IwahoriWeylChamberLemmas
import Langlands.Geometry.Building.AffineChamberTransitivityStatement
import Langlands.Geometry.Building.UnramifiedZeroTransport
import Langlands.Geometry.Building.UnramifiedZeroIndependenceStatement
import Langlands.GroupScheme.Rational.BruhatContractionReduction
import Langlands.GroupScheme.RepresentedSubgroupTransport
import Langlands.Geometry.Building.SimplyConnectedImageNormal
import Langlands.Geometry.Building.KPSimplyConnectedImageNormal
import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.Geometry.Building.KPMinimalLeviZeroStatement
import Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylStatement
import Langlands.GroupScheme.Rational.SimplyConnectedCentralizerProductStatement
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.RelativeWeylRootKernel
import Langlands.GroupScheme.Rational.RelativeWeylCharacterAction
import Langlands.GroupScheme.Absolute.RegularPerturbation

/-!
# Reductions for the Iwahori–Weyl exact sequence and chamber splitting

For the actual building data `P` of a connected reductive group over a nonarchimedean local
field, under the apartment axioms, this module derives KP Theorem 7.8.1(1)
(`IwahoriWeylExactSequenceStatement`) from four source statements, each an explicit hypothesis:

* KP Lemma 2.6.24, independence of `Z(K)^0` from its data
  (`UnramifiedZeroPointsIndependenceStatement`), giving `Z(F)^0 ⊴ N(F)`;
* KP Fact 2.6.22, `G(F) = G(F)^♮ · Z(F)` (`SimplyConnectedCentralizerProductStatement`), giving
  `G(F)^0 ⊴ G(F)` and the surjectivity of `W̃^0 → G(F)/G(F)^0`;
* KP Theorem 7.5.3(2), the image `W(Ψ)` of `N(F) ∩ G(F)^♮`
  (`SimplyConnectedNormalizerAffineWeylStatement`), giving the image of `N(F) ∩ G(F)^0`;
* KP Corollary 2.6.28, `G(F)^0 ∩ Z(F)^1 = Z(F)^0`
  (`ZeroSubgroupDatum.CentralizerZeroIntersectionStatement`), giving the kernel of the action.

It then derives KP 7.8.2 (`IwahoriWeylChamberSplittingStatement`) from KP Theorem 7.8.1(1) and
the simple transitivity of `W(Ψ)` on chambers (`AffineChamberSimpleTransitivityStatement`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LinearAlgebra.RationalSpan TensorProduct

namespace Langlands.Geometry.Building

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- KP Fact 2.6.22 for the data of `P`: `G(F) = G(F)^♮ · Z(F)`. -/
theorem exists_simplyConnectedImage_mul_centralizer
    (hprod : SimplyConnectedCentralizerProductStatement.{u}) (g : rationalPoints G) :
    ∃ c ∈ P.simplyConnectedImage, ∃ z : rationalPoints P.centralizer.Z,
      g = c * rationalPoints.map P.centralizer.j z := by
  obtain ⟨c, z, hg⟩ := hprod F P.S G P.centralizer.Z P.zeroDatum.C P.zeroDatum.D P.i
    P.centralizer.j P.zeroDatum.d P.zeroDatum.π P.zeroDatum.isSimplyConnectedDerivedCover
    P.zeroDatum.isMaximalSplitTorus P.centralizer.isRepresentedBy g
  exact ⟨_, ⟨c, rfl⟩, z, hg⟩

/-- Conjugation by `j(z)`, `z ∈ Z(F)`, preserves `G(F)^0` once `Z(F)^0` is normal in `N(F)`. -/
theorem conj_map_mem_zeroSubgroup [P.normalizerZero.Normal] (z : rationalPoints P.centralizer.Z)
    {x : rationalPoints G} (hx : x ∈ P.zeroSubgroup) :
    rationalPoints.map P.centralizer.j z * x * (rationalPoints.map P.centralizer.j z)⁻¹ ∈
      P.zeroSubgroup := by
  obtain ⟨c, hc, y, hy, rfl⟩ := P.zeroDatum.mem_zeroSubgroup_iff.1 hx
  have hc' : rationalPoints.map P.centralizer.j z * c *
      (rationalPoints.map P.centralizer.j z)⁻¹ ∈ P.simplyConnectedImage :=
    (inferInstance : P.zeroDatum.simplyConnectedImage.Normal).conj_mem c hc _
  have hy' : P.centralizer.toNormalizer z * P.centralizer.toNormalizer y *
      (P.centralizer.toNormalizer z)⁻¹ ∈ P.normalizerZero :=
    (inferInstance : P.normalizerZero.Normal).conj_mem _ ⟨y, hy, rfl⟩ _
  rw [mem_normalizerZero_iff] at hy'
  have hy'' : rationalPoints.map P.centralizer.j z * rationalPoints.map P.centralizer.j y *
      (rationalPoints.map P.centralizer.j z)⁻¹ ∈ P.zeroSubgroup :=
    P.zeroDatum.map_centralizerZero_le_zeroSubgroup (by simpa using hy')
  have := P.zeroSubgroup.mul_mem (P.zeroDatum.simplyConnectedImage_le_zeroSubgroup hc') hy''
  simpa [mul_assoc] using this

/-- `G(F)^0` is normal in `G(F)`, from KP Fact 2.6.22 and the normality of `Z(F)^0` in
`N(F)` (KP Lemma 2.6.24). -/
theorem zeroSubgroup_normal [P.normalizerZero.Normal]
    (hprod : SimplyConnectedCentralizerProductStatement.{u}) : P.zeroSubgroup.Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨c, hc, z, rfl⟩ := P.exists_simplyConnectedImage_mul_centralizer hprod g
  have h1 := P.conj_map_mem_zeroSubgroup z hx
  have hc0 := P.zeroDatum.simplyConnectedImage_le_zeroSubgroup hc
  have := P.zeroSubgroup.mul_mem (P.zeroSubgroup.mul_mem hc0 h1) (P.zeroSubgroup.inv_mem hc0)
  simpa [mul_assoc] using this

/-- `W̃^0 → G(F)/G(F)^0` is surjective, from KP Fact 2.6.22. -/
theorem toComponents_surjective [P.normalizerZero.Normal] [P.zeroSubgroup.Normal]
    (hprod : SimplyConnectedCentralizerProductStatement.{u}) :
    Function.Surjective P.toComponents := by
  rw [toComponents_surjective_iff]
  intro g
  obtain ⟨c, hc, z, rfl⟩ := P.exists_simplyConnectedImage_mul_centralizer hprod g
  refine ⟨P.centralizer.toNormalizer z, ?_⟩
  rw [QuotientGroup.eq]
  have hc0 := P.zeroDatum.simplyConnectedImage_le_zeroSubgroup hc
  have := (inferInstance : P.zeroSubgroup.Normal).conj_mem c hc0
    (rationalPoints.map P.centralizer.j z)⁻¹
  simpa [mul_assoc] using this

/-- `Z(F)^0` acts trivially on the apartment. -/
theorem normalizerAffineEquiv_eq_one_of_mem_normalizerZero {n : normalizerPoints P.i}
    (hn : n ∈ P.normalizerZero) : P.apartment.normalizerAffineEquiv n = 1 := by
  obtain ⟨z, hz, rfl⟩ := hn
  have hz1 := P.zeroDatum.centralizerZero_le_rationalCommonNormKernel hz
  exact AffineEquiv.ext fun x => P.isOmegaCompatible.smul_eq_self hz1 x

/-- The range statement of KP Theorem 7.5.3(2) for `N^♮ = N(F) ∩ G(F)^♮` and the data `P`. -/
theorem map_simplyConnectedImage_normalizerAffineEquiv
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hW : SimplyConnectedNormalizerAffineWeylStatement.{u}) :
    (P.simplyConnectedImage.subgroupOf (normalizerPoints P.i)).map
        P.apartment.normalizerAffineEquiv =
      AffineRootSystem.affineWeylGroup P.affineRoots :=
  hW F G P hP

/-- `N(F) ∩ G(F)^0` acts on the apartment through `W(Ψ)`. -/
theorem normalizerAffineEquiv_mem_affineWeylGroup
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hW : SimplyConnectedNormalizerAffineWeylStatement.{u}) (n : P.normalizerZeroComponent) :
    P.apartment.normalizerAffineEquiv n ∈ AffineRootSystem.affineWeylGroup P.affineRoots := by
  have hn : ((n : normalizerPoints P.i) : rationalPoints G) ∈ P.zeroSubgroup :=
    Subgroup.mem_subgroupOf.1 n.property
  obtain ⟨c, hc, y, hy, hcy⟩ := P.zeroDatum.mem_zeroSubgroup_iff.1 hn
  set m : normalizerPoints P.i :=
    (n : normalizerPoints P.i) * (P.centralizer.toNormalizer y)⁻¹ with hm
  have hmc : (m : rationalPoints G) = c := by
    rw [hm, Subgroup.coe_mul, Subgroup.coe_inv, coe_centralizerToNormalizer, ← hcy,
      mul_inv_cancel_right]
  have hm' : m ∈ P.simplyConnectedImage.subgroupOf (normalizerPoints P.i) := by
    rw [Subgroup.mem_subgroupOf, hmc]
    exact hc
  have hnm : (n : normalizerPoints P.i) = m * P.centralizer.toNormalizer y := by
    rw [hm, inv_mul_cancel_right]
  rw [hnm, map_mul, P.normalizerAffineEquiv_eq_one_of_mem_normalizerZero ⟨y, hy, rfl⟩,
    mul_one, ← P.map_simplyConnectedImage_normalizerAffineEquiv hP hW]
  exact ⟨m, hm', rfl⟩

/-- Every element of `W(Ψ)` is the action of an element of `N(F) ∩ G(F)^0`. -/
theorem exists_normalizerZeroComponent_normalizerAffineEquiv_eq
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hW : SimplyConnectedNormalizerAffineWeylStatement.{u})
    (w : AffineRootSystem.affineWeylGroup P.affineRoots) :
    ∃ n : P.normalizerZeroComponent,
      P.apartment.normalizerAffineEquiv n = (w : P.Apartment ≃ᵃ[ℝ] P.Apartment) := by
  have hw : (w : P.Apartment ≃ᵃ[ℝ] P.Apartment) ∈
      (P.simplyConnectedImage.subgroupOf (normalizerPoints P.i)).map
        P.apartment.normalizerAffineEquiv := by
    rw [P.map_simplyConnectedImage_normalizerAffineEquiv hP hW]
    exact w.property
  obtain ⟨m, hm, hmw⟩ := hw
  refine ⟨⟨m, ?_⟩, hmw⟩
  rw [normalizerZeroComponent, Subgroup.mem_subgroupOf]
  exact P.zeroDatum.simplyConnectedImage_le_zeroSubgroup (Subgroup.mem_subgroupOf.1 hm)

/-- An element of `N(F)` whose linear action on the apartment is trivial centralizes `S`
(faithfulness of the relative Weyl group on `V(S)/V(S)^Φ`). -/
theorem mem_centralizerPoints_of_translationAction_eq_one {n : normalizerPoints P.i}
    (hn : translationAction P.i n = 1) :
    (n : rationalPoints G) ∈ centralizerPoints P.i := by
  have hT : IsSplitTorus P.S.toGrp := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hroots : ∀ α ∈ relativeRoots P.i, weylAction P.i n⁻¹ α = α := by
    intro α hα
    apply hT.isPerfPair_latticePairing.bijective_left.1
    apply LinearMap.ext
    intro ν
    have hq := congrArg (fun e : TranslationSpace P.i ≃ₗ[ℝ] TranslationSpace P.i =>
      e (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] ν))) hn
    simp only [translationAction_mk, LinearEquiv.coe_one, id] at hq
    have hv := (Submodule.Quotient.eq _).1 hq
    rw [mem_rootAnnihilator] at hv
    have h := hv α hα
    rw [map_sub, RealTorusSpace.eval_normalizer_smul, sub_eq_zero, RealTorusSpace.eval_tmul,
      RealTorusSpace.eval_tmul, one_mul, one_mul] at h
    exact_mod_cast h
  have hspan := relativeRootsRestrictedCharactersSpan F G P.isConnectedReductive P.S P.i
    P.isMaximalSplitTorus
  have h1 : weylAction P.i n⁻¹ = 1 := hT.weylAction_eq_one_of_fixed_roots P.i hspan n⁻¹ hroots
  have h2 : weylAction P.i n = 1 := by
    rw [map_inv] at h1
    exact inv_eq_one.1 h1
  exact (hT.weylAction_eq_one_iff P.i n).1 h2

/-- A point of `N(F)` centralizing `S` comes from `Z(F)`. -/
theorem exists_toNormalizer_eq_of_mem_centralizerPoints {n : normalizerPoints P.i}
    (hn : (n : rationalPoints G) ∈ centralizerPoints P.i) :
    ∃ z : rationalPoints P.centralizer.Z, P.centralizer.toNormalizer z = n := by
  rw [← torusCentralizer_carrier_base, ← P.centralizer.isRepresentedBy.2] at hn
  obtain ⟨z, hz⟩ := hn
  exact ⟨z, Subtype.ext hz⟩

/-- A real cocharacter killed by the relative roots and by the restrictions of all rational
characters of `G` is killed by every character of `S`. -/
theorem eval_eq_zero_of_relativeRoots_of_torusCharacterRestrict {v : RealTorusSpace.V P.S}
    (hroot : ∀ α ∈ relativeRoots P.i, RealTorusSpace.eval P.S α v = 0)
    (hres : ∀ χ : rationalCharacters G,
      RealTorusSpace.eval P.S (torusCharacterRestrict P.i χ) v = 0)
    (β : characterLattice P.S) : RealTorusSpace.eval P.S β v = 0 := by
  let l : characterLattice P.S →ₗ[ℤ] ℝ :=
    (AddMonoidHom.mk' (fun β => RealTorusSpace.eval P.S β v) (by
      intro β γ
      simp only [RealTorusSpace.eval_eq_pair, tmul_add, map_add, LinearMap.add_apply])).toIntLinearMap
  have hl : ∀ β, l β = RealTorusSpace.eval P.S β v := fun _ => rfl
  let g : ℚ ⊗[ℤ] characterLattice P.S →ₗ[ℚ] ℝ := l.liftBaseChange ℚ
  have hg : ∀ β, g (toRat β) = RealTorusSpace.eval P.S β v := by
    intro β
    rw [toRat_apply, LinearMap.liftBaseChange_tmul, one_smul, hl]
  have hspan := relativeRootsRestrictedCharactersSpan F G P.isConnectedReductive P.S P.i
    P.isMaximalSplitTorus
  have hle : Submodule.span ℚ
      (toRat '' (relativeRoots P.i ∪ Set.range (torusCharacterRestrict P.i))) ≤
        LinearMap.ker g := by
    rw [Submodule.span_le]
    rintro _ ⟨γ, hγ, rfl⟩
    change g (toRat γ) = 0
    rw [hg]
    rcases hγ with hγ | ⟨χ, rfl⟩
    · exact hroot γ hγ
    · exact hres χ
  have hβ : toRat β ∈ LinearMap.ker g := hle (hspan ▸ Submodule.mem_top)
  rw [LinearMap.mem_ker, hg] at hβ
  exact hβ

/-- If `j(z) ∈ G(F)^1`, then `ν(z)` is killed by the restriction to `S` of every rational
character of `G`. -/
theorem eval_torusCharacterRestrict_translation {z : rationalPoints P.centralizer.Z}
    (hz : rationalPoints.map P.centralizer.j z ∈ Plancherel.rationalCommonNormKernel G)
    (χ : rationalCharacters G) :
    RealTorusSpace.eval P.S (torusCharacterRestrict P.i χ)
      (P.centralizer.translation z).toAdd = 0 := by
  have hres : BruhatTits.Cartan.characterRestriction P.centralizer.s
      (characterRestrict P.centralizer.j χ) = torusCharacterRestrict P.i χ := by
    simp only [BruhatTits.Cartan.characterRestriction, torusCharacterRestrict, AddMonoidHom.coe_comp,
      Function.comp_apply]
    rw [← AddMonoidHom.comp_apply (characterRestrict P.centralizer.s), ← characterRestrict_comp,
      P.centralizer.comp_eq]
  rw [← hres, eval_centralizerTranslation]
  rw [Plancherel.mem_rationalCommonNormKernel_iff_valuation] at hz
  have h := hz χ
  rw [Plancherel.rationalCharacterValuation_apply] at h
  rw [Plancherel.rationalCharacterValuation_apply, rationalCharacterEval_characterRestrict, h]
  simp

/-- If `z ∈ Z(F)` acts trivially on the apartment, then `ν(z)` is killed by the relative
roots. -/
theorem eval_translation_eq_zero_of_normalizerAffineEquiv_eq_one
    {z : rationalPoints P.centralizer.Z}
    (hz : P.apartment.normalizerAffineEquiv (P.centralizer.toNormalizer z) = 1) :
    ∀ α ∈ relativeRoots P.i,
      RealTorusSpace.eval P.S α (P.centralizer.translation z).toAdd = 0 := by
  rw [P.isOmegaCompatible.normalizerAffineEquiv_eq z] at hz
  obtain ⟨x⟩ := (inferInstance : Nonempty P.Apartment)
  have hx := congrArg (fun e : P.Apartment ≃ᵃ[ℝ] P.Apartment => e x) hz
  simp only [AffineEquiv.constVAdd_apply, AffineEquiv.coe_one, id] at hx
  have h0 : (Submodule.Quotient.mk (P.centralizer.translation z).toAdd :
      TranslationSpace P.i) = 0 := by
    rw [← vadd_right_cancel_iff x, zero_vadd]
    exact hx
  rw [Submodule.Quotient.mk_eq_zero, mem_rootAnnihilator] at h0
  exact h0

/-- If `z ∈ Z(F)` acts trivially on the apartment and `j(z) ∈ G(F)^1`, then `z ∈ Z(F)^1`. -/
theorem mem_rationalCommonNormKernel_of_normalizerAffineEquiv_eq_one
    {z : rationalPoints P.centralizer.Z}
    (hz : P.apartment.normalizerAffineEquiv (P.centralizer.toNormalizer z) = 1)
    (hjz : rationalPoints.map P.centralizer.j z ∈ Plancherel.rationalCommonNormKernel G) :
    z ∈ Plancherel.rationalCommonNormKernel P.centralizer.Z := by
  rw [Plancherel.mem_rationalCommonNormKernel_iff_valuation]
  intro χ
  have h := P.eval_eq_zero_of_relativeRoots_of_torusCharacterRestrict
    (P.eval_translation_eq_zero_of_normalizerAffineEquiv_eq_one hz)
    (P.eval_torusCharacterRestrict_translation hjz)
    (BruhatTits.Cartan.characterRestriction P.centralizer.s χ)
  rw [eval_centralizerTranslation, neg_eq_zero] at h
  exact_mod_cast h

/-- The kernel of the action of `N(F) ∩ G(F)^0` on the apartment is `Z(F)^0`, given KP
Corollary 2.6.28 for the data of `P`. -/
theorem normalizerAffineEquiv_eq_one_iff
    (hcor : P.zeroDatum.CentralizerZeroIntersectionStatement) (n : P.normalizerZeroComponent) :
    P.apartment.normalizerAffineEquiv n = 1 ↔ (n : normalizerPoints P.i) ∈ P.normalizerZero := by
  refine ⟨fun hn => ?_, P.normalizerAffineEquiv_eq_one_of_mem_normalizerZero⟩
  have hlin : translationAction P.i (n : normalizerPoints P.i) = 1 :=
    congrArg AffineEquiv.linear hn
  obtain ⟨z, hz⟩ := P.exists_toNormalizer_eq_of_mem_centralizerPoints
    (P.mem_centralizerPoints_of_translationAction_eq_one hlin)
  have hjz : rationalPoints.map P.centralizer.j z ∈ P.zeroSubgroup := by
    have h := Subgroup.mem_subgroupOf.1 n.property
    rwa [← hz, coe_centralizerToNormalizer] at h
  have hz1 := P.mem_rationalCommonNormKernel_of_normalizerAffineEquiv_eq_one (hz ▸ hn)
    (P.zeroDatum.zeroSubgroup_le_rationalCommonNormKernel hjz)
  have hz0 : z ∈ P.centralizerZero := by
    change z ∈ P.zeroDatum.centralizerZero
    change P.zeroDatum.zeroSubgroup.comap (rationalPoints.map P.centralizer.j) ⊓
      Plancherel.rationalCommonNormKernel P.centralizer.Z = P.zeroDatum.centralizerZero at hcor
    rw [← hcor]
    exact ⟨hjz, hz1⟩
  rw [← hz]
  exact ⟨z, hz0, rfl⟩

/-! ### Normality of `Z(F)^0` in `N(F)` -/

/-- Conjugation by `n ∈ N(F)` restricted to the centralizer `Z = Z_G(S)`. -/
def centralizerConjIso (n : normalizerPoints P.i) : P.centralizer.Z ≅ P.centralizer.Z :=
  SubgroupFunctor.IsRepresentedBy.isoOfComap P.centralizer.isRepresentedBy
    P.centralizer.isRepresentedBy (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X))
    (torusCentralizer_comap_innerIso_normalizer P.i n)

theorem map_centralizerConjIso (n : normalizerPoints P.i) (z : rationalPoints P.centralizer.Z) :
    rationalPoints.map P.centralizer.j (rationalPoints.map (P.centralizerConjIso n).hom z) =
      (n : rationalPoints G) * rationalPoints.map P.centralizer.j z *
        (n : rationalPoints G)⁻¹ := by
  rw [← rationalPoints.map_comp_apply, centralizerConjIso,
    SubgroupFunctor.IsRepresentedBy.isoOfComap_hom_comp, rationalPoints.map_comp_apply,
    rationalPoints.map_apply (G.innerIso _).hom, comp_innerIso_hom, constantPoint_self]

/-- Conjugation by `n ∈ N(F)` preserves `Z(F)^0`, given the independence of `Z(K)^0` from its
defining data (KP Lemma 2.6.24). -/
theorem map_centralizerConjIso_mem_centralizerZero
    (hind : UnramifiedZeroPointsIndependenceStatement.{u}) (n : normalizerPoints P.i)
    {z : rationalPoints P.centralizer.Z} (hz : z ∈ P.centralizerZero) :
    rationalPoints.map (P.centralizerConjIso n).hom z ∈ P.centralizerZero :=
  map_mem_anisotropicZeroPoints hind P.zeroDatum.centralizerDatum (P.centralizerConjIso n) hz

/-- `Z(F)^0` is normal in `N(F)`, from KP Lemma 2.6.24. -/
theorem normalizerZero_normal (hind : UnramifiedZeroPointsIndependenceStatement.{u}) :
    P.normalizerZero.Normal := by
  refine ⟨fun m hm n => ?_⟩
  obtain ⟨z, hz, rfl⟩ := hm
  refine ⟨_, P.map_centralizerConjIso_mem_centralizerZero hind n hz, ?_⟩
  apply Subtype.ext
  rw [coe_centralizerToNormalizer, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_centralizerToNormalizer]
  exact P.map_centralizerConjIso n z

/-! ### Assembly -/

/-- KP Theorem 7.8.1(1) for the data `P`, from the four prerequisite statements. -/
theorem iwahoriWeylExactSequence_of_prerequisites
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hind : UnramifiedZeroPointsIndependenceStatement.{u})
    (hprod : SimplyConnectedCentralizerProductStatement.{u})
    (hW : SimplyConnectedNormalizerAffineWeylStatement.{u})
    (hcor : P.zeroDatum.CentralizerZeroIntersectionStatement) :
    P.IwahoriWeylExactSequence := by
  have hN : P.normalizerZero.Normal := P.normalizerZero_normal hind
  have hG : P.zeroSubgroup.Normal := P.zeroSubgroup_normal hprod
  exact ⟨hN, hG, P.exists_affinePart_equiv_of_action
      (P.normalizerAffineEquiv_mem_affineWeylGroup hP hW) (P.normalizerAffineEquiv_eq_one_iff hcor)
      (P.exists_normalizerZeroComponent_normalizerAffineEquiv_eq hP hW),
    P.toComponents_ker_eq_affinePart, P.toComponents_surjective hprod⟩

end ParahoricBuildingData

/-- KP Theorem 7.8.1(1) from the four prerequisite statements: KP Lemma 2.6.24
(independence), KP Fact 2.6.22, KP Theorem 7.5.3(2) (range) and KP Corollary 2.6.28. -/
theorem iwahoriWeylExactSequenceStatement_of_prerequisites
    (hind : UnramifiedZeroPointsIndependenceStatement.{u})
    (hprod : SimplyConnectedCentralizerProductStatement.{u})
    (hW : SimplyConnectedNormalizerAffineWeylStatement.{u})
    (hcor : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] {S : CommGroupScheme (Spec (CommRingCat.of F))}
      {G Z : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G} {j : Z ⟶ G}
      (E : ZeroSubgroupDatum i j), E.CentralizerZeroIntersectionStatement) :
    IwahoriWeylExactSequenceStatement.{u} := by
  intro F _ _ _ _ G _ P hP
  exact P.iwahoriWeylExactSequence_of_prerequisites hP hind hprod hW (hcor F P.zeroDatum)

/-- KP 7.8.2 from KP Theorem 7.8.1(1) and the simple transitivity of the affine Weyl group on
chambers (KP Lemma 1.3.17). -/
theorem iwahoriWeylChamberSplittingStatement_of_exactSequence
    (hex : IwahoriWeylExactSequenceStatement.{u})
    (htrans : AffineChamberSimpleTransitivityStatement.{u, u}) :
    IwahoriWeylChamberSplittingStatement.{u} := by
  intro F _ _ _ _ G _ P hP C hC
  exact iwahoriWeylChamberReduction F G P hP (hex F G P hP)
    (htrans _ P.Apartment P.affineRoots hP.isAffineRootSystem_affineRoots) C hC

end Langlands.Geometry.Building
