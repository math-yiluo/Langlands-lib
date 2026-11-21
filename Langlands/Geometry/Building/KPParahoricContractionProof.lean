import Langlands.Geometry.Building.KPParahoricContractionStatement
import Langlands.Geometry.Building.IwasawaDecompositionProof
import Langlands.Geometry.Building.BuildingFacetIncidence
import Langlands.BruhatTits.IntegralModels.DepthZeroInduction
import Langlands.GroupScheme.Rational.SimultaneousStandardConjugation
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.GroupScheme.Rational.EndpointReductions
import Langlands.GroupScheme.Rational.StandardLeviRootTransport
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Dynamic.Decomposition
import Langlands.GroupScheme.Lie.InnerAdjoint
import Langlands.GroupScheme.Lie.Functoriality

/-!
# Proof of the parahoric contraction statement (contraction clause of KP 13.6.4)
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

section Lie

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- `𝔤_{>0}(ν)` as the sum of the weight spaces of the characters `t ↦ t^{n+1}`. -/
theorem cocharacterPositiveLie_eq_iSup_succ
    (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    cocharacterPositiveLie ν =
      ⨆ n : ℕ, weightSpace ν (Gm.powerHom _ (n + 1)) := by
  rw [cocharacterPositiveLie, RelativeRoot.positiveWeightSpan]
  apply le_antisymm
  · refine iSup_le fun n => le_iSup_of_le (n.1 - 1) ?_
    have hn : n.1 - 1 + 1 = n.1 := Nat.sub_add_cancel n.2
    have he : ((n.1 - 1 : ℕ) : ℤ) + 1 = (n.1 : ℤ) := by exact_mod_cast hn
    simp [he]
  · refine iSup_le fun n => le_iSup_of_le ⟨n + 1, Nat.succ_pos _⟩ ?_
    have hn : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by simp
    rw [Gm.powerHom_apply, hn]
    exact le_rfl

omit [IsAffineHom G.X.hom] in
/-- The constant point of a rational point on the self-coefficient test is its coefficient
point. -/
theorem constantPoint_eq_sectionsCoeffEquiv (g : rationalPoints G) :
    G.constantPoint g ((algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of (CommRingCat.of k) k))) =
      AffineWeil.sectionsCoeffEquiv k G g := by
  apply Over.OverMorphism.ext
  rw [AffineWeil.sectionsCoeffEquiv_left]
  simp [GroupScheme.constantPoint]
  exact Category.id_comp _

variable {R : Type u} [CommRing R] [Algebra R k]

/-- The adjoint action of `h` carries `𝔤_{>0}(ν)` into `𝔤_{>0}(h ν h⁻¹)`. -/
theorem adjoint_mem_cocharacterPositiveLie_innerIso
    (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (h : rationalPoints G)
    {Y : GenericLie R G} (hY : GenericLie.equiv R G Y ∈ cocharacterPositiveLie ν) :
    GenericLie.equiv R G (GenericLie.adjoint R h Y) ∈
      cocharacterPositiveLie (ν ≫ (G.innerIso h).hom) := by
  rw [GenericLie.adjoint_apply, LinearEquiv.apply_symm_apply,
    ← constantPoint_eq_sectionsCoeffEquiv, ← Lie.targetMapLinear_innerIso]
  set f := (G.innerIso h).hom with hf
  have hle : ∀ n : ℕ, weightSpace ν (Gm.powerHom _ (n + 1)) ≤
      (weightSpace (ν ≫ f) (Gm.powerHom _ (n + 1))).comap (Lie.targetMapLinear f k) :=
    fun n _ hx => lieKernelHomLinear_mem_weightSpace f ν _ hx
  have key : (⨆ n : ℕ, weightSpace ν (Gm.powerHom _ (n + 1))) ≤
      (⨆ n : ℕ, weightSpace (ν ≫ f) (Gm.powerHom _ (n + 1))).comap
        (Lie.targetMapLinear f k) :=
    iSup_le fun n => (hle n).trans (Submodule.comap_mono
      (le_iSup (fun n : ℕ => weightSpace (ν ≫ f) (Gm.powerHom _ (n + 1))) n))
  rw [cocharacterPositiveLie_eq_iSup_succ] at hY ⊢
  exact key hY

/-- Points of the dynamic parabolic `P(ν)` preserve `𝔤_{>0}(ν) = Lie U(ν)`. -/
theorem adjoint_mem_cocharacterPositiveLie_of_mem_parabolic [LocallyOfFiniteType G.X.hom]
    (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) {h : rationalPoints G}
    (hh : h ∈ (Dynamic.parabolic ν).carrier (Over.mk (𝟙 _)))
    {Y : GenericLie R G} (hY : GenericLie.equiv R G Y ∈ cocharacterPositiveLie ν) :
    GenericLie.equiv R G (GenericLie.adjoint R h Y) ∈ cocharacterPositiveLie ν := by
  rw [cocharacterPositiveLie_eq_iSup_succ] at hY ⊢
  rw [GenericLie.adjoint_apply, LinearEquiv.apply_symm_apply]
  have hlie := dynamicLie k G ν
  have hy := ((hlie (GenericLie.equiv R G Y).toMul).2.2).2 hY
  apply ((hlie (adjoint G k (AffineWeil.sectionsCoeffEquiv k G h)
    (GenericLie.equiv R G Y)).toMul).2.2).1
  rw [adjoint_val]
  refine Dynamic.conj_mem_unipotent ν ?_ hy
  rw [Lie.constant, Lie.affineMap_apply]
  refine (Dynamic.parabolic ν).comp_mem _ ?_
  rw [← constantPoint_eq_sectionsCoeffEquiv]
  exact (Dynamic.parabolic ν).comp_mem _ hh

end Lie

/-- **Contraction clause of KP Proposition 13.6.4.** -/
theorem parahoricContractionInApartment : ParahoricContractionInApartmentStatement.{u} := by
  intro F _ _ _ _ G _ P hP c x hc hx X hX
  obtain ⟨lam, hlam⟩ := hX
  have hG := P.isConnectedReductive
  have : Smooth G.X.hom := hG.smooth
  have hT : IsSplitTorus P.S.toGrp := P.isMaximalSplitTorus.isSplitSubtorus.1
  obtain ⟨ν₀, hν₀⟩ := hT.exists_genericCocharacter P.i
  obtain ⟨g, J, ζ, hζ, hgζ⟩ :=
    exists_innerIso_comp_eq_standardCocharacter smoothMaximalSplitTorusConjugacy hG
      P.isMaximalSplitTorus (relativeRootSystem F G hG P.S P.i P.isMaximalSplitTorus) hν₀ lam
  have hC : AffineRootSystem.IsChamber P.affineRoots
      (AffineRootSystem.facet P.affineRoots c) := ⟨c, hc, rfl⟩
  obtain ⟨u, hu, n, p, hp, hg⟩ :=
    iwasawaDecomposition F G P Langlands.BruhatTits.IntegralModels.henselianLocalRing_integer
      inferInstance hP _ ν₀ hC hν₀ g
  have hpx : p ∈ P.parahoricAt x := by
    have h1 : P.parahoric (AffineRootSystem.facet P.affineRoots c) ≤ P.parahoric {c} :=
      P.parahoric_anti (Set.singleton_subset_iff.2 (AffineRootSystem.mem_facet_self _ c))
    have h2 : P.parahoric {c} ≤ P.parahoric {x} :=
      sup_le_sup_left
        (P.apartment.sharpFixer_singleton_le_of_mem_facetClosure hP.mem_or_two_smul_mem hx) _
    exact h2 (h1 hp)
  refine ⟨p, hpx, cocharacterAut (normalizingAut P.i n⁻¹) ζ, ?_⟩
  -- Step 1: `Ad(g) X` is contracted by `ζ`.
  have h1 : GenericLie.equiv 𝒪[F] G (GenericLie.adjoint 𝒪[F] g X) ∈
      cocharacterPositiveLie (CommGroupScheme.groupHom ζ ≫ P.i) := by
    have := adjoint_mem_cocharacterPositiveLie_innerIso lam g hlam
    rwa [hgζ] at this
  -- Step 2: `u⁻¹ ∈ P(ζ)`.
  have hu' : u⁻¹ ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ P.i)).carrier
      (Over.mk (𝟙 _)) := by
    have hle := (relativeRootSignInclusions F G hG P.S P.i P.isMaximalSplitTorus ν₀ ζ).1.mpr
      (fun α hα hnn => hζ.pairing_nonneg_of_positive P.i ν₀
        ⟨hα, lt_of_le_of_ne hnn (hν₀ α hα).symm⟩)
    have h₁ := standardUnipotent_le_standardParabolic P.i ν₀ ∅ _ hu
    have h₂ := standardParabolic_empty_le P.i ν₀ _ h₁
    exact Subgroup.inv_mem _ (hle _ h₂)
  have h2 := adjoint_mem_cocharacterPositiveLie_of_mem_parabolic _ hu' h1
  -- Step 3: transport by `n⁻¹`.
  have h3 := adjoint_mem_cocharacterPositiveLie_innerIso _
    ((n⁻¹ : normalizerPoints P.i) : rationalPoints G) h2
  rw [← groupHom_cocharacterAut_comp] at h3
  have hp' : p = ((n⁻¹ : normalizerPoints P.i) : rationalPoints G) * u⁻¹ * g := by
    rw [hg]
    simp only [InvMemClass.coe_inv]
    group
  rw [hp', GenericLie.adjoint_mul, GenericLie.adjoint_mul]
  exact h3

end Langlands.Geometry.Building
