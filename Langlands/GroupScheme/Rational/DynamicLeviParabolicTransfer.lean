import Langlands.GroupScheme.Rational.ParabolicFunctorCocharacter
import Langlands.GroupScheme.Rational.DynamicLeviCocharacterRealizationStatement
import Langlands.GroupScheme.Rational.DynamicLeviParabolicCorrespondenceStatement
import Langlands.GroupScheme.Rational.ParabolicCocharacterConjugacy
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsStatement
import Langlands.GroupScheme.Rational.RelativeRootNegationStatement
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.PointDecomposition
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.LeviParabolicExtension

/-! # Parabolicity transfer along a represented dynamic Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Conjugation by a point of the dynamic centralizer fixes the cocharacter. -/
theorem Dynamic.comp_innerIso_hom_of_mem_centralizer {S : Scheme.{u}} {G : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ G) {z : Over.mk (𝟙 S) ⟶ G.X}
    (hz : z ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 S))) :
    χ ≫ (G.innerIso z).hom = χ := by
  rw [← torusCentralizer_gm_eq_dynamicCentralizer] at hz
  refine hom_ext_points fun U x => ?_
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
  have hc : Commute (G.constantPoint z U) (x ≫ χ.hom.hom) := hz U (Over.homMk U.hom (by simp)) x
  rw [hc.eq, mul_inv_cancel_right]

variable {k : Type u} [Field k]

/-- Root-sign step: if `P(ζ) ≤ P(ξ)` for two cocharacters of a maximal split torus,
then `U(ξ) ≤ P(ζ)`, given the root-sign inclusions and negation stability of the
actual relative roots. -/
theorem unipotent_le_parabolic_of_parabolic_le
    (hRS : RelativeRootSignInclusionsStatement.{u}) (hNeg : RelativeRootNegationStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (ζ ξ : cocharacterLattice T)
    (h : Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i)) :
    Dynamic.unipotent (CommGroupScheme.groupHom ξ ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) := by
  have := hG.isAffineHom
  have := hG.smooth
  have hpos : ∀ α ∈ relativeRoots i,
      0 < latticePairing T α ξ → 0 < latticePairing T α ζ := by
    intro α hα hξ
    by_contra hζ
    have h1 := (hRS k G hG T i hi ζ ξ).1.1 h (-α) (hNeg k G hG T i hi α hα)
      (by simp only [map_neg, LinearMap.neg_apply]; omega)
    simp only [map_neg, LinearMap.neg_apply] at h1
    omega
  obtain ⟨M, hM⟩ :=
    ((hi.isSplitSubtorus.1.finite_relativeRoots i).image
      fun α => latticePairing T α ξ).bddAbove
  have hM' : ∀ α ∈ relativeRoots i, latticePairing T α ξ ≤ M :=
    fun α hα => hM ⟨α, hα, rfl⟩
  set N : ℤ := max M 0 + 1 with hN
  have hpair : ∀ α : characterLattice T,
      latticePairing T α (N • ζ + ξ) = N * latticePairing T α ζ + latticePairing T α ξ := by
    intro α
    simp only [map_add, map_zsmul, smul_eq_mul]
  have hU : Dynamic.unipotent (CommGroupScheme.groupHom ξ ≫ i) ≤
      Dynamic.unipotent (CommGroupScheme.groupHom (N • ζ + ξ) ≫ i) := by
    refine (hRS k G hG T i hi ξ (N • ζ + ξ)).2 fun α hα hξ => ?_
    have hζ := hpos α hα hξ
    rw [hpair]
    have : 0 < N := by omega
    nlinarith
  have hP : Dynamic.parabolic (CommGroupScheme.groupHom (N • ζ + ξ) ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) := by
    refine (hRS k G hG T i hi (N • ζ + ξ) ζ).1.2 fun α hα hη => ?_
    rw [hpair] at hη
    have hξM := hM' α hα
    by_contra hζ
    have h1 : latticePairing T α ζ + 1 ≤ 0 := by omega
    have h2 : N * (latticePairing T α ζ + 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by omega) h1
    have h3 : M ≤ max M 0 := le_max_left _ _
    nlinarith
  exact hU.trans ((Dynamic.unipotent_le_parabolic _).trans hP)

namespace Dynamic

variable {G L : GroupScheme (Spec (CommRingCat.of k))}

/-- Descent of dynamic parabolics: a dynamic parabolic of a connected reductive group
contained in `P(χ)` is the exact extension of a dynamic parabolic of a closed
representative of the dynamic centralizer of `χ`, given conjugacy of maximal split tori,
connectedness of dynamic subgroups, the root-sign inclusions and negation stability of
the actual relative roots. -/
theorem exists_parabolic_eq_extendFromCentralizer_of_parabolic_le
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hconn : DynamicConnectedStatement.{u})
    (hRS : RelativeRootSignInclusionsStatement.{u}) (hNeg : RelativeRootNegationStatement.{u})
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (j : L ⟶ G) (hjc : IsClosedSubgroup j) (hj : (centralizer χ).IsRepresentedBy j)
    (ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (hψ : parabolic ψ ≤ parabolic χ) :
    ∃ ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ L,
      parabolic ψ = extendFromCentralizer χ j hj (parabolic ν) := by
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  have := hG.isSeparated
  obtain ⟨T, i, ν₁, hi, rfl⟩ := cocharacterMaximalSplitTorus k G ψ
  obtain ⟨g, ξ, hg, hgξ⟩ :=
    exists_mem_parabolic_innerIso_comp_eq_cocharacter hconj dynamicSmooth hconn hi ν₁ χ hψ
  obtain ⟨⟨u, z⟩, ⟨hu, hz, rfl⟩, -⟩ := RationalPoint.existsUnique_unipotent_mul_levi χ hg
  have huξ : χ ≫ (G.innerIso u).hom = CommGroupScheme.groupHom ξ ≫ i := by
    rw [innerIso_mul_hom, ← Category.assoc, comp_innerIso_hom_of_mem_centralizer χ hz] at hgξ
    exact hgξ
  have hu' : u⁻¹ ∈ (unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
    Subgroup.inv_mem _ hu
  have hPχ : parabolic χ = parabolic (CommGroupScheme.groupHom ξ ≫ i) := by
    have h1 := parabolic_eq_comap_of_iso χ (G.innerIso u)
    rw [huξ] at h1
    have h2 := (SubgroupFunctor.eq_comap_iso_iff (G.innerIso u)).1 h1
    rwa [← innerIso_inv_hom, SubgroupFunctor.comap_innerIso_hom_eq_of_mem _
      (unipotent_le_parabolic χ _ hu')] at h2
  have hUχ : unipotent χ = unipotent (CommGroupScheme.groupHom ξ ≫ i) := by
    have h1 := unipotent_eq_comap_of_iso χ (G.innerIso u)
    rw [huξ] at h1
    have h2 := (SubgroupFunctor.eq_comap_iso_iff (G.innerIso u)).1 h1
    rwa [← innerIso_inv_hom, SubgroupFunctor.comap_innerIso_hom_eq_of_mem _ hu'] at h2
  have hUψ : unipotent χ ≤ parabolic (CommGroupScheme.groupHom ν₁ ≫ i) := by
    rw [hUχ]
    exact unipotent_le_parabolic_of_parabolic_le hRS hNeg hG hi ν₁ ξ (hψ.trans hPχ.le)
  have hψ₀ : parabolic (CommGroupScheme.groupHom ν₁ ≫ i ≫ (G.innerIso u).inv) =
      parabolic (CommGroupScheme.groupHom ν₁ ≫ i) := by
    have h1 := parabolic_eq_comap_of_iso
      (CommGroupScheme.groupHom ν₁ ≫ i ≫ (G.innerIso u).inv) (G.innerIso u)
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id] at h1
    rw [h1, SubgroupFunctor.comap_innerIso_hom_eq_of_mem _ (hUψ _ hu)]
  have hχ : χ = CommGroupScheme.groupHom ξ ≫ i ≫ (G.innerIso u).inv := by
    rw [← Category.assoc, ← huξ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hj' : (centralizer (CommGroupScheme.groupHom ξ ≫ i ≫ (G.innerIso u).inv)).IsRepresentedBy
      j := hχ ▸ hj
  refine ⟨CommGroupScheme.groupHom ν₁ ≫
    torusFactor (i ≫ (G.innerIso u).inv) (CommGroupScheme.groupHom ξ) hj', ?_⟩
  rw [parabolic_eq_comap_of_isClosedSubgroup _ j hjc, Category.assoc, torusFactor_comp, hψ₀]
  exact (extendFromCentralizer_comap χ j hj hUψ hψ).symm

/-- The exact extension of an actual parabolic of a represented dynamic Levi
is an actual parabolic of the ambient group, conditional on the three named
published structure statements. -/
theorem isParabolicFunctor_extendFromCentralizer_of_structural_statements
    (hPD : ParabolicDynamicStatement.{u})
    (hCR : DynamicCentralizerReductiveStatement.{u})
    (hReal : DynamicLeviCocharacterRealizationStatement.{u})
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (j : L ⟶ G) (hjc : IsClosedSubgroup j) (hj : (centralizer χ).IsRepresentedBy j)
    {F : SubgroupFunctor L} (hF : IsParabolicFunctor F) :
    IsParabolicFunctor (extendFromCentralizer χ j hj F) := by
  have hL : IsConnectedReductive L := hCR k G hG χ L j hjc hj
  obtain ⟨ν, rfl⟩ := hF.exists_dynamicCocharacter hPD hL
  obtain ⟨ψ, hψ, -, -⟩ := hReal k G hG χ L j hjc hj ν
  rw [← hψ]
  exact isParabolicFunctor_dynamic_of_parabolicDynamic hPD hG ψ

/-- Every actual ambient parabolic contained in `parabolic χ` is the exact
extension of an actual parabolic of the represented dynamic Levi, given the
descent of dynamic parabolics for this `χ` and `j` as the explicit input
`hdesc`, together with the two named published structure statements. -/
theorem exists_isParabolicFunctor_extendFromCentralizer_eq_of_descent
    (hPD : ParabolicDynamicStatement.{u})
    (hCR : DynamicCentralizerReductiveStatement.{u})
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (j : L ⟶ G) (hjc : IsClosedSubgroup j) (hj : (centralizer χ).IsRepresentedBy j)
    (hdesc : ∀ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      parabolic ψ ≤ parabolic χ →
        ∃ ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ L,
          parabolic ψ = extendFromCentralizer χ j hj (parabolic ν))
    {Q : SubgroupFunctor G} (hQ : IsParabolicFunctor Q) (hQχ : Q ≤ parabolic χ) :
    ∃ F : SubgroupFunctor L, IsParabolicFunctor F ∧ extendFromCentralizer χ j hj F = Q := by
  have hL : IsConnectedReductive L := hCR k G hG χ L j hjc hj
  obtain ⟨ψ, rfl⟩ := hQ.exists_dynamicCocharacter hPD hG
  obtain ⟨ν, hν⟩ := hdesc ψ hQχ
  exact ⟨parabolic ν, isParabolicFunctor_dynamic_of_parabolicDynamic hPD hL ν, hν.symm⟩

/-- Exact extension as an order isomorphism from the actual parabolics of a closed
representative `L` of the dynamic centralizer of `χ` onto the actual parabolics of `G`
contained in `P(χ)`, conditional on seven named published structure statements; its
inverse is inverse image along `j`. -/
def extendFromCentralizerOrderIsoOfStructuralStatements
    (hPD : ParabolicDynamicStatement.{u})
    (hCR : DynamicCentralizerReductiveStatement.{u})
    (hReal : DynamicLeviCocharacterRealizationStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hconn : DynamicConnectedStatement.{u})
    (hRS : RelativeRootSignInclusionsStatement.{u}) (hNeg : RelativeRootNegationStatement.{u})
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (j : L ⟶ G) (hjc : IsClosedSubgroup j) (hj : (centralizer χ).IsRepresentedBy j) :
    ParabolicFunctor L ≃o ParabolicFunctorBelow (parabolic χ) :=
  haveI := hG.isSeparated
  extendFromCentralizerOrderIso χ j hj
    (fun _ hF => isParabolicFunctor_extendFromCentralizer_of_structural_statements
      hPD hCR hReal hG χ j hjc hj hF)
    (fun _ hQ hQχ => exists_isParabolicFunctor_extendFromCentralizer_eq_of_descent
      hPD hCR hG χ j hjc hj
      (exists_parabolic_eq_extendFromCentralizer_of_parabolic_le
        hconj hconn hRS hNeg hG χ j hjc hj) hQ hQχ)

end Dynamic

/-- The parabolic correspondence along a represented dynamic Levi holds, given the
seven named published structure statements. -/
theorem dynamicLeviParabolicCorrespondenceStatement_of_structural_statements
    (hPD : ParabolicDynamicStatement.{u})
    (hCR : DynamicCentralizerReductiveStatement.{u})
    (hReal : DynamicLeviCocharacterRealizationStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hconn : DynamicConnectedStatement.{u})
    (hRS : RelativeRootSignInclusionsStatement.{u}) (hNeg : RelativeRootNegationStatement.{u}) :
    DynamicLeviParabolicCorrespondenceStatement.{u} :=
  fun _ _ _ hG χ _ j hjc hj =>
    ⟨Dynamic.extendFromCentralizerOrderIsoOfStructuralStatements
      hPD hCR hReal hconj hconn hRS hNeg hG χ j hjc hj, fun _ => rfl, fun _ => rfl⟩

end Langlands.GroupScheme
