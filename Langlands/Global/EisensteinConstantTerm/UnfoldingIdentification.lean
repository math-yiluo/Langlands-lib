import Langlands.Global.EisensteinConstantTerm.UnfoldingDynamic
import Langlands.Global.AdelicEisensteinConstantTermStatement
import Langlands.Global.AdelicEisensteinDoubleCosetsProof
import Langlands.GroupScheme.Rational.ParabolicIntersectionSplitTorusProof
import Langlands.BruhatTits.IntegralModels.UnramifiedResidueFixedTorusAttainment
import Langlands.Representation.Geometric.RepresentedGeometricLemmaDynamicRealization
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisExactnessProof
import Langlands.GroupScheme.Rational.PointContainmentFromDensity
import Langlands.GroupScheme.Rational.ConnectedGroupUnirationalityProof
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Rational.ParabolicConnectedConjugacy
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.NormalSubgroupParabolicIntersection

/-! # The geometric-lemma parabolics as dynamic parabolics of commuting cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.Dynamic AdelicGroupPoints
  Langlands.Automorphic.GroupSchemeFunctions Langlands.AlgebraicGeometry.PointTopology
  Langlands.GroupScheme.GaloisPointComparison

section Points

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- On rational points, the range of `j` followed by the inverse inner automorphism of `w` is the
conjugate of the range of `j` by `w⁻¹`. -/
theorem carrier_range_comp_innerIso_inv (j : H ⟶ G)
    (w : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    (SubgroupFunctor.range (j ≫ (G.innerIso w).inv)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =
      ((SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))).map
        (MulAut.conj w⁻¹).toMonoidHom := by
  have h := MultiplicativeTypeGaloisExactness.range_comp_iso_hom j (G.innerIso w).symm
  rw [Iso.symm_hom, Iso.symm_inv] at h
  rw [h]
  ext x
  rw [SubgroupFunctor.mem_comap, comp_innerIso_hom, constantPoint_self, Subgroup.mem_map_equiv]
  simp

end Points

section Principal

variable (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))

theorem principalPoint_injective [IsAffine G.X.left] :
    Function.Injective (principalPoint F G) :=
  (rational_injective F G).comp (rationalCoeffEquiv F G).injective

theorem map_conj_map_principalPoint (H : Subgroup (rationalPoints G)) (x : rationalPoints G) :
    (H.map (MulAut.conj x).toMonoidHom).map (principalPoint F G) =
      (H.map (principalPoint F G)).map
        (MulAut.conj (principalPoint F G x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro y
  change principalPoint F G (x * y * x⁻¹) =
    principalPoint F G x * principalPoint F G y * (principalPoint F G x)⁻¹
  rw [map_mul, map_mul, map_inv]

end Principal

section Density

variable {k : Type u} [Field k] [PerfectField k] [Infinite k]
  {G H K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- A closed smooth connected subgroup has dense rational points. -/
theorem hasDenseRationalPoints_of_closedSubgroup {i : H ⟶ G} (hi : IsClosedSubgroup i)
    (hs : Smooth H.X.hom) (hc : ConnectedSpace H.X.left) : HasDenseRationalPoints k H.X := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom H.X.hom := by rw [← Over.w i.hom.hom]; infer_instance
  exact ((connectedGroupUnirationality k H).1 inferInstance hs inferInstance hc).hasDenseRationalPoints

/-- Two closed smooth connected subgroups with the same rational points are equal. -/
theorem range_eq_of_carrier_eq {i : H ⟶ G} {j : K ⟶ G} (hi : IsClosedSubgroup i)
    (hj : IsClosedSubgroup j) (hHs : Smooth H.X.hom) (hHc : ConnectedSpace H.X.left)
    (hKs : Smooth K.X.hom) (hKc : ConnectedSpace K.X.left)
    (h : (SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =
      (SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    SubgroupFunctor.range i = SubgroupFunctor.range j := by
  have : IsReduced H.X.left :=
    AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k H.X.left H.X.hom
  have : IsReduced K.X.left :=
    AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k K.X.left K.X.hom
  exact le_antisymm
    (SubgroupFunctor.range_le_of_dense_rationalPoints
      (hasDenseRationalPoints_of_closedSubgroup hi hHs hHc) hj h.le)
    (SubgroupFunctor.range_le_of_dense_rationalPoints
      (hasDenseRationalPoints_of_closedSubgroup hj hKs hKc) hi h.ge)

end Density

section Identification

variable (F : Type u) [Field F] [NumberField F]
  {G P U Q V P' U' Q' V' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (p : P ⟶ G) (iU : U ⟶ P) (q : Q ⟶ G) (iV : V ⟶ Q)
  (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
  (f : P' ⟶ P) (iU' : U' ⟶ P') (g' : Q' ⟶ Q) (iV' : V' ⟶ Q')

/-- **The geometric-lemma parabolics are dynamic.** There are cocharacters `χ`, `τ` of one
maximal split torus with `P = P(χ)`, `U = U(χ)`, `w⁻¹ Q w = P(τ)`, `w⁻¹ V w = U(τ)`, and
commuting refinements `ψ` of `χ` by `τ` and `θ` of `τ` by `χ` with `P' = P(ψ)`, `U' = U(ψ)`,
`w⁻¹ Q' w = P(θ)`, `w⁻¹ V' w = U(θ)`, all as subgroup functors. Moreover
`U(τ) ∩ P(χ) ⊆ U(ψ)`. -/
theorem exists_dynamic_unfolding_data (hG : IsConnectedReductive G)
    (hP : IsParabolicSubgroup p) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hQ : IsParabolicSubgroup q) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hP' : IsParabolicSubgroup (f ≫ p)) (hU' : LeviSubgroup.IsGeometricUnipotentRadical iU')
    (hQ' : IsParabolicSubgroup (g' ≫ q)) (hV' : LeviSubgroup.IsGeometricUnipotentRadical iV')
    (hDat : IsGeometricLemmaDatum p iU q iV f g' w) :
    ∃ χ τ ψ θ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G,
      IsCommutingRefinement χ τ ψ ∧ IsCommutingRefinement τ χ θ ∧
      unipotent τ ⊓ parabolic χ ≤ unipotent ψ ∧
      SubgroupFunctor.range p = parabolic χ ∧ SubgroupFunctor.range (iU ≫ p) = unipotent χ ∧
      SubgroupFunctor.range (q ≫ (G.innerIso w).inv) = parabolic τ ∧
      SubgroupFunctor.range (iV ≫ q ≫ (G.innerIso w).inv) = unipotent τ ∧
      SubgroupFunctor.range (f ≫ p) = parabolic ψ ∧
      SubgroupFunctor.range (iU' ≫ f ≫ p) = unipotent ψ ∧
      SubgroupFunctor.range (g' ≫ q ≫ (G.innerIso w).inv) = parabolic θ ∧
      SubgroupFunctor.range (iV' ≫ g' ≫ q ≫ (G.innerIso w).inv) = unipotent θ := by
  have := hG.isSeparated
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have hQw : IsParabolicSubgroup (q ≫ (G.innerIso w).inv) := by
    have := hQ.comp_iso (G.innerIso w).symm
    rwa [Iso.symm_hom] at this
  have hQ'w : IsParabolicSubgroup ((g' ≫ q) ≫ (G.innerIso w).inv) := by
    have := hQ'.comp_iso (G.innerIso w).symm
    rwa [Iso.symm_hom] at this
  obtain ⟨S, i, hi, fP, fQ, hfP, hfQ⟩ :=
    parabolicIntersectionSplitTorus F G hG P Q p (q ≫ (G.innerIso w).inv) hP hQw
  obtain ⟨lam, hlam⟩ :=
    IsParabolicSubgroup.exists_cocharacter_of_maximalSplitTorus hG i hi p hP fP hfP
  obtain ⟨mu, hmu⟩ := IsParabolicSubgroup.exists_cocharacter_of_maximalSplitTorus hG i hi
    (q ≫ (G.innerIso w).inv) hQw fQ hfQ
  have hτ : SubgroupFunctor.range (CommGroupScheme.groupHom mu ≫ i) ≤
      centralizer (CommGroupScheme.groupHom lam ≫ i) :=
    (NormalSubgroupParabolicIntersection.range_comp_le _ i).trans
      ((range_le_torusCentralizer i).trans (torusCentralizer_le_dynamicCentralizer i _))
  obtain ⟨ψ, θ, hψ, hθ, -⟩ := exists_common_levi_refinements _ _ hτ
  have hUχ : SubgroupFunctor.range (iU ≫ p) = unipotent (CommGroupScheme.groupHom lam ≫ i) :=
    radical_range_eq_dynamic_unipotent hG hP hU _ hlam
  have hUτ : SubgroupFunctor.range (iV ≫ q ≫ (G.innerIso w).inv) =
      unipotent (CommGroupScheme.groupHom mu ≫ i) := by
    rw [← Category.assoc]
    exact radical_range_eq_dynamic_unipotent hG hQw hV _ hmu
  have hinj := principalPoint_injective F G
  have hconj : ∀ (H : GroupScheme (Spec (CommRingCat.of F))) (j : H ⟶ G),
      ((SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))).map
        (principalPoint F G) = rationalImage F j := fun H j => (rationalImage_eq_map_range F G j).symm
  -- rational points of the smaller parabolics
  have hPF : (SubgroupFunctor.range (f ≫ p)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) =
      ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) ⊓
        (SubgroupFunctor.range (q ≫ (G.innerIso w).inv)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))) ⊔
        (SubgroupFunctor.range (iU ≫ p)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ hinj, carrier_range_comp_innerIso_inv,
      map_conj_map_principalPoint, map_inv, principalPoint_eq_innerAdelicPoint, hconj, hconj,
      hconj, hconj, hDat.rationalImage_left]
  have hQF0 : (SubgroupFunctor.range (g' ≫ q)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) =
      ((SubgroupFunctor.range q).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) ⊓
        ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))).map
          (MulAut.conj w).toMonoidHom) ⊔
        (SubgroupFunctor.range (iV ≫ q)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))) := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ hinj, map_conj_map_principalPoint,
      principalPoint_eq_innerAdelicPoint, hconj, hconj, hconj, hconj, hDat.rationalImage_right]
  have hconjid : ∀ H : Subgroup (rationalPoints G),
      (H.map (MulAut.conj w).toMonoidHom).map (MulAut.conj w⁻¹).toMonoidHom = H := by
    intro H
    rw [Subgroup.map_map]
    convert Subgroup.map_id H
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hQF : (SubgroupFunctor.range ((g' ≫ q) ≫ (G.innerIso w).inv)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F)))) =
      ((SubgroupFunctor.range (q ≫ (G.innerIso w).inv)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F)))) ⊓
        (SubgroupFunctor.range p).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))) ⊔
        (SubgroupFunctor.range (iV ≫ q ≫ (G.innerIso w).inv)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F)))) := by
    rw [carrier_range_comp_innerIso_inv, hQF0, Subgroup.map_sup,
      Subgroup.map_inf _ _ _ (MulAut.conj w⁻¹).injective, hconjid,
      carrier_range_comp_innerIso_inv, ← Category.assoc, carrier_range_comp_innerIso_inv]
  -- density: the smaller parabolics are the dynamic parabolics
  have hdyn : ∀ ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G,
      Smooth (Affine.parabolicScheme ξ).X.hom ∧ ConnectedSpace (Affine.parabolicScheme ξ).X.left :=
    fun ξ => ⟨(dynamicSmooth F G ξ _ _).1 (Affine.isRepresentedBy_parabolicHom ξ),
      ((dynamicConnected F G ξ _ _).2 inferInstance).1 (Affine.isRepresentedBy_parabolicHom ξ)⟩
  have hP'ψ : SubgroupFunctor.range (f ≫ p) = parabolic ψ := by
    rw [← (Affine.isRepresentedBy_parabolicHom ψ).2]
    refine range_eq_of_carrier_eq hP'.isClosedSubgroup (Affine.isClosedSubgroup_parabolicHom ψ)
      hP'.smooth hP'.connectedSpace (hdyn ψ).1 (hdyn ψ).2 ?_
    rw [(Affine.isRepresentedBy_parabolicHom ψ).2, hPF, hlam, hmu, hUχ]
    exact (parabolic_refinement_eq_sup i (CommGroupScheme.groupHom mu)
      (CommGroupScheme.groupHom lam) ψ hψ _).symm
  have hQ'θ : SubgroupFunctor.range ((g' ≫ q) ≫ (G.innerIso w).inv) = parabolic θ := by
    rw [← (Affine.isRepresentedBy_parabolicHom θ).2]
    refine range_eq_of_carrier_eq hQ'w.isClosedSubgroup (Affine.isClosedSubgroup_parabolicHom θ)
      hQ'w.smooth hQ'w.connectedSpace (hdyn θ).1 (hdyn θ).2 ?_
    rw [(Affine.isRepresentedBy_parabolicHom θ).2, hQF, hlam, hmu, hUτ]
    exact (parabolic_refinement_eq_sup i (CommGroupScheme.groupHom lam)
      (CommGroupScheme.groupHom mu) θ hθ _).symm
  refine ⟨_, _, ψ, θ, hψ, hθ,
    unipotent_inf_parabolic_le_refinement i (CommGroupScheme.groupHom mu)
      (CommGroupScheme.groupHom lam) ψ hψ,
    hlam, hUχ, hmu, hUτ, hP'ψ, radical_range_eq_dynamic_unipotent hG hP' hU' ψ hP'ψ, ?_, ?_⟩
  · rw [← Category.assoc]; exact hQ'θ
  · have := radical_range_eq_dynamic_unipotent hG hQ'w hV' θ hQ'θ
    simpa only [Category.assoc] using this

end Identification

end Langlands.Global
