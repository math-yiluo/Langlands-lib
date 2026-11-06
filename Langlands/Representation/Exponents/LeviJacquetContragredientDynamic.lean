import Langlands.Representation.Exponents.LeviJacquetContragredientReduction
import Langlands.Representation.Exponents.UniformCompressionStabilizationStatement
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityReduction
import Langlands.Representation.Aubert.General.IwahoriNaturalJacquetDuality
import Langlands.Representation.Aubert.General.IwahoriJacquetStableLift

/-! # Jacquet modules of contragredients for dynamic opposite parabolics

Renard 2026, VI.9.6 Theorem (VI.9.6.2) (printed p.201, PDF p.207), for the parabolic of a
cocharacter `χ`: `N = N(χ)`, `M = M(χ)` and `N̄ = N(χ⁻¹)`. The natural isomorphism
`r_{N̄}(π~) ≅ (r_N π)~` of `nonempty_contragredient_normalizedJacquet_iso_of_splits`
needs an `M`-central element with an opposite contraction basis, reciprocal Haar
characters and the two compression splittings. For a dynamic parabolic the element is
the Library contraction point of `χ⁻¹`, and the splittings are instances of the VI.9.1
uniform stabilization statement, taken here as a hypothesis. Reciprocity of the Haar
characters of `N(χ)` and `N(χ⁻¹)` on `M(χ)` is also a hypothesis.
-/

noncomputable section

universe u v uG uM

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

/-- Reciprocal Haar scaling characters give reciprocal complex inverse-half characters. -/
theorem closedInverseHalfCharacter_mul_eq_one_of_closedRestrictCharacter
    {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [LocallyCompactSpace Γ]
    [IsTopologicalGroup Γ]
    (U M O : Subgroup Γ) (hU : IsClosed (U : Set Γ)) (hO : IsClosed (O : Set Γ))
    (hMU : M ≤ Subgroup.normalizer U) (hMO : M ≤ Subgroup.normalizer O) (m : M)
    (hδ : HaarModulus.closedRestrictCharacter U hU M hMU m *
      HaarModulus.closedRestrictCharacter O hO M hMO m = 1) :
    (HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂ) *
      (HaarModulus.closedInverseHalfCharacter O hO M hMO m : ℂ) = 1 := by
  let F : NNReal ˣ →* ℂˣ :=
    (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom).comp
      (Units.map NNReal.sqrtHom.toMonoidHom)
  change ((F (HaarModulus.closedRestrictCharacter U hU M hMU m))⁻¹ : ℂˣ).val *
    ((F (HaarModulus.closedRestrictCharacter O hO M hMO m))⁻¹ : ℂˣ).val = 1
  rw [← Units.val_mul, ← mul_inv, ← map_mul, hδ, map_one, inv_one]
  rfl

end Langlands.Aubert.General

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance dynamicJacquetContragredientPointTopology :
    TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Every cocharacter `χ` has an `M(χ)`-central rational point `g` with an
ambient-cofinal opposite contraction basis for `(N(χ), M(χ), N(χ⁻¹))`. This is
`dynamic_hasOppositeIwahoriContractionBasis` with the centrality of `g` kept. -/
theorem dynamic_exists_central_hasOppositeIwahoriContractionBasis
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    ∃ g : rationalPoints G,
      (∀ m ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)), m * g = g * m) ∧
      Jacquet.HasOppositeIwahoriContractionBasis
        ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
        ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
        ((Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _))) g := by
  have := hG.smooth
  have := hG.isSeparated
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨g, hgM, hcomm, hcontrU, hcontrO⟩ :=
    BruhatTits.DynamicUnipotentContainment.exists_central_contractingPoint (F := k) χ
  refine ⟨g, hcomm, Jacquet.hasOppositeIwahoriContractionBasis_of_contraction
    (BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints
      (Dynamic.inverseCocharacter χ))
    (BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints χ)
    hgM hcomm ?_ ?_ (dynamic_opposite_factorization_unique χ) ?_ hcontrU hcontrO⟩
  · rw [← Dynamic.centralizer_inverseCocharacter χ]
    exact Dynamic.centralizer_le_normalizer_unipotent _ _
  · exact Dynamic.centralizer_le_normalizer_unipotent _ _
  · have htop : (pointTopology : TopologicalSpace (rationalPoints G)) =
        rationalSchemeTopology k G.X :=
      rationalPointTopology_eq_rationalSchemeTopology k G.X
    have hcell := Dynamic.opposite_cell_mem_nhds_one k G χ
    rw [← htop] at hcell
    exact hcell

/-- The VI.9.1 uniform stabilization statement gives the Fitting splitting of compression
by every `M(χ)`-central element satisfying the Iwahori contraction conditions for
`(N(χ), M(χ), N(χ⁻¹))`, on every smooth representation. -/
theorem compactCompressionSplits_of_uniformCompressionStabilization
    (hstab : UniformCompressionStabilizationStatement.{u, v})
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (g : rationalPoints G)
    (hc : ∀ m ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)), m * g = g * m)
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (K : OpenSubgroup (rationalPoints G))
    (hK : IsCompact (K : Set (rationalPoints G)))
    (hI : Jacquet.IsIwahoriContraction K
      ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
      ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
      ((Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _))) g) :
    Jacquet.CompactCompressionSplits A.representation A.isSmooth K hK g := by
  obtain ⟨b, hb⟩ := hstab k G hG χ K hK g hc hI
  exact (hb A A.representation A.isSmooth).2

/-- Renard VI.9.6 (VI.9.6.2) for the dynamic parabolic of a cocharacter `χ`, on abstract
subgroups equal to `N(χ⁻¹)`, `M(χ)` and `N(χ)`: given the VI.9.1 uniform stabilization
statement and reciprocity of the Haar scaling characters of `N(χ⁻¹)` and `N(χ)` on
`M(χ)`, the functors `π ↦ r_{N̄}(π~)` and `π ↦ (r_N π)~` to smooth representations of
`M(χ)` are naturally isomorphic. -/
theorem nonempty_contragredient_normalizedJacquet_iso_of_dynamic
    (hstab : UniformCompressionStabilizationStatement.{u, v})
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (U M O : Subgroup (rationalPoints G))
    (hUχ : U = (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)))
    (hMχ : M = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
    (hOχ : O = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
    (hU : IsClosed (U : Set (rationalPoints G))) (hO : IsClosed (O : Set (rationalPoints G)))
    (hMU : M ≤ Subgroup.normalizer (U : Set (rationalPoints G)))
    (hMO : M ≤ Subgroup.normalizer (O : Set (rationalPoints G)))
    (hrec : ∀ x : M, HaarModulus.closedRestrictCharacter U hU M hMU x *
      HaarModulus.closedRestrictCharacter O hO M hMO x = 1) :
    Nonempty (SmoothRep.contragredientFunctor.{0, u, v} ⋙
        normalizedJacquetFunctor.{u, v} U M hU hMU ≅
      (normalizedJacquetFunctor.{u, v} O M hO hMO).op ⋙
        SmoothRep.contragredientFunctor.{0, u, v}) := by
  subst hUχ hMχ hOχ
  obtain ⟨g, hc, hB⟩ :=
    dynamic_exists_central_hasOppositeIwahoriContractionBasis hG
      (Dynamic.inverseCocharacter χ)
  rw [Dynamic.centralizer_inverseCocharacter, Dynamic.inverseCocharacter_inverseCocharacter]
    at hB
  rw [Dynamic.centralizer_inverseCocharacter] at hc
  refine nonempty_contragredient_normalizedJacquet_iso_of_splits _ _ _ hU hO hMU hMO g hc hB
    (fun x => closedInverseHalfCharacter_mul_eq_one_of_closedRestrictCharacter
      _ _ _ hU hO hMU hMO x (hrec x)) ?_ ?_
  · intro A K hK hI
    refine compactCompressionSplits_of_uniformCompressionStabilization hstab hG
      (Dynamic.inverseCocharacter χ) g ?_ A K hK ?_
    · rwa [Dynamic.centralizer_inverseCocharacter]
    · rwa [Dynamic.centralizer_inverseCocharacter,
        Dynamic.inverseCocharacter_inverseCocharacter]
  · intro A K hK hI
    refine compactCompressionSplits_of_uniformCompressionStabilization hstab hG χ g⁻¹
      (fun x hx => (show Commute x g from hc x hx).inv_right) A K hK hI

/-- The stable-lift form of `nonempty_contragredient_normalizedJacquet_iso_of_dynamic`: under
the same hypotheses there is an `M`-central element `g` with an opposite contraction basis for
`(U, M, O)` and a natural isomorphism `Ψ : r_{N̄}(π~) ≅ (r_N π)~` satisfying the stable-lift
formula `IsStableLiftDuality` for `g`. -/
theorem exists_isStableLiftDuality_of_dynamic
    (hstab : UniformCompressionStabilizationStatement.{u, v})
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (U M O : Subgroup (rationalPoints G))
    (hUχ : U = (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)))
    (hMχ : M = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
    (hOχ : O = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
    (hU : IsClosed (U : Set (rationalPoints G))) (hO : IsClosed (O : Set (rationalPoints G)))
    (hMU : M ≤ Subgroup.normalizer (U : Set (rationalPoints G)))
    (hMO : M ≤ Subgroup.normalizer (O : Set (rationalPoints G)))
    (hrec : ∀ x : M, HaarModulus.closedRestrictCharacter U hU M hMU x *
      HaarModulus.closedRestrictCharacter O hO M hMO x = 1) :
    ∃ g : rationalPoints G, (∀ m ∈ M, m * g = g * m) ∧
      Jacquet.HasOppositeIwahoriContractionBasis U M O g ∧
      ∃ Ψ : SmoothRep.contragredientFunctor.{0, u, v} ⋙
          normalizedJacquetFunctor.{u, v} U M hU hMU ≅
        (normalizedJacquetFunctor.{u, v} O M hO hMO).op ⋙
          SmoothRep.contragredientFunctor.{0, u, v},
        IsStableLiftDuality.{u, v} U M O hU hO hMU hMO g Ψ := by
  subst hUχ hMχ hOχ
  obtain ⟨g, hc, hB⟩ :=
    dynamic_exists_central_hasOppositeIwahoriContractionBasis hG
      (Dynamic.inverseCocharacter χ)
  rw [Dynamic.centralizer_inverseCocharacter, Dynamic.inverseCocharacter_inverseCocharacter]
    at hB
  rw [Dynamic.centralizer_inverseCocharacter] at hc
  refine ⟨g, hc, hB, exists_isStableLiftDuality_of_splits _ _ _ hU hO hMU hMO g hc hB
    (fun x => closedInverseHalfCharacter_mul_eq_one_of_closedRestrictCharacter
      _ _ _ hU hO hMU hMO x (hrec x)) ?_ ?_⟩
  · intro A K hK hI
    refine compactCompressionSplits_of_uniformCompressionStabilization hstab hG
      (Dynamic.inverseCocharacter χ) g ?_ A K hK ?_
    · rwa [Dynamic.centralizer_inverseCocharacter]
    · rwa [Dynamic.centralizer_inverseCocharacter,
        Dynamic.inverseCocharacter_inverseCocharacter]
  · intro A K hK hI
    refine compactCompressionSplits_of_uniformCompressionStabilization hstab hG χ g⁻¹
      (fun x hx => (show Commute x g from hc x hx).inv_right) A K hK hI

end Langlands.Aubert.General.RationalPointFamily

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance dynamicLeviJacquetContragredientPointTopology :
    TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Renard VI.9.6 Theorem (VI.9.6.2) for represented parabolics realized by a cocharacter:
if `P = MN` and `P̄ = M N̄` have `mbar ≫ pbar = m ≫ p`, and the literal point images of
`N`, `M` and `N̄` are `N(χ)`, `M(χ)` and `N(χ⁻¹)` for a cocharacter `χ`, then the VI.9.1
uniform stabilization statement and reciprocity of the Haar scaling characters of
`N(χ⁻¹)` and `N(χ)` on `M(χ)` give a natural isomorphism `r_{P̄}^G(π~) ≅ (r_P^G π)~` of
functors to smooth representations of `M(F)`. -/
theorem nonempty_leviJacquetContragredient_iso_of_dynamic
    (hstab : RationalPointFamily.UniformCompressionStabilizationStatement.{u, v})
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication m n))
    (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
    (hpbar : IsParabolicSubgroup pbar) (hmbar : IsRationalLeviSubgroup mbar)
    (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
    (hmulbar : IsIso (subgroupMultiplication mbar nbar))
    (hP : mbar ≫ pbar = m ≫ p)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hN : pointImage (n ≫ p) = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
    (hM : pointImage (m ≫ p) = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
    (hNbar : pointImage (nbar ≫ pbar) =
      (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)))
    (hrec : ∀ (hU : IsClosed (pointImage (nbar ≫ pbar) : Set (rationalPoints G)))
      (hO : IsClosed (pointImage (n ≫ p) : Set (rationalPoints G)))
      (hMU : pointImage (m ≫ p) ≤
        Subgroup.normalizer (pointImage (nbar ≫ pbar) : Set (rationalPoints G)))
      (hMO : pointImage (m ≫ p) ≤
        Subgroup.normalizer (pointImage (n ≫ p) : Set (rationalPoints G)))
      (x : pointImage (m ≫ p)),
      HaarModulus.closedRestrictCharacter _ hU _ hMU x *
        HaarModulus.closedRestrictCharacter _ hO _ hMO x = 1) :
    letI := leviPointTopology m hm
    haveI : NonarchimedeanGroup (rationalPoints M) :=
      leviPoints_nonarchimedeanGroup p m hp hm
    Nonempty
      (SmoothRep.contragredientFunctor.{0, u, v} ⋙
          leviJacquetFunctor.{u, v} pbar mbar nbar hpbar hnbar hmbar hmulbar ≅
        (leviJacquetFunctor.{u, v} p m n hp hn hm hmul).op ⋙
          SmoothRep.contragredientFunctor.{0, u, v}) :=
  nonempty_leviJacquetContragredient_iso_of_pointImage p m n hp hm hn hmul
    pbar mbar nbar hpbar hmbar hnbar hmulbar hP fun hU hO hMU hMO =>
      RationalPointFamily.nonempty_contragredient_normalizedJacquet_iso_of_dynamic hstab hG χ
        _ _ _ hNbar hM hN hU hO hMU hMO (hrec hU hO hMU hMO)

end Langlands.Aubert.General.RepresentedParabolic
