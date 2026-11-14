import Langlands.Global.AdelicGaloisOverlapMatching
import Langlands.Global.AdelicSplitFundamentalSet
import Langlands.Global.AdelicSiegelSetupExistence
import Langlands.GroupScheme.Rational.NormalizerGaloisAction
import Langlands.GroupScheme.Rational.UnipotentRadicalGalois
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Derived.MaximalSplitTorusProof
import Langlands.GroupScheme.Derived.CentralSplitTorusProductProof
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Rational.RadicalGaloisInnerTransport

/-! # Proof of the twisted split factorization with Galois inverse-orbit matching -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme

/-- Every maximal split torus with a generic cocharacter of a connected reductive group
over a number field extends to an actual algebraic Siegel setup. -/
theorem exists_isSiegelAlgebraicSetup (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) :
    ∃ (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
      IsSiegelAlgebraicSetup F G T i ν T₀ j := by
  obtain ⟨D, d, -, -, hd⟩ := derivedSubgroupRepresentability F G
  obtain ⟨T₀, t₀, e, ht₀, he_closed, he⟩ := derivedMaximalSplitTorus F G D d hG hd T i hi
  obtain ⟨⟨A, a, ha⟩, -⟩ := splitComponentStatement F G hG
  obtain ⟨c, hc, -, -⟩ := ha.exists_commFactor_of_isMaximalSplitTorus hi
  have hiso := derivedCentralSplitTorusProduct F G D d hG hd T T₀ A i t₀ e a c hi ht₀
    he_closed he ha hc
  obtain ⟨-, hRL, hU⟩ := standardMinimalLeviStructure F G T i ν hG hi hν
  refine ⟨T₀, e, hi, hν,
    Standard.isMinimalParabolicSubgroup_parabolicHom_of_genericMinimal i ν
      genericMinimalParabolic hG hi hν,
    hRL, hU, standardLevi_empty_eq_torusCentralizer_of_generic i ν hG hi hν,
    relativeRoots_torusToStandardParabolic F G T i ν hG hi hν,
    ⟨D, d, t₀, hd, ht₀, he⟩, A, c, ?_, ?_⟩
  · rw [hc]
    exact ha
  · rw [subgroupProductMap_eq_prodHom e c]
    exact hiso.surjective

end Langlands.Global.AdelicSiegelFactors

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors GaloisPointComparison

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance : IsAffineHom (AffineWeil.unitBaseChange F L G).X.hom :=
  isAffineHom_of_isAffine _

variable (T : CommGroupScheme (Spec (CommRingCat.of L)))
  (i : T.toGrp ⟶ AffineWeil.unitBaseChange F L G) (ν : cocharacterLattice T)

omit [NumberField F] [NumberField L] [FiniteDimensional F L] [IsGalois F L]
  [LocallyOfFiniteType G.X.hom] in
/-- The inverse-orbit matching premise from the Galois twisting data and rational parabolic
quotients `m_σ⁻¹ · σ(q) · q⁻¹ ∈ P_(Δ \ {α})(L)`. -/
theorem exists_inverseOrbitMatching
    (m : (L ≃ₐ[F] L) → rationalPoints (AffineWeil.unitBaseChange F L G))
    (a : (L ≃ₐ[F] L) → characterLattice T → characterLattice T)
    (htw : ∀ σ, ∀ β ∈ simpleRelativeRoots i ν, a σ β ∈ simpleRelativeRoots i ν ∧
      SubgroupFunctor.range
          (radicalGaloisHom (Standard.parabolicHom i ν (simpleRelativeRoots i ν \ {β})) σ) =
        SubgroupFunctor.range
          (Standard.parabolicHom i ν (simpleRelativeRoots i ν \ {a σ β}) ≫
            ((AffineWeil.unitBaseChange F L G).innerIso (m σ)).hom))
    (ha1 : ∀ β ∈ simpleRelativeRoots i ν, a 1 β = β)
    (hamul : ∀ σ τ, ∀ β ∈ simpleRelativeRoots i ν, a (σ * τ) β = a σ (a τ β))
    (q : rationalPoints (AffineWeil.unitBaseChange F L G))
    (α : characterLattice T) (hα : α ∈ simpleRelativeRoots i ν)
    (hr : ∀ σ : L ≃ₐ[F] L, ∃ p : rationalPoints
        (Standard.parabolicScheme i ν (simpleRelativeRoots i ν \ {α})),
      rationalPoints.map (Standard.parabolicHom i ν (simpleRelativeRoots i ν \ {α})) p =
        (m σ)⁻¹ * rationalConjugate F L G σ q * q⁻¹) :
    ∃ J : (L ≃ₐ[F] L) → Set (characterLattice T),
      (∀ σ, J σ ⊆ simpleRelativeRoots i ν) ∧
        J 1 = simpleRelativeRoots i ν \ {α} ∧
        ∀ σ : L ≃ₐ[F] L,
          SubgroupFunctor.range
              (radicalGaloisHom (Standard.parabolicHom i ν (J σ⁻¹) ≫
                ((AffineWeil.unitBaseChange F L G).innerIso q⁻¹).hom) σ) =
            SubgroupFunctor.range (Standard.parabolicHom i ν (J 1) ≫
              ((AffineWeil.unitBaseChange F L G).innerIso q⁻¹).hom) := by
  refine ⟨fun τ => simpleRelativeRoots i ν \ {a τ α}, fun σ => Set.sdiff_subset,
    by simp only [ha1 α hα], fun σ => ?_⟩
  beta_reduce
  rw [ha1 α hα]
  have hβ := (htw σ⁻¹ α hα).1
  have hY := (htw σ (a σ⁻¹ α) hβ).2
  have haσ : a σ (a σ⁻¹ α) = α := by rw [← hamul σ σ⁻¹ α hα, mul_inv_cancel, ha1 α hα]
  rw [haσ] at hY
  obtain ⟨p, hp⟩ := hr σ
  refine range_eq_of_innerIso_transport _ _ _ (rationalConjugate F L G σ q⁻¹) (m σ) q⁻¹
    (rationalPoints.map (Standard.parabolicHom i ν (simpleRelativeRoots i ν \ {α})) p⁻¹) p⁻¹
    (rationalPoints.map_apply _ _)
    (radicalGaloisHom_comp_innerIso _ _ σ) hY ?_
  rw [map_inv (rationalConjugate F L G σ),
    map_inv (rationalPoints.map (Standard.parabolicHom i ν (simpleRelativeRoots i ν \ {α}))) p,
    hp]
  group

omit [IsGalois F L] in
/-- Springer's §3.5 argument for one finite Galois split maximal model: the split
fundamental-set theorem and the split overlap estimate over `L`, together with a Galois
twisting of the split Borel pair, give the twisted factorization with inverse-orbit
matching. -/
theorem hasTwistedOverlapMatching_of
    [LocallyOfFiniteType (AffineWeil.unitBaseChange F L G).X.hom]
    (hF : SplitAdelicFundamentalSetStatement.{u})
    (hO : SplitSiegelOverlapStatement.{u})
    (hGL : IsConnectedReductive (AffineWeil.unitBaseChange F L G))
    (hi : IsMaximalSplitTorus i) (hmax : IsMaximalTorus i) (hν : IsGenericCocharacter i ν)
    (htw : HasGaloisBorelTwisting F L G T i ν) :
    HasTwistedOverlapMatching F L G T i ν := by
  obtain ⟨φ, m, a, htwist, ha1, hamul⟩ := htw
  obtain ⟨T₀, j, hsetup⟩ :=
    exists_isSiegelAlgebraicSetup L (AffineWeil.unitBaseChange F L G) hGL T i ν hi hν
  obtain ⟨C₁, hC₁, c, hfund⟩ :=
    hF L (AffineWeil.unitBaseChange F L G) hGL T i ν T₀ j hsetup hmax
  set C₀ : Set (AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) :=
    Subtype.val '' C₁ with hC₀def
  have hC₀ : IsCompact C₀ := hC₁.image continuous_subtype_val
  set C : Set (AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) :=
    C₀ ∪ ⋃ σ : L ≃ₐ[F] L,
      (fun y => φ σ y * rationalSection F L G (m σ)) '' C₀ with hCdef
  have hC : IsCompact C :=
    hC₀.union (isCompact_iUnion fun σ =>
      hC₀.image ((map_continuous (φ σ)).mul continuous_const))
  have hd := fun α (hα : α ∈ simpleRelativeRoots i ν) =>
    hO L (AffineWeil.unitBaseChange F L G) hGL T i ν hi hmax hν C hC c α hα
  choose! dα hdα using hd
  have hΔ : (simpleRelativeRoots i ν).Finite :=
    hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  obtain ⟨d, hdlow⟩ := (hΔ.image dα).bddBelow
  refine ⟨C, hC, c, d, fun g => ?_⟩
  obtain ⟨q₀, s, p, hs, hsc, x, hx, hfac⟩ := hfund (scalarExtensionNormOneMap F L G g)
  set q : rationalPoints (AffineWeil.unitBaseChange F L G) :=
    (rationalCoeffEquiv L (AffineWeil.unitBaseChange F L G)).symm q₀ with hqdef
  have hq : rationalSection F L G q = rational L (AffineWeil.unitBaseChange F L G) q₀ := by
    simp only [rationalSection, hqdef, MulEquiv.apply_symm_apply]
  have hxC : (x : AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) ∈ C :=
    Or.inl ⟨x, hx, rfl⟩
  refine ⟨x, hxC, s, p, q, ?_, hs, hsc, fun α hα hsα => ?_⟩
  · rw [hq, hfac]
  apply exists_inverseOrbitMatching F L G T i ν m a
    (fun σ β hβ => (htwist σ).2.2.2.2 β hβ) ha1 hamul q α hα
  intro σ
  obtain ⟨h1, h2, h3, h4, -⟩ := htwist σ
  obtain ⟨s', hφs, hs'n, hs'r⟩ := h3 s
  obtain ⟨p', hφp⟩ := h4 p
  set M := rationalSection F L G (m σ) with hMdef
  set q₀' := rationalCoeffEquiv L (AffineWeil.unitBaseChange F L G)
    ((m σ)⁻¹ * rationalConjugate F L G σ q) with hq₀'def
  have hx'C : φ σ (x : AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) * M ∈ C :=
    Or.inr (Set.mem_iUnion.mpr ⟨σ, ⟨x, ⟨x, hx, rfl⟩, rfl⟩⟩)
  have hsc' : ∀ β ∈ simpleRelativeRoots i ν, PositiveRealTorus.normCharacter L T β s' ≤ c := by
    intro β hβ
    obtain ⟨β', hβ', heq⟩ := hs'r β hβ
    rw [heq]
    exact hsc β' hβ'
  have hrat : M⁻¹ * rationalSection F L G (rationalConjugate F L G σ q) =
      rational L (AffineWeil.unitBaseChange F L G) q₀' := by
    simp only [hMdef, hq₀'def, rationalSection, map_mul, map_inv]
  have heq : (x : AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) *
        map L T.toGrp _ i s * map L _ _ (Standard.parabolicHom i ν ∅) p *
          rational L (AffineWeil.unitBaseChange F L G) q₀ =
      (φ σ (x : AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) * M) *
        map L T.toGrp _ i s' * map L _ _ (Standard.parabolicHom i ν ∅) p' *
          rational L (AffineWeil.unitBaseChange F L G) q₀' := by
    have hφ := congrArg (φ σ) hfac
    rw [h2 g, ← hfac, ← hq, map_mul, map_mul, map_mul, hφs, hφp, h1] at hφ
    rw [← hq, ← hφ, ← hrat]
    group
  obtain ⟨r, hr⟩ := hdα α hα x hxC _ hx'C s s' p p' q₀ q₀' hs (hs'n hs) hsc hsc'
    (hsα.trans (hdlow ⟨α, hα, rfl⟩)) heq
  refine ⟨(rationalCoeffEquiv L _).symm r, ?_⟩
  apply (rationalCoeffEquiv L (AffineWeil.unitBaseChange F L G)).injective
  rw [rationalCoeffEquiv_map, MulEquiv.apply_symm_apply, hr, hq₀'def]
  simp only [map_mul, map_inv, hqdef, MulEquiv.apply_symm_apply]

end Langlands.Global.AdelicGaloisUnit

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme

/-- Springer's §3.5 dichotomy: the split fundamental-set theorem and the split overlap
estimate give the twisted factorization with inverse-orbit matching for every finite
Galois split maximal model carrying a Galois twisting of its Borel pair. -/
theorem splitGaloisOverlapMatching : SplitGaloisOverlapMatchingStatement.{u} := by
  intro hF hO F _ _ G _ _ hG
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro D
  let : NumberField D.carrier := NumberField.of_module_finite F D.carrier
  intro ν hν htw
  exact hasTwistedOverlapMatching_of F D.carrier G D.torus D.inclusion ν hF hO
    (D.isConnectedReductive hG) (D.isMaximalTorus.isMaximalSplitTorus D.isSplitTorus)
    D.isMaximalTorus hν htw

end Langlands.Global.AdelicGaloisUnit
