import Langlands.Geometry.Building.UnramifiedZeroJumpFieldComparisonStatement
import Langlands.Geometry.Building.TorusRestrictedRootInvariance

/-! # The zero-jump comparison over `F` and `F^ur`, given the two Galois descents

This module reduces `Langlands.Geometry.Building.UnramifiedZeroJumpFieldComparisonStatement`
to two principles about a family `ψ` of root functions of `(G_K, S_K)`, `K = F^ur`, that
satisfies three hypotheses on the root group `U_{α_K}(K)`: an ultrametric inequality (H1),
invariance under `Aut(K/F)` (H2), and invariance under conjugation by points of `S_K` at which
every rational character has valuation one (H3).

* `hfwd` (ascent, in contrapositive form): if `α_K` has no jump at `0` for `ψ`, then `α` has
  no jump at `0` for `fieldRestrict ψ`.
* `hdesc` (descent, as in `unramifiedZeroJumpDescent_of_galoisDescent`): a jump of `α_K` at
  `0` for `ψ` gives a jump of `α` at `0` for `fieldRestrict ψ`.

The torus restriction `ψ x` of a Galois-fixed point `x` satisfies (H1)–(H3) (module
`TorusRestrictedRootInvariance`), and `φ x = fieldRestrict (ψ x)` by definition. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

section Core

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "f_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b)
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b)
local notation "a_K" a => characterLattice.baseChange b S a

/-- The three hypotheses (H1)–(H3) on `U_{α_K}(K)` hold for the torus restriction of a
Galois-fixed V6-compatible valuation `φ` of the root datum of `(G_K, T_K)`. -/
theorem torusRestrictedRootFunctionFamily_descentHypotheses
    [Smooth (baseChanged k K G).X.hom]
    (iS : S.toGrp ⟶ G) (iT : T.toGrp ⟶ G) (f : S ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    [Mono (j_K iT).hom.hom.left]
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus (T_K).toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs (j_K iT))
    (v : Valuation K (WithZero (Multiplicative ℤ))) (C : CentralizerDatum (j_K iT))
    {φ : RootFunctionFamily T_K (baseChanged k K G)} (hφ : IsRootDatumValuation (j_K iT) φ)
    (hV : IntegerValuation.IsCentralizerCompatible v (j_K iT) C.j C.s C.bijective φ)
    (hfixed : ∀ σ : K ≃ₐ[k] K, RootFunctionFamily.galoisAction k K T G σ φ = φ)
    {α : characterLattice S} (hα : α ∈ relativeRoots iS) :
    let ψ : RootFunctionFamily S_K G_K :=
      torusRestrictedRootFunctionFamily (hS.baseChange b) hT hE hφ (f_K f)
    (∀ g ∈ rootGroupPoints (j_K iS) (a_K α), ∀ h ∈ rootGroupPoints (j_K iS) (a_K α),
        min (ψ (a_K α) g) (ψ (a_K α) h) ≤ ψ (a_K α) (g * h⁻¹)) ∧
      (∀ σ : K ≃ₐ[k] K, ∀ g ∈ rootGroupPoints (j_K iS) (a_K α),
        ψ (a_K α) (rationalConjugate k K G σ g) = ψ (a_K α) g) ∧
      (∀ t ∈ characterValuationKernel v (S_K).toGrp, ∀ g ∈ rootGroupPoints (j_K iS) (a_K α),
        ψ (a_K α) (rationalPoints.map (j_K iS) t * g * (rationalPoints.map (j_K iS) t)⁻¹) =
          ψ (a_K α) g) := by
  intro ψ
  have hfactor : CommGroupScheme.groupHom (f_K f) ≫ j_K iT = j_K iS := by
    rw [← hf, Functor.map_comp]
    rfl
  have hαK : (a_K α) ∈ relativeRoots (CommGroupScheme.groupHom (f_K f) ≫ j_K iT) := by
    rw [hfactor]
    exact (mem_roots_baseChange_iff (K := K) G S hS iS α).mpr hα
  refine ⟨fun g hg h hh => ?_, fun σ g _ => ?_, fun t ht g _ => ?_⟩
  · rw [← hfactor] at hg hh
    exact torusRestrictedRootFunctionFamily_min_le_mul_inv (hS.baseChange b) hT hE hφ (f_K f)
      _ hαK g h hg hh
  · exact torusRestrictedRootFunctionFamily_rationalConjugate k K iT (hS.baseChange b) hT hE hφ
      f hfixed σ α g
  · have hc := torusRestrictedRootFunctionFamily_conj_of_mem_characterValuationKernel
      (hS.baseChange b) hT hE hφ v C.j C.s C.bijective C.isRepresentedBy C.comp_eq hV (f_K f)
      ht (a_K α) g
    rw [hfactor] at hc
    exact hc

/-- The core of the assembly over an arbitrary field extension `K/k`: given an ascent and a
descent principle for zero-value jumps of families on `(G_K, S_K)` satisfying (H1)–(H3)
(`hfwd` in contrapositive form), the torus-and-field restriction of a Galois-fixed
V6-compatible valuation `φ` of `(G_K, T_K)` has a zero-value jump at `α` if and only if the
torus restriction of `φ` has one at `α_K`. -/
theorem isRootFiltrationJump_torusFieldRestricted_iff_of_galoisDescent
    [Smooth (baseChanged k K G).X.hom]
    (iS : S.toGrp ⟶ G) (iT : T.toGrp ⟶ G) (f : S ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    [Mono (j_K iT).hom.hom.left]
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus (T_K).toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs (j_K iT))
    (v : Valuation K (WithZero (Multiplicative ℤ))) (C : CentralizerDatum (j_K iT))
    {φ : RootFunctionFamily T_K (baseChanged k K G)} (hφ : IsRootDatumValuation (j_K iT) φ)
    (hV : IntegerValuation.IsCentralizerCompatible v (j_K iT) C.j C.s C.bijective φ)
    (hfixed : ∀ σ : K ≃ₐ[k] K, RootFunctionFamily.galoisAction k K T G σ φ = φ)
    {α : characterLattice S} (hα : α ∈ relativeRoots iS)
    (hfwd : ∀ ψ : RootFunctionFamily S_K G_K,
      (∀ g ∈ rootGroupPoints (j_K iS) (a_K α), ∀ h ∈ rootGroupPoints (j_K iS) (a_K α),
        min (ψ (a_K α) g) (ψ (a_K α) h) ≤ ψ (a_K α) (g * h⁻¹)) →
      (∀ σ : K ≃ₐ[k] K, ∀ g ∈ rootGroupPoints (j_K iS) (a_K α),
        ψ (a_K α) (rationalConjugate k K G σ g) = ψ (a_K α) g) →
      (∀ t ∈ characterValuationKernel v (S_K).toGrp, ∀ g ∈ rootGroupPoints (j_K iS) (a_K α),
        ψ (a_K α) (rationalPoints.map (j_K iS) t * g * (rationalPoints.map (j_K iS) t)⁻¹) =
          ψ (a_K α) g) →
      ¬ IsRootFiltrationJump (j_K iS) ψ (a_K α) 0 →
        ¬ IsRootFiltrationJump iS (RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ) α 0)
    (hdesc : ∀ ψ : RootFunctionFamily S_K G_K,
      (∀ g ∈ rootGroupPoints (j_K iS) (a_K α), ∀ h ∈ rootGroupPoints (j_K iS) (a_K α),
        min (ψ (a_K α) g) (ψ (a_K α) h) ≤ ψ (a_K α) (g * h⁻¹)) →
      (∀ σ : K ≃ₐ[k] K, ∀ g ∈ rootGroupPoints (j_K iS) (a_K α),
        ψ (a_K α) (rationalConjugate k K G σ g) = ψ (a_K α) g) →
      (∀ t ∈ characterValuationKernel v (S_K).toGrp, ∀ g ∈ rootGroupPoints (j_K iS) (a_K α),
        ψ (a_K α) (rationalPoints.map (j_K iS) t * g * (rationalPoints.map (j_K iS) t)⁻¹) =
          ψ (a_K α) g) →
      IsRootFiltrationJump (j_K iS) ψ (a_K α) 0 →
        IsRootFiltrationJump iS (RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ) α 0) :
    IsRootFiltrationJump iS
        (torusFieldRestrictedRootFunctionFamily (k := k) (K := K) hS hT hE hφ (f_K f)) α 0 ↔
      IsRootFiltrationJump (j_K iS)
        (torusRestrictedRootFunctionFamily (hS.baseChange b) hT hE hφ (f_K f)) (a_K α) 0 := by
  have key := torusRestrictedRootFunctionFamily_descentHypotheses iS iT f hf hS hT
    hE v C hφ hV hfixed hα
  set ψ : RootFunctionFamily S_K G_K :=
    torusRestrictedRootFunctionFamily (hS.baseChange b) hT hE hφ (f_K f) with hψ
  have hfr : torusFieldRestrictedRootFunctionFamily (k := k) (K := K) hS hT hE hφ (f_K f) =
      RootFunctionFamily.fieldRestrict (k := k) (K := K) ψ := rfl
  rw [hfr]
  exact ⟨fun hF => by_contra fun hK => hfwd ψ key.1 key.2.1 key.2.2 hK hF,
    hdesc ψ key.1 key.2.1 key.2.2⟩

end Core

set_option maxHeartbeats 6400000 in
/-- **The zero-jump comparison over `F` and `F^ur`, given the two Galois descents.** The
hypothesis `hfwd` says: for a local field `F`, `K = F^ur`, a maximal split torus `S` of a
connected reductive `G`, a root `α` of `(G, S)`, and a family `ψ` of root functions of
`(G_K, S_K)` satisfying (H1)–(H3) on `U_{α_K}(K)`, if `α_K` has no jump at `0` for `ψ`, then
`α` has no jump at `0` for `fieldRestrict ψ`. The hypothesis `hdesc` has the same binders and
says that a jump of `α_K` at `0` for `ψ` gives a jump of `α` at `0` for `fieldRestrict ψ`.
Together they imply `UnramifiedZeroJumpFieldComparisonStatement`. -/
theorem unramifiedZeroJumpFieldComparison_of_galoisDescent
    (hfwd : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
      (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
      (hiS : IsMaximalSplitTorus iS),
      letI : IsAffineHom G.X.hom := hG.isAffineHom
      letI : Smooth G.X.hom := hG.smooth
      haveI := mono_of_isMaximalSplitTorus hiS
      ∀ α ∈ relativeRoots iS,
      ∀ ψ : RootFunctionFamily
          ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj G),
        (∀ g ∈ rootGroupPoints
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α),
          ∀ h ∈ rootGroupPoints
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α),
          min (ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) g)
              (ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) h) ≤
            ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α)
              (g * h⁻¹)) →
        (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
          ∀ g ∈ rootGroupPoints
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α),
          ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α)
              (rationalConjugate F (inertiaFixedField F) G σ g) =
            ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) g) →
        (∀ t ∈ characterValuationKernel (MaximalUnramified.valuation F)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S).toGrp,
          ∀ g ∈ rootGroupPoints
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α),
          ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α)
              (rationalPoints.map
                ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS) t *
                g * (rationalPoints.map
                  ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
                    t)⁻¹) =
            ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) g) →
        ¬ IsRootFiltrationJump
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS) ψ
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) 0 →
          ¬ IsRootFiltrationJump iS
            (RootFunctionFamily.fieldRestrict (k := F) (K := inertiaFixedField F) ψ) α 0)
    (hdesc : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
      (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
      (hiS : IsMaximalSplitTorus iS),
      letI : IsAffineHom G.X.hom := hG.isAffineHom
      letI : Smooth G.X.hom := hG.smooth
      haveI := mono_of_isMaximalSplitTorus hiS
      ∀ α ∈ relativeRoots iS,
      ∀ ψ : RootFunctionFamily
          ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj G),
        (∀ g ∈ rootGroupPoints
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α),
          ∀ h ∈ rootGroupPoints
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α),
          min (ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) g)
              (ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) h) ≤
            ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α)
              (g * h⁻¹)) →
        (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
          ∀ g ∈ rootGroupPoints
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α),
          ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α)
              (rationalConjugate F (inertiaFixedField F) G σ g) =
            ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) g) →
        (∀ t ∈ characterValuationKernel (MaximalUnramified.valuation F)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S).toGrp,
          ∀ g ∈ rootGroupPoints
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α),
          ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α)
              (rationalPoints.map
                ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS) t *
                g * (rationalPoints.map
                  ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
                    t)⁻¹) =
            ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) g) →
        IsRootFiltrationJump
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS) ψ
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) 0 →
          IsRootFiltrationJump iS
            (RootFunctionFamily.fieldRestrict (k := F) (K := inertiaFixedField F) ψ) α 0) :
    UnramifiedZeroJumpFieldComparisonStatement.{u} := by
  intro F _ _ _ _ G hG S iS hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  have := mono_of_isMaximalSplitTorus hiS
  intro hiT
  have := mono_of_isMaximalSplitTorus hiT
  intro hE D C hΩ fixed φ ψ x hx φx ψx hφx hψx α hα
  subst hφx hψx
  exact isRootFiltrationJump_torusFieldRestricted_iff_of_galoisDescent iS iT f hf
    hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (MaximalUnramified.valuation F) C
    (D.isRootDatumValuation_of_mem x.mem) (hΩ x.val x.mem) hx hα
    (hfwd F G hG S iS hiS α hα) (hdesc F G hG S iS hiS α hα)

end Langlands.Geometry.Building
