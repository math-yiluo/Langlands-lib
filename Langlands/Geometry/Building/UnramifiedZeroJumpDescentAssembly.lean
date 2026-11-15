import Langlands.Geometry.Building.UnramifiedAffineRootRestrictionReduction
import Langlands.Geometry.Building.TorusRestrictedRootJump
import Langlands.Geometry.Building.TorusRestrictedRootInvariance
import Langlands.Geometry.Building.RootValuationFieldDescent
import Langlands.GroupScheme.Torus.RootSupportBaseChange
import Langlands.GroupScheme.Rational.KernelCentralizerComponentReductiveProof

/-! # Zero-value root jumps descend, given an abstract Galois descent of jumps

This module reduces `Langlands.Geometry.Building.UnramifiedZeroJumpDescentStatement` to a
descent principle for zero-value jumps of a family `ψ` of root functions of `(G_K, S_K)`,
`K = F^ur`, that satisfies three hypotheses on the root group `U_{α_K}(K)`: an ultrametric
inequality (H1), invariance under `Aut(K/F)` (H2), and invariance under conjugation by points of
`S_K` at which every rational character has valuation one (H3). A jump of a root `χ` of
`(G_K, T_K)` first passes to a jump of `α_K` for the torus restriction `ψ x` of `x`
(`isRootFiltrationJump_torusRestricted_of_isRootFiltrationJump`); `ψ x` satisfies (H1)–(H3)
(module `TorusRestrictedRootInvariance`); the descent principle then gives a jump of `α` for
`φ x = fieldRestrict (ψ x)`. -/

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

/-- The core of the assembly over an arbitrary field extension `K/k`: given a descent
principle for zero-value jumps from families on `(G_K, S_K)` satisfying (H1)–(H3), a
zero-value jump of a root `χ` of `(G_K, T_K)` for a Galois-fixed V6-compatible valuation `φ`
gives a zero-value jump of its restriction `α` for the torus-and-field restriction of `φ`. -/
theorem isRootFiltrationJump_torusFieldRestricted_of_descent
    [Smooth (baseChanged k K G).X.hom]
    (iS : S.toGrp ⟶ G) [Mono iS.hom.hom.left] (iT : T.toGrp ⟶ G) (f : S ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    [Mono (j_K iT).hom.hom.left]
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus (T_K).toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs (j_K iT))
    (hEbase : RelativeRoot.HasOppositeFactorPairs iS)
    (v : Valuation K (WithZero (Multiplicative ℤ))) (C : CentralizerDatum (j_K iT))
    {φ : RootFunctionFamily T_K (baseChanged k K G)} (hφ : IsRootDatumValuation (j_K iT) φ)
    (hV : IntegerValuation.IsCentralizerCompatible v (j_K iT) C.j C.s C.bijective φ)
    (hfixed : ∀ σ : K ≃ₐ[k] K, RootFunctionFamily.galoisAction k K T G σ φ = φ)
    {χ : characterLattice T_K} (hχ : χ ∈ relativeRoots (j_K iT))
    {α : characterLattice S} (hα : α ∈ relativeRoots iS) (hfχ : f_K f ≫ χ = a_K α)
    (hjump : IsRootFiltrationJump (j_K iT) φ χ 0)
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
      (torusFieldRestrictedRootFunctionFamily (k := k) (K := K) hS hT hE hφ (f_K f)) α 0 := by
  have hfactor : CommGroupScheme.groupHom (f_K f) ≫ j_K iT = j_K iS := by
    rw [← hf, Functor.map_comp]
    rfl
  have hαK : (a_K α) ∈ relativeRoots (CommGroupScheme.groupHom (f_K f) ≫ j_K iT) := by
    rw [hfactor]
    exact (mem_roots_baseChange_iff (K := K) G S hS iS α).mpr hα
  have hhigh : ∀ n : ℕ, 3 ≤ n →
      n • (a_K α) ∉ relativeRoots (CommGroupScheme.groupHom (f_K f) ≫ j_K iT) := by
    intro n hn hroot
    rw [hfactor, ← map_nsmul] at hroot
    have hnroot : n • α ∈ relativeRoots iS :=
      (mem_roots_baseChange_iff (K := K) G S hS iS _).mp hroot
    have hle := RelativeRoot.HasOppositeFactorPairs.nat_multiple_le_two iS hS hEbase hα
      (by omega) hnroot
    omega
  have hJK := isRootFiltrationJump_torusRestricted_of_isRootFiltrationJump
    (hS.baseChange b) hT hE hφ (f_K f) hαK hhigh hχ hfχ 0 hjump
  rw [hfactor] at hJK
  refine hdesc _ (fun g hg h hh => ?_) (fun σ g _ => ?_) (fun t ht g _ => ?_) hJK
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

end Core

set_option maxHeartbeats 6400000 in
/-- **Zero-value root jumps descend, given the abstract Galois descent.** The hypothesis
`hdesc` says: for a local field `F`, `K = F^ur`, a maximal split torus `S` of a connected
reductive `G`, a root `α` of `(G, S)`, and a family `ψ` of root functions of `(G_K, S_K)`
satisfying (H1)–(H3) on `U_{α_K}(K)`, a jump of `α_K` at `0` for `ψ` gives a jump of `α` at `0`
for `fieldRestrict ψ`. It implies `UnramifiedZeroJumpDescentStatement`. -/
theorem unramifiedZeroJumpDescent_of_galoisDescent
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
    UnramifiedZeroJumpDescentStatement.{u} := by
  intro F _ _ _ _ G hG S iS hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  have := mono_of_isMaximalSplitTorus hiS
  intro hiT
  have := mono_of_isMaximalSplitTorus hiT
  intro hE D C hΩ fixed φ x hx χ hχ α hα hfχ hjump
  have hEbase : RelativeRoot.HasOppositeFactorPairs iS := fun a ha g hg _ =>
    RelativeRoot.exists_oppositeFactorPair_of_componentReductivity
      RelativeRoot.kernelCentralizerComponentReductive F G hG S iS hiS a ha.1 g hg
  have hcore := isRootFiltrationJump_torusFieldRestricted_of_descent iS iT f hf
    hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE hEbase (MaximalUnramified.valuation F) C
    (D.isRootDatumValuation_of_mem x.mem) (hΩ x.val x.mem) hx hχ hα hfχ hjump
  have hd := hdesc F G hG S iS hiS α hα
  have hJ := hcore hd
  exact hJ

end Langlands.Geometry.Building
