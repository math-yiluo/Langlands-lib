import Langlands.BruhatTits.SpecialCompact.LeviSpecialPoint
import Langlands.Geometry.Building.SpecialPointRootJumpDescent
import Langlands.Geometry.Building.UnramifiedAffineRootRestrictionStatement
import Langlands.Geometry.Building.TorusFieldRootDirections
import Langlands.Geometry.Building.ChamberExchange

/-! # Unramified descent of affine roots from zero-value root jumps -/

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

/-- **Zero-value root jumps lift, non-multipliable case** (an internal pointwise form of the
first part of KP Proposition 9.4.28, at a point where the affine root vanishes). The setting
(`F`, `K = F^ur`, `G`, `S`, `T`, `D`, `fixed`, `φ`) is that of
`UnramifiedAffineRootRestrictionStatement`. Let `x` be an `Aut(K/F)`-fixed point of the
apartment of `D` and `α` a relative root of `(G, S)` with `2α ∉ Φ(S)`. If `α` has a filtration
jump at value `0` for the restricted valuation `φ x`, that is
`U_{α,φx,0} ⊈ U_{α,φx,0+} · U_{2α}(F)`, then some root `χ` of `(G_K, T_K)` restricting to `α`
has a filtration jump at value `0` for `x`: `U_{χ,x,0} ⊈ U_{χ,x,0+} · U_{2χ}(K)`. -/
def UnramifiedZeroJumpLiftReducedStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
    (hiS : IsMaximalSplitTorus iS)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T),
    CommGroupScheme.groupHom f ≫ iT = iS →
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : Smooth G.X.hom := hG.smooth
    haveI := mono_of_isMaximalSplitTorus hiS
    ∀ (hiT : IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      haveI := mono_of_isMaximalSplitTorus hiT
      haveI : Mono ((GroupScheme.baseChange
          (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
        mono_of_isMaximalSplitTorus hiT
      ∀ (hE : RelativeRoot.HasOppositeFactorPairs
          (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
        (D : KPApartmentData
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
          (IntegerValuation.order (MaximalUnramified.valuation F)))
        (C : CentralizerDatum
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
        IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C →
        let fixed : D.Apartment → Prop := fun x =>
          ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val
        let φ : D.Apartment → RootFunctionFamily S G := fun x =>
          torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
            hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE
            (D.isRootDatumValuation_of_mem x.mem)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)
        ∀ (x : D.Apartment), fixed x →
          ∀ α ∈ relativeRoots iS, 2 • α ∉ relativeRoots iS →
            ¬ (rootFiltration iS (φ x) α 0 ⊆
                {g | g ∈ rootGroupPoints iS α ∧ ((0 : ℝ) : WithTop ℝ) < φ x α g} *
                  (doubleRootGroupPoints iS α : Set (rationalPoints G))) →
            ∃ χ ∈ relativeRoots
                ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT),
              (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f ≫ χ =
                  characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α ∧
                ¬ (rootFiltration
                    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
                    x.val χ 0 ⊆
                  {g | g ∈ rootGroupPoints
                      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
                      χ ∧ ((0 : ℝ) : WithTop ℝ) < x.val χ g} *
                    (doubleRootGroupPoints
                      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
                      χ : Set _))

/-- **Zero-value root jumps lift, multipliable case** (an internal pointwise form of the first
part of KP Proposition 9.4.28, at a point where the affine root vanishes). The setting is that of
`UnramifiedAffineRootRestrictionStatement`. Let `x` be an `Aut(K/F)`-fixed point of the
apartment of `D` and `α` a relative root of `(G, S)` with `2α ∈ Φ(S)`. If `α` has a filtration
jump at value `0` for the restricted valuation `φ x`, that is
`U_{α,φx,0} ⊈ U_{α,φx,0+} · U_{2α}(F)`, then some root `χ` of `(G_K, T_K)` restricting to `α`
has a filtration jump at value `0` for `x`: `U_{χ,x,0} ⊈ U_{χ,x,0+} · U_{2χ}(K)`. -/
def UnramifiedZeroJumpLiftMultipliableStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
    (hiS : IsMaximalSplitTorus iS)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T),
    CommGroupScheme.groupHom f ≫ iT = iS →
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : Smooth G.X.hom := hG.smooth
    haveI := mono_of_isMaximalSplitTorus hiS
    ∀ (hiT : IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      haveI := mono_of_isMaximalSplitTorus hiT
      haveI : Mono ((GroupScheme.baseChange
          (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
        mono_of_isMaximalSplitTorus hiT
      ∀ (hE : RelativeRoot.HasOppositeFactorPairs
          (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
        (D : KPApartmentData
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
          (IntegerValuation.order (MaximalUnramified.valuation F)))
        (C : CentralizerDatum
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
        IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C →
        let fixed : D.Apartment → Prop := fun x =>
          ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val
        let φ : D.Apartment → RootFunctionFamily S G := fun x =>
          torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
            hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE
            (D.isRootDatumValuation_of_mem x.mem)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)
        ∀ (x : D.Apartment), fixed x →
          ∀ α ∈ relativeRoots iS, 2 • α ∈ relativeRoots iS →
            ¬ (rootFiltration iS (φ x) α 0 ⊆
                {g | g ∈ rootGroupPoints iS α ∧ ((0 : ℝ) : WithTop ℝ) < φ x α g} *
                  (doubleRootGroupPoints iS α : Set (rationalPoints G))) →
            ∃ χ ∈ relativeRoots
                ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT),
              (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f ≫ χ =
                  characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α ∧
                ¬ (rootFiltration
                    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
                    x.val χ 0 ⊆
                  {g | g ∈ rootGroupPoints
                      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
                      χ ∧ ((0 : ℝ) : WithTop ℝ) < x.val χ g} *
                    (doubleRootGroupPoints
                      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
                      χ : Set _))

/-- **Zero-value root jumps descend** (an internal pointwise form of the converse part of KP
Proposition 9.4.28, at a point where the affine root vanishes). The setting is that of
`UnramifiedAffineRootRestrictionStatement`. Let `x` be an `Aut(K/F)`-fixed point of the
apartment of `D`. If a root `χ` of `(G_K, T_K)` restricts to a relative root `α` of `(G, S)` and
has a filtration jump at value `0` for `x`, that is `U_{χ,x,0} ⊈ U_{χ,x,0+} · U_{2χ}(K)`, then
`α` has a filtration jump at value `0` for the restricted valuation `φ x`:
`U_{α,φx,0} ⊈ U_{α,φx,0+} · U_{2α}(F)`. -/
def UnramifiedZeroJumpDescentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
    (hiS : IsMaximalSplitTorus iS)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T),
    CommGroupScheme.groupHom f ≫ iT = iS →
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : Smooth G.X.hom := hG.smooth
    haveI := mono_of_isMaximalSplitTorus hiS
    ∀ (hiT : IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      haveI := mono_of_isMaximalSplitTorus hiT
      haveI : Mono ((GroupScheme.baseChange
          (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
        mono_of_isMaximalSplitTorus hiT
      ∀ (hE : RelativeRoot.HasOppositeFactorPairs
          (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
        (D : KPApartmentData
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
          (IntegerValuation.order (MaximalUnramified.valuation F)))
        (C : CentralizerDatum
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
        IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C →
        let fixed : D.Apartment → Prop := fun x =>
          ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val
        let φ : D.Apartment → RootFunctionFamily S G := fun x =>
          torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
            hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE
            (D.isRootDatumValuation_of_mem x.mem)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)
        ∀ (x : D.Apartment), fixed x →
          ∀ χ ∈ relativeRoots
              ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT),
            ∀ α ∈ relativeRoots iS,
              (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f ≫ χ =
                  characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α →
              ¬ (rootFiltration
                  ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
                  x.val χ 0 ⊆
                {g | g ∈ rootGroupPoints
                    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
                    χ ∧ ((0 : ℝ) : WithTop ℝ) < x.val χ g} *
                  (doubleRootGroupPoints
                    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
                    χ : Set _)) →
              ¬ (rootFiltration iS (φ x) α 0 ⊆
                  {g | g ∈ rootGroupPoints iS α ∧ ((0 : ℝ) : WithTop ℝ) < φ x α g} *
                    (doubleRootGroupPoints iS α : Set (rationalPoints G)))

/-- The root form of a relative root of a split torus is nonzero. -/
theorem rootForm_ne_zero_of_isSplitTorus {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp) (α : relativeRoots i) :
    rootForm i α ≠ 0 := by
  exact Langlands.BruhatTits.SpecialCompact.rootForm_ne_zero_of_split hS i α

section Helpers

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (hS : IsSplitTorus S.toGrp) (f : S ⟶ T)
  (iS : S.toGrp ⟶ G) (iT : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "f_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) f
local notation "iT_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) iT

private instance zeroJumpAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance zeroJumpFiniteType : LocallyOfFiniteType (G_K).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- If an upper character restricts to the base change of a lower character, then evaluating
it on pushed-forward real cocharacters is evaluating the lower character. -/
theorem eval_descentCocharacterMap_of_comp_eq (χ : characterLattice T_K)
    (α : characterLattice S) (h : f_K ≫ χ = characterLattice.baseChange b S α) (v : V S) :
    eval T_K χ (descentCocharacterMap k K f hS v) = eval S α v := by
  rw [eval_descentCocharacterMap, h, eval_splitCocharacterBaseChange]

omit [LocallyOfFiniteType G.X.hom] in
/-- If an upper root restricts to the base change of a lower root, then the pullback of its
root form along `torusFieldTranslationMap` is the lower root form. -/
theorem rootForm_comp_torusFieldTranslationMap_of_comp_eq
    (β : relativeRoots (k := K) (T := T_K) (G := G_K) iT_K) (α : relativeRoots iS)
    (h : f_K ≫ β.val = characterLattice.baseChange b S α.val) :
    (rootForm (S := T_K) iT_K β).comp (torusFieldTranslationMap k K f iT hS) =
      (rootForm iS α).comp (rootAnnihilator iS).mkQ := by
  exact rootForm_comp_torusFieldTranslationMap iS iT f hS α β h

include hS in
/-- A nonzero restriction `f_K ≫ β` of an upper root is the base change of a lower relative
root. -/
theorem exists_relativeRoot_comp_eq_baseChange
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (β : relativeRoots (k := K) (T := T_K) (G := G_K) iT_K) (hne : f_K ≫ β.val ≠ 0) :
    ∃ α ∈ relativeRoots iS, f_K ≫ β.val = characterLattice.baseChange b S α := by
  have hχ : characterLattice.baseChange b S
      ((characterLattice.baseChangeEquiv b S hS).symm (f_K ≫ β.val)) = f_K ≫ β.val :=
    (characterLattice.baseChangeEquiv b S hS).apply_symm_apply _
  have hroot : f_K ≫ β.val ∈ relativeRoots
      (CommGroupScheme.groupHom f_K ≫ iT_K) :=
    (rootRestriction f_K iT_K ⟨β.val, β.property, hne⟩).property
  have hfactor : CommGroupScheme.groupHom f_K ≫ iT_K =
      (GroupScheme.baseChange b).map iS := by
    rw [← hf, CategoryTheory.Functor.map_comp]
    rfl
  refine ⟨(characterLattice.baseChangeEquiv b S hS).symm (f_K ≫ β.val), ?_, hχ.symm⟩
  apply (mem_roots_baseChange_iff (K := K) G S hS iS _).mp
  rw [hχ, ← hfactor]
  exact hroot

/-- **Generic reduction.** Let `a` be an affine map from an apartment of `(G, S)` to an
apartment of `(G_K, T_K)` whose linear part is induced by `V(S) → V(T_K)`. Suppose that at every
point `w`, zero-value filtration jumps of relative roots `α` for `w` lift to zero-value jumps for
`a w` of roots `χ` restricting to `α`, and conversely descend. Then the nonconstant restrictions
along `a` of the affine roots of the upper apartment are exactly the affine roots of the lower
apartment. -/
theorem restrictedRoots_affineRoots_eq_of_zeroJumps [Mono iS.hom.hom.left]
    [Mono (iT_K).hom.hom.left] (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    {ω : Kˣ → ℝ} {ω' : kˣ → ℝ} (D : KPApartmentData (k := K) (S := T_K) (G := G_K) iT_K ω)
    (DS : KPApartmentData iS ω') (a : DS.Apartment →ᵃ[ℝ] D.Apartment)
    (hlin : a.linear.comp (rootAnnihilator iS).mkQ = torusFieldTranslationMap k K f iT hS)
    (hL : ∀ (w : DS.Apartment), ∀ α ∈ relativeRoots iS,
      ¬ (rootFiltration iS w.val α 0 ⊆
          {g | g ∈ rootGroupPoints iS α ∧ ((0 : ℝ) : WithTop ℝ) < w.val α g} *
            (doubleRootGroupPoints iS α : Set (rationalPoints G))) →
      ∃ χ ∈ relativeRoots (k := K) (T := T_K) (G := G_K) iT_K,
        f_K ≫ χ = characterLattice.baseChange b S α ∧
          ¬ (rootFiltration (k := K) (S := T_K) (G := G_K) iT_K (a w).val χ 0 ⊆
            {g | g ∈ rootGroupPoints (k := K) (S := T_K) (G := G_K) iT_K χ ∧
                ((0 : ℝ) : WithTop ℝ) < (a w).val χ g} *
              (doubleRootGroupPoints (k := K) (S := T_K) (G := G_K) iT_K χ :
                Set (rationalPoints G_K))))
    (hD : ∀ (w : DS.Apartment), ∀ χ ∈ relativeRoots (k := K) (T := T_K) (G := G_K) iT_K,
      ∀ α ∈ relativeRoots iS, f_K ≫ χ = characterLattice.baseChange b S α →
      ¬ (rootFiltration (k := K) (S := T_K) (G := G_K) iT_K (a w).val χ 0 ⊆
          {g | g ∈ rootGroupPoints (k := K) (S := T_K) (G := G_K) iT_K χ ∧
              ((0 : ℝ) : WithTop ℝ) < (a w).val χ g} *
            (doubleRootGroupPoints (k := K) (S := T_K) (G := G_K) iT_K χ :
              Set (rationalPoints G_K))) →
      ¬ (rootFiltration iS w.val α 0 ⊆
          {g | g ∈ rootGroupPoints iS α ∧ ((0 : ℝ) : WithTop ℝ) < w.val α g} *
            (doubleRootGroupPoints iS α : Set (rationalPoints G)))) :
    AffineRootSystem.restrictedRoots a D.affineRoots = DS.affineRoots := by
  ext ψ
  constructor
  · rintro ⟨ψ', ⟨β, hβlin, hβjump⟩, rfl, hne⟩
    have hcomp : (ψ'.comp a).linear.comp (rootAnnihilator iS).mkQ =
        (rootForm _ β).comp (torusFieldTranslationMap k K f iT hS) := by
      rw [AffineMap.comp_linear, LinearMap.comp_assoc, hlin, hβlin]
    have hne0 : f_K ≫ β.val ≠ 0 := by
      intro hz
      apply hne
      apply Submodule.linearMap_qext (rootAnnihilator iS)
      rw [hcomp, LinearMap.zero_comp]
      apply LinearMap.ext
      intro v
      change eval _ β.val (descentCocharacterMap k K f hS v) = 0
      rw [eval_descentCocharacterMap, hz]
      exact eval_zero_char _
    obtain ⟨α₀, hα₀, hα₀eq⟩ := exists_relativeRoot_comp_eq_baseChange hS f iS iT hf β hne0
    have hlinα : (ψ'.comp a).linear = rootForm iS ⟨α₀, hα₀⟩ :=
      Submodule.linearMap_qext (rootAnnihilator iS)
        (hcomp.trans (rootForm_comp_torusFieldTranslationMap_of_comp_eq hS f iS iT β
          ⟨α₀, hα₀⟩ hα₀eq))
    obtain ⟨w₀, hw₀⟩ := AffineRootSystem.exists_apply_eq_zero (ψ := ψ'.comp a) hne
    have hx₀ : ψ' (a w₀) = 0 := hw₀
    have hlow := hD w₀ β.val β.property α₀ hα₀ hα₀eq (by
      intro hsub
      apply hβjump
      intro u hu
      rw [SetLike.mem_coe, D.mem_affineRootGroup_iff hβlin (a w₀), hx₀] at hu
      obtain ⟨g, hg, d, hd, rfl⟩ := hsub hu
      refine ⟨g, ?_, d, hd, rfl⟩
      rw [SetLike.mem_coe, D.mem_affineRootGroupPlus_iff hβlin (a w₀), hx₀]
      exact hg)
    refine ⟨⟨α₀, hα₀⟩, hlinα, fun hsub => hlow fun u hu => ?_⟩
    obtain ⟨g, hg, d, hd, rfl⟩ := hsub (by
      rw [SetLike.mem_coe, DS.mem_affineRootGroup_iff hlinα w₀, hw₀]
      exact hu)
    refine ⟨g, ?_, d, hd, rfl⟩
    rw [SetLike.mem_coe, DS.mem_affineRootGroupPlus_iff hlinα w₀, hw₀] at hg
    exact hg
  · rintro ⟨α, hαlin, hαjump⟩
    have hne : ψ.linear ≠ 0 := hαlin ▸ rootForm_ne_zero_of_isSplitTorus iS hS α
    obtain ⟨w₀, hw₀⟩ := AffineRootSystem.exists_apply_eq_zero (ψ := ψ) hne
    obtain ⟨χ, hχ, hχeq, hup⟩ := hL w₀ α.val α.property (by
      intro hsub
      apply hαjump
      intro u hu
      rw [SetLike.mem_coe, DS.mem_affineRootGroup_iff hαlin w₀, hw₀] at hu
      obtain ⟨g, hg, d, hd, rfl⟩ := hsub hu
      refine ⟨g, ?_, d, hd, rfl⟩
      rw [SetLike.mem_coe, DS.mem_affineRootGroupPlus_iff hαlin w₀, hw₀]
      exact hg)
    let β : relativeRoots (k := K) (T := T_K) (G := G_K) iT_K := ⟨χ, hχ⟩
    have hβlin := D.affineFunctional_linear β (a w₀) 0
    have hβ0 : D.affineFunctional β (a w₀) 0 (a w₀) = 0 := by
      rw [KPApartmentData.affineFunctional_apply, vsub_self, map_zero, zero_add]
    refine ⟨D.affineFunctional β (a w₀) 0, ⟨β, hβlin, fun hsub => hup fun u hu => ?_⟩, ?_, hne⟩
    · obtain ⟨g, hg, d, hd, rfl⟩ := hsub (by
        rw [SetLike.mem_coe, D.mem_affineRootGroup_iff hβlin (a w₀), hβ0]
        exact hu)
      refine ⟨g, ?_, d, hd, rfl⟩
      rw [SetLike.mem_coe, D.mem_affineRootGroupPlus_iff hβlin (a w₀), hβ0] at hg
      exact hg
    · apply AffineMap.ext_linear (p := w₀)
      · rw [AffineMap.comp_linear, hβlin, hαlin]
        apply Submodule.linearMap_qext (rootAnnihilator iS)
        rw [LinearMap.comp_assoc, hlin]
        exact rootForm_comp_torusFieldTranslationMap_of_comp_eq hS f iS iT β α hχeq
      · rw [AffineMap.comp_apply, hβ0, hw₀]

/-- **Generic reduction, fixed-point form.** The hypotheses of
`restrictedRoots_affineRoots_eq_of_zeroJumps` follow from lift and descent statements at the
points `x` of the upper apartment satisfying a predicate `fixed`, phrased through a restriction
map `φ`, provided that `a` takes values in `fixed` and that `w = φ (a w)` for every `w`. -/
theorem restrictedRoots_affineRoots_eq_of_fixedZeroJumps [Mono iS.hom.hom.left]
    [Mono (iT_K).hom.hom.left] (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    {ω : Kˣ → ℝ} {ω' : kˣ → ℝ} (D : KPApartmentData (k := K) (S := T_K) (G := G_K) iT_K ω)
    (DS : KPApartmentData iS ω') (a : DS.Apartment →ᵃ[ℝ] D.Apartment)
    (hlin : a.linear.comp (rootAnnihilator iS).mkQ = torusFieldTranslationMap k K f iT hS)
    {fixed : D.Apartment → Prop} {φ : D.Apartment → RootFunctionFamily S G}
    (hLR : ∀ (x : D.Apartment), fixed x →
      ∀ α ∈ relativeRoots iS, 2 • α ∉ relativeRoots iS →
        ¬ (rootFiltration iS (φ x) α 0 ⊆
            {g | g ∈ rootGroupPoints iS α ∧ ((0 : ℝ) : WithTop ℝ) < φ x α g} *
              (doubleRootGroupPoints iS α : Set (rationalPoints G))) →
        ∃ χ ∈ relativeRoots (k := K) (T := T_K) (G := G_K) iT_K,
          f_K ≫ χ = characterLattice.baseChange b S α ∧
            ¬ (rootFiltration (k := K) (S := T_K) (G := G_K) iT_K x.val χ 0 ⊆
              {g | g ∈ rootGroupPoints (k := K) (S := T_K) (G := G_K) iT_K χ ∧
                  ((0 : ℝ) : WithTop ℝ) < x.val χ g} *
                (doubleRootGroupPoints (k := K) (S := T_K) (G := G_K) iT_K χ :
                  Set (rationalPoints G_K))))
    (hLM : ∀ (x : D.Apartment), fixed x →
      ∀ α ∈ relativeRoots iS, 2 • α ∈ relativeRoots iS →
        ¬ (rootFiltration iS (φ x) α 0 ⊆
            {g | g ∈ rootGroupPoints iS α ∧ ((0 : ℝ) : WithTop ℝ) < φ x α g} *
              (doubleRootGroupPoints iS α : Set (rationalPoints G))) →
        ∃ χ ∈ relativeRoots (k := K) (T := T_K) (G := G_K) iT_K,
          f_K ≫ χ = characterLattice.baseChange b S α ∧
            ¬ (rootFiltration (k := K) (S := T_K) (G := G_K) iT_K x.val χ 0 ⊆
              {g | g ∈ rootGroupPoints (k := K) (S := T_K) (G := G_K) iT_K χ ∧
                  ((0 : ℝ) : WithTop ℝ) < x.val χ g} *
                (doubleRootGroupPoints (k := K) (S := T_K) (G := G_K) iT_K χ :
                  Set (rationalPoints G_K))))
    (hD : ∀ (x : D.Apartment), fixed x →
      ∀ χ ∈ relativeRoots (k := K) (T := T_K) (G := G_K) iT_K, ∀ α ∈ relativeRoots iS,
        f_K ≫ χ = characterLattice.baseChange b S α →
        ¬ (rootFiltration (k := K) (S := T_K) (G := G_K) iT_K x.val χ 0 ⊆
            {g | g ∈ rootGroupPoints (k := K) (S := T_K) (G := G_K) iT_K χ ∧
                ((0 : ℝ) : WithTop ℝ) < x.val χ g} *
              (doubleRootGroupPoints (k := K) (S := T_K) (G := G_K) iT_K χ :
                Set (rationalPoints G_K))) →
        ¬ (rootFiltration iS (φ x) α 0 ⊆
            {g | g ∈ rootGroupPoints iS α ∧ ((0 : ℝ) : WithTop ℝ) < φ x α g} *
              (doubleRootGroupPoints iS α : Set (rationalPoints G))))
    (hfix : ∀ w, fixed (a w)) (hval : ∀ w, w.val = φ (a w)) :
    AffineRootSystem.restrictedRoots a D.affineRoots = DS.affineRoots := by
  refine restrictedRoots_affineRoots_eq_of_zeroJumps hS f iS iT hf D DS a hlin ?_ ?_
  · intro w α hα hjump
    rw [hval w] at hjump
    by_cases h2 : 2 • α ∈ relativeRoots iS
    · exact hLM (a w) (hfix w) α hα h2 hjump
    · exact hLR (a w) (hfix w) α hα h2 hjump
  · intro w χ hχ α hα hχα hjump
    rw [hval w]
    exact hD (a w) (hfix w) χ hχ α hα hχα hjump

end Helpers

set_option maxHeartbeats 2000000 in
/-- **Unramified descent of affine roots from zero-value root jumps.** The two lift statements
(non-multipliable and multipliable roots) and the descent statement for zero-value root jumps
at `Aut(K/F)`-fixed points imply `UnramifiedAffineRootRestrictionStatement`. -/
theorem unramifiedAffineRootRestriction_of_zeroJumps
    (hliftR : UnramifiedZeroJumpLiftReducedStatement.{u})
    (hliftM : UnramifiedZeroJumpLiftMultipliableStatement.{u})
    (hdesc : UnramifiedZeroJumpDescentStatement.{u}) :
    UnramifiedAffineRootRestrictionStatement.{u} := by
  intro F _ _ _ _ G hG S iS hiS T iT f hf
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : Mono iS.hom.hom.left := mono_of_isMaximalSplitTorus hiS
  intro hiT
  have : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro hE D C h6
  have hLR := hliftR F G hG S iS hiS T iT f hf hiT hE D C h6
  have hLM := hliftM F G hG S iS hiS T iT f hf hiT hE D C h6
  have hD := hdesc F G hG S iS hiS T iT f hf hiT hE D C h6
  dsimp only at hLR hLM hD ⊢
  intro DS _ a hfix hval hlin
  exact restrictedRoots_affineRoots_eq_of_fixedZeroJumps hiS.isSplitSubtorus.1 f iS iT hf D DS
    a hlin hLR hLM hD hfix hval

end Langlands.Geometry.Building
