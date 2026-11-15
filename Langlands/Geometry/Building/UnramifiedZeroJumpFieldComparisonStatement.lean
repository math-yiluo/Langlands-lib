import Langlands.Geometry.Building.UnramifiedAffineRootRestrictionReduction
import Langlands.Geometry.Building.RootJumpLiftNonMultipliable

/-! # Zero-value root jumps over `F` and over the maximal unramified extension -/

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

/-- **Zero-value root jumps over `F` and over `F^ur`** (an internal intermediate form of KP
Proposition 9.4.28, at a point where the affine root vanishes). The setting (`F`, `K = F^ur`,
`G`, `S`, `T`, `D`, `fixed`, `φ`) is that of `UnramifiedZeroJumpLiftMultipliableStatement`. For
a point `x` of the apartment of `D`, `ψ x` is the torus restriction of `x` from `T_K` to `S_K`,
a family of root functions of `(G_K, S_K)`; the restricted valuation `φ x` of `(G, S)` is its
restriction to `F`-points. Let `x` be `Aut(K/F)`-fixed and `α` a relative root of `(G, S)`.
Then `α` has a filtration jump at value `0` for `φ x`, that is
`U_{α,φx,0} ⊈ U_{α,φx,0+} · U_{2α}(F)`, if and only if `α_K` has a filtration jump at value `0`
for `ψ x`, that is `U_{α_K,ψx,0} ⊈ U_{α_K,ψx,0+} · U_{2α_K}(K)`. The families enter through
variables `φx` and `ψx` with the hypotheses `φ x = φx` and `ψ x = ψx`, so that the statement
can be applied to any expression of these two families. -/
def UnramifiedZeroJumpFieldComparisonStatement : Prop :=
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
        let ψ : D.Apartment → RootFunctionFamily
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S)
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj G) := fun x =>
          torusRestrictedRootFunctionFamily
            (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
            (i := (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
            (hiS.isSplitSubtorus.1.baseChange (algebraBaseMap F (inertiaFixedField F)))
            hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)
        ∀ (x : D.Apartment), fixed x →
          ∀ (φx : RootFunctionFamily S G)
            (ψx : RootFunctionFamily
              ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S)
              ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj G)),
            φ x = φx → ψ x = ψx →
            ∀ α ∈ relativeRoots iS,
              (IsRootFiltrationJump iS φx α 0 ↔
                IsRootFiltrationJump
                  ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS) ψx
                  (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) 0)

end Langlands.Geometry.Building
