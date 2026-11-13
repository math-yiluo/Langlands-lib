import Langlands.Geometry.Building.UnramifiedValuationDescentStatement
import Langlands.Geometry.Building.QuasiSplitApartmentShifts

/-! # Unramified descent of vanishing root directions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance unramifiedRootJumpDescentAffineHom {k K : Type u} [Field k]
    [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged k K G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- Push original real cocharacters to the upper reduced translation space. -/
def torusFieldTranslationMap (k K : Type u) [Field k] [Field K] [Algebra k K]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (f : S ⟶ T) (iT : T.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp) :
    V S →ₗ[ℝ] TranslationSpace
      (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map iT) :=
  (rootAnnihilator (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map iT)).mkQ.comp
    (descentCocharacterMap k K f hS)

set_option maxHeartbeats 1000000 in
/-- Internal filtration formulation of the root-hyperplane restriction step in
KP Proposition 9.9.2. At every Galois-fixed upper apartment point, a vanishing upper
root with nonconstant restriction gives a lower zero filtration jump in the same
direction. No specialness or lower apartment datum is assumed. -/
def UnramifiedRootJumpDescentStatement : Prop :=
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
        let P := torusFieldTranslationMap F (inertiaFixedField F) f iT hiS.isSplitSubtorus.1
        let Q : RealTorusSpace.V S →ₗ[ℝ] TranslationSpace iS := (rootAnnihilator iS).mkQ
        ∀ (x : D.Apartment), fixed x →
          ∀ (ψ : D.affineRoots), ψ.val x = 0 →
            ψ.val.linear.comp P ≠ 0 →
            ∃ (a : relativeRoots iS) (g : rationalPoints G),
              g ∈ rootGroupPoints iS a ∧ φ x a g = (0 : WithTop ℝ) ∧
                LinearMap.ker ((rootForm iS a).comp Q) =
                  LinearMap.ker (ψ.val.linear.comp P)

end Langlands.Geometry.Building
