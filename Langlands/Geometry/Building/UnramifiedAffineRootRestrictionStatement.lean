import Langlands.Geometry.Building.UnramifiedRootJumpDescentStatement
import Langlands.Geometry.Building.AffineRootRestriction
import Langlands.Geometry.Building.KPBuilding

/-! # Unramified descent of affine roots -/

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

set_option maxHeartbeats 1000000 in
/-- **Relative affine roots are the nonconstant restrictions of absolute affine roots**
(an internal set-equality form of KP Proposition 9.4.28, in the setting of KP 9.4.27).
Let `K` be the maximal unramified extension of a
nonarchimedean local field `F`, `S` a maximal `F`-split torus of a connected reductive
`F`-group `G`, and `T ⊇ S` an `F`-torus with `T_K` a maximal `K`-split torus of `G_K`. Let `D`
be an equipollence class of valuations of the root datum of `(G_K, T_K)` satisfying V 6 for
the order of `K`, and `DS` an equipollence class of valuations of the root datum of `(G, S)`
whose members are exactly the field restrictions `φ x` of the `Aut(K/F)`-fixed points `x` of
the apartment of `D`. For every affine map `a` from the apartment of `DS` to the apartment of
`D` sending each point `w` to an `Aut(K/F)`-fixed point whose restriction is `w`, and whose
linear part is induced by the inclusion of real cocharacters `V(S) → V(T_K)`, the affine roots
of `DS` are exactly the nonconstant restrictions along `a` of the affine roots of `D`. -/
def UnramifiedAffineRootRestrictionStatement : Prop :=
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
        ∀ (DS : KPApartmentData iS (localFieldOrder F)),
          (∀ ψ : RootFunctionFamily S G, ψ ∈ DS.carrier ↔ ∃ x, fixed x ∧ ψ = φ x) →
          ∀ (a : DS.Apartment →ᵃ[ℝ] D.Apartment),
            (∀ w, fixed (a w)) → (∀ w, w.val = φ (a w)) →
            a.linear.comp (rootAnnihilator iS).mkQ =
              torusFieldTranslationMap F (inertiaFixedField F) f iT hiS.isSplitSubtorus.1 →
            AffineRootSystem.restrictedRoots a D.affineRoots = DS.affineRoots

end Langlands.Geometry.Building
