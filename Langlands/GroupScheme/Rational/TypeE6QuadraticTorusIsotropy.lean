import Langlands.GroupScheme.Rational.AnisotropicGaloisFixedCharacters
import Langlands.GroupScheme.Reductive.StarActionFiniteStageProof
import Langlands.GroupScheme.Reductive.RootPinningFromSplitTorus
import Langlands.GroupScheme.SimplyConnected.TypeE6Opposition

/-! # Isotropy of inner E6 with a quadratically split maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.RootDatumNegation

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

/-- The nonidentity automorphism of a quadratic Galois extension acts by
negation on characters of a closed torus in an anisotropic group. -/
theorem IsAnisotropic.quadratic_character_action_eq_neg
    {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hG : IsAnisotropic G) {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
    (hi : IsClosedSubgroup i) (hT : IsTorus T.toGrp) (hL : Module.finrank F L = 2)
    (σ : L ≃ₐ[F] L) (hσ : σ ≠ 1)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T)) :
    characterLattice.galoisRepresentation F L T σ χ = -χ := by
  let ρ := characterLattice.galoisRepresentation F L T
  have hcard := (IsGalois.card_aut_eq_finrank F L).trans hL
  obtain ⟨_, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).mp hcard
  have hσ2 : σ * σ = 1 := by
    have h := pow_card_eq_one' (x := σ)
    rwa [hcard, pow_two] at h
  have hzero : ρ σ χ + χ = 0 := by
    apply hG.galoisFixed_character_eq_zero hi hT L
    intro τ
    by_cases hτ : τ = 1
    · rw [hτ, map_one]
      rfl
    · rw [(huniq τ hτ).trans (huniq σ hσ).symm, map_add,
        ← Module.End.mul_apply, ← map_mul, hσ2, map_one]
      exact add_comm _ _
  exact eq_neg_of_add_eq_zero_left hzero

/-- An affine locally finite-type simply connected inner E6 group with a
maximal torus splitting over a quadratic Galois extension is isotropic. -/
def TypeE6QuadraticTorusIsotropyStatement : Prop :=
  ∀ (F : Type u) [Field F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (e : d.Vertex ≃ Fin 6),
    IsSimplyConnected G →
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    (∀ (τ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex), d.star τ a = a) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L],
      Module.finrank F L = 2 →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G),
        IsMaximalTorus i →
        IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T).toGrp →
        ¬ IsAnisotropic G

open StarActionFiniteStage StarActionIndependence in
theorem typeE6QuadraticTorusIsotropy : TypeE6QuadraticTorusIsotropyStatement.{u} := by
  classical
  intro F _ G _ _ d e hsc hE hinner L _ _ _ _ hL T i hi hT han
  let Ω := SeparableClosure F
  let ι : L →ₐ[F] Ω := IsSepClosed.lift
  let : Algebra L Ω := ι.toRingHom.toAlgebra
  let : IsScalarTower F L Ω := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  let b := algebraBaseMap F L
  let j := algebraBaseMap L Ω
  let c := algebraBaseMap F Ω
  have hc : j ≫ b = c := by
    simp only [j, b, c, algebraBaseMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq F L Ω]
  let TL := (CommGroupScheme.baseChange b).obj T
  let TΩ := (CommGroupScheme.baseChange c).obj T
  let GΩ := (GroupScheme.baseChange c).obj G
  let iΩ : TΩ.toGrp ⟶ GΩ := (GroupScheme.baseChange c).map i
  let : IsAffineHom GΩ.X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom c))
  have hGΩ := d.pinning.isConnectedReductive
  let : Smooth G.X.hom := d.isSemisimple.isConnectedReductive.smooth
  have hTΩ := GaloisPinningData.isSplitTorus_separableClosure T hi.1
  have hiΩ : IsMaximalTorus iΩ := (maximalTorusBaseChange F Ω G T i hi.1 hi.2.1).mp hi
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence Ω GΩ hGΩ TΩ hTΩ iΩ hiΩ
  let : Finite J := hJ
  let : P.IsReduced := hred
  let B := Langlands.LinearAlgebra.RootDatumBase.base P
  let p : GaloisPinningData F Ω G :=
    { torus := T
      inclusion := i
      isConnectedReductive := hGΩ
      isSplitTorus := hTΩ
      isMaximalTorus := hiΩ
      rootIndex := J
      rootDatum := P
      isRootDatum := hP
      isReduced := hred
      base := B
      pinning := RootPinning.ofSplitMaximalTorus hGΩ hTΩ iΩ hiΩ P hP B }
  obtain ⟨σ, hσ, _⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).mp
    ((IsGalois.card_aut_eq_finrank F L).trans hL)
  let τ : Ω ≃ₐ[F] Ω := σ.liftNormal Ω
  let extend := towerCharacterOf b j T c hc
  have hs : Function.Surjective extend :=
    (characterLattice.congr (towerIsoOf b j T c hc).symm).surjective.comp
      (hT.characterLattice_baseChange_bijective j TL).surjective
  have hneg : p.galoisAction τ = negAut P := by
    apply equiv_ext_of_weightMap
    intro χ
    obtain ⟨χ₀, rfl⟩ := hs χ
    rw [galoisAction_weightMap_apply, negAut_weightMap]
    have htransport := towerCharacterOf_transport b j T c hc (galoisBaseMap F L σ)
      (galoisBaseMap_over F L σ) (galoisBaseMap F Ω τ) (galoisBaseMap_over F Ω τ)
      (algebraBaseMap_comp_galoisBaseMap σ τ (AlgEquiv.liftNormal_commutes σ Ω)) χ₀
    change extend (characterLattice.galoisRepresentation F L T σ χ₀) =
      characterLattice.galoisRepresentation F Ω T τ (extend χ₀) at htransport
    rw [← htransport, han.quadratic_character_action_eq_neg hi.2.1 hi.1 hL σ hσ]
    change (towerIsoOf b j T c hc).hom ≫ characterLattice.baseChange j TL (-χ₀) =
      -((towerIsoOf b j T c hc).hom ≫ characterLattice.baseChange j TL χ₀)
    rw [map_neg, Preadditive.comp_neg]
  have hstar : d.pinning.starAction τ = 1 := by
    apply Subtype.ext
    exact InnerTypeANormOneReduction.aut_eq_one_of_simple d.pinning.base
      (d.pinning_corootSpan_eq_top hsc) _ (fun a => congrArg Subtype.val (hinner τ a))
  obtain ⟨_, _, a, _, _, _, ha⟩ := starActionIndependence F Ω G d.pinning p
  have hpstar : p.starAction τ = 1 := by
    apply Subtype.ext
    apply equiv_ext_of_weightMap
    intro χ
    obtain ⟨ψ, rfl⟩ := a.weightEquiv.surjective χ
    have h := ha τ
    rw [hstar] at h
    exact (congrArg (fun q => q.weightMap ψ) h).symm
  have hw : negAut P ∈ P.weylGroup := hneg ▸ (p.starAction_eq_one_iff τ).mp hpstar
  have hw' := conjAut_mem_weylGroup a.symm hw
  have hconj : conjAut a.symm (negAut P) = negAut d.pinning.rootDatum := by
    apply equiv_ext_of_weightMap
    intro χ
    let q := a.symm
    change (conjAut q (negAut p.toSplitPinning.rootDatum)).weightMap χ =
      (negAut d.pinning.toSplitPinning.rootDatum).weightMap χ
    rw [conjAut_weightMap, negAut_weightMap]
    have hn (x : characterLattice p.toSplitPinning.torus) :
        (negAut p.toSplitPinning.rootDatum).weightEquiv x = -x :=
      negAut_weightMap p.toSplitPinning.rootDatum x
    rw [hn, map_neg, LinearEquiv.apply_symm_apply]
  rw [hconj] at hw'
  exact Langlands.TypeE6NegationWeyl.negAut_not_mem_weylGroup d.pinning.rootDatum
    d.pinning.base e hE (d.pinning_corootSpan_eq_top hsc) hw'

end Langlands.GroupScheme
