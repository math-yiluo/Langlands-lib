import Langlands.GroupScheme.Rational.NumberFieldTotallyComplexClassicalTypeDIsotropy
import Langlands.GroupScheme.Rational.NumberFieldTypeE6CubicSplitTypeDFactor
import Langlands.GroupScheme.Reductive.TitsIndexFieldExtensionCartan
import Langlands.GroupScheme.SimplyConnected.TypeD4StarOrbits
import Langlands.GroupScheme.SimplyConnected.TypeDRankOneOrbit

/-! # Isotropy for cubically split E6 from trialitarian isotropy -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000

private local instance affineBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [IsAffineHom G.X.hom] : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›

private local instance finiteTypeBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [LocallyOfFiniteType G.X.hom] : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹LocallyOfFiniteType G.X.hom›

/-- A supplied splitting field realizes the absolute Cartan matrix by a
numbered pinning of the scalar-extended group. -/
theorem TitsIndexData.exists_numbered_splitPinning
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    [Algebra K (SeparableClosure F)] [IsScalarTower F K (SeparableClosure F)]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n) (C : Matrix (Fin n) (Fin n) ℤ)
    (hC : ∀ a b, d.cartan a b = C (e a) (e b))
    (hsplit : HasSplitMaximalTorus ((GroupScheme.baseChange (algebraBaseMap F K)).obj G)) :
    ∃ (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap F K)).obj G))
      (eK : p.base.support ≃ Fin n),
      ∀ a b, p.rootDatum.pairing a.val b.val = C (eK a) (eK b) := by
  let GK := (GroupScheme.baseChange (algebraBaseMap F K)).obj G
  have hGK := connectedReductiveFieldExtensionStatement F K G d.isSemisimple.isConnectedReductive
  obtain ⟨T, t, hT, ht⟩ := hsplit
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence K GK hGK T hT t ht
  let : Finite J := hJ
  let : P.IsReduced := hred
  let B := d.splitMaximalTorusBase hT ht hP
  let p : SplitPinning GK :=
    { isConnectedReductive := hGK
      torus := T
      inclusion := t
      isSplitTorus := hT
      isMaximalTorus := ht
      rootIndex := J
      rootDatum := P
      isRootDatum := hP
      isReduced := hred
      base := B
      pinning := RootPinning.ofSplitMaximalTorus hGK hT t ht P hP B }
  let v := d.splitMaximalTorusBaseEquiv hT ht hP
  refine ⟨p, v.symm.trans e, fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := v.surjective a
  obtain ⟨b, rfl⟩ := v.surjective b
  have hc := (P.algebraMap_pairingIn ℤ (v a).val (v b).val).symm.trans
    (d.cartanMatrix_splitMaximalTorusBaseEquiv hT ht hP a b)
  change P.pairing (v a).val (v b).val = C (e (v.symm (v a))) (e (v.symm (v b)))
  rw [v.symm_apply_apply, v.symm_apply_apply]
  exact hc.trans (hC a b)

/-- Trialitarian D4 isotropy over a totally complex number field. The
trialitarian condition means that every leaf has a mover under the star action. -/
def NumberFieldTotallyComplexTrialitarianTypeD4IsotropyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F], IsTotallyComplex F →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4),
      IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
      (∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b)) →
      (∀ a, e a ≠ 1 → ∃ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a ≠ a) →
      ¬ IsAnisotropic G

private theorem not_isAnisotropic_of_typeD_of_trialitarian
    (hTri : NumberFieldTotallyComplexTrialitarianTypeD4IsotropyStatement.{u})
    {F : Type u} [Field F] [NumberField F] (hF : IsTotallyComplex F)
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) {n : ℕ} (hn : 4 ≤ n) (e : d.Vertex ≃ Fin n)
    (hsc : IsSimplyConnected G) (habs : IsAbsolutelyAlmostSimple G)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b)) : ¬ IsAnisotropic G := by
  rcases eq_or_lt_of_le hn with he | h
  · subst n
    by_cases hl : ∃ a, e a ≠ 1 ∧ ∀ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a = a
    · obtain ⟨a, ha, hfix⟩ := hl
      exact numberFieldTotallyComplexClassicalTypeDIsotropy F hF G d 4 (d.d4NumberingAt e a) le_rfl
        hsc habs (d.d4NumberingAt_cartan e hD a ha)
        (d.star_fixes_nonfork_of_D4_fixed_leaf e hD a ha hfix)
    · push Not at hl
      exact hTri F hF G d e hsc habs hD hl
  · exact numberFieldTotallyComplexClassicalTypeDIsotropy F hF G d n e hn hsc habs hD
      (d.star_fixes_nonfork_of_D h e hD)

/-- Cubically split simply connected type E6 is isotropic over a totally
complex number field. -/
def NumberFieldTotallyComplexTypeE6CubicSplitIsotropyStatement : Prop :=
  ∀ (F K : Type u) [Field F] [NumberField F] [Field K] [Algebra F K]
      [FiniteDimensional F K] [IsGalois F K], IsTotallyComplex F → Module.finrank F K = 3 →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
        IsSimplyConnected G → (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
        HasSplitMaximalTorus ((GroupScheme.baseChange (algebraBaseMap F K)).obj G) →
        ¬ IsAnisotropic G

/-- Trialitarian D4 isotropy suffices for the cubic splitting case of E6. -/
def NumberFieldTotallyComplexTypeE6CubicSplitIsotropyReductionStatement : Prop :=
  NumberFieldTotallyComplexTrialitarianTypeD4IsotropyStatement.{u} →
    NumberFieldTotallyComplexTypeE6CubicSplitIsotropyStatement.{u}

/-- The trialitarian D4 case completes the orthogonal factor argument for
cubically split E6 over totally complex fields. -/
theorem numberFieldTotallyComplexTypeE6CubicSplitIsotropy_of_trialitarian
    (hTri : NumberFieldTotallyComplexTrialitarianTypeD4IsotropyStatement.{u}) :
    NumberFieldTotallyComplexTypeE6CubicSplitIsotropyStatement.{u} := by
  intro F K _ _ _ _ _ _ hF hK G _ _ d e hsc hE hsplit hAni
  let φ : K →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let : Algebra K (SeparableClosure F) := φ.toRingHom.toAlgebra
  let : IsScalarTower F K (SeparableClosure F) :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  obtain ⟨p, eK, hEK⟩ := d.exists_numbered_splitPinning e (CartanMatrix.E 6) hE hsplit
  obtain ⟨L, _, _, _, _, Q, _, _, dQ, hscQ, habsQ, hAniQ, n, hn, _, eQ, hD⟩ :=
    numberFieldTotallyComplexTypeE6CubicSplitTypeDFactor F K hF hK G hAni hsc p eK hEK
  let : NumberField L := NumberField.of_module_finite F L
  let : IsTotallyComplex F := hF
  exact not_isAnisotropic_of_typeD_of_trialitarian hTri (isTotallyComplex_of_algebra F L)
    dQ hn eQ hscQ habsQ hD hAniQ

end Langlands.GroupScheme
