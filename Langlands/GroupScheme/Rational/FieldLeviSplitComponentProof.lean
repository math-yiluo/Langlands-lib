import Langlands.GroupScheme.Rational.FieldLeviSplitComponentStatement
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.Rational.LeviSplitComponentInclusionProof
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Reductive.FieldExtensionProof

/-! # Split components of nested Levi subgroups over a field extension -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The base change of the split component of a rational Levi `M` factors through the split
component of a rational Levi `M₁` of the scalar extension contained in `M_K`. -/
theorem fieldLeviSplitComponentInclusion : FieldLeviSplitComponentInclusionStatement.{u} := by
  intro k K _ _ _ G _ _ hG f BC P M p l hP hl P₁ M₁ p₁ l₁ hP₁ hl₁ m hm A a hA A₁ a₁ hA₁
  have hGK : IsConnectedReductive (BC.obj G) := connectedReductiveFieldExtensionStatement k K G hG
  have hM₁ : IsClosedSubgroup (l₁ ≫ p₁) := hl₁.isClosedSubgroup.comp hP₁.isClosedSubgroup
  have hMK : IsClosedSubgroup (BC.map (l ≫ p)) :=
    (hl.isClosedSubgroup.comp hP.isClosedSubgroup).baseChange f
  have hZ : (torusCentralizer (a₁ ≫ l₁ ≫ p₁)).IsRepresentedBy (l₁ ≫ p₁) :=
    ⟨hM₁.mono_overHom,
      (leviSplitComponentCentralizer K (BC.obj G) hGK P₁ M₁ p₁ l₁ hP₁ hl₁ A₁ a₁ hA₁).symm⟩
  have haCentral : IsCentral (BC.map a) := hA.isCentralSplitTorus.isCentral.baseChange f
  have ha₁InMK : (a₁ ≫ m) ≫ BC.map (l ≫ p) = a₁ ≫ l₁ ≫ p₁ := by
    rw [Category.assoc, hm]
  have hRange : SubgroupFunctor.range (BC.map a ≫ BC.map (l ≫ p)) ≤
      torusCentralizer (a₁ ≫ l₁ ≫ p₁) :=
    haCentral.range_comp_le_torusCentralizer_of_factor (BC.map (l ≫ p)) _ (a₁ ≫ m) ha₁InMK
  let g := hZ.factorHom (BC.map a ≫ BC.map (l ≫ p)) hRange
  have hgG : g ≫ l₁ ≫ p₁ = BC.map a ≫ BC.map (l ≫ p) := hZ.factorHom_comp _ _
  have hMKRep : (SubgroupFunctor.range (BC.map (l ≫ p))).IsRepresentedBy (BC.map (l ≫ p)) :=
    ⟨hMK.mono_overHom, rfl⟩
  have hg : g ≫ m = BC.map a := by
    apply hMKRep.hom_ext
    rw [Category.assoc, hm, hgG]
  have hmClosed : IsClosedSubgroup m := IsClosedSubgroup.of_comp hMK (by
    rw [hm]
    exact hM₁)
  have hgCentral : IsCentral g := by
    apply IsCentral.of_comp hmClosed.mono_overHom
    rwa [hg]
  have : IsAffineHom M₁.X.hom := hl₁.isConnectedReductive.isAffineHom
  obtain ⟨j, hj⟩ := hA₁.exists_factor
    (hA.isCentralSplitTorus.isSplitSubtorus.1.baseChange f) hgCentral
  refine ⟨Additive.ofMul j, ?_⟩
  change j ≫ a₁ ≫ m = BC.map a
  rw [← Category.assoc, hj, hg]

end Langlands.GroupScheme
