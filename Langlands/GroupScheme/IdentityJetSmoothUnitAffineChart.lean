import Langlands.AlgebraicGeometry.Descent.FppfClosedLocusDescentProof
import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.IdentityJetAffineNeighborhoodBaseChange
import Langlands.GroupScheme.IdentityJetSmoothUnitLocality
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Closed charts for fixed-rank smoothness along the unit -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IdentityJet

open Algebra.SectionJet Langlands.GroupScheme.CoordinateWeights
open Langlands.AlgebraicGeometry.FppfClosedLocusDescent

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- A test map on which the pulled-back group is smooth of fixed rank along its unit. -/
def SmoothUnitRankTest (r : ℕ) {T : Scheme.{u}} (g : T ⟶ S) : Prop :=
  SmoothAlongUnitOfRank ((GroupScheme.baseChange g).obj G) r

section Locality

variable [IsSeparated G.X.hom] [LocallyOfFinitePresentation G.X.hom]

/-- Iterating the test pullback gives the same condition as the composite test. -/
theorem smoothUnitRankTest_comp_iff (r : ℕ) {T U : Scheme.{u}} (g : T ⟶ S) (b : U ⟶ T) :
    SmoothUnitRankTest ((GroupScheme.baseChange g).obj G) r b ↔ SmoothUnitRankTest G r (b ≫ g) := by
  let G' := (GroupScheme.baseChange g).obj G
  let K := (GroupScheme.baseChange b).obj G'
  let H := (GroupScheme.baseChange (b ≫ g)).obj G
  let e := Descent.pullbackComparison g b (b ≫ g) rfl G
  have : IsSeparated G'.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom g))
  have : LocallyOfFinitePresentation G'.X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom g))
  have : IsSeparated K.X.hom := inferInstanceAs (IsSeparated (pullback.snd G'.X.hom b))
  have : LocallyOfFinitePresentation K.X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G'.X.hom b))
  have : IsSeparated H.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom (b ≫ g)))
  have : LocallyOfFinitePresentation H.X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom (b ≫ g)))
  exact ⟨fun h => (show SmoothAlongUnitOfRank K r from h).of_iso e.symm,
    fun h => (show SmoothAlongUnitOfRank H r from h).of_iso e⟩

theorem SmoothUnitRankTest.comp {r : ℕ} {T U : Scheme.{u}} {g : T ⟶ S}
    (h : SmoothUnitRankTest G r g) (b : U ⟶ T) : SmoothUnitRankTest G r (b ≫ g) := by
  let K := (GroupScheme.baseChange g).obj G
  have : IsSeparated K.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom g))
  have : LocallyOfFinitePresentation K.X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom g))
  exact (smoothUnitRankTest_comp_iff G r g b).mp (SmoothAlongUnitOfRank.baseChange h b)

theorem smoothUnitRankTest_of_openCover {r : ℕ} {T : Scheme.{u}} (g : T ⟶ S) (𝒰 : T.OpenCover)
    (h : ∀ i, SmoothUnitRankTest G r (𝒰.f i ≫ g)) : SmoothUnitRankTest G r g := by
  let K := (GroupScheme.baseChange g).obj G
  have : IsSeparated K.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom g))
  have : LocallyOfFinitePresentation K.X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom g))
  exact smoothAlongUnitOfRank_of_openCover 𝒰 fun i => (smoothUnitRankTest_comp_iff G r g (𝒰.f i)).mpr (h i)

end Locality

private theorem factors_SpecQuotient_iff {R : Type u} [CommRing R] (I : Ideal R)
    {T : Scheme.{u}} (g : T ⟶ Spec (.of R)) :
    (∃ k : T ⟶ Spec (.of (R ⧸ I)), k ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = g) ↔
      I ≤ RingHom.ker ((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop).hom := by
  let f := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let j := Spec.map f
  have : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective f Ideal.Quotient.mk_surjective
  rw [factors_iff_ker_appTop_le j g]
  let e := (Scheme.ΓSpecIso (.of R)).inv
  rw [← Ideal.comap_le_comap_iff_of_surjective e.hom (ConcreteCategory.bijective_of_isIso e).2,
    RingHom.comap_ker, RingHom.comap_ker, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  have he : e ≫ j.appTop = f ≫ (Scheme.ΓSpecIso (.of (R ⧸ I))).inv :=
    (Scheme.ΓSpecIso_inv_naturality f).symm
  rw [he, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of (R ⧸ I))).inv).1]
  change RingHom.ker (Ideal.Quotient.mk I) ≤ _ ↔ _
  rw [Ideal.mk_ker]

variable [IsAffine S]

/-- The basic affine base open presented by localization of global functions. -/
abbrev smoothUnitBasicMap (a : Γ(S, ⊤)) : Spec (.of (Localization.Away a)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (Localization.Away a))) ≫ S.isoSpec.inv

/-- Over a basic open with a specified spanning tuple, fixed-rank smoothness
along the unit is represented by the closed coefficient ideal. -/
theorem exists_closed_smoothUnitBasicChart [IsLocallyNoetherian S]
    [IsSeparated G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    {W : Scheme.{u}} [IsAffine W] (v : W ⟶ G.X.left) [IsOpenImmersion v]
    (e : S ⟶ W) (he : e ≫ v = G.identitySection) (r : ℕ) (a : Γ(S, ⊤))
    (z : Fin r → RingHom.ker (neighborhoodAugmentation G v e he))
    (hspan : letI := neighborhoodAlgebra G v
      Submodule.span (Localization.Away a) (Set.range fun i =>
        AugmentedAlgebra.classMap
          (baseChangeAugmentation (neighborhoodAugmentation G v e he) (Localization.Away a))
          ((1 : Localization.Away a) ⊗ₜ[Γ(S, ⊤)] (z i : Γ(W, ⊤)))) = ⊤) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ Spec (.of (Localization.Away a))), IsClosedImmersion j ∧
      ∀ (T : Scheme.{u}) (g : T ⟶ Spec (.of (Localization.Away a))),
        (∃ k : T ⟶ Z, k ≫ j = g) ↔ SmoothUnitRankTest G r (g ≫ smoothUnitBasicMap a) := by
  let R := Γ(S, ⊤)
  let A := Γ(W, ⊤)
  let L := Localization.Away a
  let := neighborhoodAlgebra G v
  let ε := neighborhoodAugmentation G v e he
  let εL := baseChangeAugmentation ε L
  let zL : Fin r → L ⊗[R] A := fun i => (1 : L) ⊗ₜ[R] (z i : A)
  have hzL (i : Fin r) : εL (zL i) = 0 := by
    change baseChangeAugmentation ε L ((1 : L) ⊗ₜ[R] (z i : A)) = 0
    rw [baseChangeAugmentation_tmul, show ε (z i : A) = 0 from (z i).property, map_zero, mul_zero]
  let J := jetIsomorphismIdeal (Coordinates.aeval_preserves_augmentation zL hzL)
  let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let b := smoothUnitBasicMap a
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  have : IsNoetherianRing L := IsLocalization.isNoetherianRing (Submonoid.powers a) L inferInstance
  have : LocallyOfFinitePresentation (v ≫ G.X.hom) := inferInstance
  have : Algebra.FinitePresentation R A := HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation)
    (v ≫ G.X.hom) inferInstance
  have : IsClosedImmersion j := IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of L) J
  have haff (T : Scheme.{u}) [IsAffine T] (g : T ⟶ Spec (.of L)) :
      (∃ k : T ⟶ Spec (.of (L ⧸ J)), k ≫ j = g) ↔ SmoothUnitRankTest G r (g ≫ b) := by
    let B := Γ(T, ⊤)
    let f := g ≫ b
    let φ : CommRingCat.of L ⟶ B := (Scheme.ΓSpecIso (.of L)).inv ≫ g.appTop
    let : Algebra L B := φ.hom.toAlgebra
    let : Algebra R B := f.appTop.hom.toAlgebra
    have htower : IsScalarTower R L B := IsScalarTower.of_algebraMap_eq' (by
      change f.appTop.hom = φ.hom.comp (algebraMap R L)
      rw [Scheme.Hom.comp_appTop, appTop_specMap_comp_isoSpec_inv]
      rfl)
    have hsp : Submodule.span L (Set.range (AugmentedAlgebra.classMap εL ∘ zL)) = ⊤ := hspan
    have hJ := Coordinates.sectionJetSmoothRankLocus L (L ⊗[R] A) B εL r zL hzL hsp
    have hcancel := smoothAlongSectionOfRank_iff_equiv (Algebra.TensorProduct.cancelBaseChange R L B B A)
      (baseChangeAugmentation_cancelBaseChange (B := L) ε) r
    have hf := smoothAlongUnitOfRank_baseChange_iff_affine G v e he f r
    exact (factors_SpecQuotient_iff J g).trans (hJ.trans (hcancel.trans hf.symm))
  refine ⟨Spec (.of (L ⧸ J)), j, inferInstance, fun T g => ?_⟩
  constructor
  · rintro ⟨k, hk⟩
    apply smoothUnitRankTest_of_openCover G (g ≫ b) T.affineCover
    intro i
    rw [← Category.assoc]
    exact (haff _ _).mp ⟨T.affineCover.f i ≫ k, by rw [Category.assoc, hk]⟩
  · intro hg
    refine exists_lift_of_covering Scheme.zariskiTopology j g _ T.affineCover.mem_grothendieckTopology ?_
    intro T' f hf
    obtain ⟨_, m, _, ⟨i⟩, rfl⟩ := hf
    have hloc : SmoothUnitRankTest G r ((T.affineCover.f i ≫ g) ≫ b) := by
      rw [Category.assoc]
      exact SmoothUnitRankTest.comp G hg (T.affineCover.f i)
    obtain ⟨k, hk⟩ := (haff _ _).mpr hloc
    exact ⟨m ≫ k, by rw [Category.assoc, hk, Category.assoc]⟩

end Langlands.GroupScheme.IdentityJet
