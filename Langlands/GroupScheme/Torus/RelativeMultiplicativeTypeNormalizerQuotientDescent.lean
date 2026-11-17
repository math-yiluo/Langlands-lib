import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeNormalizerSmooth
import Langlands.GroupScheme.HomogeneousQuotientFiniteCover
import Langlands.GroupScheme.HomogeneousQuotientLocalModels
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact

/-! # Descent of diagonalizable normalizer quotients to multiplicative type -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
open Langlands.GroupScheme.RelativeMultiplicativeType

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

/-- The precise ring-local input needed to construct normalizer quotients over
all bases: actual quasi-affine models for closed diagonalizable subgroups. -/
def DiagonalizableNormalizerQuotientLocalModels : Prop :=
  ∀ (R : CommRingCat.{u}) (M : Type u) [AddCommGroup M] [AddGroup.FG M]
    (G N : GroupScheme (Spec R)) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G), IsClosedSubgroup i →
    ∀ (n : N ⟶ G), (SubgroupFunctor.range i).normalizer.IsRepresentedBy n →
      ∃ Q : HomogeneousQuotient n, Q.scheme.left.IsQuasiAffine

variable (hdiag : DiagonalizableNormalizerQuotientLocalModels.{u})

include hdiag

/-- The ring-local input is invariant under a supplied diagonalizable source
presentation, with the same supplied normalizer inclusion. -/
theorem diagonalizableNormalizer_quotient_overSpec_of_localModels
    {R : CommRingCat.{u}} {G N H : GroupScheme (Spec R)}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hH : IsDiagonalizable H) (hi : IsClosedSubgroup i)
    (n : N ⟶ G) (hn : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n) :
    ∃ Q : HomogeneousQuotient n, Q.scheme.left.IsQuasiAffine := by
  obtain ⟨M, _, hM, ⟨e⟩⟩ := hH
  let : AddGroup.FG M := hM
  let e' : H ≅ (Diagonalizable.groupScheme R M).toGrp :=
    e ≪≫ Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec R)) M
  have hi' : IsClosedSubgroup (e'.inv ≫ i) := (IsClosedSubgroup.of_iso e'.symm).comp hi
  have hn' : (SubgroupFunctor.range (e'.inv ≫ i)).normalizer.IsRepresentedBy n := by
    change (SubgroupFunctor.range (e'.symm.hom ≫ i)).normalizer.IsRepresentedBy n
    rw [SubgroupFunctor.range_iso_comp e'.symm i]
    exact hn
  exact hdiag R M G N (e'.inv ≫ i) hi' n hn'

/-- Finite affine refinement of a splitting fppf cover descends the actual
normalizer quotient over any affine base. -/
theorem relativeMultiplicativeTypeNormalizer_quotient_affine_of_localModels
    {S : Scheme.{u}} [IsAffine S] {G N H : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hH : IsMultiplicativeType H) (hi : IsClosedSubgroup i)
    (n : N ⟶ G) (hn : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n) :
    ∃ Q : HomogeneousQuotient n, Q.scheme.left.IsQuasiAffine := by
  classical
  let : Mono n.hom.hom := hn.1
  have hN : Smooth N.X.hom := relativeMultiplicativeTypeNormalizer_smooth i hH hi n hn
  obtain ⟨𝒰, h𝒰⟩ := hH
  have hprop (k : 𝒰.I₀) : Flat (𝒰.f k) ∧ LocallyOfFinitePresentation (𝒰.f k) :=
    𝒰.map_prop k
  have : QuasiCompactCover 𝒰.toPreZeroHypercover := .of_isOpenMap fun k => by
    have := (hprop k).1
    have := (hprop k).2
    exact (𝒰.f k).isOpenMap
  obtain ⟨𝒱, f, hfin, _⟩ := QuasiCompactCover.exists_hom 𝒰
  let : Finite 𝒱.I₀ := hfin
  have (k : 𝒱.I₀) : Flat (𝒱.f k) := (𝒱.map_prop k).1
  have (k : 𝒱.I₀) : LocallyOfFinitePresentation (𝒱.f k) := (𝒱.map_prop k).2
  have hsplit (k : 𝒱.I₀) : IsDiagonalizable
      ((GroupScheme.baseChange (𝒱.f k)).obj H) :=
    IsDiagonalizable.of_iso
      (Descent.pullbackComparison (𝒰.f (f.s₀ k)) (f.h₀ k) (𝒱.f k) (f.w₀ k) H).symm
      ((h𝒰 (f.s₀ k)).baseChange (f.h₀ k))
  let Q := HomogeneousQuotientSheaf.quotientOfFiniteAffineCover n hN
    (fun k => Spec (𝒱.X k)) 𝒱.f (fun s => 𝒱.cover.exists_eq s) (fun k => by
      let b := 𝒱.f k
      let B := GroupScheme.baseChange b
      let : Smooth (B.obj G).X.hom := MorphismProperty.pullback_snd G.X.hom b inferInstance
      let : IsAffineHom (B.obj G).X.hom :=
        MorphismProperty.pullback_snd G.X.hom b inferInstance
      have hn' := hn.baseChange b
      rw [SubgroupFunctor.normalizer_baseChange, ← SubgroupFunctor.range_baseChangeHom] at hn'
      exact diagonalizableNormalizer_quotient_overSpec_of_localModels hdiag
        (B.map i) (hsplit k) (hi.baseChange b) (B.map n) hn')
  exact ⟨Q.val, Q.property.2⟩

/-- The split ring-local normalizer quotient input supplies the exact quotient
clause over arbitrary schemes and all supplied normalizer representatives. -/
theorem relativeMultiplicativeTypeNormalizer_quotient_of_localModels
    {S : Scheme.{u}} {G N H : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hH : IsMultiplicativeType H) (hi : IsClosedSubgroup i)
    (n : N ⟶ G) (hn : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n) :
    ∃ Q : HomogeneousQuotient n, Smooth Q.scheme.hom ∧
      ∀ U : S.affineOpens, (Q.scheme.hom ⁻¹ᵁ (U : S.Opens)).toScheme.IsQuasiAffine := by
  let : Mono n.hom.hom := hn.1
  have hN : Smooth N.X.hom := relativeMultiplicativeTypeNormalizer_smooth i hH hi n hn
  apply HomogeneousQuotientSheaf.exists_quotient_of_affine_local_models n hN
  intro T b _ _
  let B := GroupScheme.baseChange b
  let : Smooth (B.obj G).X.hom := MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : IsAffineHom (B.obj G).X.hom := MorphismProperty.pullback_snd G.X.hom b inferInstance
  have hn' := hn.baseChange b
  rw [SubgroupFunctor.normalizer_baseChange, ← SubgroupFunctor.range_baseChangeHom] at hn'
  exact relativeMultiplicativeTypeNormalizer_quotient_affine_of_localModels hdiag
    (B.map i) (hH.baseChange b) (hi.baseChange b) (B.map n) hn'

/-- Choose the global smooth relatively quasi-affine quotient supplied by the
explicit split ring-local normalizer quotient construction. -/
def relativeMultiplicativeTypeNormalizerQuotientOfLocalModels
    {S : Scheme.{u}} {G N H : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hH : IsMultiplicativeType H) (hi : IsClosedSubgroup i)
    (n : N ⟶ G) (hn : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n) :
    {Q : HomogeneousQuotient n // Smooth Q.scheme.hom ∧
      ∀ U : S.affineOpens, (Q.scheme.hom ⁻¹ᵁ (U : S.Opens)).toScheme.IsQuasiAffine} :=
  ⟨_, (relativeMultiplicativeTypeNormalizer_quotient_of_localModels hdiag i hH hi n hn).choose_spec⟩

end Langlands.GroupScheme
