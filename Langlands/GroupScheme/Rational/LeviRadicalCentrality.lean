import Langlands.GroupScheme.Rational.NormalSolvableCentrality
import Langlands.GroupScheme.Rational.LeviPreimageSolvableRadical

/-! # Centrality of a solvable radical under a rational Levi retraction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A smooth connected affine solvable normal subgroup has central image under
any split homomorphism to a connected reductive group. -/
theorem IsSolvableGroupScheme.isCentral_comp_split
    {k : Type u} [Field k]
    {P L R : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom R.X.hom] [Smooth R.X.hom] [ConnectedSpace R.X.left]
    (hR : IsSolvableGroupScheme R) (hL : IsConnectedReductive L)
    (l : L ⟶ P) (q : P ⟶ L) (r : R ⟶ P)
    (hlq : l ≫ q = 𝟙 L) (hn : (SubgroupFunctor.range r).IsNormal) :
    IsCentral (r ≫ q) := by
  let : IsAffineHom L.X.hom := hL.isAffineHom
  let : Smooth L.X.hom := hL.smooth
  let : GeometricallyIntegral R.X.hom :=
    smoothConnectedAffineGeometry.1 k R inferInstance inferInstance inferInstance
  let φ := r ≫ q
  let : Smooth (SchematicImage.image φ).X.hom := HomImage.smooth_image φ
  let : Surjective (SchematicImage.projection φ).hom.hom.left :=
    HomImage.surjective_projection φ
  have hsol := LeviPreimageRadical.isSolvableGroupScheme_of_surjective
    (SchematicImage.projection φ) hR
  have hcentral := hsol.isCentral_of_normal_of_isConnectedReductive_field hL
    (SchematicImage.inclusion φ) (HomImage.isClosedSubgroup_inclusion φ)
    (LeviPreimageRadical.isNormal_range_imageInclusion l q r hlq hn)
  have h := hcentral.comp (SchematicImage.projection φ)
  rwa [SchematicImage.projection_inclusion] at h

/-- A rational Levi admits a retraction under which the specified solvable
radical is central. -/
def RationalLeviRadicalCentralityStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (P L R : GroupScheme (Spec (CommRingCat.of k)))
    (l : L ⟶ P) (r : R ⟶ P),
    IsRationalLeviSubgroup l → IsSolvableRadical r →
    ∃ q : P ⟶ L, l ≫ q = 𝟙 L ∧ IsCentral (r ≫ q)

theorem rationalLeviRadicalCentrality : RationalLeviRadicalCentralityStatement.{u} := by
  intro k _ P L R l r hl hr
  obtain ⟨U, u, hu, hmul⟩ := hl.exists_unipotentRadical
  let : IsIso (subgroupMultiplication l u) := hmul
  let : IsAffineHom P.X.hom := hl.isAffineHom
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  let : IsAffineHom R.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  let : Smooth R.X.hom := hr.smooth
  let : ConnectedSpace R.X.left := hr.connectedSpace
  let q := leviRetraction l u hu.1.isNormal
  have hlq : l ≫ q = 𝟙 L := levi_comp_leviRetraction l u hu.1.isNormal
  exact ⟨q, hlq, hr.isSolvableGroupScheme.isCentral_comp_split
    hl.isConnectedReductive l q r hlq hr.isNormal⟩

/-- Every subgroup of the specified solvable radical that factors into a
rational Levi is central in that Levi. -/
theorem IsRationalLeviSubgroup.isCentral_of_factor_solvableRadical
    {k : Type u} [Field k]
    {P L R A : GroupScheme (Spec (CommRingCat.of k))}
    {l : L ⟶ P} {r : R ⟶ P}
    (hl : IsRationalLeviSubgroup l) (hr : IsSolvableRadical r)
    (aR : A ⟶ R) (aL : A ⟶ L) (h : aL ≫ l = aR ≫ r) :
    IsCentral aL := by
  obtain ⟨q, hlq, hc⟩ := rationalLeviRadicalCentrality k P L R l r hl hr
  have ha : aR ≫ (r ≫ q) = aL := by
    rw [← Category.assoc, ← h, Category.assoc, hlq, Category.comp_id]
  simpa only [ha] using hc.comp aR

end Langlands.GroupScheme
