import Langlands.Geometry.Analytic.QuotientRelativeDomainGluing
import Mathlib.CategoryTheory.Sites.Sheaf

/-! # The actual quotient-Hom sheaf on original-chart domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation.SourceCategory

open CategoryTheory Set
open IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : SaturatedAtlasPresentation.{u, v, w} K}

/-- Every compatible family of actual quotient morphisms on any covering
sieve has an amalgamation, including sieves over proper domains. -/
theorem exists_domainSieveAmalgamation
    {S : A.presentation.atlas.OriginalChartDomain} (R : Sieve S)
    (hR : R ∈ quasinetTopology A.presentation.atlas S)
    (x : Presieve.FamilyOfElements (domainHomPresheaf A B) R.arrows)
    (hx : x.Compatible) : ∃ F, x.IsAmalgamation F := by
  let ι := Σ T : A.presentation.atlas.OriginalChartDomain, {f : T ⟶ S // R f}
  let D : ι → A.presentation.atlas.OriginalChartDomain := fun k => k.1
  let hDS : ∀ k : ι, D k ≤ S := fun k => leOfHom k.2.val
  let d : QuotientDomainMatchingFamily A B D :=
    { localMap := fun k => x k.2.val k.2.property
      overlap := fun k l => hx
        (homOfLE (inf_le_left : D k ⊓ D l ≤ D k))
        (homOfLE (inf_le_right : D k ⊓ D l ≤ D l))
        k.2.property l.2.property (Subsingleton.elim _ _) }
  have hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {S.carrier} := by
    apply AtlasTopology.LocallyRefines.mono hR ?_ Subset.rfl
    rintro U ⟨T, hTS, hRT, rfl⟩
    exact ⟨⟨T, homOfLE hTS, hRT⟩, rfl⟩
  refine ⟨d.glueRelative S hDS hD, ?_⟩
  intro T f hf
  exact d.glueRelative_restrict S hDS hD ⟨T, f, hf⟩

/-- The actual quotient-Hom presheaf satisfies existence and uniqueness of
gluing on every sieve of the original-domain quasinet topology. -/
theorem domainHomPresheaf_isSheaf (A B : SaturatedAtlasPresentation.{u, v, w} K) :
    Presieve.IsSheaf (quasinetTopology A.presentation.atlas)
      (domainHomPresheaf A B) :=
  (domainHomPresheaf_isSeparated A B).isSheaf
    (fun _ R hR x hx => exists_domainSieveAmalgamation R hR x hx)

/-- Bundle actual quotient morphisms on all original-chart domains as a
sheaf of types, with the original precomposition restrictions. -/
def domainHomSheaf (A B : SaturatedAtlasPresentation.{u, v, w} K) :
    Sheaf (quasinetTopology A.presentation.atlas) (Type (max u v w)) where
  obj := domainHomPresheaf A B
  property := (isSheaf_iff_isSheaf_of_type _ _).mpr (domainHomPresheaf_isSheaf A B)

/-- Postcomposition by every actual quotient arrow is a morphism of the
constructed domain-Hom sheaves. -/
def domainHomSheafMap (F : ofPresentation B ⟶ ofPresentation C) :
    domainHomSheaf A B ⟶ domainHomSheaf A C :=
  ⟨domainHomPresheafMap F⟩

end Langlands.Analytic.SaturatedAtlasPresentation.SourceCategory
