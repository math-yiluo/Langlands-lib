import Langlands.Geometry.Analytic.ChosenAtlasLocallyConstantTransport
import Mathlib.CategoryTheory.Action.Basic

/-! # Coherent action on actual original domains and their sections -/

noncomputable section

universe u v w z t

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K} {D E : Type z}

/-- A domain together with an arbitrary actual locally constant section on it. -/
structure OriginalDomainSection (A : AffinoidAtlasPresentation.{u, v, w} K) (D : Type z) where
  domain : A.atlas.OriginalChartDomain
  value : LocallyConstant domain D

namespace OriginalDomainSection

/-- Equality compares the actual domains and the values on their common points. -/
@[ext]
theorem ext {s r : OriginalDomainSection A D} (h : s.domain = r.domain)
    (hv : ∀ (x : A.space) (hs : x ∈ s.domain) (hr : x ∈ r.domain),
      s.value ⟨x, hs⟩ = r.value ⟨x, hr⟩) : s = r := by
  cases s with
  | mk S f =>
    cases r with
    | mk T k =>
      dsimp only at h
      subst T
      congr
      ext x
      exact hv x.val x.property x.property

/-- Move the domain by the full chosen isomorphism and its section by inverse
precomposition with the actual restricted homeomorphism. -/
def transport (e : A ≅ B) (s : OriginalDomainSection A D) :
    OriginalDomainSection B D :=
  ⟨isoOriginalDomain e s.domain, (isoOriginalDomainLocallyConstantEquiv e s.domain).symm
    s.value⟩

@[simp]
theorem transport_domain (e : A ≅ B) (s : OriginalDomainSection A D) :
    (transport e s).domain = isoOriginalDomain e s.domain := rfl

@[simp]
theorem transport_section_apply (e : A ≅ B) (s : OriginalDomainSection A D)
    (x : isoOriginalDomain e s.domain) :
    (transport e s).value x =
      s.value ((isoOriginalDomainHomeomorph e s.domain).symm x) := rfl

/-- At the actual image point, transport recovers the original value. -/
@[simp]
theorem transport_section_image (e : A ≅ B) (s : OriginalDomainSection A D)
    (x : s.domain) :
    (transport e s).value (isoOriginalDomainHomeomorph e s.domain x) = s.value x :=
  congrArg s.value ((isoOriginalDomainHomeomorph e s.domain).symm_apply_apply x)

/-- Coherence holds for entire domain-section pairs, without dependent casts. -/
@[simp]
theorem transport_refl (s : OriginalDomainSection A D) :
    transport (Iso.refl A) s = s := by
  apply OriginalDomainSection.ext
  · apply SetLike.coe_injective
    exact Set.image_id _
  · intro x hs hr
    rfl

theorem transport_trans (e : A ≅ B) (f : B ≅ C) (s : OriginalDomainSection A D) :
    transport (e.trans f) s = transport f (transport e s) := by
  apply OriginalDomainSection.ext
  · apply SetLike.coe_injective
    exact Set.image_comp f.hom.baseMap e.hom.baseMap _
  · intro x hs hr
    rfl

/-- Restriction uses the original literal domain inclusion. -/
def restrict (s : OriginalDomainSection A D) (S : A.atlas.OriginalChartDomain)
    (hS : S ≤ s.domain) : OriginalDomainSection A D :=
  ⟨S, locallyConstantRestrict hS s.value⟩

@[simp]
theorem restrict_self (s : OriginalDomainSection A D) :
    restrict s s.domain le_rfl = s := by
  apply OriginalDomainSection.ext rfl
  intro x hs hr
  rfl

theorem restrict_restrict (s : OriginalDomainSection A D)
    {S T : A.atlas.OriginalChartDomain} (hT : T ≤ s.domain) (hST : S ≤ T) :
    restrict (restrict s T hT) S hST = restrict s S (hST.trans hT) := by
  apply OriginalDomainSection.ext rfl
  intro x hs hr
  rfl

/-- Moving a restricted pair equals restricting the moved pair to the actual
image subdomain, including equality of their entire sections. -/
theorem transport_restrict (e : A ≅ B) (s : OriginalDomainSection A D)
    (S : A.atlas.OriginalChartDomain) (hS : S ≤ s.domain) :
    transport e (restrict s S hS) =
      restrict (transport e s) (isoOriginalDomain e S) (isoOriginalDomain_mono e hS) := by
  apply OriginalDomainSection.ext rfl
  intro x hs hr
  rfl

/-- Coefficient change retains the actual domain and postcomposes its function. -/
def map (φ : D → E) (s : OriginalDomainSection A D) : OriginalDomainSection A E :=
  ⟨s.domain, LocallyConstant.map φ s.value⟩

@[simp]
theorem map_id (s : OriginalDomainSection A D) : map id s = s := by
  apply OriginalDomainSection.ext rfl
  intro x hs hr
  rfl

theorem map_comp {F : Type z} (φ : D → E) (ψ : E → F)
    (s : OriginalDomainSection A D) : map (ψ ∘ φ) s = map ψ (map φ s) := by
  apply OriginalDomainSection.ext rfl
  intro x hs hr
  rfl

theorem transport_map (e : A ≅ B) (φ : D → E) (s : OriginalDomainSection A D) :
    transport e (map φ s) = map φ (transport e s) := by
  apply OriginalDomainSection.ext rfl
  intro x hs hr
  rfl

theorem restrict_map (φ : D → E) (s : OriginalDomainSection A D)
    (S : A.atlas.OriginalChartDomain) (hS : S ≤ s.domain) :
    restrict (map φ s) S hS = map φ (restrict s S hS) := by
  apply OriginalDomainSection.ext rfl
  intro x hs hr
  rfl

end OriginalDomainSection

namespace ChosenAtlasSectionAction

variable {G : Type t} [Group G]
  (X : Action (AffinoidAtlasPresentation.{u, v, w} K) G)

/-- The complete function sets over all actual original domains, with their
coherent action induced by the original chosen bounded atlas action. -/
def action (D : Type z) : Action (Type (max v z)) G where
  V := OriginalDomainSection X.V D
  ρ :=
    { toFun g := TypeCat.ofHom (OriginalDomainSection.transport (X.ρAut g))
      map_one' := by
        apply ConcreteCategory.hom_ext
        intro s
        change OriginalDomainSection.transport (X.ρAut 1) s = s
        rw [map_one]
        exact OriginalDomainSection.transport_refl s
      map_mul' g h := by
        apply ConcreteCategory.hom_ext
        intro s
        change OriginalDomainSection.transport (X.ρAut (g * h)) s =
          OriginalDomainSection.transport (X.ρAut g)
            (OriginalDomainSection.transport (X.ρAut h) s)
        rw [map_mul]
        exact OriginalDomainSection.transport_trans (X.ρAut h) (X.ρAut g) s }

@[simp]
theorem action_domain (D : Type z) (g : G) (s : OriginalDomainSection X.V D) :
    (((action X D).ρ g).hom s).domain = isoOriginalDomain (X.ρAut g) s.domain := rfl

/-- The section operator is inverse precomposition by the original group action. -/
@[simp]
theorem action_section_apply (D : Type z) (g : G) (s : OriginalDomainSection X.V D)
    (x : isoOriginalDomain (X.ρAut g) s.domain) :
    (((action X D).ρ g).hom s).value x =
      s.value ((isoOriginalDomainHomeomorph (X.ρAut g) s.domain).symm x) := rfl

/-- Actual coefficient postcomposition is equivariant on all varying domains. -/
def coefficientMap (φ : D → E) : action X D ⟶ action X E where
  hom := TypeCat.ofHom (OriginalDomainSection.map φ)
  comm g := by
    apply ConcreteCategory.hom_ext
    intro s
    exact OriginalDomainSection.transport_map (X.ρAut g) φ s

end ChosenAtlasSectionAction

end Langlands.Analytic.AffinoidAtlasPresentation
