import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAutomorphism
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseTransport

/-! # Conjugating the section actions of moved full domains -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism

open CategoryTheory
open scoped Pointwise

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}

/-- Retain both specified bounded maps of an actual automorphism. -/
def boundedEquiv (g : Aut A) : BoundedAlgEquiv K A A :=
  BoundedAlgEquiv.ofHomInv g.hom g.inv
    (fun a => congrArg (fun f : BoundedAlgHom K A A => f a) g.hom_inv_id)
    (fun a => congrArg (fun f : BoundedAlgHom K A A => f a) g.inv_hom_id)

@[simp] theorem boundedEquiv_hom (g : Aut A) :
    (boundedEquiv g).toBoundedAlgHom = g.hom := by ext a; rfl

@[simp] theorem boundedEquiv_symm_hom (g : Aut A) :
    (boundedEquiv g).symm.toBoundedAlgHom = g.inv := by ext a; rfl

variable [CompleteSpace K]

/-- Move a full represented domain by changing its base map. Its actual
section algebra and quotient norm are retained exactly. -/
def movedDomain (U : Domain K A) (g : Aut A) : Domain K A :=
  U.transportBase (boundedEquiv g)

@[simp] theorem movedDomain_algebra (U : Domain K A) (g : Aut A) :
    (movedDomain U g).algebra = U.algebra := rfl

@[simp] theorem movedDomain_baseMap (U : Domain K A) (g : Aut A) :
    (movedDomain U g).baseMap = U.baseMap.comp g.inv := by
  change U.baseMap.comp (boundedEquiv g).symm.toBoundedAlgHom = _
  rw [boundedEquiv_symm_hom]

theorem mem_movedDomain_locus (U : Domain K A) (g : Aut A)
    (x : BanachSpectrum A) :
    x ∈ (movedDomain U g).locus ↔ g⁻¹ • x ∈ U.locus := Iff.rfl

/-- The transported represented locus is exactly the image under the
given automorphism's inverse-comap point action. -/
theorem movedDomain_locus (U : Domain K A) (g : Aut A) :
    (movedDomain U g).locus =
      (fun x : BanachSpectrum A => g • x) '' U.locus := by
  ext x
  rw [mem_movedDomain_locus]
  constructor
  · intro hx
    exact ⟨g⁻¹ • x, hx, smul_inv_smul g x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [inv_smul_smul] using hy

/-- Stabilizers of moved loci are the conjugate stabilizers, without
requiring equality of chosen domain presentations. -/
theorem conjugate_mem_locusStabilizer_iff (U : Domain K A) (g h : Aut A) :
    g * h * g⁻¹ ∈ locusStabilizer (movedDomain U g) ↔
      h ∈ locusStabilizer U := by
  change (g * h * g⁻¹) • (movedDomain U g).locus = (movedDomain U g).locus ↔
    h • U.locus = U.locus
  rw [movedDomain_locus]
  change (g * h * g⁻¹) • (g • U.locus) = g • U.locus ↔
    h • U.locus = U.locus
  constructor
  · intro heq
    have heq' := congrArg (fun S : Set (BanachSpectrum A) => g⁻¹ • S) heq
    simpa only [mul_smul, inv_smul_smul] using heq'
  · intro heq
    simp only [mul_smul, inv_smul_smul, heq]

/-- The moved section map, explicitly typed on the retained original algebra. -/
def movedSectionMap (U : Domain K A) (g : Aut A)
    (h : locusStabilizer (movedDomain U g)) :
    BoundedAlgHom K U.algebra U.algebra :=
  stabilizerSectionMap (movedDomain U g) h

/-- The moved section automorphism, on the same retained original algebra. -/
def movedSectionAut (U : Domain K A) (g : Aut A)
    (h : locusStabilizer (movedDomain U g)) : Aut U.algebra :=
  stabilizerSectionAut (movedDomain U g) h

/-- The moved-domain section operator for the conjugate base operator has
the original untwisted base equation on the retained section algebra. -/
theorem conjugateSectionMap_comp_baseMap (U : Domain K A) (g h : Aut A)
    (hm : g * h * g⁻¹ ∈ locusStabilizer (movedDomain U g)) :
    (movedSectionMap U g ⟨g * h * g⁻¹, hm⟩).comp U.baseMap =
      U.baseMap.comp h.hom := by
  apply BoundedAlgHom.ext
  intro a
  have hinv (b : A) : g.inv.toAlgHom (g.hom.toAlgHom b) = b :=
    congrArg (fun f : BoundedAlgHom K A A => f b) g.hom_inv_id
  have heq := congrArg (fun f : BoundedAlgHom K A U.algebra =>
    f (g.hom.toAlgHom a))
    (stabilizerSectionMap_comp_baseMap (movedDomain U g) ⟨g * h * g⁻¹, hm⟩)
  change stabilizerSectionMap (movedDomain U g) ⟨g * h * g⁻¹, hm⟩
      (U.baseMap (g.inv.toAlgHom (g.hom.toAlgHom a))) =
    U.baseMap (g.inv.toAlgHom (g.hom.toAlgHom
      (h.hom.toAlgHom (g.inv.toAlgHom (g.hom.toAlgHom a))))) at heq
  simp only [hinv] at heq
  change movedSectionMap U g ⟨g * h * g⁻¹, hm⟩ (U.baseMap a) =
    U.baseMap (h.hom.toAlgHom a)
  exact heq

/-- Conjugating on the base and moving the domain leaves the full bounded
section operator unchanged on its retained quotient algebra. -/
theorem stabilizerSectionMap_conjugate (U : Domain K A) (g h : Aut A)
    (hh : h ∈ locusStabilizer U)
    (hm : g * h * g⁻¹ ∈ locusStabilizer (movedDomain U g)) :
    movedSectionMap U g ⟨g * h * g⁻¹, hm⟩ =
      stabilizerSectionMap U ⟨h, hh⟩ := by
  apply boundedHom_ext U
  rw [conjugateSectionMap_comp_baseMap, stabilizerSectionMap_comp_baseMap]

/-- The same comparison holds for the complete bounded automorphisms,
including the constructed inverse maps. -/
theorem stabilizerSectionAut_conjugate (U : Domain K A) (g h : Aut A)
    (hh : h ∈ locusStabilizer U)
    (hm : g * h * g⁻¹ ∈ locusStabilizer (movedDomain U g)) :
    movedSectionAut U g ⟨g * h * g⁻¹, hm⟩ =
      stabilizerSectionAut U ⟨h, hh⟩ := by
  apply CategoryTheory.Iso.ext
  exact stabilizerSectionMap_conjugate U g h hh hm

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism
