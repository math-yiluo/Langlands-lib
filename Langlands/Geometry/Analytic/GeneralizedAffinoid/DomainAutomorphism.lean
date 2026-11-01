import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.NormContinuousAction
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.GroupTheory.GroupAction.Defs

/-! # Bounded section actions on full represented affinoid domains -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism

open CategoryTheory
open scoped Pointwise

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

/-- The subgroup preserving the represented locus setwise. -/
def locusStabilizer (U : Domain K A) : Subgroup (Aut A) :=
  MulAction.stabilizer (Aut A) U.locus

@[simp] theorem mem_locusStabilizer (U : Domain K A) (g : Aut A) :
    g ∈ locusStabilizer U ↔
      (fun x : BanachSpectrum A => g • x) '' U.locus = U.locus := Iff.rfl

theorem smul_mem_locus (U : Domain K A) (g : locusStabilizer U)
    {x : BanachSpectrum A} (hx : x ∈ U.locus) :
    (g : Aut A) • x ∈ U.locus := by
  rw [← (mem_locusStabilizer U g).1 g.property]
  exact Set.mem_image_of_mem _ hx

/-- Composing an arbitrary bounded map with the domain structural map
still has spectrum image in the represented locus. -/
theorem hasImageIn_comp_baseMap (U : Domain K A)
    {R : PresentedAffinoidAlgebra K} (f : BoundedAlgHom K U.algebra R) :
    HasImageIn K (f.comp U.baseMap) U.locus := by
  intro x
  have hx := U.represents.hasImageIn
    (BanachSpectrum.comap f.toBoundedRingHom x)
  convert hx using 1
  apply BanachSpectrum.ext
  intro a
  rfl

/-- Full-map uniqueness follows from the representation property even when
the common structural composite is a nonidentity base map. -/
theorem boundedHom_ext (U : Domain K A) {R : PresentedAffinoidAlgebra K}
    {f h : BoundedAlgHom K U.algebra R}
    (heq : f.comp U.baseMap = h.comp U.baseMap) : f = h :=
  (U.represents.2.2 R (h.comp U.baseMap)
    (hasImageIn_comp_baseMap U h)).unique heq rfl

/-- A stabilizing forward base map has image in the domain: its comap is
the inverse stabilizer acting on the structural spectrum map. -/
theorem twistedBase_hasImageIn (U : Domain K A) (g : locusStabilizer U) :
    HasImageIn K (U.baseMap.comp (g : Aut A).hom) U.locus := by
  intro x
  have hx := smul_mem_locus U g⁻¹ (U.represents.hasImageIn x)
  convert hx using 1
  apply BanachSpectrum.ext
  intro a
  rfl

/-- The actual bounded section map is constructed by unique factorization
against the domain's own positive-polyradius affinoid algebra. -/
def stabilizerSectionMap (U : Domain K A) (g : locusStabilizer U) :
    BoundedAlgHom K U.algebra U.algebra :=
  (U.represents.2.2 U.algebra (U.baseMap.comp (g : Aut A).hom)
    (twistedBase_hasImageIn U g)).choose

@[simp] theorem stabilizerSectionMap_comp_baseMap
    (U : Domain K A) (g : locusStabilizer U) :
    (stabilizerSectionMap U g).comp U.baseMap =
      U.baseMap.comp (g : Aut A).hom :=
  (U.represents.2.2 U.algebra (U.baseMap.comp (g : Aut A).hom)
    (twistedBase_hasImageIn U g)).choose_spec.1

@[simp] theorem stabilizerSectionMap_one (U : Domain K A) :
    stabilizerSectionMap U 1 = BoundedAlgHom.id K U.algebra := by
  apply boundedHom_ext U
  rw [stabilizerSectionMap_comp_baseMap]
  rfl

/-- The right factor is applied first on the section algebra. -/
theorem stabilizerSectionMap_mul (U : Domain K A) (g h : locusStabilizer U) :
    stabilizerSectionMap U (g * h) =
      (stabilizerSectionMap U g).comp (stabilizerSectionMap U h) := by
  apply boundedHom_ext U
  rw [stabilizerSectionMap_comp_baseMap, BoundedAlgHom.comp_assoc,
    stabilizerSectionMap_comp_baseMap, ← BoundedAlgHom.comp_assoc,
    stabilizerSectionMap_comp_baseMap]
  rfl

/-- Both bounded inverse maps are constructed from the stabilizer and its
inverse; the full unique-factorization property proves their inverse laws. -/
def stabilizerSectionAut (U : Domain K A) (g : locusStabilizer U) :
    Aut U.algebra where
  hom := stabilizerSectionMap U g
  inv := stabilizerSectionMap U g⁻¹
  hom_inv_id := by
    change (stabilizerSectionMap U g⁻¹).comp (stabilizerSectionMap U g) = _
    rw [← stabilizerSectionMap_mul, inv_mul_cancel, stabilizerSectionMap_one]
    rfl
  inv_hom_id := by
    change (stabilizerSectionMap U g).comp (stabilizerSectionMap U g⁻¹) = _
    rw [← stabilizerSectionMap_mul, mul_inv_cancel, stabilizerSectionMap_one]
    rfl

/-- The locus stabilizer acts on the fixed actual domain algebra. -/
def stabilizerSectionAction (U : Domain K A) :
    locusStabilizer U →* Aut U.algebra where
  toFun := stabilizerSectionAut U
  map_one' := by
    apply CategoryTheory.Iso.ext
    exact stabilizerSectionMap_one U
  map_mul' g h := by
    apply CategoryTheory.Iso.ext
    exact stabilizerSectionMap_mul U g h

@[simp] theorem stabilizerSectionAction_baseMap
    (U : Domain K A) (g : locusStabilizer U) (a : A) :
    (stabilizerSectionAction U g).hom.toAlgHom (U.baseMap a) =
      U.baseMap ((g : Aut A).hom.toAlgHom a) :=
  congrArg (fun f : BoundedAlgHom K A U.algebra => f a)
    (stabilizerSectionMap_comp_baseMap U g)

/-- Actual restrictions commute with the constructed section operators
whenever the same base automorphism preserves both loci. -/
theorem stabilizerSectionMap_restriction {U V : Domain K A} (f : U ⟶ V)
    (g : Aut A) (hU : g ∈ locusStabilizer U) (hV : g ∈ locusStabilizer V) :
    (stabilizerSectionMap U ⟨g, hU⟩).comp f.restriction =
      f.restriction.comp (stabilizerSectionMap V ⟨g, hV⟩) := by
  apply boundedHom_ext V
  rw [BoundedAlgHom.comp_assoc, f.comp_baseMap,
    stabilizerSectionMap_comp_baseMap, BoundedAlgHom.comp_assoc,
    stabilizerSectionMap_comp_baseMap, ← BoundedAlgHom.comp_assoc, f.comp_baseMap]

/-- The structural spectrum map intertwines the actual inverse-comap
action on sections with the given action on the base spectrum. -/
theorem stabilizerSectionAction_spectrumMap (U : Domain K A)
    (g : locusStabilizer U) (x : BanachSpectrum U.algebra) :
    U.spectrumMap ((stabilizerSectionAction U g) • x) =
      (g : Aut A) • U.spectrumMap x := by
  apply BanachSpectrum.ext
  intro a
  exact congrArg (fun b : U.algebra => x b)
    (stabilizerSectionAction_baseMap U g⁻¹ a)

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism
