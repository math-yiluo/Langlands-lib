import Langlands.GroupScheme.HopfFiberCentrality
import Langlands.GroupScheme.CentralIsogeny.FpqcReflectionHelpers

/-! # Canonical scheme residue fibres and Hopf centrality loci -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology

namespace Langlands.GroupScheme.HopfFiberCentralityResidue

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A commuting square of group isomorphisms preserves and reflects centrality. -/
theorem isCentral_iff_of_iso_square
    {S : Scheme.{u}} {H G H' G' : GroupScheme S}
    (i : H ⟶ G) (j : H' ⟶ G') (eH : H ≅ H') (eG : G ≅ G')
    (w : i ≫ eG.hom = eH.hom ≫ j) : IsCentral i ↔ IsCentral j := by
  constructor
  · intro hi
    have h := (hi.comp_iso eG).comp eH.inv
    change IsCentral (eH.inv ≫ (i ≫ eG.hom)) at h
    rw [w, Iso.inv_hom_id_assoc] at h
    exact h
  · intro hj
    have h := (hj.comp eH.hom).comp_iso eG.symm
    change IsCentral ((eH.hom ≫ j) ≫ eG.inv) at h
    rw [← w, Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
    exact h

/-- The standard natural pullback comparison identifies the two centrality tests. -/
theorem isCentral_baseChange_comp_iff
    {S S' S'' : Scheme.{u}} (a : S' ⟶ S) (b : S'' ⟶ S')
    {H G : GroupScheme S} (i : H ⟶ G) :
    IsCentral ((baseChange (b ≫ a)).map i) ↔
      IsCentral ((baseChange b).map ((baseChange a).map i)) := by
  let E : baseChange (b ≫ a) ≅ baseChange a ⋙ baseChange b :=
    (Functor.mapGrpNatIso (Over.pullbackComp b a)) ≪≫ Functor.mapGrpCompIso
  exact isCentral_iff_of_iso_square _ _ (E.app H) (E.app G) (E.hom.naturality i)

/-- The ideal residue-field and canonical scheme-stalk residue-field pullbacks
have equivalent all-test centrality. -/
theorem isCentral_idealResidue_iff_schemeResidue
    (R : CommRingCat.{u}) {H G : GroupScheme (Spec R)} (i : H ⟶ G)
    (p : PrimeSpectrum R) :
    IsCentral ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)))).map i) ↔
    IsCentral ((baseChange ((Spec R).fromSpecResidueField p)).map i) := by
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R p,
    isCentral_baseChange_comp_iff]
  exact ⟨fun h => h.baseChange _, fun h => IsCentral.of_baseChange _ h⟩

open HopfFiberCentrality

variable {R : CommRingCat.{u}} {A C : CommHopfAlgCat.{u} R}

/-- The Hopf centrality locus is exactly the locus of central canonical
scheme-residue fibres of the actual Hopf-spectrum homomorphism. -/
theorem mem_fiberCentralityLocus_iff (π : A ⟶ C) (p : PrimeSpectrum R) :
    p ∈ fiberCentralityLocus π ↔
      IsCentral ((baseChange ((Spec R).fromSpecResidueField p)).map
        ((hopfSpec R).map π.op)) :=
  isCentral_idealResidue_iff_schemeResidue R _ p

/-- Centrality on canonical scheme-residue fibres of the actual Hopf spectrum. -/
def schemeFiberCentralityLocus (π : A ⟶ C) : Set (Spec R) :=
  {p | IsCentral ((baseChange ((Spec R).fromSpecResidueField p)).map
    ((hopfSpec R).map π.op))}

theorem schemeFiberCentralityLocus_eq (π : A ⟶ C) :
    schemeFiberCentralityLocus π = fiberCentralityLocus π := by
  ext p
  exact (mem_fiberCentralityLocus_iff π p).symm

/-- Canonical scheme-residue centrality has the full arbitrary scalar-extension
inverse-image identity. -/
theorem schemeFiberCentralityLocus_scalarExtension
    (S : Type u) [CommRing S] [Algebra R S] (π : A ⟶ C) :
    schemeFiberCentralityLocus (R := CommRingCat.of S) (scalarExtensionMap S π) =
      PrimeSpectrum.comap (algebraMap R S) ⁻¹' schemeFiberCentralityLocus π := by
  simp only [schemeFiberCentralityLocus_eq]
  exact fiberCentralityLocus_scalarExtension S π

/-- The actual canonical residue-fibre centrality locus is constructible under
noetherian and finite-type hypotheses. -/
theorem isConstructible_schemeFiberCentralityLocus
    [IsNoetherianRing R] [Algebra.FiniteType R A] [Algebra.FiniteType R C]
    (π : A ⟶ C) : IsConstructible (schemeFiberCentralityLocus π) := by
  rw [schemeFiberCentralityLocus_eq]
  exact isConstructible_fiberCentralityLocus π

section Coefficients

variable (S : Type u) [CommRing S] [Algebra R S]

/-- An actual noetherian coefficient algebra retaining specified coefficients
and centrality on every canonical scheme-residue fibre. -/
structure SchemeFiberCentralityCoefficientModel (π : A ⟶ C) (t : Finset S) where
  coefficients : Subalgebra R S
  finiteGeneration : coefficients.FG
  noetherian : IsNoetherianRing coefficients
  contains : (↑t : Set S) ⊆ coefficients
  centralFibres : ∀ p : Spec (CommRingCat.of coefficients),
    IsCentral ((baseChange ((Spec (CommRingCat.of coefficients)).fromSpecResidueField p)).map
      ((hopfSpec (CommRingCat.of coefficients)).map
        (scalarExtensionMap coefficients π).op))

/-- Choose a noetherian coefficient algebra retaining centrality on all
canonical scheme-residue fibres of the actual scalar-extension map. -/
def schemeFiberCentralityCoefficientModel
    [IsNoetherianRing R] [Algebra.FiniteType R A] [Algebra.FiniteType R C]
    (π : A ⟶ C)
    (H : schemeFiberCentralityLocus (R := CommRingCat.of S)
      (scalarExtensionMap S π) = Set.univ)
    (t : Finset S) : SchemeFiberCentralityCoefficientModel S π t := by
  rw [schemeFiberCentralityLocus_eq] at H
  let M := fiberCentralityCoefficientModel S π H t
  refine ⟨M.coefficients, M.finiteGeneration,
    isNoetherianRing_of_fg M.finiteGeneration, M.contains, ?_⟩
  intro p
  apply (mem_fiberCentralityLocus_iff _ p).mp
  rw [M.centralFibres]
  exact Set.mem_univ p

end Coefficients

end Langlands.GroupScheme.HopfFiberCentralityResidue
