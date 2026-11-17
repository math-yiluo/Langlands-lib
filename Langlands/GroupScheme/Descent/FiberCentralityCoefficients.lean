import Langlands.GroupScheme.HopfFiberCentralityResidue
import Langlands.GroupScheme.AffineHopfMorphism
import Langlands.GroupScheme.AffineCoordinatesFiniteType

/-! # Finite coefficients preserving affine residue-fibre centrality -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Topology

namespace Langlands.GroupScheme.Descent.FiberCentralityCoefficients

open HopfFiberCentrality HopfFiberCentralityResidue

variable {R : CommRingCat.{u}}

/-- Centrality on the canonical scheme-residue fibres of an actual homomorphism. -/
def centralFiberLocus {H G : GroupScheme (Spec R)} (i : H ⟶ G) : Set (Spec R) :=
  {p | IsCentral ((baseChange ((Spec R).fromSpecResidueField p)).map i)}

/-- A commuting square of group isomorphisms identifies the residue-fibre loci. -/
theorem centralFiberLocus_iso_square
    {H G H' G' : GroupScheme (Spec R)}
    (i : H ⟶ G) (j : H' ⟶ G') (eH : H ≅ H') (eG : G ≅ G')
    (w : i ≫ eG.hom = eH.hom ≫ j) :
    centralFiberLocus i = centralFiberLocus j := by
  ext p
  let F := baseChange ((Spec R).fromSpecResidueField p)
  apply isCentral_iff_of_iso_square _ _ (F.mapIso eH) (F.mapIso eG)
  change F.map i ≫ F.map eG.hom = F.map eH.hom ≫ F.map j
  simp only [← Functor.map_comp, w]

/-- The locus for an affine homomorphism is the locus for its actual coordinate
Hopf map. -/
theorem centralFiberLocus_eq_hopf
    {H G : GroupScheme (Spec R)} [IsAffine H.X.left] [IsAffine G.X.left]
    (i : H ⟶ G) :
    centralFiberLocus i = schemeFiberCentralityLocus (AffineHopfMorphism.pullback i) := by
  symm
  apply centralFiberLocus_iso_square _ _ (AffineCoordinates.hopfSpecIso H)
    (AffineCoordinates.hopfSpecIso G)
  rw [AffineHopfMorphism.pullback_map]
  simp

/-- Centrality on canonical residue fibres is preserved and reflected at the
contracted prime under any affine scalar extension. -/
theorem centralFiberLocus_baseChange
    {H G : GroupScheme (Spec R)} [IsAffine H.X.left] [IsAffine G.X.left]
    (S : Type u) [CommRing S] [Algebra R S] (i : H ⟶ G) :
    centralFiberLocus
        ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map i) =
      PrimeSpectrum.comap (algebraMap R S) ⁻¹' centralFiberLocus i := by
  let π := AffineHopfMorphism.pullback i
  let F := baseChange (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  have w : (hopfSpec R).map π.op ≫ (AffineCoordinates.hopfSpecIso G).hom =
      (AffineCoordinates.hopfSpecIso H).hom ≫ i := by
    rw [AffineHopfMorphism.pullback_map]
    simp
  have h₁ : centralFiberLocus (F.map ((hopfSpec R).map π.op)) =
      centralFiberLocus (F.map i) := by
    apply centralFiberLocus_iso_square _ _ (F.mapIso (AffineCoordinates.hopfSpecIso H))
      (F.mapIso (AffineCoordinates.hopfSpecIso G))
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    simp only [← Functor.map_comp, w]
  have h₂ : centralFiberLocus (F.map ((hopfSpec R).map π.op)) =
      schemeFiberCentralityLocus (R := CommRingCat.of S) (scalarExtensionMap S π) := by
    apply centralFiberLocus_iso_square _ _
      (HopfCoordinates.baseChangeSpecIso R S (AffineCoordinates.hopfAlgebra H))
      (HopfCoordinates.baseChangeSpecIso R S (AffineCoordinates.hopfAlgebra G))
    rw [baseChange_hopfSpec]
    simp
  rw [← h₁, h₂, schemeFiberCentralityLocus_scalarExtension, centralFiberLocus_eq_hopf]

/-- The canonical residue-fibre centrality locus of a finite-type affine
homomorphism over a noetherian ring is constructible. -/
theorem isConstructible_centralFiberLocus
    [IsNoetherianRing R]
    {H G : GroupScheme (Spec R)} [IsAffine H.X.left] [IsAffine G.X.left]
    [LocallyOfFiniteType H.X.hom] [LocallyOfFiniteType G.X.hom] (i : H ⟶ G) :
    IsConstructible (centralFiberLocus i) := by
  let : Algebra.FiniteType R (AffineCoordinates.hopfAlgebra G) :=
    AffineCoordinates.algebraFiniteType G
  let : Algebra.FiniteType R (AffineCoordinates.hopfAlgebra H) :=
    AffineCoordinates.algebraFiniteType H
  rw [centralFiberLocus_eq_hopf]
  exact isConstructible_schemeFiberCentralityLocus _

section Coefficients

variable (S : Type u) [CommRing S] [Algebra R S]
  {H G : GroupScheme (Spec R)}

/-- An actual coefficient algebra retaining canonical residue-fibre centrality. -/
structure CentralFiberCoefficientModel (i : H ⟶ G) (t : Finset S) where
  coefficients : Subalgebra R S
  finiteGeneration : coefficients.FG
  noetherian : IsNoetherianRing coefficients
  contains : (↑t : Set S) ⊆ coefficients
  centralFibres : centralFiberLocus
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R coefficients)))).map i) =
      Set.univ

/-- Finite coefficient enlargement preserves supplied centrality on every
canonical residue fibre of the actual scalar extension. -/
theorem exists_fg_subalgebra_centralFibres
    [IsNoetherianRing R] [IsAffine H.X.left] [IsAffine G.X.left]
    [LocallyOfFiniteType H.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : H ⟶ G)
    (h : centralFiberLocus
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map i) = Set.univ)
    (t : Finset S) :
    ∃ T : Subalgebra R S, T.FG ∧ (↑t : Set S) ⊆ T ∧
      centralFiberLocus
        ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R T)))).map i) = Set.univ := by
  rw [centralFiberLocus_baseChange] at h
  obtain ⟨T, hT, ht, hc⟩ :=
    Langlands.AlgebraicGeometry.FiberMapEqualityDescent.exists_fg_subalgebra_preimage_eq_univ
      (centralFiberLocus i) (isConstructible_centralFiberLocus i) h t
  exact ⟨T, hT, ht, (centralFiberLocus_baseChange T i).trans hc⟩

/-- Choose a noetherian finite coefficient algebra preserving supplied
canonical residue-fibre centrality and prescribed finite coefficients. -/
def centralFiberCoefficientModel
    [IsNoetherianRing R] [IsAffine H.X.left] [IsAffine G.X.left]
    [LocallyOfFiniteType H.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : H ⟶ G)
    (h : centralFiberLocus
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map i) = Set.univ)
    (t : Finset S) : CentralFiberCoefficientModel S i t := by
  let hT := exists_fg_subalgebra_centralFibres S i h t
  let T := Classical.choose hT
  have hfg : T.FG := (Classical.choose_spec hT).1
  exact ⟨T, hfg, isNoetherianRing_of_fg hfg,
    (Classical.choose_spec hT).2.1, (Classical.choose_spec hT).2.2⟩

end Coefficients

end Langlands.GroupScheme.Descent.FiberCentralityCoefficients
