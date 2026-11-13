import Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealResidueProductIso
import Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCoordinateSquare

/-! # Common residue coordinates and naturality for elementary Artinian ideals -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology

open StructureKernelModule Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Deformation

section Basis

variable {R S : Type u} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [IsArtinianRing R] [IsArtinianRing S]
  [Algebra R S]
  [hs : Fact (Function.Surjective (algebraMap R S))]
  [he : Fact (maximalIdeal R * RingHom.ker (algebraMap R S) = ⊥)]

local instance : Module (ResidueField S) (RingHom.ker (algebraMap R S)) :=
  OriginalResidueProduct.kernelResidueModule (R := R) (S := S)

variable {ι : Type u} [Finite ι]
  (b : Module.Basis ι (ResidueField S) (RingHom.ker (algebraMap R S)))

/-- Orient the actual ideal comparison toward its residue-product coordinates. -/
def idealResidueIso (X : Over (Spec (CommRingCat.of R))) [Flat X.hom] :
    ideal (algebraMap R S) X ≅ ∏ᶜ fun _ : ι => residueModule (algebraMap R S) X :=
  (OriginalResidueProduct.residueProductIdealIso (S := S) X b).symm

/-- The same kernel basis gives the prescribed square for every compatible ideal map. -/
theorem idealResidueIso_square
    (X Y : Over (Spec (CommRingCat.of R))) [Flat X.hom] [Flat Y.hom]
    (f : Y ⟶ X)
    (k : ideal (algebraMap R S) X ⟶
      (Scheme.Modules.pushforward f.left).obj (ideal (algebraMap R S) Y))
    (hk : Compatible (algebraMap R S) f k) (j : ι) :
    k ≫ (Scheme.Modules.pushforward f.left).map
        ((idealResidueIso b Y).hom ≫
          Pi.π (fun _ : ι => residueModule (algebraMap R S) Y) j) =
      (idealResidueIso b X).hom ≫
        Pi.π (fun _ : ι => residueModule (algebraMap R S) X) j ≫
          residueCoefficient (algebraMap R S) f := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  apply coordinate_square_of_compatible (algebraMap R S) ι
    (idealResidueIso b X) (idealResidueIso b Y) f ?_ k hk j
  apply idealCoordinateCoefficient_compatible (algebraMap R S) ι
    (idealResidueIso b X) (idealResidueIso b Y) (fun j => (b j).val)
  · intro U hU r s hs
    exact OriginalResidueProduct.productToIdeal_app_lift_affine (S := S) X b U hU r s hs
  · intro U r s hs
    exact OriginalResidueProduct.productToIdeal_app_lift (S := S) Y b U r s hs
  · intro U hU
    exact residueι_app_surjective (algebraMap R S) hs.out U hU

end Basis

/-- One finite coordinate system works for all flat schemes and all compatible maps. -/
theorem exists_idealResidueProductIso
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsArtinianRing R] [IsArtinianRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ)
    (hker : maximalIdeal R * RingHom.ker φ = ⊥) :
    ∃ (ι : Type u) (_ : Finite ι)
      (e : ∀ (X : Over (Spec (CommRingCat.of R))) [Flat X.hom],
        ideal φ X ≅ ∏ᶜ fun _ : ι => residueModule φ X),
      ∀ (X Y : Over (Spec (CommRingCat.of R))) [Flat X.hom] [Flat Y.hom]
        (f : Y ⟶ X)
        (k : ideal φ X ⟶ (Scheme.Modules.pushforward f.left).obj (ideal φ Y)),
        Compatible φ f k → ∀ j : ι,
          k ≫ (Scheme.Modules.pushforward f.left).map
              ((e Y).hom ≫ Pi.π (fun _ : ι => residueModule φ Y) j) =
            (e X).hom ≫ Pi.π (fun _ : ι => residueModule φ X) j ≫
              residueCoefficient φ f := by
  let : Algebra R S := φ.toAlgebra
  let : Fact (Function.Surjective (algebraMap R S)) := ⟨hφ⟩
  let : Fact (maximalIdeal R * RingHom.ker (algebraMap R S) = ⊥) := ⟨hker⟩
  let : Module (ResidueField S) (RingHom.ker (algebraMap R S)) :=
    OriginalResidueProduct.kernelResidueModule (R := R) (S := S)
  let : FiniteDimensional (ResidueField S) (RingHom.ker (algebraMap R S)) :=
    ArtinianTest.ElementaryKernel.finiteDimensional
      (ArtinianSurjectionTests.arrow (R := R) (S := S) hφ)
      (ArtinianSurjectionTests.arrow_isElementary hφ hker)
  let ι := Module.Free.ChooseBasisIndex (ResidueField S) (RingHom.ker (algebraMap R S))
  let b := Module.Free.chooseBasis (ResidueField S) (RingHom.ker (algebraMap R S))
  refine ⟨ι, inferInstance, fun X _ => idealResidueIso b X, ?_⟩
  intro X Y _ _ f k hk j
  exact idealResidueIso_square b X Y f k hk j

end Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology
