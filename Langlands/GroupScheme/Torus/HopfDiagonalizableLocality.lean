import Langlands.GroupScheme.HopfBaseChange
import Langlands.GroupScheme.Torus.DiagonalizableHopf
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Diagonalizable Hopf models on principal neighborhoods -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.HopfCoordinates

/-- A Hopf-algebra model gives an actual diagonalizable group-scheme model. -/
def diagonalizableIsoOfBialgEquiv (R : CommRingCat.{u}) (A : CommHopfAlgCat.{u} R)
    {M : Type u} [AddCommGroup M] (e : A ≃ₐc[R] AddMonoidAlgebra R M) :
    (hopfSpec R).obj (op A) ≅ RelativeMultiplicativeType.diagonalizable (Spec R) M :=
  (hopfSpec R).mapIso
    (((CommHopfAlgCat.ofIsoSelf A).symm ≪≫ CommHopfAlgCat.isoMk e).symm.op) ≪≫
      Diagonalizable.hopfSpecIso R M ≪≫
      (Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec R)) M).symm

/-- Finite generation of a Hopf model's characters gives diagonalizability. -/
theorem isDiagonalizable_of_bialgEquiv (R : CommRingCat.{u}) (A : CommHopfAlgCat.{u} R)
    {M : Type u} [AddCommGroup M] [AddGroup.FG M]
    (e : A ≃ₐc[R] AddMonoidAlgebra R M) :
    RelativeMultiplicativeType.IsDiagonalizable ((hopfSpec R).obj (op A)) :=
  ⟨M, inferInstance, inferInstance, ⟨diagonalizableIsoOfBialgEquiv R A e⟩⟩

/-- Diagonalizable models on principal neighborhoods of all primes give
an fppf splitting cover of the actual Hopf spectrum. -/
theorem isMultiplicativeType_of_forall_exists_away
    (R : CommRingCat.{u}) (A : CommHopfAlgCat.{u} R)
    (h : ∀ p : PrimeSpectrum R, ∃ f : R, f ∉ p.asIdeal ∧
      RelativeMultiplicativeType.IsDiagonalizable
        ((hopfSpec (CommRingCat.of (Localization.Away f))).obj
          (op (scalarExtension R (Localization.Away f) A)))) :
    RelativeMultiplicativeType.IsMultiplicativeType ((hopfSpec R).obj (op A)) := by
  choose f hf hdiag using h
  let b (p : PrimeSpectrum R) : Spec (CommRingCat.of (Localization.Away (f p))) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f p))))
  have hopen (p : PrimeSpectrum R) : IsOpenImmersion (b p) :=
    IsOpenImmersion.of_isLocalization (f p)
  let 𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) (Spec R) :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation)
      (PrimeSpectrum R) (fun p => Spec (CommRingCat.of (Localization.Away (f p)))) b
      (fun p => by
        refine ⟨p, ?_⟩
        change p ∈ Set.range (PrimeSpectrum.comap
          (algebraMap R (Localization.Away (f p))))
        rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (f p)) (f p)]
        exact hf p)
      (fun p => by
        let : IsOpenImmersion (b p) := hopen p
        exact ⟨inferInstance, inferInstance⟩)
  refine ⟨𝒰, fun p => ?_⟩
  exact RelativeMultiplicativeType.IsDiagonalizable.of_iso
    (baseChangeSpecIso R (Localization.Away (f p)) A) (hdiag p)

end Langlands.GroupScheme.HopfCoordinates
