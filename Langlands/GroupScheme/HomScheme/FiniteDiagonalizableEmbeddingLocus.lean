import Langlands.CommutativeAlgebra.FiniteDiagonalCoalgebraLocus
import Langlands.GroupScheme.Torus.ClosedImmersionLocus
import Langlands.GroupScheme.HomScheme.FiniteDiagonalizableHom
import Langlands.GroupScheme.Reductive.MonomorphismNoetherianReductionProof
import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # The quasi-compact open embedding locus for finite diagonalizable sources -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Langlands.CommutativeAlgebra.DiagonalCoalgebraLocus

namespace Langlands.GroupScheme.HomScheme.FiniteDiagonalizableEmbeddingLocus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

/-- Factoring a spectrum map through the complement of an ideal's zero locus
is exactly the condition that the extended ideal is the unit ideal. -/
theorem range_specMap_subset_compl_zeroLocus_iff
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) (I : Ideal R) :
    Set.range (Spec.map (CommRingCat.ofHom f)) ⊆ (PrimeSpectrum.zeroLocus (I : Set R))ᶜ ↔
      I.map f = ⊤ := by
  change Set.range (PrimeSpectrum.comap f) ⊆ _ ↔ _
  rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top]
  have he : PrimeSpectrum.zeroLocus (I.map f : Set A) =
      PrimeSpectrum.comap f ⁻¹' PrimeSpectrum.zeroLocus (I : Set R) := by
    rw [PrimeSpectrum.preimage_comap_zeroLocus]
    exact PrimeSpectrum.zeroLocus_span _
  rw [he]
  simp only [Set.range_subset_iff, Set.mem_compl_iff, Set.eq_empty_iff_forall_notMem,
    Set.mem_preimage]

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M] [Fintype M]
  {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (i : TorusClosedImmersionLocus.diagonalSource R M ⟶ G)

/-- The coordinate ideal cutting out the complement of the full embedding locus. -/
def embeddingIdeal : Ideal R :=
  surjectivityIdeal (R := R) (M := M) (B := AffineCoordinates.hopfAlgebra G)
    (TorusClosedImmersionLocus.diagonalCoordinateMap i)

/-- The open base locus over which the given diagonalizable homomorphism is closed. -/
def embeddingOpen : (Spec R).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (embeddingIdeal i : Set R))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- On spectra of arbitrary coefficient algebras, the embedding open has the
exact scheme-theoretic closed-immersion condition. -/
theorem range_subset_embeddingOpen_iff_spec
    (A : CommRingCat.{u}) (b : Spec A ⟶ Spec R) :
    Set.range b ⊆ embeddingOpen i ↔
      IsClosedImmersion ((GroupScheme.baseChange b).map i).hom.hom.left := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective b
  let : Algebra R A := f.hom.toAlgebra
  have hf : CommRingCat.ofHom (algebraMap R A) = f := rfl
  rw [← hf]
  rw [TorusClosedImmersionLocus.diagonal_closed_iff i A,
    scalarExtension_surjective_iff_surjectivityIdeal]
  exact range_specMap_subset_compl_zeroLocus_iff f.hom (embeddingIdeal i)

/-- The open embedding locus recognizes closed immersions on every test
scheme, including non-affine and disconnected ones. -/
theorem range_subset_embeddingOpen_iff {T : Scheme.{u}} (b : T ⟶ Spec R) :
    Set.range b ⊆ embeddingOpen i ↔
      IsClosedImmersion ((GroupScheme.baseChange b).map i).hom.hom.left := by
  constructor
  · intro hb
    apply ReductiveMonomorphismNoetherianReduction.isClosedImmersion_of_openCover
      ((GroupScheme.baseChange b).map i) T.affineOpenCover.openCover
    intro k
    have h := (range_subset_embeddingOpen_iff_spec i (T.affineOpenCover.X k)
      (T.affineOpenCover.f k ≫ b)).mp (by
        rintro _ ⟨x, rfl⟩
        exact hb ⟨T.affineOpenCover.f k x, by simp only [Scheme.Hom.comp_apply]⟩)
    exact (TorusClosedImmersionLocus.closed_comp_baseChange_iff b
      (T.affineOpenCover.f k) i).mp h
  · intro hb
    rintro _ ⟨t, rfl⟩
    obtain ⟨k, x, rfl⟩ := T.affineOpenCover.openCover.exists_eq t
    have h : IsClosedImmersion
        ((GroupScheme.baseChange (T.affineOpenCover.f k ≫ b)).map i).hom.hom.left :=
      (TorusClosedImmersionLocus.closed_comp_baseChange_iff b
        (T.affineOpenCover.f k) i).mpr (IsClosedSubgroup.baseChange
          (T.affineOpenCover.f k) hb)
    exact (range_subset_embeddingOpen_iff_spec i (T.affineOpenCover.X k)
      (T.affineOpenCover.f k ≫ b)).mpr h ⟨x, by simp only [Scheme.Hom.comp_apply]; rfl⟩

/-- The actual factorization property represented by the open embedding locus. -/
theorem exists_lift_embeddingOpen_iff {T : Scheme.{u}} (b : T ⟶ Spec R) :
    (∃ a : T ⟶ (embeddingOpen i).toScheme, a ≫ (embeddingOpen i).ι = b) ↔
      IsClosedImmersion ((GroupScheme.baseChange b).map i).hom.hom.left := by
  rw [← range_subset_embeddingOpen_iff]
  constructor
  · rintro ⟨a, rfl⟩ _ ⟨t, rfl⟩
    exact (a t).property
  · intro hb
    exact ⟨IsOpenImmersion.lift (embeddingOpen i).ι b (by
      simpa only [Scheme.Opens.range_ι] using hb), IsOpenImmersion.lift_fac _ _ _⟩

/-- The universal family restricted to its embedding open is a closed immersion. -/
theorem isClosedImmersion_embeddingOpen :
    IsClosedImmersion
      ((GroupScheme.baseChange (embeddingOpen i).ι).map i).hom.hom.left :=
  (range_subset_embeddingOpen_iff i (embeddingOpen i).ι).mp (by
    rw [Scheme.Opens.range_ι])

/-- For finitely presented affine ambient groups the embedding locus is
quasi-affine, since its complementary ideal is finitely generated. -/
theorem embeddingOpen_isQuasiAffine [LocallyOfFinitePresentation G.X.hom] :
    (embeddingOpen i).toScheme.IsQuasiAffine := by
  let : Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G) :=
    FiniteDiagonalizable.finitePresentation_hopfAlgebra G
  have hfg : (embeddingIdeal i).FG := surjectivityIdeal_fg _
  have hc : IsCompact (embeddingOpen i : Set (Spec R)) :=
    (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr ⟨embeddingIdeal i, hfg, rfl⟩).1
  let : CompactSpace (embeddingOpen i) := isCompact_iff_compactSpace.mp hc
  exact Scheme.IsQuasiAffine.of_isImmersion (embeddingOpen i).ι

end Langlands.GroupScheme.HomScheme.FiniteDiagonalizableEmbeddingLocus
