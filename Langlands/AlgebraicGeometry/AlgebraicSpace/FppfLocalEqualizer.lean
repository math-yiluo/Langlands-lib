import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Langlands.AlgebraicGeometry.Descent.FppfImmersionLocusDescent
import Mathlib.CategoryTheory.Sites.LocallyInjective

/-! # Immersed equalizer loci from fppf-local representatives -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {F : Presheaf S}

/-- The equalizer of two arbitrary presheaf sections as a sieve on the
underlying test scheme. -/
def sectionEqualizerSieve {T : Over S} (x y : F.obj (op T)) : Sieve T.left :=
  Sieve.overEquiv T (Presheaf.equalizerSieve (F := F) x y)

/-- Equality in an fppf sheaf is an fppf-closed condition on the test scheme. -/
theorem sectionEqualizerSieve_isClosed (hF : Presheaf.IsSheaf (fppfTopology S) F)
    {T : Over S} (x y : F.obj (op T)) :
    Scheme.fppfTopology.IsClosed (sectionEqualizerSieve x y) := by
  intro V g hg
  let V' : Over S := Over.mk (g ≫ T.hom)
  let g' : V' ⟶ T := Over.homMk g
  have hcov : (Presheaf.equalizerSieve (F := F) x y).pullback g' ∈ (fppfTopology S) V' := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_pullback]
    exact hg
  rw [sectionEqualizerSieve, Sieve.overEquiv_iff]
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp hF).isSeparated _ hcov).ext
  intro W h hh
  change F.map (h ≫ g').op x = F.map (h ≫ g').op y at hh
  simpa only [op_comp, Functor.map_comp, types_comp_apply] using hh

/-- Convert an equalizer representation over the base to its factorization
criterion on underlying schemes. -/
theorem RepresentsEqualizer.factors_iff_sectionEqualizerSieve
    {T Z : Over S} {ι : Z ⟶ T} {x y : F.obj (op T)}
    (hι : RepresentsEqualizer ι x y) {V : Scheme.{u}} (g : V ⟶ T.left) :
    (∃ k : V ⟶ Z.left, k ≫ ι.left = g) ↔ sectionEqualizerSieve x y g := by
  rw [sectionEqualizerSieve, Sieve.overEquiv_iff]
  change _ ↔ F.map (Over.homMk g : Over.mk (g ≫ T.hom) ⟶ T).op x =
    F.map (Over.homMk g : Over.mk (g ≫ T.hom) ⟶ T).op y
  rw [← hι (Over.homMk g : Over.mk (g ≫ T.hom) ⟶ T)]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨Over.homMk k (by
      change k ≫ Z.hom = g ≫ T.hom
      rw [← Over.w ι, ← Category.assoc, hk]), ?_⟩
    ext
    exact hk
  · rintro ⟨k, hk⟩
    exact ⟨k.left, congrArg Over.Hom.left hk⟩

/-- Immersed representations of the equality locus on an fppf-covering sieve
glue to an immersed representation for the original arbitrary sections. -/
theorem exists_representsEqualizer_of_fppf_local
    (hF : Presheaf.IsSheaf (fppfTopology S) F) {T : Over S}
    (x y : F.obj (op T)) (R : Sieve T) (hR : R ∈ (fppfTopology S) T)
    (h : ∀ ⦃V : Over S⦄ (g : V ⟶ T), R g →
      ∃ (Z : Over S) (ι : Z ⟶ V), IsImmersion ι.left ∧
        RepresentsEqualizer ι (F.map g.op x) (F.map g.op y)) :
    ∃ (Z : Over S) (ι : Z ⟶ T), RepresentsEqualizer ι x y ∧ IsImmersion ι.left := by
  let E := sectionEqualizerSieve x y
  obtain ⟨Z, ι, hι, hrep⟩ := fppfImmersionLocusDescent T.left E
    (sectionEqualizerSieve_isClosed hF x y) (Sieve.overEquiv T R)
    ((GrothendieckTopology.mem_over_iff _ _).mp hR) (by
      intro V g hg
      let V' : Over S := Over.mk (g ≫ T.hom)
      let g' : V' ⟶ T := Over.homMk g
      obtain ⟨Z, ι, hι, hrep⟩ := h g' ((Sieve.overEquiv_iff R g).mp hg)
      refine ⟨Z.left, ι.left, hι, fun W k ↦ ?_⟩
      rw [hrep.factors_iff_sectionEqualizerSieve k]
      have heq : (Presheaf.equalizerSieve (F := F) x y).pullback g' =
          Presheaf.equalizerSieve (F := F) (F.map g'.op x) (F.map g'.op y) := by
        ext A j
        change F.map (j ≫ g').op x = F.map (j ≫ g').op y ↔
          F.map j.op (F.map g'.op x) = F.map j.op (F.map g'.op y)
        simp only [op_comp, Functor.map_comp, types_comp_apply]
      change (Sieve.overEquiv V'
        (Presheaf.equalizerSieve (F := F) (F.map g'.op x) (F.map g'.op y))) k ↔
        ((Sieve.overEquiv T (Presheaf.equalizerSieve (F := F) x y)).pullback g) k
      rw [← heq, Sieve.overEquiv_pullback]
      rfl)
  refine ⟨Over.mk (ι ≫ T.hom), Over.homMk ι, fun V g ↦ ?_, hι⟩
  change _ ↔ (Presheaf.equalizerSieve (F := F) x y) g
  have he : E g.left ↔ (Presheaf.equalizerSieve (F := F) x y) g := by
    change Sieve.overEquiv T (Presheaf.equalizerSieve (F := F) x y) g.left ↔ _
    rw [← Sieve.overEquiv_symm_iff]
    simp only [OrderIso.symm_apply_apply]
  rw [← he, ← hrep g.left]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k.left, congrArg Over.Hom.left hk⟩
  · rintro ⟨k, hk⟩
    refine ⟨Over.homMk k (by
      change k ≫ (ι ≫ T.hom) = V.hom
      rw [← Category.assoc, hk, Over.w g]), ?_⟩
    ext
    exact hk

end Langlands.AlgebraicGeometry.AlgebraicSpace
