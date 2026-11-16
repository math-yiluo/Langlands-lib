import Langlands.AlgebraicGeometry.Picard.PresheafLineBundleComparison
import Langlands.AlgebraicGeometry.Picard.AmpleFiniteAffineOpen
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof

/-! # Ampleness of universal line bundles is independent of the representer -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.PresheafLineBundle

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}
    (L : PresheafLineBundle F)

/-- A coherent presheaf line bundle is ample if it has an ample universal
bundle on a representing scheme. -/
def IsAmple : Prop :=
  ∃ (M : Over S) (e : F.RepresentableBy M), (L.universal e).IsAmple

/-- An ample universal bundle on one supplied representer is ample on every
supplied representer of the same presheaf. -/
theorem universal_isAmple_of {M N : Over S} (e : F.RepresentableBy M)
    (d : F.RepresentableBy N) (hL : (L.universal e).IsAmple) :
    (L.universal d).IsAmple := by
  have : IsIso (d.uniqueUpToIso e).hom.left :=
    (Over.forget S).map_isIso (d.uniqueUpToIso e).hom
  exact (hL.pullback_of_isAffineHom (d.uniqueUpToIso e).hom.left).of_iso
    ((LineBundle.forget _).mapIso (L.universalCompareIso d e))

/-- Ampleness of a coherent line bundle's universal family does not depend on
the supplied representing scheme. -/
theorem universal_isAmple_iff {M N : Over S} (e : F.RepresentableBy M)
    (d : F.RepresentableBy N) :
    (L.universal e).IsAmple ↔ (L.universal d).IsAmple :=
  ⟨L.universal_isAmple_of e d, L.universal_isAmple_of d e⟩

/-- Intrinsic ampleness is equivalent to ampleness of the universal bundle
on any supplied representing scheme. -/
theorem isAmple_iff_universal {M : Over S} (e : F.RepresentableBy M) :
    L.IsAmple ↔ (L.universal e).IsAmple := by
  constructor
  · rintro ⟨N, d, hL⟩
    exact L.universal_isAmple_of d e hL
  · intro hL
    exact ⟨M, e, hL⟩

/-- A presheaf isomorphism and an arbitrary change of supplied representer
preserve ampleness of the universal line bundle. -/
theorem reindex_universal_isAmple_iff {G : (Over S)ᵒᵖ ⥤ Type v}
    (φ : G ≅ F) {M N : Over S} (e : G.RepresentableBy M)
    (d : F.RepresentableBy N) :
    ((L.reindex φ.hom).universal e).IsAmple ↔ (L.universal d).IsAmple := by
  rw [L.universal_reindex_ofIso e φ]
  exact L.universal_isAmple_iff (e.ofIso φ) d

/-- Reindexing along a presheaf isomorphism preserves intrinsic ampleness,
including the existence of an ample representing scheme. -/
theorem reindex_isAmple_iff {G : (Over S)ᵒᵖ ⥤ Type v} (φ : G ≅ F) :
    (L.reindex φ.hom).IsAmple ↔ L.IsAmple := by
  constructor
  · rintro ⟨M, e, hL⟩
    exact ⟨M, e.ofIso φ,
      (L.reindex_universal_isAmple_iff φ e (e.ofIso φ)).mp hL⟩
  · rintro ⟨M, e, hL⟩
    exact ⟨M, e.ofIso φ.symm,
      (L.reindex_universal_isAmple_iff φ (e.ofIso φ.symm) e).mpr hL⟩

end Langlands.AlgebraicGeometry.Picard.PresheafLineBundle
