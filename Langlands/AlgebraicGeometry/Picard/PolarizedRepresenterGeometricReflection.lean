import Langlands.AlgebraicGeometry.Picard.PresheafLineBundleBaseChange
import Langlands.AlgebraicGeometry.Picard.PresheafLineBundleAmple
import Langlands.AlgebraicGeometry.Picard.FlatBaseChangeAmpleReflection
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent

/-! # Geometric reflection for a supplied global polarized representer -/

noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard

variable {S U : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}

/-- Compare the base change of a supplied global representer with any supplied
local representer of the restricted presheaf. -/
def localRepresenterComparison (p : U ⟶ S) {N : Over S} {M : Over U}
    (eN : F.RepresentableBy N) (eM : ((Over.map p).op ⋙ F).RepresentableBy M) :
    (Over.pullback p).obj N ≅ M :=
  (representableByBaseChange eN p).uniqueUpToIso eM

/-- Smoothness, properness, and ampleness of the coherent universal bundle
reflect to any supplied global representer along a flat surjective map between
affine bases. The scheme and value universes are independent. -/
theorem geometricReflection_of_representable [IsAffine S] [IsAffine U]
    (p : U ⟶ S) [Flat p] [Surjective p]
    (L : PresheafLineBundle F) {N : Over S} {M : Over U}
    (eN : F.RepresentableBy N) (eM : ((Over.map p).op ⋙ F).RepresentableBy M)
    (hM : Smooth M.hom) (hP : IsProper M.hom)
    (hL : ((L.baseChange p).universal eM).IsAmple) :
    Smooth N.hom ∧ IsProper N.hom ∧ (L.universal eN).IsAmple := by
  let : Smooth M.hom := hM
  let : IsProper M.hom := hP
  let e := localRepresenterComparison p eN eM
  let : IsIso e.hom.left := (Over.forget U).map_isIso e.hom
  have hs : Smooth (pullback.snd N.hom p) := by
    change Smooth ((Over.pullback p).obj N).hom
    rw [← Over.w e.hom]
    infer_instance
  have hp : IsProper (pullback.snd N.hom p) := by
    change IsProper ((Over.pullback p).obj N).hom
    rw [← Over.w e.hom]
    infer_instance
  let Q : MorphismProperty Scheme.{u} := @Surjective ⊓ @Flat ⊓ @QuasiCompact
  have hb : Q p :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hsq := IsPullback.of_hasPullback N.hom p
  have hsN : Smooth N.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := Q) hsq.flip hb hs
  have hpN : IsProper N.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @IsProper)
      (Q := Q) hsq.flip hb hp
  have hL' := (L.baseChange p).universal_isAmple_of eM (representableByBaseChange eN p) hL
  have hLP : ((LineBundle.pullback (pullback.fst N.hom p)).obj (L.universal eN)).IsAmple :=
    hL'.of_iso ((LineBundle.forget _).mapIso (L.universalBaseChangePullbackIso eN p).symm)
  exact ⟨hsN, hpN, LineBundle.isAmple_of_affine_flat_surjective_baseChange
    p N.hom (pullback.snd N.hom p) (pullback.fst N.hom p) hsq (L.universal eN) hLP⟩

end Langlands.AlgebraicGeometry.Picard
