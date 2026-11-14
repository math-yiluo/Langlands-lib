import Langlands.GroupScheme.ZExtensionCentralSurjectionStatement
import Langlands.GroupScheme.CentralSurjection.DerivedMap
import Langlands.GroupScheme.Derived.SemisimpleProof

/-! # Ascent of simply connected derived groups along central surjections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A central surjection of connected reductive groups preserves simple
connectedness of the derived group in the direction from target to source. -/
theorem simplyConnectedDerivedAscent : SimplyConnectedDerivedAscentStatement.{u} := by
  intro k _ E G hE hG p _ hp hsc
  let : IsAffineHom E.X.hom := hE.isAffineHom
  let : Smooth E.X.hom := hE.smooth
  let : LocallyOfFiniteType E.X.hom := inferInstance
  obtain ⟨D, d, _, _, hd⟩ := derivedSubgroupRepresentability k E
  obtain ⟨D', d', hd', hD'⟩ := hsc
  have hD : IsSemisimple D := derivedSubgroupSemisimple k E D d hE hd
  have hpD : IsCentralIsogeny (hd.map hd' p) :=
    hd.isCentralIsogeny_map hd' p hE hG hp
  have : IsIso (hd.map hd' p) := hD'.central_isogeny_isIso D _ hD hpD
  exact ⟨D, d, hd, hD'.of_iso (asIso (hd.map hd' p))⟩

/-- Convenient local form of `simplyConnectedDerivedAscent`. -/
theorem HasSimplyConnectedDerivedGroup.of_centralSurjection
    {k : Type u} [Field k]
    {E G : GroupScheme (Spec (CommRingCat.of k))}
    (hE : IsConnectedReductive E) (hG : IsConnectedReductive G)
    (p : E ⟶ G) [Surjective p.hom.hom.left]
    (hp : IsCentral (kernelι p)) (hsc : HasSimplyConnectedDerivedGroup G) :
    HasSimplyConnectedDerivedGroup E :=
  simplyConnectedDerivedAscent k E G hE hG p hp hsc

end Langlands.GroupScheme
