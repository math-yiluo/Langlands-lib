import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Torus.Lattice
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Integrality of tori over fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- A split torus over a field is integral. -/
theorem IsSplitTorus.isIntegral {k : Type u} [Field k]
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T) :
    IsIntegral T.X.left := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let e' := e ≪≫ splitTorus.laurentIso I (CommRingCat.of k)
  have : IsIntegral (splitTorus.laurentGroupScheme I (CommRingCat.of k)).X.left := by
    change IsIntegral (Spec (CommRingCat.of
      (splitTorus.LaurentAlgebra I (CommRingCat.of k))))
    infer_instance
  exact IsIntegral.of_isIso e'.inv.hom.hom.left

/-- A torus over a field is integral, even when it is not split over that field. -/
theorem IsTorus.isIntegral {k : Type u} [Field k]
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T) :
    IsIntegral T.X.left := by
  obtain ⟨K, hK, hAlgebra, hsplit⟩ := hT
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : Surjective b := ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩
  let : IsSchemeTheoreticallyDominant b := .of_isDominant _
  let p := pullback.fst T.X.hom b
  have : IsIntegral (pullback T.X.hom b) := hsplit.isIntegral
  have : IsReduced T.X.left := IsSchemeTheoreticallyDominant.isReduced p
  have : IrreducibleSpace T.X.left := p.surjective.irreducibleSpace p.continuous
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end Langlands.GroupScheme
