import Langlands.GroupScheme.SimplyConnected.Basic

/-! # A recovered cover of a simply connected target is an isomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {G D : GroupScheme (Spec (CommRingCat.of k))}
variable {C : GroupScheme (Spec (CommRingCat.of K))}

namespace IsSimplyConnected

/-- A central arrow over a simply connected target, recovered after base change
through an actual source isomorphism, makes the recovered arrow an isomorphism. -/
def isoOfCoverRecovery (hG : IsSimplyConnected G) (a : D ⟶ G)
    (hD : IsSemisimple D) (ha : IsCentralIsogeny a)
    (π : C ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)
    (j : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj D ≅ C)
    (hrec : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map a =
      j.hom ≫ π) :
    C ≅ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G := by
  have : IsIso a := hG.central_isogeny_isIso D a hD ha
  have : IsIso (j.hom ≫ π) := by
    rw [← hrec]
    infer_instance
  have : IsIso π := IsIso.of_isIso_comp_left j.hom π
  exact asIso π

/-- The constructed isomorphism has the supplied covering arrow as its hom. -/
@[simp]
theorem isoOfCoverRecovery_hom (hG : IsSimplyConnected G) (a : D ⟶ G)
    (hD : IsSemisimple D) (ha : IsCentralIsogeny a)
    (π : C ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)
    (j : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj D ≅ C)
    (hrec : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map a =
      j.hom ≫ π) :
    (hG.isoOfCoverRecovery a hD ha π j hrec).hom = π := rfl

/-- Simple connectedness of the recovered cover source transfers to the
actual base change of the original simply connected target. -/
theorem fieldExtension_of_coverRecovery (hG : IsSimplyConnected G) (a : D ⟶ G)
    (hD : IsSemisimple D) (ha : IsCentralIsogeny a)
    (π : C ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)
    (j : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj D ≅ C)
    (hrec : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map a =
      j.hom ≫ π) (hC : IsSimplyConnected C) :
    IsSimplyConnected
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) :=
  hC.of_iso (hG.isoOfCoverRecovery a hD ha π j hrec).symm

end IsSimplyConnected

end Langlands.GroupScheme
