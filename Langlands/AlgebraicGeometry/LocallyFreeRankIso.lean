import Langlands.AlgebraicGeometry.LocallyFreeRank

/-! # Transport of fixed finite local rank along actual sheaf isomorphisms -/

noncomputable section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

namespace Langlands.Scheme.Modules

variable {S : AlgebraicGeometry.Scheme.{u}} {M N : S.Modules}

/-- Move the actual local generating sections along the restricted sheaf isomorphisms. -/
def localGeneratorsDataOfIso (e : M ≅ N) (q : SheafOfModules.LocalGeneratorsData.{u} M) :
    SheafOfModules.LocalGeneratorsData.{u} N where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.generators i).ofEpi
    ((SheafOfModules.overFunctor S.ringCatSheaf (q.X i)).mapIso e).hom

/-- The transported local bases are still actual bases, with the same indexing types. -/
instance (e : M ≅ N) (q : SheafOfModules.LocalGeneratorsData.{u} M)
    [q.IsLocallyFreeData] : (localGeneratorsDataOfIso e q).IsLocallyFreeData where
  isIso i := by
    let e' := (SheafOfModules.overFunctor S.ringCatSheaf (q.X i)).mapIso e
    change IsIso ((q.generators i).ofEpi e'.hom).π
    exact (congrArg IsIso
      (SheafOfModules.GeneratingSections.ofEpi_π (q.generators i) e'.hom)).mpr
        (inferInstanceAs (IsIso ((q.generators i).π ≫ e'.hom)))

/-- Fixed finite local rank is preserved by an actual module-sheaf isomorphism. -/
lemma IsLocallyFreeOfRank.ofIso {n : ℕ} (h : IsLocallyFreeOfRank M n) (e : M ≅ N) :
    IsLocallyFreeOfRank N n := by
  obtain ⟨q, hq, hn⟩ := h
  let := hq
  exact ⟨localGeneratorsDataOfIso e q, inferInstance, hn⟩

/-- The same fixed rank holds on both sides of an actual sheaf isomorphism. -/
lemma isLocallyFreeOfRank_iff_of_iso (e : M ≅ N) (n : ℕ) :
    IsLocallyFreeOfRank M n ↔ IsLocallyFreeOfRank N n :=
  ⟨fun h => h.ofIso e, fun h => h.ofIso e.symm⟩

end Langlands.Scheme.Modules
