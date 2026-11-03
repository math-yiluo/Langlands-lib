import Langlands.GroupScheme.Rational.MinimalParabolicStatement
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Minimal rational parabolics inside rational parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A rational parabolic contains a minimal rational parabolic. The proof uses
the ascending chain condition on ideals of the affine coordinate ring. -/
theorem parabolicContainsMinimalStatement : ParabolicContainsMinimalStatement.{u} := by
  intro k _ G hG P j hj
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  have : IsLocallyNoetherian G.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  let U : G.X.left.affineOpens := ⟨⊤, isAffineOpen_top G.X.left⟩
  have : IsNoetherianRing Γ(G.X.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian U
  let ideals : Set (Ideal Γ(G.X.left, ⊤)) :=
    { I | ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (i : Q ⟶ G),
        IsParabolicSubgroup i ∧
        SubgroupFunctor.range i ≤ SubgroupFunctor.range j ∧
        i.hom.hom.left.ker.ideal U = I }
  have hne : ideals.Nonempty :=
    ⟨j.hom.hom.left.ker.ideal U, P, j, hj, le_rfl, rfl⟩
  obtain ⟨I, hI, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr
      (inferInstance : IsNoetherian Γ(G.X.left, ⊤) Γ(G.X.left, ⊤)) ideals hne
  obtain ⟨Q, i, hi, hQi, rfl⟩ := hI
  refine ⟨Q, i, ⟨hi, ?_⟩, hQi⟩
  intro Q' i' hi' hle
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsClosedImmersion i'.hom.hom.left := hi'.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  let f := SubgroupFunctor.factorOfRangeLE hle
  have hf : f ≫ i = i' := SubgroupFunctor.factorOfRangeLE_comp hle
  have hfs : f.hom.hom.left ≫ i.hom.hom.left = i'.hom.hom.left :=
    congrArg (fun z : Q' ⟶ G => z.hom.hom.left) hf
  have hk : i.hom.hom.left.ker ≤ i'.hom.hom.left.ker := by
    rw [← hfs]
    exact Scheme.Hom.le_ker_comp _ _
  have hJ : i'.hom.hom.left.ker.ideal U ∈ ideals :=
    ⟨Q', i', hi', hle.trans hQi, rfl⟩
  have heq : i.hom.hom.left.ker.ideal U = i'.hom.hom.left.ker.ideal U :=
    eq_of_le_of_not_lt (hk U) (hmax _ hJ)
  have hker : i'.hom.hom.left.ker = i.hom.hom.left.ker :=
    Scheme.IdealSheafData.ext_of_isAffine heq.symm
  have : IsIso f.hom.hom.left :=
    IsClosedImmersion.isIso_of_ker_eq _ _ _ hfs hker
  have : IsIso f.hom.hom :=
    (isIso_iff_of_reflects_iso _ (Over.forget _)).mp
      (show IsIso f.hom.hom.left from inferInstance)
  have : IsIso f.hom :=
    (isIso_iff_of_reflects_iso _ (Mon.forget _)).mp
      (show IsIso f.hom.hom from inferInstance)
  have : IsIso f :=
    (isIso_iff_of_reflects_iso _ (Grp.forget₂Mon _)).mp
      (show IsIso f.hom from inferInstance)
  apply le_antisymm hle
  apply SubgroupFunctor.range_le_of_factor (inv f)
  rw [← hf, IsIso.inv_hom_id_assoc]

end Langlands.GroupScheme
