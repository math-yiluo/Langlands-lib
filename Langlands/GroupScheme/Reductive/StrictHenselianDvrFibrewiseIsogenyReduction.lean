import Langlands.AlgebraicGeometry.DiscreteValuationFibreIsomorphism
import Langlands.GroupScheme.Reductive.StrictHenselianDvrKernelRemovalStatement
import Langlands.GroupScheme.Reductive.StrictHenselianDVRIsogenyRigidityStatement
import Langlands.AbelianScheme.IsogenyStability

/-! # Reducing the strictly Henselian DVR isogeny criterion to two local inputs -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The fibrewise-isogeny criterion restricted to strictly Henselian DVR bases. -/
def StrictHenselianDvrFibrewiseIsogenyStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    (G H : GroupScheme (Spec (CommRingCat.of R))),
    IsReductive G → IsReductive H →
    ∀ f : G ⟶ H,
      (∀ s : Spec (CommRingCat.of R),
        IsIsogeny ((baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map f)) →
      IsIsogeny f

/-- The generic and closed fibres detect an isomorphism of the specified group
homomorphism under the usual flatness and finite-presentation hypotheses. -/
theorem isIso_groupHom_of_generic_special
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {G H : GroupScheme (Spec (CommRingCat.of R))} (f : G ⟶ H)
    [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] [LocallyOfFiniteType H.X.hom]
    (hgen : IsIso ((baseChange (Spec.algebraMap R K)).map f))
    (hspec : IsIso ((baseChange
      (Spec.algebraMap R (IsLocalRing.ResidueField R))).map f)) :
    IsIso f := by
  have hgen' : IsIso ((Over.pullback (Spec.algebraMap R K)).map f.hom.hom) := by
    let := hgen
    exact inferInstanceAs (IsIso ((Grp.forget _).map
      ((baseChange (Spec.algebraMap R K)).map f)))
  have hspec' : IsIso ((Over.pullback
      (Spec.algebraMap R (IsLocalRing.ResidueField R))).map f.hom.hom) := by
    let := hspec
    exact inferInstanceAs (IsIso ((Grp.forget _).map
      ((baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).map f)))
  have : IsIso f.hom.hom :=
    Langlands.AlgebraicGeometry.isIso_of_generic_special f.hom.hom ⟨hgen', hspec'⟩
  let e : G ≅ H := Grp.mkIso' (asIso f.hom.hom)
  change IsIso e.hom
  infer_instance

/-- Finite kernel removal and prescribed-map generic rigidity imply the full
isogeny criterion over every strictly Henselian DVR. -/
theorem strictHenselianDvrFibrewiseIsogeny_of_kernelRemoval_and_rigidity
    (hkernel : StrictHenselianDvrKernelRemovalStatement.{u})
    (hrigidity : StrictHenselianDVRIsogenyRigidityStatement.{u}) :
    StrictHenselianDvrFibrewiseIsogenyStatement.{u} := by
  intro R _ _ _ _ _ G H hG hH f hf
  obtain ⟨Q, q, g, hQ, hq, hcomp, hgfib, hgspec⟩ :=
    hkernel R G H hG hH f hf
  have hggen : IsIso ((baseChange (Spec.algebraMap R (FractionRing R))).map g) :=
    hrigidity R (FractionRing R) Q H hQ hH g hgfib hgspec
  let := hQ.smooth
  let := hH.smooth
  have : IsIso g := isIso_groupHom_of_generic_special g hggen hgspec
  have : IsIso g.hom.hom.left :=
    inferInstanceAs (IsIso ((Grp.forget _ ⋙ Over.forget _).map g))
  have hg : IsIsogeny g := ⟨inferInstance, inferInstance, inferInstance⟩
  rw [← hcomp]
  exact hq.comp hg

end Langlands.GroupScheme
