import Langlands.GroupScheme.Reductive.LocalSplitRootSpaces
import Langlands.GroupScheme.Torus.FibrewiseMaximalBaseChange
import Langlands.GroupScheme.Torus.EtaleLocalMaximalExistenceProof
import Langlands.GroupScheme.RelativeLevi.HenselianBorelReduction
import Langlands.GroupScheme.RelativeLevi.HenselianQuasiSplitStatement
import Langlands.CommutativeAlgebra.HenselianFiniteEtaleRefinementStatement

/-! # Split data after a finite étale refinement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- Pull a coordinate maximal torus through an actual factorization and
assemble full split data over the resulting local algebra. -/
def localSplitDataOfFactoredNeighbourhood
    {R : Type u} [CommRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    {A : Type u} [CommRing A]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (I : Type u) [Fintype I]
    (i : splitTorus (Spec (CommRingCat.of A)) I ⟶ (baseChange f).obj G)
    (hic : IsClosedSubgroup i)
    (hi : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {R' : Type u} [CommRing R'] [IsLocalRing R'] [Algebra R R']
    (g : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of A))
    (hfac : g ≫ f = Spec.algebraMap R R') :
    haveI := hG.isAffineHom
    haveI : IsAffineHom ((baseChange (Spec.algebraMap R R')).obj G).X.hom :=
      inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom _))
    {j : splitTorus (Spec (CommRingCat.of R')) I ⟶
        (baseChange (Spec.algebraMap R R')).obj G //
      IsClosedSubgroup j ∧
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) j ∧
      ∃ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
        IsFibrewiseRootDatumOf I ((baseChange (Spec.algebraMap R R')).obj G) j P ∧
        ∀ α : J, Nonempty (splitTorus.exponentWeightSpace I
          ((baseChange (Spec.algebraMap R R')).obj G) j (P.root α) ≃ₗ[R'] R')} := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let H := (baseChange f).obj G
  let : Smooth H.X.hom :=
    inferInstanceAs (Smooth (Limits.pullback.snd G.X.hom f))
  let : IsAffineHom H.X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom f))
  let t := splitTorus.fibrewiseMaximalBaseChange I H i g hic hi
  let e : (baseChange g).obj H ≅ (baseChange (Spec.algebraMap R R')).obj G :=
    (baseChangeCompIso f g G).symm ≪≫
      eqToIso (congrArg (fun b => (baseChange b).obj G) hfac)
  let j := t.val ≫ e.hom
  have hjc : IsClosedSubgroup j := t.property.1.comp_iso e
  have hjm : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) j := by
    intro s
    simpa only [j, Functor.map_comp, Functor.mapIso_hom] using
      (t.property.2 s).comp_iso
        ((baseChange ((Spec (CommRingCat.of R')).fromSpecResidueField s)).mapIso e)
  let : IsAffineHom ((baseChange (Spec.algebraMap R R')).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom _))
  exact ⟨j, hjc, hjm, localSplitDataOfFibrewiseMaximalTorus R'
    ((baseChange (Spec.algebraMap R R')).obj G)
    (hG.baseChange (Spec.algebraMap R R')) I j hjc hjm⟩

/-- Borel representability and finite étale refinement suffice for the
full unchanged target, using published affine torus neighbourhoods. -/
theorem henselianFiniteResidueQuasiSplit_of_inputs
    (hBor : RelativeBorelSchemeStatement.{u})
    (hRef : Langlands.CommutativeAlgebra.HenselianFiniteEtaleRefinementStatement.{u}) :
    HenselianFiniteResidueQuasiSplitStatement.{u} := by
  intro R _ _ _ G hG
  refine ⟨henselianFiniteResidueQuasiSplit_of_borelScheme hBor R G hG, ?_⟩
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨A, hA, f, hf, hx, I, hI, i, hic, hi⟩ :=
    exists_etale_affine_split_maximalTorus _ G hG (IsLocalRing.closedPoint R)
  let : CommRing A := hA
  let : Fintype I := hI
  obtain ⟨R', hR', hlR', aR', he, hm, g, hfac⟩ := hRef R A f hf hx
  let : CommRing R' := hR'
  let : IsLocalRing R' := hlR'
  let : Algebra R R' := aR'
  obtain ⟨j, hjc, hjm, J, P, hP, hline⟩ :=
    localSplitDataOfFactoredNeighbourhood G hG f I i hic hi g hfac
  exact ⟨R', hR', hlR', aR', he, hm, I, hI, j, hjc, hjm, J, P, hP, hline⟩

end Langlands.GroupScheme
