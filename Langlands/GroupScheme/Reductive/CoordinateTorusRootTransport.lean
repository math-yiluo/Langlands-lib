import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Reductive.LocalSplitCell
import Langlands.GroupScheme.Reductive.LocalSplitCommonTorus
import Langlands.GroupScheme.Reductive.GeometricRootDatumComparison
import Langlands.GroupScheme.Rational.CrossTorusRootTransport
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Full root data and actual root ranges under a fixed coordinate-torus isomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open LocalSplitCell CoordinateRootDatum

variable {R : Type u} [CommRing R] [Nontrivial R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [DecidableEq I] [DecidableEq I']
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  (E : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ)) (f : G ≅ H)
  (hsquare : i ≫ f.hom = precompTorus E j)
  (hG : IsReductive G) (hH : IsReductive H)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  (hP : IsFibrewiseRootDatumOf I G i P)
  (hQ : IsFibrewiseRootDatumOf I' H j Q)

include hsquare hG hH hmax hmax' hP hQ in
/-- The actual compatible coordinate-torus square determines a full equivalence
of supplied coordinate root data with precisely the prescribed weight map. -/
theorem exists_rootDatumEquiv_of_coordinateTorusIso :
    ∃ e : RootPairing.Equiv P Q, e.toHom.weightMap = E.toLinearMap := by
  obtain ⟨a, ha⟩ := Ideal.exists_maximal R
  let : a.IsMaximal := ha
  let : Field (R ⧸ a) := Ideal.Quotient.field a
  let k := R ⧸ a
  let b := algebraBaseMap R k
  let GK := (GroupScheme.baseChange b).obj G
  let HK := (GroupScheme.baseChange b).obj H
  have hGK : IsConnectedReductive GK := hG.isConnectedReductive_algebraMap k
  have hHK : IsConnectedReductive HK := hH.isConnectedReductive_algebraMap k
  let := hG.smooth
  let := hH.smooth
  let := hGK.isAffineHom
  let := hHK.isAffineHom
  let iK := splitTorus.baseChangeHom (K := k) G I i
  let jK := splitTorus.baseChangeHom (K := k) H I' j
  let fK := (GroupScheme.baseChange b).mapIso f
  let tK := splitTorus.exponentEquivIso (Spec (CommRingCat.of k)) E
  have hiK : IsMaximalTorus (T := splitTorus.commGroupScheme _ I) iK :=
    splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax k
  have hjK : IsMaximalTorus (T := splitTorus.commGroupScheme _ I') jK :=
    splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I' H j hmax' k
  have hsK : iK ≫ fK.hom = CommGroupScheme.groupHom tK.hom ≫ jK := by
    have h := congrArg (fun t => splitTorus.baseChangeHom (K := k) H I t) hsquare
    rw [baseChangeHom_precompTorus] at h
    simpa only [iK, jK, fK, tK, b, Functor.mapIso_hom,
      splitTorus.baseChangeHom, Functor.map_comp, Category.assoc] using h
  have hsK' : jK ≫ fK.inv = CommGroupScheme.groupHom tK.inv ≫ iK := by
    apply (cancel_mono fK.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, hsK,
      ← Category.assoc]
    change jK = CommGroupScheme.groupHom (tK.inv ≫ tK.hom) ≫ jK
    rw [Iso.inv_hom_id]
    exact (Category.id_comp jK).symm
  obtain ⟨eK, heK, -⟩ := exists_rootDatumEquiv_of_torusCompatibleIso
    hHK hGK (isSplitTorus_splitTorus I') (isSplitTorus_splitTorus I)
    hjK hiK fK.symm tK.symm hsK' (hQ.field k) (hP.field k)
  let e := equivOfFieldRealizationEquiv k P Q eK
  refine ⟨e, ?_⟩
  apply LinearMap.ext
  intro m
  have hclass : eK.toHom.weightMap ((fieldRealizationEquiv k P).toHom.weightMap m) =
      (fieldRealizationEquiv k Q).toHom.weightMap (E m) := by
    rw [fieldRealizationEquiv_weightMap, fieldRealizationEquiv_weightMap, heK]
    exact splitTorus.congr_exponentEquivIso (Spec (CommRingCat.of k)) E m
  change (fieldRealizationEquiv k Q).weightEquiv.symm
    (eK.toHom.weightMap ((fieldRealizationEquiv k P).toHom.weightMap m)) = E m
  rw [hclass]
  exact (fieldRealizationEquiv k Q).weightEquiv_symm_weightMap (E m)

/-- Choose the full datum equivalence with the proved prescribed coordinate map. -/
def rootDatumEquivOfCoordinateTorusIso : RootPairing.Equiv P Q :=
  Classical.choose (exists_rootDatumEquiv_of_coordinateTorusIso E f hsquare hG hH hmax hmax' hP hQ)

/-- The chosen full equivalence retains precisely the original coordinate map. -/
theorem rootDatumEquivOfCoordinateTorusIso_weightMap :
    (rootDatumEquivOfCoordinateTorusIso E f hsquare hG hH hmax hmax' hP hQ).toHom.weightMap =
      E.toLinearMap :=
  Classical.choose_spec (exists_rootDatumEquiv_of_coordinateTorusIso E f hsquare hG hH hmax hmax' hP hQ)

variable {fam : J → (Ga R ⟶ G)} {fam' : J' → (Ga R ⟶ H)}
  (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a))
  (hfam' : ∀ a, IsRootParametrization j (Q.root a) (fam' a))

include hsquare hG hH hmax hmax' hP hQ hfam hfam' in
/-- The same actual square matches the complete ambient root ranges, through
the full datum equivalence whose coordinate map was just determined. -/
theorem range_root_comp_coordinateTorusIso (a : J) :
    SubgroupFunctor.range (fam a ≫ f.hom) =
      SubgroupFunctor.range (fam'
        ((rootDatumEquivOfCoordinateTorusIso E f hsquare hG hH hmax hmax' hP hQ).indexEquiv a)) := by
  let e := rootDatumEquivOfCoordinateTorusIso E f hsquare hG hH hmax hmax' hP hQ
  let t := splitTorus.exponentEquivIso (Spec (CommRingCat.of R)) E
  have hchar : t.inv ≫ splitTorus.exponentCharacter _ I (P.root a) =
      splitTorus.exponentCharacter _ I' (Q.root (e.indexEquiv a)) := by
    have hr := e.root_weightMap_apply P Q a
    rw [rootDatumEquivOfCoordinateTorusIso_weightMap] at hr
    change E (P.root a) = Q.root (e.indexEquiv a) at hr
    rw [← hr]
    exact splitTorus.congr_exponentEquivIso (Spec (CommRingCat.of R)) E (P.root a)
  have h := RelativeRoot.subgroup_comap_of_transport t f hsquare
    (splitTorus.exponentCharacter _ I (P.root a))
  rw [characterLattice.congr_apply, hchar, ← (hfam a).represents.2,
    ← (hfam' (e.indexEquiv a)).represents.2] at h
  rw [SubgroupFunctor.range_comp_iso, ← h, ← SubgroupFunctor.comap_comp,
    Iso.inv_hom_id, SubgroupFunctor.comap_id]

end Langlands.GroupScheme
