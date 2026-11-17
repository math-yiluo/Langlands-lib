import Langlands.GroupScheme.Reductive.ConnectedSchemeRootDatum
import Langlands.GroupScheme.Reductive.RootDatumFieldComparison

/-! # Full coordinate root-data comparison from a local group isomorphism -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section GlobalComparison

variable {S : Scheme.{u}} {I I' : Type u} [Fintype I] [Fintype I']
  {G H : GroupScheme S} (hG : IsReductive G) (hH : IsReductive H)
  {i : splitTorus S I ⟶ G} {j : splitTorus S I' ⟶ H}
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  {J J' : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  (hP : letI := hG.isAffineHom; CoordinateRootDatum.IsGlobalCoordinateRootDatumOf I G i P)
  (hQ : letI := hH.isAffineHom; CoordinateRootDatum.IsGlobalCoordinateRootDatumOf I' H j Q)

include hG hH hmax hmax' hP hQ

/-- An isomorphism on one supplied actual field fibre identifies two full
global coordinate root data, without requiring it to carry the chosen tori. -/
theorem nonempty_globalCoordinateRootDatumEquiv_of_fieldIso
    (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (e : (baseChange b).obj G ≅ (baseChange b).obj H) :
    Nonempty (RootPairing.Equiv P Q) := by
  let := hG.isAffineHom
  let := hH.isAffineHom
  let := hG.smooth
  let := hH.smooth
  have hi : IsMaximalTorus (T := splitTorus.commGroupScheme _ I)
      ((splitTorus.baseChangeIso b I).inv ≫ (baseChange b).map i) :=
    IsMaximalTorus.iso_comp
      (T := (CommGroupScheme.baseChange b).obj (splitTorus.commGroupScheme _ I))
      (T' := splitTorus.commGroupScheme _ I)
      (splitTorus.baseChangeIso b I).symm (hmax.fieldPoint b)
  have hj : IsMaximalTorus (T := splitTorus.commGroupScheme _ I')
      ((splitTorus.baseChangeIso b I').inv ≫ (baseChange b).map j) :=
    IsMaximalTorus.iso_comp
      (T := (CommGroupScheme.baseChange b).obj (splitTorus.commGroupScheme _ I'))
      (T' := splitTorus.commGroupScheme _ I')
      (splitTorus.baseChangeIso b I').symm (hmax'.fieldPoint b)
  obtain ⟨f⟩ := nonempty_rootDatumEquiv_of_iso
    (hG.isConnectedReductive_baseChange b) (hH.isConnectedReductive_baseChange b)
    (isSplitTorus_splitTorus I) (isSplitTorus_splitTorus I') hi hj e
    (hP.2.2 k b) (hQ.2.2 k b)
  exact ⟨CoordinateRootDatum.equivOfFieldRealizationEquiv k P Q f⟩

/-- Étale-local isomorphism over a nonempty base identifies the full global
coordinate root data of any two supplied split maximal tori. -/
theorem nonempty_globalCoordinateRootDatumEquiv_of_etaleLocalIso [Nonempty S]
    (hloc : ∃ 𝒱 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      ∀ a : 𝒱.I₀, Nonempty ((baseChange (𝒱.f a)).obj G ≅
        (baseChange (𝒱.f a)).obj H)) :
    Nonempty (RootPairing.Equiv P Q) := by
  obtain ⟨𝒱, h𝒱⟩ := hloc
  let s : S := Classical.choice inferInstance
  obtain ⟨a, y, -⟩ := 𝒱.exists_eq s
  let k := (𝒱.X a).residueField y
  let b := (𝒱.X a).fromSpecResidueField y
  let f := Classical.choice (h𝒱 a)
  let e : (baseChange (b ≫ 𝒱.f a)).obj G ≅ (baseChange (b ≫ 𝒱.f a)).obj H :=
    baseChangeCompIso (𝒱.f a) b G ≪≫ (baseChange b).mapIso f ≪≫
      (baseChangeCompIso (𝒱.f a) b H).symm
  exact nonempty_globalCoordinateRootDatumEquiv_of_fieldIso
    hG hH hmax hmax' hP hQ k (b ≫ 𝒱.f a) e

/-- Choose the full coordinate root-data equivalence determined to exist by
an étale-local group isomorphism. Both entire coordinate lattices are retained. -/
def globalCoordinateRootDatumEquivOfEtaleLocalIso [Nonempty S]
    (hloc : ∃ 𝒱 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      ∀ a : 𝒱.I₀, Nonempty ((baseChange (𝒱.f a)).obj G ≅
        (baseChange (𝒱.f a)).obj H)) :
    RootPairing.Equiv P Q :=
  Classical.choice (nonempty_globalCoordinateRootDatumEquiv_of_etaleLocalIso
    hG hH hmax hmax' hP hQ hloc)

end GlobalComparison

end Langlands.GroupScheme
