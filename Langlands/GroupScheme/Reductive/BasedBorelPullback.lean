import Langlands.GroupScheme.Reductive.BasedBorelTransport
import Langlands.GroupScheme.Descent.ClosedSubgroups

/-! # Pullbacks and inherited descent data for canonical based parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace BasedBorelTransport

variable {S T : Scheme.{u}} {I J : Type u} [Fintype I] [Fintype J]
  {G : GroupScheme S}

/-- The pulled-back coordinate torus inclusion with the canonical split-torus
source over the new base. -/
def baseChangeInclusion (a : T ⟶ S) (i : splitTorus S I ⟶ G) :
    splitTorus T I ⟶ (GroupScheme.baseChange a).obj G :=
  (splitTorus.baseChangeIso a I).inv ≫ (GroupScheme.baseChange a).map i

/-- The canonical based cocharacter commutes exactly with arbitrary base change
after normalizing the coordinate torus source. -/
theorem cocharacter_baseChange (a : T ⟶ S) (i : splitTorus S I ⟶ G)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base) :
    Dynamic.baseChangeCocharacter a (cocharacter i P b) =
      cocharacter (baseChangeInclusion a i) P b := by
  rw [cocharacter, cocharacter, Dynamic.baseChangeCocharacter_comp,
    ← splitTorus.groupHom_exponentCocharacter_baseChange S I a
      (BasedBorelExponent.positiveCorootSum P b)]
  simp only [baseChangeInclusion, Category.assoc, Iso.hom_inv_id_assoc]

/-- Any representative of a canonical dynamic parabolic remains a
representative for the normalized pulled-back coordinate inclusion. -/
theorem isRepresentedBy_baseChange (a : T ⟶ S) (i : splitTorus S I ⟶ G)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base)
    {B : GroupScheme S} {k : B ⟶ G}
    (hk : (Dynamic.parabolic (cocharacter i P b)).IsRepresentedBy k) :
    (Dynamic.parabolic (cocharacter (baseChangeInclusion a i) P b)).IsRepresentedBy
      ((GroupScheme.baseChange a).map k) := by
  rw [← cocharacter_baseChange, Dynamic.parabolic_baseChange]
  exact hk.baseChange a

end BasedBorelTransport

namespace BasedCoordinateIso

open BasedBorelTransport

variable {S S' T : Scheme.{u}} {I I' J J' : Type u}
  [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
  {G : GroupScheme S} {H : GroupScheme S'}
  {i : splitTorus S I ⟶ G} {j : splitTorus S' I' ⟶ H}
  {P : RootDatum J (I → ℤ) (I → ℤ)} {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  {b : P.Base} {c : Q.Base} {a : T ⟶ S} {a' : T ⟶ S'}
  (d : BasedCoordinateIso (baseChangeInclusion a i) (baseChangeInclusion a' j) P Q b c)
  {B : GroupScheme S} {B' : GroupScheme S'} {k : B ⟶ G} {l : B' ⟶ H}
  (hk : (Dynamic.parabolic (cocharacter i P b)).IsRepresentedBy k)
  (hl : (Dynamic.parabolic (cocharacter j Q c)).IsRepresentedBy l)

/-- A supplied based coordinate comparison on a common pullback gives an actual
isomorphism of the pulled-back parabolic representatives. -/
def pullbackParabolicIso :
    (GroupScheme.baseChange a).obj B ≅ (GroupScheme.baseChange a').obj B' :=
  d.parabolicIso (isRepresentedBy_baseChange a i P b hk)
    (isRepresentedBy_baseChange a' j Q c hl)

/-- The pullback comparison respects the original pulled-back inclusions. -/
theorem pullbackParabolicIso_hom_comp :
    (d.pullbackParabolicIso hk hl).hom ≫ (GroupScheme.baseChange a').map l =
      (GroupScheme.baseChange a).map k ≫ d.groupIso.hom :=
  d.parabolicIso_hom_comp (isRepresentedBy_baseChange a i P b hk)
    (isRepresentedBy_baseChange a' j Q c hl)

include hk hl in
/-- The pulled-back parabolic inclusions have the required all-test range
equality on the common base. -/
theorem range_pullback_parabolic_comp :
    SubgroupFunctor.range ((GroupScheme.baseChange a).map k ≫ d.groupIso.hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange a').map l) :=
  d.range_parabolic_comp (isRepresentedBy_baseChange a i P b hk)
    (isRepresentedBy_baseChange a' j Q c hl)

omit [Fintype J] [Fintype J'] in
/-- Removing the coordinate-source normalizations gives the overlap range
equality for the original pulled-back torus inclusions. -/
theorem range_pullback_torus_comp :
    SubgroupFunctor.range ((GroupScheme.baseChange a).map i ≫ d.groupIso.hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange a').map j) := by
  calc
    _ = SubgroupFunctor.range
        ((splitTorus.baseChangeIso a I).symm.hom ≫
          ((GroupScheme.baseChange a).map i ≫ d.groupIso.hom)) :=
      (SubgroupFunctor.range_iso_comp (splitTorus.baseChangeIso a I).symm _).symm
    _ = SubgroupFunctor.range
        ((splitTorus.baseChangeIso a' I').symm.hom ≫ (GroupScheme.baseChange a').map j) := by
      simpa only [baseChangeInclusion, Iso.symm_hom, Category.assoc] using d.range_torus_comp
    _ = _ := SubgroupFunctor.range_iso_comp (splitTorus.baseChangeIso a' I').symm _

end BasedCoordinateIso

namespace Descent.Datum

open BasedBorelTransport

variable {S U : Scheme.{u}} {p : U ⟶ S} {G B : GroupScheme U}
  {I J : Type u} [Fintype I] [Fintype J]
  {i : splitTorus U I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {b : P.Base} {k : B ⟶ G}
  (D : Datum p G)
  (d : BasedCoordinateIso (baseChangeInclusion (fst p) i)
    (baseChangeInclusion (snd p) i) P P b b)
  (hd : d.groupIso = D.overlap)
  (hk : (Dynamic.parabolic (cocharacter i P b)).IsRepresentedBy k)
  (hkClosed : IsClosedSubgroup k)

/-- A supplied based overlap comparison lifts the existing ambient descent
datum to any closed representative of the canonical based parabolic. -/
def basedParabolicSubgroup : Datum p B :=
  D.closedSubgroup hkClosed (by
    have h := d.range_pullback_parabolic_comp hk hk
    rwa [hd] at h)

include hd hk hkClosed in
/-- The original parabolic inclusion is compatible with the inherited datum. -/
theorem compatible_basedParabolicSubgroup :
    Compatible (D.basedParabolicSubgroup d hd hk hkClosed) D k :=
  D.compatible_closedSubgroup hkClosed _

variable (hiClosed : IsClosedSubgroup i)

/-- The same based overlap comparison gives actual descent data on the
coordinate torus, inheriting the ambient cocycle through its closed inclusion. -/
def basedCoordinateTorusSubgroup : Datum p (splitTorus U I) :=
  D.closedSubgroup hiClosed (by
    have h := d.range_pullback_torus_comp
    rwa [hd] at h)

omit [Fintype J] in
include hd hiClosed in
/-- The original coordinate-torus inclusion is compatible with its inherited datum. -/
theorem compatible_basedCoordinateTorusSubgroup :
    Compatible (D.basedCoordinateTorusSubgroup d hd hiClosed) D i :=
  D.compatible_closedSubgroup hiClosed _

end Descent.Datum

end Langlands.GroupScheme
