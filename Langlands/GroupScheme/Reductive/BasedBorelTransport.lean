import Langlands.GroupScheme.Reductive.BasedAffineBorel
import Langlands.GroupScheme.Torus.ExponentTransport
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # Actual transport of canonical based dynamic Borels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace BasedBorelTransport

variable {S : Scheme.{u}} {I J : Type u} [Fintype I] [Fintype J]
  {G : GroupScheme S}

/-- The actual cocharacter of the canonical sum of positive coroots, over any base. -/
def cocharacter (i : splitTorus S I ⟶ G)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base) :
    (Gm S).toGrp ⟶ G :=
  CommGroupScheme.groupHom
    (splitTorus.exponentCocharacter S I (BasedBorelExponent.positiveCorootSum P b)) ≫ i

end BasedBorelTransport

variable {S : Scheme.{u}} {I I' J J' : Type u}
  [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
  {G H : GroupScheme S}
  (i : splitTorus S I ⟶ G) (j : splitTorus S I' ⟶ H)
  (P : RootDatum J (I → ℤ) (I → ℤ)) (Q : RootDatum J' (I' → ℤ) (I' → ℤ))
  (b : P.Base) (c : Q.Base)

/-- Supplied actual group and coordinate-torus isomorphisms inducing a based
root-datum equivalence by character pullback. This records transport data, not
an existence or lifting theorem. -/
structure BasedCoordinateIso where
  groupIso : G ≅ H
  torusIso : splitTorus S I ≅ splitTorus S I'
  rootEquiv : RootPairing.Equiv Q P
  sourcePairing : ∀ m n, P.toLinearMap m n = ∑ a, m a * n a
  targetPairing : ∀ m n, Q.toLinearMap m n = ∑ a, m a * n a
  simple_iff : ∀ a : J', a ∈ c.support ↔ rootEquiv.indexEquiv a ∈ b.support
  square : i ≫ groupIso.hom = torusIso.hom ≫ j
  characters : ∀ (U : Over S) (x : U ⟶ (splitTorus S I).X) (m : I' → ℤ),
    ∏ a, splitTorus.pointsEquiv I' U (x ≫ torusIso.hom.hom.hom) a ^ m a =
      ∏ a, splitTorus.pointsEquiv I U x a ^ rootEquiv.weightMap m a

namespace BasedCoordinateIso

variable {i j P Q b c} (d : BasedCoordinateIso i j P Q b c)

open BasedBorelTransport

/-- The supplied torus isomorphism preserves the actual canonical cocharacter. -/
theorem torus_cocharacter_comp :
    CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter S I (BasedBorelExponent.positiveCorootSum P b)) ≫
        d.torusIso.hom =
      CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter S I' (BasedBorelExponent.positiveCorootSum Q c)) := by
  have hn := splitTorus.exponentPushforward_eq_coweightMap d.rootEquiv
    d.sourcePairing d.targetPairing (BasedBorelExponent.positiveCorootSum P b)
  rw [BasedBorelExponent.positiveCorootSum_coweightMap c b d.rootEquiv d.simple_iff] at hn
  have h := splitTorus.groupHom_exponentCocharacter_comp
    d.torusIso.hom d.rootEquiv.weightMap d.characters
    (BasedBorelExponent.positiveCorootSum P b)
  rwa [hn] at h

/-- The exact inclusion square gives transport of the canonical ambient cocharacter. -/
theorem cocharacter_comp :
    cocharacter i P b ≫ d.groupIso.hom = cocharacter j Q c := by
  unfold cocharacter
  rw [Category.assoc, d.square, ← Category.assoc, d.torus_cocharacter_comp]

/-- The inverse ambient isomorphism recovers the original canonical cocharacter. -/
theorem cocharacter_inv_comp :
    cocharacter j Q c ≫ d.groupIso.inv = cocharacter i P b := by
  rw [← d.cocharacter_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Canonical dynamic parabolics are carried to each other on every test scheme. -/
theorem parabolic_comap :
    (Dynamic.parabolic (cocharacter i P b)).comap d.groupIso.inv =
      Dynamic.parabolic (cocharacter j Q c) := by
  have h := Dynamic.parabolic_eq_comap_of_iso (cocharacter j Q c) d.groupIso.symm
  rw [Iso.symm_hom, d.cocharacter_inv_comp] at h
  exact h.symm

omit [Fintype J] [Fintype J'] in
/-- The torus inclusion has precisely the same range after actual transport. -/
theorem range_torus_comp :
    SubgroupFunctor.range (i ≫ d.groupIso.hom) = SubgroupFunctor.range j := by
  rw [d.square]
  exact SubgroupFunctor.range_iso_comp d.torusIso j

variable {B B' : GroupScheme S} {k : B ⟶ G} {l : B' ⟶ H}
  (hk : (Dynamic.parabolic (cocharacter i P b)).IsRepresentedBy k)
  (hl : (Dynamic.parabolic (cocharacter j Q c)).IsRepresentedBy l)

include hk in
/-- The transported source inclusion represents the target dynamic parabolic. -/
theorem isRepresentedBy_parabolic_comp :
    (Dynamic.parabolic (cocharacter j Q c)).IsRepresentedBy (k ≫ d.groupIso.hom) := by
  have h := hk.comp_iso d.groupIso
  rwa [d.parabolic_comap] at h

/-- An actual isomorphism between any supplied representatives of the canonical
dynamic parabolics, including pullbacks of affine canonical Borels. -/
def parabolicIso : B ≅ B' :=
  (d.isRepresentedBy_parabolic_comp hk).isoOfIsRepresentedBy hl

include hk hl in
/-- The constructed parabolic isomorphism respects the actual inclusions. -/
theorem parabolicIso_hom_comp :
    (d.parabolicIso hk hl).hom ≫ l = k ≫ d.groupIso.hom :=
  (d.isRepresentedBy_parabolic_comp hk).isoOfIsRepresentedBy_hom_comp hl

include hk hl in
/-- The canonical parabolic inclusions have equal all-test ranges after transport. -/
theorem range_parabolic_comp :
    SubgroupFunctor.range (k ≫ d.groupIso.hom) = SubgroupFunctor.range l := by
  rw [← d.parabolicIso_hom_comp hk hl]
  exact SubgroupFunctor.range_iso_comp (d.parabolicIso hk hl) l

include hk hl in
/-- The actual inclusion equation retains range invariance after any base change. -/
theorem range_baseChange_parabolic_comp {T : Scheme.{u}} (a : T ⟶ S) :
    SubgroupFunctor.range
        ((GroupScheme.baseChange a).map k ≫ (GroupScheme.baseChange a).map d.groupIso.hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange a).map l) := by
  rw [← Functor.map_comp, ← d.parabolicIso_hom_comp hk hl, Functor.map_comp]
  exact SubgroupFunctor.range_iso_comp
    ((GroupScheme.baseChange a).mapIso (d.parabolicIso hk hl)) _

end BasedCoordinateIso

end Langlands.GroupScheme
