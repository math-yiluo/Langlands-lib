import Langlands.GroupScheme.Reductive.RelativeIsogenyRootUnit
import Langlands.GroupScheme.Reductive.LocalSimpleRootPowerRigidity
import Langlands.LinearAlgebra.RootDatumIsogenyReflections

/-! # Simple-root power formulas for finite maps with supplied root data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace OppositePower

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- Equality of actual root restrictions determines their power coefficients.
The degrees may differ: evaluation at the unit point suffices. -/
theorem HasPowerFormula.coefficient_eq_of_maps_eq
    {I : Type u} [Fintype I]
    {j : splitTorus (Spec (CommRingCat.of R)) I ⟶ H}
    {m : I → ℤ} {xp : Ga R ⟶ G} {yp : Ga R ⟶ H}
    (hy : IsRootParametrization j m yp)
    {f F : G ⟶ H} {c c' : R} {q q' : ℕ}
    (hf : HasPowerFormula f xp yp c q)
    (hF : HasPowerFormula F xp yp c' q')
    (he : xp ≫ f = xp ≫ F) : c = c' := by
  let A : CommAlgCat.{u} (CommRingCat.of R) := CommAlgCat.of R R
  let Z := Corepresented.RingCoordinates.specOver (CommRingCat.of R) A
  have hp : rootPoint yp Z (baseScalar Z c) = rootPoint yp Z (baseScalar Z c') := by
    have h := congrArg (fun v : Ga R ⟶ H => rootPoint v Z 1) he
    rw [rootPoint_comp, rootPoint_comp, hf, hF] at h
    simpa only [one_pow, mul_one] using h
  have hs := hy.rootPoint_injective Z hp
  have hb := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom hs
  rw [gamma_baseScalar A c, gamma_baseScalar A c'] at hb
  exact hb

end OppositePower

namespace RelativeIsogeny

open LocalSplitCell OppositePower

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u}
  [Fintype I] [Fintype I'] [Finite J] [Finite J']
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced]
  {p : ℕ}

/-- Simple and negative-simple power formulas whose indices and degrees come
from the supplied root-datum isogeny. -/
def HasSimpleRootRestrictionFormulas
    (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (b : P.Base) (u : J → (Ga R ⟶ G)) (v : J' → (Ga R ⟶ H))
    (phi : G ⟶ H) : Prop :=
  ∃ (c : J → Rˣ) (d : J → R),
    HasSimpleRootPowerFormulas P Q b u v r.indexEquiv.symm phi c d
      (fun a => r.rootFactor (r.indexEquiv.symm a))

variable [IsLocalRing R]
  [DecidableEq I] [DecidableEq I']
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
  (hP : IsFibrewiseRootDatumOf I G i P)
  (hQ : IsFibrewiseRootDatumOf I' H j Q)
  (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
  (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
    splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
  (hweight : ∀ m : I' → ℤ, tau ≫ splitTorus.exponentCharacter _ I' m =
    splitTorus.exponentCharacter _ I (r.weightMap m))
  (phi : G ⟶ H) (hphi : i ≫ phi = CommGroupScheme.groupHom tau ≫ j)
  (hH : IsReductive H)
  (hmaxH : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  [IsFinite phi.hom.hom.left]

include hP hQ hweight hphi hH hmaxH

/-- Actual restrictions of a finite map provide all simple and opposite power
formulas, with unit positive coefficients and the same degree at opposites. -/
theorem hasSimpleRootRestrictionFormulas
    (b : P.Base) (u : J → (Ga R ⟶ G)) (v : J' → (Ga R ⟶ H))
    (hu : ∀ a ∈ b.support,
      IsRootParametrization i (P.root a) (u a) ∧
      IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a)))
    (hv : ∀ a ∈ b.support,
      IsRootParametrization j (Q.root (r.indexEquiv.symm a)) (v (r.indexEquiv.symm a)) ∧
      IsRootParametrization j
        (Q.root (Q.reflectionPerm (r.indexEquiv.symm a) (r.indexEquiv.symm a)))
        (v (Q.reflectionPerm (r.indexEquiv.symm a) (r.indexEquiv.symm a)))) :
    HasSimpleRootRestrictionFormulas r b u v phi := by
  classical
  have hp (a : J) (ha : a ∈ b.support) :
      IsRootParametrization i (P.root (r.indexEquiv (r.indexEquiv.symm a))) (u a) := by
    simpa only [Equiv.apply_symm_apply] using (hu a ha).1
  have hn (a : J) (ha : a ∈ b.support) :
      IsRootParametrization i
        (P.root (r.indexEquiv
          (Q.reflectionPerm (r.indexEquiv.symm a) (r.indexEquiv.symm a))))
        (u (P.reflectionPerm a a)) := by
    simpa only [r.indexEquiv_reflectionPerm, Equiv.apply_symm_apply] using (hu a ha).2
  let c : J → Rˣ := fun a =>
    if ha : a ∈ b.support then
      rootRestrictionUnit i j hP hQ r tau hweight phi hphi hH hmaxH
        (r.indexEquiv.symm a) (hp a ha) (hv a ha).1
    else 1
  let d : J → R := fun a =>
    if ha : a ∈ b.support then
      (rootRestrictionUnit i j hP hQ r tau hweight phi hphi hH hmaxH
        (Q.reflectionPerm (r.indexEquiv.symm a) (r.indexEquiv.symm a))
        (hn a ha) (hv a ha).2 : R)
    else 0
  refine ⟨c, d, fun a ha => ⟨?_, ?_⟩⟩
  · simpa only [HasPowerFormula, c, dite_eq_left ha] using
      rootRestriction_unit_power_rootPoint i j hP hQ r tau hweight phi hphi hH hmaxH
        (r.indexEquiv.symm a) (hp a ha) (hv a ha).1
  · simpa only [HasPowerFormula, d, dite_eq_left ha, r.rootFactor_reflectionPerm] using
      rootRestriction_unit_power_rootPoint i j hP hQ r tau hweight phi hphi hH hmaxH
        (Q.reflectionPerm (r.indexEquiv.symm a) (r.indexEquiv.symm a))
        (hn a ha) (hv a ha).2

/-- Finite homomorphisms with the supplied common root-datum and torus maps
are determined by their actual positive simple-root restrictions. -/
theorem hom_ext_of_simpleRootRestrictions
    (Phi : G ⟶ H) [IsFinite Phi.hom.hom.left]
    (hPhi : i ≫ Phi = CommGroupScheme.groupHom tau ≫ j)
    (hG : IsReductive G) (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (hmaxG : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (b : P.Base) (u : J → (Ga R ⟶ G)) (v : J' → (Ga R ⟶ H))
    (hu : ∀ a ∈ b.support,
      IsRootParametrization i (P.root a) (u a) ∧
      IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a)))
    (hv : ∀ a ∈ b.support,
      IsRootParametrization j (Q.root (r.indexEquiv.symm a)) (v (r.indexEquiv.symm a)) ∧
      IsRootParametrization j
        (Q.root (Q.reflectionPerm (r.indexEquiv.symm a) (r.indexEquiv.symm a)))
        (v (Q.reflectionPerm (r.indexEquiv.symm a) (r.indexEquiv.symm a))))
    (hw : ∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a))
    (he : ∀ a ∈ b.support, u a ≫ phi = u a ≫ Phi) : phi = Phi := by
  obtain ⟨c, d, hf⟩ := hasSimpleRootRestrictionFormulas
    i j hP hQ r tau hweight phi hphi hH hmaxH b u v hu hv
  obtain ⟨c', d', hF⟩ := hasSimpleRootRestrictionFormulas
    i j hP hQ r tau hweight Phi hPhi hH hmaxH b u v hu hv
  have hc (a : J) (ha : a ∈ b.support) : c a = c' a := by
    apply Units.ext
    exact (hf a ha).1.coefficient_eq_of_maps_eq (hv a ha).1 (hF a ha).1 (he a ha)
  apply hom_ext_of_simpleRootPowerFormulas hG hH i j hi hj hmaxG hmaxH hP hQ
    b u v r.indexEquiv.symm hu hv hw phi Phi (CommGroupScheme.groupHom tau)
    hphi hPhi c d d' (fun a => r.rootFactor (r.indexEquiv.symm a))
    (fun a _ => r.rootFactor_pos _) hf
  intro a ha
  simpa only [hc a ha] using hF a ha

end RelativeIsogeny

end Langlands.GroupScheme
