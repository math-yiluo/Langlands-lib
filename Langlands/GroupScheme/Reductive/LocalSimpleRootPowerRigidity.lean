import Langlands.GroupScheme.Reductive.LocalOppositeRootRigidity
import Langlands.GroupScheme.Reductive.SplitHomomorphismRigidity
import Langlands.GroupScheme.Reductive.LocalSplitSimpleRootGroupLocal

/-! # Homomorphism rigidity from simple-root power formulas -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace OppositePower

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- Two homomorphisms with the same all-test power formula agree on that
actual root map. No unit or positive-degree hypothesis is needed here. -/
theorem HasPowerFormula.maps_eq
    {f F : G ⟶ H} {xp : Ga R ⟶ G} {yp : Ga R ⟶ H} {c : R} {q : ℕ}
    (h : HasPowerFormula f xp yp c q) (h' : HasPowerFormula F xp yp c q) :
    xp ≫ f = xp ≫ F := by
  apply hom_ext_rootPoint
  intro Z x
  rw [rootPoint_comp, rootPoint_comp, h, h']

end OppositePower

namespace LocalSplitCell

open OppositePower

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- Prescribed all-test power formulas at the simple roots and their
negatives, with unit positive coefficients and arbitrary negative coefficients. -/
def HasSimpleRootPowerFormulas
    (P : RootDatum J (I → ℤ) (I → ℤ))
    (Q : RootDatum J' (I' → ℤ) (I' → ℤ))
    (b : P.Base) (u : J → (Ga R ⟶ G)) (v : J' → (Ga R ⟶ H))
    (e : J → J') (f : G ⟶ H) (c : J → Rˣ) (d : J → R) (q : J → ℕ) : Prop :=
  ∀ a ∈ b.support,
    HasPowerFormula f (u a) (v (e a)) (c a : R) (q a) ∧
    HasPowerFormula f (u (P.reflectionPerm a a))
      (v (Q.reflectionPerm (e a) (e a))) (d a) (q a)

variable [IsLocalRing R]
  [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}

/-- Agreement on the torus and matching positive unit power formulas at the
simple roots determine a homomorphism once all opposite formulas are supplied.
The source family has the actual simple-reflection Weyl points. -/
theorem hom_ext_of_simpleRootPowerFormulas
    (hG : IsReductive G) (hH : IsReductive H)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hQ : IsFibrewiseRootDatumOf I' H j Q)
    (b : P.Base) (u : J → (Ga R ⟶ G)) (v : J' → (Ga R ⟶ H)) (e : J → J')
    (hu : ∀ a ∈ b.support,
      IsRootParametrization i (P.root a) (u a) ∧
      IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a)))
    (hv : ∀ a ∈ b.support,
      IsRootParametrization j (Q.root (e a)) (v (e a)) ∧
      IsRootParametrization j (Q.root (Q.reflectionPerm (e a) (e a)))
        (v (Q.reflectionPerm (e a) (e a))))
    (hw : ∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a))
    (f F : G ⟶ H)
    (τ : splitTorus (Spec (CommRingCat.of R)) I ⟶
      splitTorus (Spec (CommRingCat.of R)) I')
    (hfT : i ≫ f = τ ≫ j) (hFT : i ≫ F = τ ≫ j)
    (c : J → Rˣ) (d d' : J → R) (q : J → ℕ)
    (hq : ∀ a ∈ b.support, 0 < q a)
    (hf : HasSimpleRootPowerFormulas P Q b u v e f c d q)
    (hF : HasSimpleRootPowerFormulas P Q b u v e F c d' q) : f = F := by
  classical
  have : Finite J := hP.finite
  have := hP.isReduced
  let W : ∀ a, SimpleWord P b a := fun a => (nonempty_simpleWord P b a).some
  have hn (a : J) (ha : a ∈ b.support) :
      u (P.reflectionPerm a a) ≫ f = u (P.reflectionPerm a a) ≫ F := by
    apply opposite_maps_eq_of_powerFormulas hG hH i j hi hj hmax hmax' hP hQ
      a (e a) (u a) (u (P.reflectionPerm a a))
      (v (e a)) (v (Q.reflectionPerm (e a) (e a))) (hu a ha).1
      (by simpa only [RootPairing.root_reflectionPerm,
        RootPairing.reflection_apply_self] using (hu a ha).2)
      (hv a ha).1
      (by simpa only [RootPairing.root_reflectionPerm,
        RootPairing.reflection_apply_self] using (hv a ha).2)
      f F τ τ hfT hFT (c a) (d a) (d' a) (hq a ha)
      (hf a ha).1 (hF a ha).1 (hf a ha).2 (hF a ha).2
  apply hom_ext_of_weylGenerators hG hmax hP W (fun a ha => (hu a ha).1) hw
  refine ⟨hfT.trans hFT.symm, fun a ha => (hf a ha).1.maps_eq (hF a ha).1, ?_⟩
  intro a ha
  rw [← rootPoint_comp, ← rootPoint_comp, hn a ha]

/-- The Library's chosen normalized simple-root families supply all source
Weyl conditions and all source and target root-parametrization conditions. -/
theorem hom_ext_of_chosenSimpleRootPowerFormulas
    (hG : IsReductive G) (hH : IsReductive H)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hQ : IsFibrewiseRootDatumOf I' H j Q)
    (b : P.Base) (b' : Q.Base) (e : J → J')
    (he : ∀ a ∈ b.support, e a ∈ b'.support)
    (f F : G ⟶ H)
    (τ : splitTorus (Spec (CommRingCat.of R)) I ⟶
      splitTorus (Spec (CommRingCat.of R)) I')
    (hfT : i ≫ f = τ ≫ j) (hFT : i ≫ F = τ ≫ j)
    (c : J → Rˣ) (d d' : J → R) (q : J → ℕ)
    (hq : ∀ a ∈ b.support, 0 < q a)
    (hf : HasSimpleRootPowerFormulas P Q b
      (simpleRootFamilyLocal hG i hi hmax hP b)
      (simpleRootFamilyLocal hH j hj hmax' hQ b') e f c d q)
    (hF : HasSimpleRootPowerFormulas P Q b
      (simpleRootFamilyLocal hG i hi hmax hP b)
      (simpleRootFamilyLocal hH j hj hmax' hQ b') e F c d' q) : f = F :=
  hom_ext_of_simpleRootPowerFormulas hG hH i j hi hj hmax hmax' hP hQ b _ _ e
    (simpleRootFamilyLocal_spec hG i hi hmax hP b).1
    (fun a ha => (simpleRootFamilyLocal_spec hH j hj hmax' hQ b').1 (e a) (he a ha))
    (simpleRootFamilyLocal_spec hG i hi hmax hP b).2 f F τ hfT hFT c d d' q hq hf hF

end LocalSplitCell

end Langlands.GroupScheme
