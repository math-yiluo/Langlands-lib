/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore
import WeilConjectures.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferRetract

/-! # Transfer from a filtered finite etale cover through extension by zero

Source: Stacks Project, proof of 03SD (lemma-vanishing-easier), paragraphs 2--4.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

/-- Transfer the constant case using a given finite etale cover, filtration and retraction.

Source: Stacks Project, 03SD (lemma-vanishing-easier), paragraphs 2--4; 05K0
(lemma-quasi-finite-separated-pass-through-finite), 0GJ1 (lemma-compatible-shriek-push-finite),
0A5C (lemma-ses-statements), 0A5D (lemma-finite-pushforward).
(blueprint: k1-filtered-finite-cover-lower-shriek-transfer)

Proof:
1. Factor j composed with v by Zariski's main theorem (05K0) as an open immersion
V -> T followed by a finite map T -> X. Replace T by the reduced closed closure Y
of V. Since V is etale over an open of reduced X, V is reduced and still embeds as
a dense open j' in Y. The induced finite map p : Y -> X makes Y a reduced separated
finite-type curve: integral incomparability bounds its dimension by that of X.
2. The open V in p^{-1}(U) is also closed. Indeed V -> p^{-1}(U) is finite by
finite permanence over a separated U-scheme. It is dense because V is dense in Y,
so its image is all of p^{-1}(U). A surjective open immersion is an isomorphism,
giving the cartesian square with j', v, p, j.
3. Apply the supplied constant-case hypothesis to Y and j'. The filtration's
monomorphisms give short exact sequences with the specified constant cokernels.
Extension by zero is exact. Starting at the zero sheaf, short-exact devissage
(0A5C) inductively gives the assertions for j'_! W i, up to i = n. Transport
along the given terminal isomorphism to obtain them for j'_! v^* G.
4. Finite pushforward (0A5D) and the exchange isomorphism of 0GJ1 give the
assertions for j_! v_* v^* G. Apply j_! to the unit and the supplied retraction;
functoriality gives a retraction of this sheaf onto j_! G. The assertions pass
to this retract. For conditional assertions all coefficient conditions pass to
the larger sheaf: both are killed by r; if a nonzero stalk of G is p-primary
then r = p, and if G has invertible torsion then either r is invertible or G is
zero. Finite locally constant pullback, finite pushforward and extension by zero
preserve constructibility. Vanishing and finiteness descend along the cohomology
retraction, while naturality makes field-extension and open-restriction maps
retracts of the corresponding maps for the larger sheaf, preserving bijectivity
and surjectivity. This proves all eight assertions for j_! G.
The degree and connectedness of the cover are not needed once its filtration and
retraction have been supplied. -/
theorem filteredFiniteCoverLowerShriekTransfer {k : Type u} [Field k] [IsAlgClosed k]
    {X U V : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (r : ℕ) [Fact r.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    [Scheme.IsFiniteLocallyConstantSheaf G] (v : V ⟶ U) [IsFinite v] [Etale v]
    (n : ℕ)
    (W : ℕ → Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    (ι : ∀ i, W i ⟶ W (i + 1)) (hzero : IsZero (W 0))
    (hend : Nonempty (W n ≅
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj G))
    (hquot : ∀ i < n, Mono (ι i) ∧ Nonempty (cokernel (ι i) ≅
      (constantSheaf V.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))).obj
        (ModuleCat.of _ (ULift.{u + 1} (ZMod r)))))
    (ρ : (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj
      ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj G) ⟶ G)
    (hρ : (Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).unit.app G ≫ ρ = 𝟙 G)
    (hconstant : ∀ {Y T : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsCurve g] [IsReduced Y]
      (a : T ⟶ Y) [IsOpenImmersion a],
      IsCurve.Assertions (ULift.{u + 1} (ZMod r)) g
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) a).obj
          ((constantSheaf T.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod r)))))) :
    IsCurve.Assertions (ULift.{u + 1} (ZMod r)) f
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) j).obj G) := by
  apply filteredFiniteCoverLowerShriekTransfer_retract f j r G v
    (filteredFiniteCoverLowerShriekTransfer_core f j r G v n W ι hzero hend
      hquot hconstant) ρ hρ

end AlgebraicGeometry.IsCurve
