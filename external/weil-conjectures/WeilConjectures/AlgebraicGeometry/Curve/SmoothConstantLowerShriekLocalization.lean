/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions
import WeilConjectures.AlgebraicGeometry.Curve.DisjointOpenPrimeAssertions
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
import WeilConjectures.AlgebraicGeometry.Curve.UnderlyingAbelianAssertions

/-! # Localization of smooth constant-coefficient curve assertions

Source: Stacks Project, Tags 03SG, 0GJA and 0A5C, proofs.
(blueprint: lem-pbc-u2-smooth-constant-lower-shriek-localization)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

/-- The constant-coefficient calculations on all smooth curves imply the corresponding
extension-by-zero calculations for every open immersion into a smooth curve.
Source: Stacks Project, Tags 03SG, 0GJA (dense-open localization) and 0A5C (finite sums).
(blueprint: lem-pbc-u2-smooth-constant-lower-shriek-localization)

Proof: Put V = image(j) and E = X minus closure(V). These are disjoint opens, and
V union E is dense, by the dense coborder lemma. The constant finite-coefficient sheaf
is constructible and annihilated by r. Apply H to X and dense-open prime-torsion
localization to V union E. The disjoint-open comparison then gives the assertions
for V_! of the restriction of the constant sheaf. Pullback preserves constant sheaves.
Identify U with V by the canonical open-immersion image isomorphism. Composition of
extension by zero, and its identification with inverse pullback for an isomorphism,
identify this sheaf with j_! of the constant sheaf on U. Transport all eight assertions
along that isomorphism. Smoothness supplies reducedness; no component decomposition
is needed. Empty opens and empty schemes are covered by the same two-open argument. -/
theorem smoothConstantLowerShriekAssertions_of_constant
    {k : Type u} [Field k] [IsAlgClosed k] (r : ℕ) [Fact r.Prime]
    (H : ∀ {C : Scheme.{u}} (g : C ⟶ Spec (.of k)) [IsCurve g] [Smooth g],
      IsCurve.Assertions (ULift.{u + 1} (ZMod r)) g
        (Etale.constantModSheaf (ULift.{u + 1} (ZMod r)) C r))
    {X U : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [Smooth f]
    (j : U ⟶ X) [IsOpenImmersion j] :
    IsCurve.Assertions (ULift.{u + 1} (ZMod r)) f
      ((Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) j).obj
        (Etale.constantModSheaf (ULift.{u + 1} (ZMod r)) U r)) := by
  classical
  let R := ULift.{u + 1} (ZMod r)
  let A := ModuleCat.{u + 1} R
  let N := ModuleCat.of R (R ⧸ (Ideal.span {(r : R)} : Ideal R))
  let F := Etale.constantModSheaf R X r
  have : IsRegular X := IsRegular.of_smooth f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have : Scheme.IsFiniteLocallyConstantSheaf F := by
    dsimp [F, Etale.constantModSheaf]
    infer_instance
  have : Scheme.IsConstructibleSheaf F :=
    ⟨Scheme.Stratification.trivial X, fun _ ↦
      Scheme.IsFiniteLocallyConstantSheaf.upperStar _ _⟩
  have hF : r • 𝟙 F = 0 := by
    dsimp [F, Etale.constantModSheaf]
    rw [← (constantSheaf _ _).map_id, ← Functor.map_nsmul,
      ← (constantSheaf _ _).map_zero]
    congr 1
    ext
    simp [← Nat.cast_smul_eq_nsmul R]
  let V : X.Opens := j.opensRange
  let E : X.Opens := ⟨(closure (V : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
  let O : Fin 2 → X.Opens := ![V, E]
  have hdisj : Pairwise (fun a b ↦ Disjoint (O a : Set X) (O b)) := by
    have hd : Disjoint (V : Set X) (E : Set X) :=
      Set.disjoint_left.mpr (fun _ hx hxc ↦ hxc (subset_closure hx))
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [O, hd.symm]
  have hdense : Dense ((⨆ a, O a : X.Opens) : Set X) := by
    have heq : ((⨆ a, O a : X.Opens) : Set X) =
        (V : Set X) ∪ (closure (V : Set X))ᶜ := by
      ext x
      simp [O, E, Fin.exists_fin_two]
    rw [heq, ← coborder_eq_union_closure_compl]
    exact dense_coborder
  have hsum := (assertions_iff_dense_open_prime R f r F hF (⨆ a, O a) hdense).mp (H f)
  have hV := ((assertions_iff_disjoint_open_prime R f r F hF 2 O hdisj).mp hsum) 0
  change Assertions R f
    ((Etale.openImmersionLowerShriek A V.ι).obj ((Etale.upperStar A V.ι).obj F)) at hV
  let e : U ≅ V.toScheme := IsOpenImmersion.isoOfRangeEq j V.ι
    (by simp [V, Scheme.Opens.range_ι])
  have he : e.inv ≫ j = V.ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  let ec : ((Etale.upperStar A V.ι).obj F) ≅ Etale.constantModSheaf R V.toScheme r :=
    (Scheme.upperStarConstantSheafIso A V.ι).app N
  let ei : ((Etale.openImmersionLowerShriek A V.ι).obj ((Etale.upperStar A V.ι).obj F)) ≅
      ((Etale.openImmersionLowerShriek A j).obj (Etale.constantModSheaf R U r)) :=
    (Etale.openImmersionLowerShriek A V.ι).mapIso ec ≪≫
      eqToIso (by simp only [he]) ≪≫
      (Etale.openImmersionLowerShriekComp A e.inv j).app
        (Etale.constantModSheaf R V.toScheme r) ≪≫
      (Etale.openImmersionLowerShriek A j).mapIso
        ((Etale.upperStarIsoOpenImmersionLowerShriekInv A e).symm.app
          (Etale.constantModSheaf R V.toScheme r)) ≪≫
      (Etale.openImmersionLowerShriek A j).mapIso ((Scheme.upperStarConstantSheafIso A e.hom).app N)
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have : Scheme.IsConstructibleSheaf ((Etale.upperStar A V.ι).obj F) :=
    Scheme.IsConstructibleSheaf.upperStar _ _
  have : TopologicalSpace.NoetherianSpace V :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι :=
    ⟨fun W _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : Scheme.IsConstructibleSheaf
      ((Etale.openImmersionLowerShriek A V.ι).obj ((Etale.upperStar A V.ι).obj F)) :=
    Scheme.IsConstructibleSheaf.openImmersionLowerShriek V.ι V.closedComplement
      (by rw [Scheme.Opens.range_closedComplement, Scheme.Opens.range_ι]) _
  have : Scheme.IsConstructibleSheaf
      ((Etale.openImmersionLowerShriek A j).obj (Etale.constantModSheaf R U r)) :=
    Scheme.IsConstructibleSheaf.of_iso ei
  exact assertions_of_underlying_abelian_iso f
    ((sheafCompose _ (forget₂ A AddCommGrpCat.{u + 1})).mapIso ei) hV

end AlgebraicGeometry.IsCurve
