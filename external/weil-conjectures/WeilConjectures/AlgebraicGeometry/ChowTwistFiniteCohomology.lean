/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProjectivePushforwardFiniteTypeIndependent
import WeilConjectures.AlgebraicGeometry.ProjectiveAffineFiniteCohomologyIndependent
import WeilConjectures.AlgebraicGeometry.ProjectiveGraphTwistVanishing
import WeilConjectures.AlgebraicGeometry.LerayAcyclicPushforwardLinearComparison
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import all WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-! # Finite cohomology of a sufficiently large Chow twist

Source: Stacks Project, Tag 02O5, proposition-proper-pushforward-coherent,
construction of the module pi_* L^n.
(blueprint: lem-pc-q2-chow-twist-finite-cohomology)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The analytic part of the Chow construction, for a specified projective model.
No integrality, birationality, or generic-stalk condition is required.

Source: Stacks Project, Tag 02O5, proposition-proper-pushforward-coherent,
paragraphs defining L and G and applying the relative Leray spectral sequence.
(blueprint: lem-pc-q2-chow-twist-finite-cohomology)

Proof:
1. Put p = pi followed by i. The scheme X is Noetherian because it is proper
   over the affine Noetherian T. Separatedness of f gives a closed graph embedding
   of Y into projective space over X. Relative graph-twist vanishing chooses n
   killing every positive higher direct image of L.tensorPow n along p.
2. Invertibility of L makes its powers quasi-coherent and finitely presented.
   The independent projective pushforward argument gives finite type of p_* L^n:
   degree-zero projective finiteness on affine opens and quasi-coherent localization
   suffice. Quasi-coherence and the locally Noetherian finite-type criterion give
   coherence. Transport this along pushforwardComp pi i to i_* pi_* L^n.
3. The given closed embedding over T gives finite cohomology of L^n over Gamma(T,O).
   A linear Leray comparison for p, whose positive higher images vanish, identifies
   these groups with the cohomology of p_* L^n. The pushforwardComp isomorphism
   identifies the latter with that of i_* pi_* L^n. Restrict scalars along f.appTop
   and transport finite generation through the two linear equivalences. -/
theorem exists_chow_twist_finite_cohomology {X W T Y : Scheme.{u}}
    (f : X ⟶ T) [IsProper f] [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    (i : W ⟶ X) [IsClosedImmersion i] (π : Y ⟶ W) [IsProper π]
    (N : Type u) [Finite N] (j : Y ⟶ ℙ(N; T)) [IsClosedImmersion j]
    (hj : j ≫ (ℙ(N; T) ↘ T) = π ≫ i ≫ f) :
    let L := (pullback j).obj
      ((pullback (ProjectiveSpace.toProjInt N T)).obj
        (Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1))
    ∃ n : ℕ,
      RingedSpace.IsCoherent X.toRingedSpace
        ((pushforward i).obj ((pushforward π).obj (L.tensorPow n))) ∧
      (∀ q : ℕ,
        letI : Module Γ(T, ⊤)
          (((pushforward i).obj ((pushforward π).obj (L.tensorPow n))).H q) :=
            Module.compHom _ f.appTop.hom
        Module.Finite Γ(T, ⊤)
          (((pushforward i).obj ((pushforward π).obj (L.tensorPow n))).H q)) := by
  classical
  let L := (pullback j).obj
    ((pullback (ProjectiveSpace.toProjInt N T)).obj
      (Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1))
  let p := π ≫ i
  have hp : IsProper p := inferInstance
  have hT : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian T.toSpecΓ
  have hX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : _root_.CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hXN : IsNoetherian X := ⟨⟩
  have : EnoughInjectives Y.Modules := (isGrothendieckAbelian Y).enoughInjectives
  have hI : HasInjectiveResolutions Y.Modules := inferInstance
  have hdiag : j ≫ (ℙ(N; T) ↘ T) = p ≫ f := by
    simpa only [p, Category.assoc] using hj
  obtain ⟨n, hn⟩ := exists_isZero_higherDirectImage_graph_twist f p N j hdiag
  have hL : L.IsInvertible := inferInstance
  have hLn : (L.tensorPow n).IsQuasicoherent := inferInstance
  have hLs : SheafOfModules.IsInvertible (R := Y.ringCatSheaf) (L.tensorPow n) :=
    IsInvertible.sheafOfModules_isInvertible _
  have : (L.tensorPow n).IsFiniteLocallyFree :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have hFP : (L.tensorPow n).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  let k := ProjectiveSpace.liftBaseChange p j hdiag.symm
  have hk : IsClosedImmersion k := inferInstance
  have hG : ((pushforward p).obj (L.tensorPow n)).IsFiniteType :=
    isFiniteType_projective_pushforward_independent p N k
      (ProjectiveSpace.liftBaseChange_over p j hdiag.symm) (L.tensorPow n)
  have hGq : ((pushforward p).obj (L.tensorPow n)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated p (L.tensorPow n)
  let e := (pushforwardComp π i).app (L.tensorPow n)
  have hG' : ((pushforward i).obj ((pushforward π).obj
      (L.tensorPow n))).IsFiniteType :=
    finiteType_of_iso.{u, u, u} e.symm
  have hGq' : ((pushforward i).obj ((pushforward π).obj
      (L.tensorPow n))).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hGq
  refine ⟨n, (isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mpr
    ⟨hGq', inferInstance⟩, ?_⟩
  intro q
  let : Module Γ(T, ⊤) ((L.tensorPow n).H q) :=
    Module.compHom _ (p ≫ f).appTop.hom
  have hfin : Module.Finite Γ(T, ⊤) ((L.tensorPow n).H q) := by
    change letI : Module Γ(T, ⊤) ((L.tensorPow n).H q) :=
      Module.compHom _ (p ≫ f).appTop.hom
      Module.Finite Γ(T, ⊤) ((L.tensorPow n).H q)
    rw [← hdiag]
    exact finite_H_projective_affine_independent N j (L.tensorPow n) q
  let : Module Γ(T, ⊤) (((pushforward p).obj (L.tensorPow n)).H q) :=
    Module.compHom _ f.appTop.hom
  let : Module Γ(T, ⊤)
      (((pushforward i).obj ((pushforward π).obj (L.tensorPow n))).H q) :=
    Module.compHom _ f.appTop.hom
  obtain ⟨a⟩ := nonempty_linearEquiv_H_pushforward_of_higherDirectImage_vanishing
    p f (L.tensorPow n) (hn n le_rfl) q
  let b : (((pushforward p).obj (L.tensorPow n)).H q) ≃ₗ[Γ(T, ⊤)]
      (((pushforward i).obj ((pushforward π).obj (L.tensorPow n))).H q) :=
    { (H.mapLinearEquiv e.symm q).toAddEquiv with
      map_smul' := fun r x ↦ (H.mapLinearEquiv e.symm q).map_smul (f.appTop r) x }
  exact Module.Finite.of_surjective (a.symm.trans b).toLinearMap
    (a.symm.trans b).surjective

end AlgebraicGeometry.Scheme.Modules
