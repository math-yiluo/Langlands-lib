/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.AffineOpenTwistVanishingIndependent
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import all WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible

/-! # Relative vanishing for the specified graph twist

Source: Stacks Project, Tags 02O5 and 02O1.
(blueprint: lem-pc-m1-projective-graph-twist-vanishing)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem projective_ample_affine (N : Type u) [Finite N]
    (S X : Scheme.{u}) [IsAffine S]
    (i : X ⟶ ℙ(N; S)) [IsClosedImmersion i] :
    ∃ hL : ((tensorPullback i).obj
        ((tensorPullback (ProjectiveSpace.toProjInt N S)).obj
          (Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1))).IsInvertible,
      @IsAmple X ((tensorPullback i).obj
        ((tensorPullback (ProjectiveSpace.toProjInt N S)).obj
          (Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1))) hL := by
  classical
  let ρ := ProjectiveSpace.toProjInt N S
  let M := Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1
  let B := (Scheme.Modules.tensorPullback ρ).obj M
  let L := (Scheme.Modules.tensorPullback i).obj B
  have hM : M.IsInvertible := inferInstance
  have hB : B.IsInvertible := AlgebraicGeometry.tensorPullback_invertible ρ M
  have hL : L.IsInvertible := AlgebraicGeometry.tensorPullback_invertible i B
  let a := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction ρ)
  let t : N → Γ(M, ⊤) := fun k ↦
    (Proj.unitToTwist (𝒜 := MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ))
      (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) k)).app ⊤
        (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)), ⊤))
  let r : N → Γ(B, ⊤) := fun k ↦ (a.unit.app M).val.app (Opposite.op ⊤) (t k)
  let s : N → Γ(L, ⊤) := fun k ↦
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app B).val.app
      (Opposite.op ⊤) (r k)
  let U : N → X.Opens := fun k ↦ i ⁻¹ᵁ ProjectiveSpace.standardOpen N S k
  have ht (k : N) : Scheme.Modules.nonvanishingLocus M (t k) =
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ))
        (MvPolynomial.X k) : Set (Proj (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)))) := by
    rw [Scheme.Modules.nonvanishingLocus_eq_compl_support_zeroLocus]
    dsimp only [t]
    erw [AlgebraicGeometry.homOfGlobalSection_appTop_one]
    exact congrArg
      (fun V : (Proj (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ))).Opens ↦
        (V : Set (Proj (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)))))
      (Proj.compl_support_zeroLocus_unitToTwist
        (Proj.exists_mem_basicOpen_homogeneousSubmodule N (ULift.{u} ℤ))
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) k))
  have hloc (k : N) : (U k : Set X) = Scheme.Modules.nonvanishingLocus L (s k) := by
    ext x
    have hp := Scheme.Modules.nonvanishing_tensorPullback i B (r k) x
    have hρ := Scheme.Modules.nonvanishing_tensorPullback ρ M (t k) (i x)
    exact (hp.trans (hρ.trans (Set.ext_iff.mp (ht k) (ρ (i x))))).symm
  have haff (k : N) : IsAffineOpen (U k) :=
    (ProjectiveSpace.isAffineOpen_standardOpen (n := N) (S := S) (i := k)).preimage i
  have hcover : (⨆ k, U k) = ⊤ :=
    i.iSup_preimage_eq_top (ProjectiveSpace.iSup_standardOpen N S)
  have hcompact : CompactSpace X := by
    apply isCompact_univ_iff.mp
    have hc := isCompact_iUnion (fun k ↦ (haff k).isCompact)
    simpa only [← TopologicalSpace.Opens.coe_iSup, hcover,
      TopologicalSpace.Opens.coe_top] using hc
  refine ⟨hL, ?_⟩
  refine ⟨hcompact, fun x ↦ ?_⟩
  have hx : x ∈ ⨆ k, U k := by rw [hcover]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let b : L ≅ L.tensorPow 1 := (MonoidalCategory.rightUnitor L).symm
  refine ⟨1, Nat.zero_lt_one, b.hom.app ⊤ (s k), U k, hk, haff k, ?_⟩
  intro y
  change y ∈ U k ↔ y ∈ Scheme.Modules.nonvanishingLocus (L.tensorPow 1) (b.hom.app ⊤ (s k))
  rw [Scheme.Modules.nonvanishingLocus_iso b, ← hloc k]
  rfl


private theorem projective_ample_affine_pullback (N : Type u) [Finite N]
    (S X : Scheme.{u}) [IsAffine S]
    (i : X ⟶ ℙ(N; S)) [IsClosedImmersion i] :
    ∃ hL : ((pullback i).obj
        ((pullback (ProjectiveSpace.toProjInt N S)).obj
          (Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1))).IsInvertible,
      @IsAmple X ((pullback i).obj
        ((pullback (ProjectiveSpace.toProjInt N S)).obj
          (Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1))) hL := by
  let t := Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1
  let ρ := ProjectiveSpace.toProjInt N S
  obtain ⟨hM, ha⟩ := projective_ample_affine N S X i
  let eρ := (Classical.choose (exists_tensorPullbackAdjunction ρ)).leftAdjointUniq
    (pullbackPushforwardAdjunction ρ)
  let ei := (Classical.choose (exists_tensorPullbackAdjunction i)).leftAdjointUniq
    (pullbackPushforwardAdjunction i)
  let e := ei.app ((tensorPullback ρ).obj t) ≪≫ (pullback i).mapIso (eρ.app t)
  have := hM
  have hL := IsInvertible.of_iso e
  exact ⟨hL, (isAmple_iff_of_iso e).mp ha⟩

/-- The graph twist is invertible and ample over affine opens of the base.
Source: Stacks Project, Tags 02O5 and 01PS; the graph construction and pullback
of the projective twisting sheaf. 
Proof: lift the graph along the separated morphism, use the closed immersion into
projective space, and pull back the standard relatively ample twisting sheaf.
The finite coordinate chart cover proves ampleness directly for any finite
coordinate type; the empty chart cover forces the source empty. -/
private theorem graph_twist_isInvertible_and_affine_ample
    {Y S T : Scheme.{u}} [IsNoetherian S]
    (g : S ⟶ T) [IsSeparated g] (p : Y ⟶ S) [IsProper p]
    (N : Type u) [Finite N] (j : Y ⟶ ℙ(N; T)) [IsClosedImmersion j]
    (hj : j ≫ (ℙ(N; T) ↘ T) = p ≫ g) :
    let L := (pullback j).obj
      ((pullback (ProjectiveSpace.toProjInt N T)).obj
        (Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1))
    ∃ _hL : L.IsInvertible,
      ∀ V : S.Opens, IsAffineOpen V →
        ∃ hV : (L.restrict (p ⁻¹ᵁ V).ι).IsInvertible,
          @IsAmple (p ⁻¹ᵁ V).toScheme (L.restrict (p ⁻¹ᵁ V).ι) hV := by
  let t := Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1
  let L := (pullback j).obj ((pullback (ProjectiveSpace.toProjInt N T)).obj t)
  have hL : L.IsInvertible := inferInstance
  refine ⟨hL, fun V hV ↦ ?_⟩
  have : IsAffine V.toScheme := hV
  let i := ProjectiveSpace.liftBaseChange p j hj.symm
  have : IsClosedImmersion i := inferInstance
  have hi : p = i ≫ (ℙ(N; S) ↘ S) :=
    (ProjectiveSpace.liftBaseChange_over p j hj.symm).symm
  have hw : (p ∣_ V) ≫ V.ι = ((p ⁻¹ᵁ V).ι ≫ i) ≫ (ℙ(N; S) ↘ S) := by
    rw [morphismRestrict_ι, hi, Category.assoc]
  let k := ProjectiveSpace.liftBaseChange (p ∣_ V) ((p ⁻¹ᵁ V).ι ≫ i) hw
  have hk : IsClosedImmersion k := by
    apply MorphismProperty.of_isPullback
      (ProjectiveSpace.isPullback_liftBaseChange (p ∣_ V)
        (show IsPullback (p ⁻¹ᵁ V).ι (p ∣_ V) (i ≫ (ℙ(N; S) ↘ S)) V.ι from
          hi ▸ (isPullback_morphismRestrict p V).flip) hw)
    infer_instance
  obtain ⟨hK, ha⟩ := projective_ample_affine_pullback N V.toScheme (p ⁻¹ᵁ V).toScheme k
  have he : k ≫ ProjectiveSpace.toProjInt N V.toScheme =
      ((p ⁻¹ᵁ V).ι ≫ j) ≫ ProjectiveSpace.toProjInt N T := by
    rw [ProjectiveSpace.liftBaseChange_toProjInt, Category.assoc,
      ProjectiveSpace.liftBaseChange_toProjInt, Category.assoc]
  let e : ((pullback k).obj
      ((pullback (ProjectiveSpace.toProjInt N V.toScheme)).obj t)) ≅
      L.restrict (p ⁻¹ᵁ V).ι := (pullbackComp k (ProjectiveSpace.toProjInt N V.toScheme)).app t ≪≫
    (pullbackCongr he).app t ≪≫
    ((pullbackComp ((p ⁻¹ᵁ V).ι ≫ j) (ProjectiveSpace.toProjInt N T)).app t).symm ≪≫
    ((pullbackComp (p ⁻¹ᵁ V).ι j).app
      ((pullback (ProjectiveSpace.toProjInt N T)).obj t)).symm ≪≫
    ((restrictFunctorIsoPullback (p ⁻¹ᵁ V).ι).app L).symm
  have : ((pullback k).obj
      ((pullback (ProjectiveSpace.toProjInt N V.toScheme)).obj t)).IsInvertible := hK
  have hR := IsInvertible.of_iso e
  exact ⟨hR, (isAmple_iff_of_iso e).mp ha⟩

/-- Relative Serre vanishing for the integral twist pulled back along a projective graph.

Source: Stacks Project, Tag 02O5, the graph construction of L, and Tag 02O1.
(blueprint: lem-pc-m1-projective-graph-twist-vanishing)

Proof: because g is separated, the lift of j to projective space over S is a closed
immersion. Compatibility with the integral projection identifies its pulled-back O(1)
with L. For nonempty finite N, reindex coordinates by ULift (Fin (m+1)); the standard
projective twisting sheaf is relatively ample. Hence L is ample on the inverse image
of each affine open of S. The structure module on Y is coherent, since p is finite
type over Noetherian S, and is quasi-coherent. Apply relative Serre vanishing (Tag 02O1)
to this structure module: affine-base vanishing gives a threshold on each member of a
finite affine cover of S; the maximum gives a common threshold for all positive
higher images. The unit tensor isomorphism identifies the resulting twists with
L.tensorPow. If N is empty, j forces Y empty; its module category is zero and one
may take threshold zero. -/
theorem exists_isZero_higherDirectImage_graph_twist
    {Y S T : Scheme.{u}} [IsNoetherian S]
    (g : S ⟶ T) [IsSeparated g] (p : Y ⟶ S) [IsProper p]
    (N : Type u) [Finite N] (j : Y ⟶ ℙ(N; T)) [IsClosedImmersion j]
    (hj : j ≫ (ℙ(N; T) ↘ T) = p ≫ g)
    [HasInjectiveResolutions Y.Modules] :
    let L := (pullback j).obj
      ((pullback (ProjectiveSpace.toProjInt N T)).obj
        (Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1))
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ q : ℕ, 0 < q →
      IsZero ((higherDirectImage p q).obj (L.tensorPow n)) := by
  let L := (pullback j).obj
    ((pullback (ProjectiveSpace.toProjInt N T)).obj
      (Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1))
  obtain ⟨hL, hA⟩ := graph_twist_isInvertible_and_affine_ample g p N j hj
  have : L.IsInvertible := hL
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : (MonoidalCategory.tensorUnit Y.Modules).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit.{u, u, u}
  have : SheafOfModules.IsInvertible (R := Y.ringCatSheaf)
      (MonoidalCategory.tensorUnit Y.Modules) :=
    IsInvertible.sheafOfModules_isInvertible _
  have : (MonoidalCategory.tensorUnit Y.Modules).IsFiniteLocallyFree :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have : (MonoidalCategory.tensorUnit Y.Modules).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have hF : RingedSpace.IsCoherent Y.toRingedSpace (MonoidalCategory.tensorUnit Y.Modules) :=
    (isCoherent_iff_isQuasicoherent_and_isFiniteType Y _).mpr
      ⟨inferInstance, inferInstance⟩
  classical
  have hv (V : S.affineOpens) :=
    exists_isZero_higherDirectImage_twist_on_affine_open p
      (MonoidalCategory.tensorUnit Y.Modules) hF L
      V.1 V.2 (hA V.1 V.2)
  choose d hd using hv
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun V : S.affineOpens ↦ (V.1 : Set S))
    (fun V ↦ V.1.isOpen) (fun x _ ↦ by
      have hx : x ∈ ⨆ V : S.affineOpens, V.1 := by
        rw [iSup_affineOpens_eq_top S]
        trivial
      obtain ⟨V, hxV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨V, hxV⟩)
  refine ⟨s.sup d, fun n hn q hq ↦ ?_⟩
  have hzero : IsZero ((higherDirectImage p q).obj
      (tensorObj (MonoidalCategory.tensorUnit Y.Modules) (L.tensorPow n))) := by
    refine isZero_of_iSup_eq_top _ (fun V : s ↦ V.val.1) ?_
      (fun V ↦ hd V.val n ((Finset.le_sup V.property).trans hn) q hq)
    apply eq_top_iff.2
    intro x _
    obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hx⟩
  exact hzero.of_iso
    ((higherDirectImage p q).mapIso (MonoidalCategory.leftUnitor (L.tensorPow n)).symm)

end AlgebraicGeometry.Scheme.Modules
