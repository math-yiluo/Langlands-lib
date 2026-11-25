/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
import all WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.AlgebraicGeometry.NonvanishingTensorPullback

/-!
# An ample invertible module from a projective closed immersion

Source: Stacks Project, Properties, Definition 01PS and Lemma 01PU; Constructions,
Definition 01MN and Lemma 01NG (blueprint: lem-weil-pbc-projective-ample-invertible).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra


/-- Uniqueness of left adjoints identifies tensor pullback with the usual pullback,
which preserves invertible modules. -/
private theorem tensorPullback_invertible {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (M : Z.Modules) [M.IsInvertible] : ((Scheme.Modules.tensorPullback g).obj M).IsInvertible := by
  let e := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction g)
  exact Scheme.Modules.IsInvertible.of_iso (e.app M).symm

/-- A module morphism out of the structure module is determined by its value at one. -/
private theorem homOfGlobalSection_appTop_one {Y : Scheme.{u}} (M : Y.Modules)
    (φ : Scheme.Modules.unit Y ⟶ M) :
    Scheme.Modules.homOfGlobalSection M (φ.app ⊤ (1 : Γ(Y, ⊤))) = φ := by
  refine (SheafOfModules.unitHomEquiv M).injective
    (Subtype.ext (funext fun V ↦ ?_))
  change (Scheme.Modules.homOfGlobalSection M (φ.app ⊤ (1 : Γ(Y, ⊤)))).app V.unop
    (1 : Γ(Y, V.unop)) = φ.app V.unop (1 : Γ(Y, V.unop))
  rw [Scheme.Modules.homOfGlobalSection_app_one, ← Scheme.Modules.Hom.app_presheaf_map]
  exact congrArg (φ.app V.unop)
    (map_one (Y.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op).hom :)

/-- Pulling back the Proj twisting sheaf O(1) along the integral-model projection and
then a closed immersion gives an invertible, absolutely ample module. The displayed
opens are exactly the non-vanishing loci of the twice-pulled coordinate sections.
The coordinates are `ULift (Fin (n+1))`, `P^n_ℤ` is `Proj` of the polynomial ring over
`ULift ℤ` with its total-degree grading, `ρ` is `ProjectiveSpace.toProjInt`, the coordinate
`T_k` is `Proj.unitToTwist (isHomogeneous_X _ k)` applied to `1`, and sections are pulled back
by the unit of the chosen tensor-pullback adjunction.
Source: Stacks Project, Properties, Definition 01PS and Lemma 01PU; Constructions,
Definition 01MN and Lemma 01NG (blueprint: lem-weil-pbc-projective-ample-invertible).

Proof:
1. The source instance proves the Proj twist invertible. Uniqueness of left adjoints
   compares tensor pullback with the usual pullback, which preserves invertibility.
   Apply this first along rho and then along the closed immersion.
2. A morphism from the structure module is recovered from its value at one. Thus
   `Scheme.Modules.nonvanishingLocus_eq_compl_support_zeroLocus`, followed by the source theorem
   `Proj.compl_support_zeroLocus_unitToTwist`, identifies the nonvanishing locus of
   each integral coordinate with its Proj basic open.
3. Apply `Scheme.Modules.nonvanishing_tensorPullback` twice. The twice-pulled coordinate locus is
   exactly the inverse image along i of `standardOpen`. The source's
   `iSup_standardOpen` proves these chart preimages cover X.
4. The source's `isAffineOpen_standardOpen` proves affineness over the affine base.
   Closed immersions are affine morphisms, so each chart preimage is affine.
5. A finite union of these compact affine opens is X, giving CompactSpace X. At any
   point choose a covering chart and transport its coordinate section along the inverse
   right unitor L ≅ L.tensorPow 1. Module isomorphisms preserve nonvanishing, so this
   affine open and exponent one witness Scheme.Modules.IsAmple.
-/
theorem projective_closedImmersion_ample_invertible (A : Type u) [CommRing A] (n : ℕ)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    (i : X ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of A))) [IsClosedImmersion i]
    (hi : i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of A)) ↘ Spec (.of A)) = f) :
    ∃ hL : ((Scheme.Modules.tensorPullback i).obj
        ((Scheme.Modules.tensorPullback
          (ProjectiveSpace.toProjInt (ULift.{u} (Fin (n + 1))) (Spec (CommRingCat.of A)))).obj
          (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1)))
            (ULift.{u} ℤ)) 1))).IsInvertible,
      @Scheme.Modules.IsAmple X ((Scheme.Modules.tensorPullback i).obj
        ((Scheme.Modules.tensorPullback
          (ProjectiveSpace.toProjInt (ULift.{u} (Fin (n + 1))) (Spec (CommRingCat.of A)))).obj
          (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1)))
            (ULift.{u} ℤ)) 1))) hL ∧
      CompactSpace X ∧
      ∃ U : ULift.{u} (Fin (n + 1)) → X.Opens,
        (∀ k, (U k : Set X) = Scheme.Modules.nonvanishingLocus
          ((Scheme.Modules.tensorPullback i).obj
            ((Scheme.Modules.tensorPullback
              (ProjectiveSpace.toProjInt (ULift.{u} (Fin (n + 1))) (Spec (CommRingCat.of A)))).obj
              (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1)))
                (ULift.{u} ℤ)) 1)))
          (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
              ((Scheme.Modules.tensorPullback
                (ProjectiveSpace.toProjInt (ULift.{u} (Fin (n + 1)))
                  (Spec (CommRingCat.of A)))).obj
                (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1)))
                  (ULift.{u} ℤ)) 1))).val.app (Opposite.op ⊤)
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
                (ProjectiveSpace.toProjInt (ULift.{u} (Fin (n + 1)))
                  (Spec (CommRingCat.of A))))).unit.app
                (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1)))
                  (ULift.{u} ℤ)) 1)).val.app (Opposite.op ⊤)
              ((Proj.unitToTwist (𝒜 := MvPolynomial.homogeneousSubmodule
                  (ULift.{u} (Fin (n + 1))) (ULift.{u} ℤ))
                  (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) k)).app ⊤
                (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1)))
                  (ULift.{u} ℤ)), ⊤)))))) ∧
        (∀ k, IsAffineOpen (U k)) ∧ (⨆ k, U k) = ⊤ := by
  classical
  have _hbase := hi
  let N := ULift.{u} (Fin (n + 1))
  let S := Spec (CommRingCat.of A)
  let ρ := ProjectiveSpace.toProjInt N S
  let M := Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1
  let B := (Scheme.Modules.tensorPullback ρ).obj M
  let L := (Scheme.Modules.tensorPullback i).obj B
  have hM : M.IsInvertible := inferInstance
  have hB : B.IsInvertible := tensorPullback_invertible ρ M
  have hL : L.IsInvertible := tensorPullback_invertible i B
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
    erw [homOfGlobalSection_appTop_one]
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
  refine ⟨hL, ?_, hcompact, U, hloc, haff, hcover⟩
  refine ⟨hcompact, fun x ↦ ?_⟩
  have hx : x ∈ ⨆ k, U k := by rw [hcover]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let b : L ≅ L.tensorPow 1 := (MonoidalCategory.rightUnitor L).symm
  refine ⟨1, Nat.zero_lt_one, b.hom.app ⊤ (s k), U k, hk, haff k, ?_⟩
  intro y
  change y ∈ U k ↔ y ∈ Scheme.Modules.nonvanishingLocus (L.tensorPow 1) (b.hom.app ⊤ (s k))
  rw [Scheme.Modules.nonvanishingLocus_iso b, ← hloc k]
  rfl

end AlgebraicGeometry
