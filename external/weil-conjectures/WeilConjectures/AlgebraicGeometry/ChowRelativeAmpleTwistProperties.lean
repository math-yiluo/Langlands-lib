/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist


/-! Auxiliary decomposition for Chow relative ampleness. -/

@[expose] public section
universe u
open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry

private theorem tensorPullback_invertible {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) [L.IsInvertible] :
    ((Scheme.Modules.tensorPullback f).obj L).IsInvertible := by
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction f
  exact Scheme.Modules.IsInvertible.of_iso
    ((adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction f)).app L).symm

private theorem tensorPullback_pair_iso {X Y Z T : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ T) (c : X ⟶ Z) (d : Z ⟶ T)
    (h : a ≫ b = c ≫ d) (L : T.Modules) :
    Nonempty ((Scheme.Modules.tensorPullback a).obj
        ((Scheme.Modules.tensorPullback b).obj L) ≅
      (Scheme.Modules.tensorPullback c).obj ((Scheme.Modules.tensorPullback d).obj L)) := by
  obtain ⟨e⟩ := Scheme.Modules.nonempty_tensorPullbackComp a b
  obtain ⟨e'⟩ := Scheme.Modules.nonempty_tensorPullbackComp c d
  exact ⟨(e.app L).symm ≪≫ (eqToIso (congrArg
    (fun f ↦ (Scheme.Modules.tensorPullback f).obj L) h)) ≪≫ e'.app L⟩

-- Apply the affine-base theorem after identifying the base with its section spectrum.
private theorem projective_ample_affine (m : ℕ) (S X : Scheme.{u}) [IsAffine S]
    (i : X ⟶ ℙ(ULift.{u} (Fin (m + 1)); S)) [IsClosedImmersion i] :
    ∃ hL : ((Scheme.Modules.tensorPullback i).obj
        ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
          (ULift.{u} (Fin (m + 1))) S)).obj
          (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
            (ULift.{u} ℤ)) 1))).IsInvertible,
      @Scheme.Modules.IsAmple X ((Scheme.Modules.tensorPullback i).obj
        ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
          (ULift.{u} (Fin (m + 1))) S)).obj
          (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
            (ULift.{u} ℤ)) 1))) hL := by
  let n := ULift.{u} (Fin (m + 1))
  let t := Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) 1
  have : IsClosedImmersion (ProjectiveSpace.map n S.toSpecΓ) :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map n S.toSpecΓ).flip
      inferInstance
  obtain ⟨hN, hample, _⟩ := projective_closedImmersion_ample_invertible
    Γ(S, ⊤) m X (i ≫ ProjectiveSpace.map n S.toSpecΓ ≫ _)
      (i ≫ ProjectiveSpace.map n S.toSpecΓ) rfl
  obtain ⟨e⟩ := tensorPullback_pair_iso
    (i ≫ ProjectiveSpace.map n S.toSpecΓ) (ProjectiveSpace.toProjInt n _) i
    (ProjectiveSpace.toProjInt n S) (by simp [Category.assoc]) t
  have := hN
  have hL := Scheme.Modules.IsInvertible.of_iso e
  exact ⟨hL, (Scheme.Modules.isAmple_iff_of_iso e).mp hample⟩

-- Restriction to an affine open is a base change of the projective closed immersion.
private theorem projective_ample_affine_open (m : ℕ) (S X : Scheme.{u})
    (f : X ⟶ S) (i : X ⟶ ℙ(ULift.{u} (Fin (m + 1)); S)) [IsClosedImmersion i]
    (hi : f = i ≫ (ℙ(ULift.{u} (Fin (m + 1)); S) ↘ S))
    (V : S.Opens) (hV : IsAffineOpen V) :
    ∃ hL : ((Scheme.Modules.tensorPullback (f ⁻¹ᵁ V).ι).obj
        ((Scheme.Modules.tensorPullback i).obj
          ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
            (ULift.{u} (Fin (m + 1))) S)).obj
            (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
              (ULift.{u} ℤ)) 1)))).IsInvertible,
      @Scheme.Modules.IsAmple (f ⁻¹ᵁ V).toScheme
        ((Scheme.Modules.tensorPullback (f ⁻¹ᵁ V).ι).obj
          ((Scheme.Modules.tensorPullback i).obj
            ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
              (ULift.{u} (Fin (m + 1))) S)).obj
              (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
                (ULift.{u} ℤ)) 1)))) hL := by
  let n := ULift.{u} (Fin (m + 1))
  let t := Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) 1
  have : IsAffine V.toScheme := hV
  have hw : (f ∣_ V) ≫ V.ι = ((f ⁻¹ᵁ V).ι ≫ i) ≫ (ℙ(n; S) ↘ S) := by
    rw [morphismRestrict_ι, hi, Category.assoc]
  let k := ProjectiveSpace.liftBaseChange (f ∣_ V) ((f ⁻¹ᵁ V).ι ≫ i) hw
  have hk : IsClosedImmersion k := by
    apply MorphismProperty.of_isPullback
      (ProjectiveSpace.isPullback_liftBaseChange (f ∣_ V)
        (show IsPullback (f ⁻¹ᵁ V).ι (f ∣_ V) (i ≫ (ℙ(n; S) ↘ S)) V.ι from
          hi ▸ (isPullback_morphismRestrict f V).flip) hw)
    infer_instance
  obtain ⟨hN, hample⟩ := projective_ample_affine m V.toScheme (f ⁻¹ᵁ V).toScheme k
  obtain ⟨e⟩ := tensorPullback_pair_iso k (ProjectiveSpace.toProjInt n V.toScheme)
    ((f ⁻¹ᵁ V).ι ≫ i) (ProjectiveSpace.toProjInt n S)
    (ProjectiveSpace.liftBaseChange_toProjInt _ _ hw) t
  obtain ⟨c⟩ := Scheme.Modules.nonempty_tensorPullbackComp (f ⁻¹ᵁ V).ι i
  let e' := e ≪≫ c.app ((Scheme.Modules.tensorPullback
    (ProjectiveSpace.toProjInt n S)).obj t)
  have := hN
  have hL := Scheme.Modules.IsInvertible.of_iso e'
  exact ⟨hL, (Scheme.Modules.isAmple_iff_of_iso e').mp hample⟩

-- The original existential invertibility witness is independent of both conjuncts.
set_option linter.unusedVariables.funArgs false in
/-- Auxiliary component of the Chow relative ampleness theorem.
Source: Stacks Project, Cohomology of Schemes, Proposition 30.19.1 (Tag 02O5).
Proof in words: this strict component is obtained by the tensor-pullback
functoriality (for the isomorphism component) or by the affine-local standard
chart argument (for the properties component), exactly as in the parent proof.
(blueprint: lem-pc-chow-relative-ample-twist-properties) -/
theorem chow_relative_ample_twist_properties (m : ℕ) (S Z X' : Scheme.{u})
    (g : Z ⟶ S) (π : X' ⟶ Z)
    (j : X' ⟶ ℙ(ULift.{u} (Fin (m + 1)); S))
    [IsProper g] [IsProper π] [IsImmersion j]
    (hj : π ≫ g = j ≫ (ℙ(ULift.{u} (Fin (m + 1)); S) ↘ S)) :
      ∃ hL : ((Scheme.Modules.tensorPullback j).obj
          ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
            (ULift.{u} (Fin (m + 1))) S)).obj
            (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
              (ULift.{u} ℤ)) 1))).IsInvertible,
        (∀ V : S.Opens, IsAffineOpen V →
          ∃ hV : ((Scheme.Modules.tensorPullback ((π ≫ g) ⁻¹ᵁ V).ι).obj
              ((Scheme.Modules.tensorPullback j).obj
              ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
                (ULift.{u} (Fin (m + 1))) S)).obj
                (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
                  (ULift.{u} ℤ)) 1)))).IsInvertible,
            @Scheme.Modules.IsAmple ((π ≫ g) ⁻¹ᵁ V).toScheme
              ((Scheme.Modules.tensorPullback ((π ≫ g) ⁻¹ᵁ V).ι).obj
                  ((Scheme.Modules.tensorPullback j).obj
                  ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
                    (ULift.{u} (Fin (m + 1))) S)).obj
                    (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
                      (ULift.{u} ℤ)) 1)))) hV) ∧
        (∀ W : Z.Opens, IsAffineOpen W →
          ∃ hW : ((Scheme.Modules.tensorPullback (π ⁻¹ᵁ W).ι).obj
              ((Scheme.Modules.tensorPullback j).obj
              ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
                (ULift.{u} (Fin (m + 1))) S)).obj
                (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
                  (ULift.{u} ℤ)) 1)))).IsInvertible,
            @Scheme.Modules.IsAmple (π ⁻¹ᵁ W).toScheme
              ((Scheme.Modules.tensorPullback (π ⁻¹ᵁ W).ι).obj
                  ((Scheme.Modules.tensorPullback j).obj
                  ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt
                    (ULift.{u} (Fin (m + 1))) S)).obj
                    (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (m + 1)))
                      (ULift.{u} ℤ)) 1)))) hW) := by
  let n := ULift.{u} (Fin (m + 1))
  let t := Proj.twist (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) 1
  let L := (Scheme.Modules.tensorPullback j).obj
    ((Scheme.Modules.tensorPullback (ProjectiveSpace.toProjInt n S)).obj t)
  have hP := tensorPullback_invertible (ProjectiveSpace.toProjInt n S) t
  have hL : L.IsInvertible := tensorPullback_invertible j _
  have : IsProper (j ≫ (ℙ(n; S) ↘ S)) := by
    rw [← hj]
    infer_instance
  have : IsProper j := IsProper.of_comp j (ℙ(n; S) ↘ S)
  have hjclosed : IsClosedImmersion j :=
    IsClosedImmersion.of_isPreimmersion j j.isClosedMap.isClosed_range
  let k := ProjectiveSpace.liftBaseChange π j hj
  have hkclosed : IsClosedImmersion k := inferInstance
  obtain ⟨e⟩ := tensorPullback_pair_iso j (ProjectiveSpace.toProjInt n S)
    k (ProjectiveSpace.toProjInt n Z)
    (ProjectiveSpace.liftBaseChange_toProjInt π j hj).symm t
  refine ⟨hL, ?_, ?_⟩
  · intro V hV
    exact projective_ample_affine_open m S X' (π ≫ g) j hj V hV
  · intro W hW
    obtain ⟨hN, hample⟩ := projective_ample_affine_open m Z X' π k
      (ProjectiveSpace.liftBaseChange_over π j hj).symm W hW
    have hM := tensorPullback_invertible (π ⁻¹ᵁ W).ι L
    let eW := (Scheme.Modules.tensorPullback (π ⁻¹ᵁ W).ι).mapIso e
    exact ⟨hM, (Scheme.Modules.isAmple_iff_of_iso eW).mpr hample⟩

end AlgebraicGeometry
