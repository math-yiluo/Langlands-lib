import Langlands.GroupScheme.IntegralModel.Smoothening.SmoothSections
import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.Core
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # Products and global functions of flat schemes over a PID -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.FlatGlobalSectionsProduct

/-- Global functions on a flat scheme over a PID form a flat module. -/
instance flat_sections {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : Over (Spec (CommRingCat.of R))) [Flat X.hom] :
    Module.Flat R ((algΓ (CommRingCat.of R)).obj X).unop := by
  have := Langlands.GroupScheme.IntegralModel.Smoothening.isTorsionFree_sections X
  infer_instance

/-- The structural map on global functions of a flat scheme over a PID is flat. -/
theorem flat_appTop {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : Over (Spec (CommRingCat.of R))) [Flat X.hom] : X.hom.appTop.hom.Flat := by
  have hf : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appTop).hom.Flat :=
    RingHom.flat_algebraMap_iff.mpr (flat_sections X)
  have hi : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have h := hi.comp hf
  change (((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appTop).hom).Flat at h
  simpa only [Iso.hom_inv_id_assoc] using h

/-- Global functions take a product of qcqs schemes to a pushout of rings when the
right scheme is flat and the left structural map on global functions is flat. -/
theorem isPushout_appTop {P X Y S : Scheme.{u}} {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (H : IsPullback p q f g) [IsAffine S] [Flat g]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (hf : f.appTop.hom.Flat) :
    IsPushout f.appTop g.appTop p.appTop q.appTop := by
  have := isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat H
    (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) (by simp) (by simp) (by simp)
    (isAffineOpen_top S) isCompact_univ isQuasiSeparated_univ
    isCompact_univ isQuasiSeparated_univ (by
      exact (congrArg (fun k : Γ(S, ⊤) ⟶ Γ(X, ⊤) => k.hom.Flat)
        (LocallyQuasiFiniteDescent.appLE_top_top f _)).mpr hf)
  convert (isIso_pushoutSection_iff H _ _ _).mp this using 1 <;>
    exact (LocallyQuasiFiniteDescent.appLE_top_top _ _).symm

/-- Global functions take products of flat qcqs schemes over a PID to ring pushouts. -/
theorem isPushout_appTop_pid {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] {P X Y : Scheme.{u}} {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
    (H : IsPullback p q f g) [Flat f] [Flat g]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    IsPushout f.appTop g.appTop p.appTop q.appTop := by
  have : Flat (Over.mk f).hom := by change Flat f; infer_instance
  exact isPushout_appTop H (flat_appTop (Over.mk f))

/-- The canonical product comparison for global functions over a PID. -/
def globalFunctionsProductIso {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] {P X Y : Scheme.{u}} {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
    (H : IsPullback p q f g) [Flat f] [Flat g]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    pushout f.appTop g.appTop ≅ Γ(P, ⊤) :=
  (isPushout_appTop_pid H).isoPushout.symm

end Langlands.AlgebraicGeometry.FlatGlobalSectionsProduct
