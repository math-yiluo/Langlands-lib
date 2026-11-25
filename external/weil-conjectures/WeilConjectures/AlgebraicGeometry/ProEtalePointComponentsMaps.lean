/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import Mathlib.Topology.Connected.TotallyDisconnected

import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent

/-!
# Maps to relative profinite test schemes

Source: Bhatt–Scholze, Section 4.2, Lemma 4.2.13(1), finite-quotient argument;
RefactorInstruction, Section 4, proof of Lemma point-eval
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

private noncomputable def componentMapEquiv (A : Type u) [TopologicalSpace A]
    (S : Profinite.{u}) : C(A, S) ≃ C(ConnectedComponents A, S) where
  toFun f := ⟨f.continuous.connectedComponentsLift,
    f.continuous.connectedComponentsLift_continuous⟩
  invFun f := f.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩
  left_inv f := by ext x; simp
  right_inv f := by
    ext x
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    simp

private noncomputable def profiniteHomContinuousEquiv (A S : Profinite.{u}) :
    (A ⟶ S) ≃ C(A, S) where
  toFun f := f.hom.hom
  invFun f := ConcreteCategory.ofHom f

-- The inverse ring map is the explicit spectrum lift. Its inverse identities are
-- checked in every prime localization, using the characteristic idempotent of a fibre.
private noncomputable def specMapEquiv (R : CommRingCat.{u}) (S : Profinite.{u}) :
    (Spec R ⟶ profiniteToScheme.obj S) ≃ C(Spec R, S) := by
  let projection (φ : LocallyConstant S ℤ →+* R) : C(PrimeSpectrum R, S) :=
    ⟨fun p ↦ ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
        (PrimeSpectrum.comap φ p)).1,
      continuous_fst.comp
        ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm.continuous.comp
          (PrimeSpectrum.continuous_comap φ))⟩
  have localization_eq (φ : LocallyConstant S ℤ →+* R)
      (p : PrimeSpectrum R) (g : LocallyConstant S ℤ) :
      algebraMap R (Localization.AtPrime p.asIdeal) (φ g) =
        algebraMap R (Localization.AtPrime p.asIdeal) (g (projection φ p) : R) := by
    classical
    let s := projection φ p
    let q := ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
      (PrimeSpectrum.comap φ p)).2
    have hp : PrimeSpectrum.comap φ p = LocallyConstant.toPrimeSpectrum (s, q) :=
      ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).apply_symm_apply _).symm
    let χ := LocallyConstant.charFn ℤ (g.isLocallyConstant.isClopen_fiber (g s))
    have hχ : φ χ ∉ p.asIdeal := by
      change χ ∉ (PrimeSpectrum.comap φ p).asIdeal
      rw [hp, LocallyConstant.mem_toPrimeSpectrum_asIdeal]
      simpa [χ, LocallyConstant.charFn_apply_of_mem] using q.isPrime.one_notMem
    have hid : IsIdempotentElem χ := by
      change χ * χ = χ
      ext x
      by_cases hx : g x = g s
      · simp [χ, LocallyConstant.charFn_apply_of_mem, hx]
      · simp [χ, LocallyConstant.charFn_apply_of_notMem, hx]
    have hχloc : algebraMap R (Localization.AtPrime p.asIdeal) (φ χ) = 1 :=
      (hid.map φ).algebraMap_localization_atPrime_of_notMem hχ
    have hmul : χ * g = χ * algebraMap ℤ (LocallyConstant S ℤ) (g s) := by
      ext x
      change χ x * g x = χ x * g s
      by_cases hx : g x = g s
      · simp [hx]
      · simp [χ, LocallyConstant.charFn_apply_of_notMem, hx]
    have h := congrArg (fun v ↦ algebraMap R (Localization.AtPrime p.asIdeal) (φ v)) hmul
    simp only [map_mul, hχloc, one_mul] at h
    change algebraMap R (Localization.AtPrime p.asIdeal) (φ g) =
      algebraMap R (Localization.AtPrime p.asIdeal) (φ ((g s : ℤ) : LocallyConstant S ℤ)) at h
    simpa only [map_intCast] using h
  refine Spec.homEquiv.trans
    { toFun := fun φ ↦ projection φ.hom
      invFun := fun f ↦ CommRingCat.ofHom
        (LocallyConstant.liftPrimeSpectrum (Int.castRingHom R) f)
      left_inv := ?_
      right_inv := ?_ }
  · intro φ
    apply CommRingCat.hom_ext
    ext g
    apply PrimeSpectrum.eq_of_forall_algebraMap_localization_eq
    intro p
    change algebraMap R (Localization.AtPrime p.asIdeal)
      (LocallyConstant.liftPrimeSpectrum (Int.castRingHom R) (projection φ.hom) g) = _
    rw [LocallyConstant.algebraMap_localization_liftPrimeSpectrum]
    exact (localization_eq φ.hom p g).symm
  · intro f
    ext p
    change ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
      (PrimeSpectrum.comap (LocallyConstant.liftPrimeSpectrum (Int.castRingHom R) f) p)).1 = _
    rw [LocallyConstant.comap_liftPrimeSpectrum]
    exact congrArg Prod.fst
      ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm_apply_apply _)

private lemma specMapEquiv_apply (R : CommRingCat.{u}) (S : Profinite.{u})
    (f : Spec R ⟶ profiniteToScheme.obj S) (x : Spec R) :
    specMapEquiv R S f x =
      ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm (f x)).1 := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  dsimp only [specMapEquiv, Equiv.trans_apply]
  erw [Spec.homEquiv_apply, Spec.preimage_map]
  rfl

private noncomputable def affineMapEquiv (A : Scheme.{u}) [IsAffine A]
    (S : Profinite.{u}) : (A ⟶ profiniteToScheme.obj S) ≃ C(A, S) :=
  (Iso.homCongr A.isoSpec (Iso.refl _)).trans
    ((specMapEquiv _ S).trans
      ((Scheme.homeoOfIso A.isoSpec.symm).continuousMapCongr (Homeomorph.refl S)))

private lemma affineMapEquiv_apply (A : Scheme.{u}) [IsAffine A] (S : Profinite.{u})
    (f : A ⟶ profiniteToScheme.obj S) (x : A) :
    affineMapEquiv A S f x =
      ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm (f x)).1 := by
  change specMapEquiv _ S (A.isoSpec.inv ≫ f ≫ 𝟙 _) (A.isoSpec.hom x) = _
  rw [specMapEquiv_apply]
  simp

-- Maps over X into the base change are maps into Spec LC(S, Z), since Spec Z is terminal.
private noncomputable def relativeMapEquiv (X : Scheme.{u}) (U : X.ProEt)
    (S : Profinite.{u}) : (U ⟶ (profiniteToProEtOf X).obj S) ≃
      (U.left ⟶ profiniteToScheme.obj S) where
  toFun f := f.left ≫ Limits.pullback.fst _ _
  invFun f := MorphismProperty.Over.homMk
    (Limits.pullback.lift f U.hom (by
      change f ≫ toSpecZ _ = U.hom ≫ toSpecZ X
      exact specULiftZIsTerminal.hom_ext _ _)) (by
        change Limits.pullback.lift _ _ _ ≫ Limits.pullback.snd _ _ = _
        simp)
  left_inv f := by
    apply MorphismProperty.Over.Hom.ext
    apply Limits.pullback.hom_ext
    · simp
    · change Limits.pullback.lift _ _ _ ≫ Limits.pullback.snd _ _ = _
      rw [Limits.pullback.lift_snd]
      exact f.w.symm
  right_inv f := by simp

private noncomputable def pointComponentsEquiv (X : Scheme.{u}) (U : X.ProEt)
    [IsAffine U.left] (S : Profinite.{u}) :
    (U ⟶ (profiniteToProEtOf X).obj S) ≃ C(ConnectedComponents U.left, S) :=
  (relativeMapEquiv X U S).trans
    ((affineMapEquiv U.left S).trans (componentMapEquiv U.left S))

private lemma pointComponentsEquiv_apply (X : Scheme.{u}) (U : X.ProEt)
    [IsAffine U.left] (S : Profinite.{u})
    (f : U ⟶ (profiniteToProEtOf X).obj S) (x : U.left) :
    pointComponentsEquiv X U S f (ConnectedComponents.mk x) =
      ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
        ((f.left ≫ Limits.pullback.fst _ _) x)).1 := by
  change (affineMapEquiv U.left S (relativeMapEquiv X U S f)) x = _
  exact affineMapEquiv_apply _ _ _ _

private lemma profiniteProjection_natural (S T : Profinite.{u}) (b : S ⟶ T)
    (x : profiniteToScheme.obj S) :
    ((LocallyConstant.homeomorphPrimeSpectrum (T := T) (R := ℤ)).symm
      (profiniteToScheme.map b x)).1 =
    b (((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm x).1) := by
  obtain ⟨⟨s, p⟩, rfl⟩ := LocallyConstant.toPrimeSpectrum_surjective x
  change ((LocallyConstant.homeomorphPrimeSpectrum (T := T) (R := ℤ)).symm
      (LocallyConstant.homeomorphPrimeSpectrum (T := T) (R := ℤ) (b s, p))).1 =
    b (((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
      (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ) (s, p))).1)
  rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]

private lemma relativeMapEquiv_target (X : Scheme.{u}) (U : X.ProEt)
    (S T : Profinite.{u}) (b : S ⟶ T) (f : U ⟶ (profiniteToProEtOf X).obj S) :
    relativeMapEquiv X U T (f ≫ (profiniteToProEtOf X).map b) =
      relativeMapEquiv X U S f ≫ profiniteToScheme.map b := by
  change (f.left ≫ ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).map
      (profiniteToProEt.map b)).left) ≫ Limits.pullback.fst _ _ = _
  rw [MorphismProperty.Over.pullback_map_left]
  simp [Category.assoc, relativeMapEquiv, profiniteToProEt]

/-- The component quotient of an affine weakly contractible pro-etale object is profinite.
Maps to `X[S]` are naturally continuous maps from this quotient to `S`.
Weak contractibility means surjectivity on sections of every epimorphism of set sheaves;
the sheaf values live in the larger universe of the small-site convention.
The single family `e` is covariant in profinite targets and contravariant in these objects.

Source: Bhatt–Scholze, Section 4.2, Lemma 4.2.13(1), with the finite-quotient argument;
RefactorInstruction, Section 4, proof of Lemma point-eval
(auxiliary; not a blueprint node).

Proof:
1. An affine scheme is compact and quasi-separated, hence spectral by
   lem-weil-pbc-qcqs-scheme-spectral and def-weil-spectral-space. By
   lem-weil-pbc-quasicompact-components-clopen-intersection, distinct components are
   separated by clopens. Clopens are saturated for the component quotient, giving
   Hausdorffness and total disconnectedness. Compactness descends along the quotient.
2. For a finite discrete target, lem-weil-pbc-profinite-test-object-functor identifies
   the test scheme with a coproduct of copies of X. Use
   lem-galois-coproduct-copies-morphisms-clopen to identify its maps with continuous
   finite-valued functions. Such functions factor uniquely through the component
   quotient, and the quotient topology gives continuity of that factor.
3. Present S by its finite quotients. The limit clause of
   lem-weil-pbc-profinite-test-object-functor identifies scheme maps with compatible
   families of finite-stage maps, hence with compatible continuous finite-stage functions.
4. The topological inverse-limit property identifies these families with continuous
   maps to S. Basic opens give continuity. Empty targets give no maps from a nonempty
   source and a unique map from an empty source; singleton targets give a unique map.
5. Precomposition pulls back finite-stage clopen fibres and induces the usual map on
   component quotients. For a target map, compose with any finite quotient of its target
   and factor this finite-valued function through a finite quotient of its source.
   The test-object functor respects these maps. Equality at every finite quotient proves
   both naturality identities. -/
theorem proEtale_point_components_maps (X : Scheme.{u}) :
    (∀ (U : X.ProEt), IsAffine U.left →
      (∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
        Epi f → Function.Surjective (f.hom.app (op U))) →
      CompactSpace (ConnectedComponents U.left) ∧
        T2Space (ConnectedComponents U.left) ∧
        TotallyDisconnectedSpace (ConnectedComponents U.left)) ∧
    ∃ e : ∀ (U : X.ProEt), IsAffine U.left →
        (∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
          Epi f → Function.Surjective (f.hom.app (op U))) →
        ∀ S : Profinite.{u},
          (U ⟶ (profiniteToProEtOf X).obj S) ≃ C(ConnectedComponents U.left, S),
      (∀ (U : X.ProEt) (hU : IsAffine U.left)
        (wU : ∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
          Epi f → Function.Surjective (f.hom.app (op U)))
        (S T : Profinite.{u}) (b : S ⟶ T) (f : U ⟶ (profiniteToProEtOf X).obj S),
        e U hU wU T (f ≫ (profiniteToProEtOf X).map b) =
          b.hom.hom.comp (e U hU wU S f)) ∧
      (∀ (U V : X.ProEt) (hU : IsAffine U.left) (hV : IsAffine V.left)
        (wU : ∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
          Epi f → Function.Surjective (f.hom.app (op U)))
        (wV : ∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
          Epi f → Function.Surjective (f.hom.app (op V)))
        (a : V ⟶ U) (S : Profinite.{u}) (f : U ⟶ (profiniteToProEtOf X).obj S),
        e V hV wV S (a ≫ f) = (e U hU wU S f).comp
          ⟨a.left.continuous.connectedComponentsMap,
            a.left.continuous.connectedComponentsMap_continuous⟩) := by
  -- The affine correspondence is stronger than needed: weak contractibility is unused.
  constructor
  · intro U hU _
    let _ := hU
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · refine ⟨fun U hU _ S ↦ @pointComponentsEquiv X U hU S, ?_, ?_⟩
    · intro U hU wU S T b f
      let _ := hU
      ext x
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
      change pointComponentsEquiv X U T (f ≫ (profiniteToProEtOf X).map b)
          (ConnectedComponents.mk x) = b (pointComponentsEquiv X U S f
            (ConnectedComponents.mk x))
      rw [pointComponentsEquiv_apply, pointComponentsEquiv_apply]
      change ((LocallyConstant.homeomorphPrimeSpectrum (T := T) (R := ℤ)).symm
          (relativeMapEquiv X U T (f ≫ (profiniteToProEtOf X).map b) x)).1 = _
      rw [relativeMapEquiv_target]
      exact profiniteProjection_natural S T b _
    · intro U V hU hV wU wV a S f
      let _ := hU
      let _ := hV
      ext x
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
      change pointComponentsEquiv X V S (a ≫ f) (ConnectedComponents.mk x) =
        pointComponentsEquiv X U S f (a.left.continuous.connectedComponentsMap
          (ConnectedComponents.mk x))
      rw [Continuous.connectedComponentsMap_mk, pointComponentsEquiv_apply,
        pointComponentsEquiv_apply]
      rfl

end AlgebraicGeometry.ProEtale
