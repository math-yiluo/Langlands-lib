import Langlands.AlgebraicGeometry.SmoothReducedProof

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Langlands.AlgebraicGeometry.GlobalFunctionsFieldProof

lemma scalar_surjective_of_integral_of_preconnected (K : Type u) (A : Type v)
    [Field K] [IsAlgClosed K] [CommRing A] [Nontrivial A] [Algebra K A]
    [Algebra.IsIntegral K A] [_root_.IsReduced A] [PreconnectedSpace (PrimeSpectrum A)] :
    Function.Surjective (algebraMap K A) := by
  intro x
  let B := Algebra.adjoin K {x}
  have : Module.Finite K B :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral x)
  have : IsArtinianRing B := isArtinian_of_tower K inferInstance
  have : _root_.IsReduced B := isReduced_of_injective B.subtype Subtype.val_injective
  have : Algebra.IsIntegral B A := ⟨fun a =>
    (Algebra.IsIntegral.isIntegral (R := K) a).tower_top⟩
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap B A)) :=
    Algebra.IsIntegral.comap_surjective B A
  have : PreconnectedSpace (PrimeSpectrum B) :=
    hsurj.denseRange.preconnectedSpace (PrimeSpectrum.continuous_comap _)
  have : Subsingleton (PrimeSpectrum B) := subsingleton_of_preconnected_totallyDisconnected
  let := (PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp this).toField
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := B)).2
    ⟨x, Algebra.self_mem_adjoin_singleton K x⟩
  exact ⟨c, congrArg Subtype.val hc⟩

lemma isIso_appTop_of_algClosed (K : Type u) [Field K] [IsAlgClosed K]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of K))
    [Smooth p] [IsProper p] [GeometricallyConnected p] : IsIso p.appTop := by
  have : AlgebraicGeometry.IsReduced X := SmoothReducedProof.isReduced_of_smooth_over_field K X p
  have : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton p
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  have : CompactSpace X := (quasiCompact_iff_compactSpace p).mp inferInstance
  have : PreconnectedSpace (PrimeSpectrum Γ(X, ⊤)) :=
    (show DenseRange X.toSpecΓ from (isDominant_iff _).mp inferInstance).preconnectedSpace
      X.toSpecΓ.continuous
  let g := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop
  have hg : g.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  algebraize [g.hom]
  have : Algebra.IsIntegral K Γ(X, ⊤) := ⟨hg⟩
  have hgiso : IsIso g := (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨RingHom.injective _, scalar_surjective_of_integral_of_preconnected K Γ(X, ⊤)⟩
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of K)).inv p.appTop

lemma isIso_of_isPushout_of_faithfullyFlat {R A B C : CommRingCat.{u}}
    (f : R ⟶ A) (g : R ⟶ B) (i : A ⟶ C) (j : B ⟶ C)
    (h : IsPushout f g i j) (hg : g.hom.FaithfullyFlat) [IsIso j] : IsIso f := by
  algebraize [f.hom, g.hom, i.hom, j.hom, i.hom.comp f.hom]
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have : Algebra.IsPushout R A B C := CommRingCat.isPushout_iff_isPushout.mp h
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact RingHom.FaithfullyFlat.codescendsAlong_bijective hg
    ((ConcreteCategory.isIso_iff_bijective j).mp inferInstance)

lemma isIso_appTop_of_field (K : Type u) [Field K]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of K))
    [Smooth p] [IsProper p] [GeometricallyConnected p] : IsIso p.appTop := by
  let L := AlgebraicClosure K
  let q := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have : Flat q := by
    apply (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : CompactSpace X := (quasiCompact_iff_compactSpace p).mp inferInstance
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated p
  have hpb := IsPullback.of_hasPullback p q
  have hpo : IsPushout p.appTop q.appTop (pullback.fst p q).appTop
      (pullback.snd p q).appTop := by
    have h := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right hpb
      (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) (by simp) (by simp) (by simp)
      (isAffineOpen_top _) (isAffineOpen_top _) CompactSpace.isCompact_univ isQuasiSeparated_univ
    convert (isIso_pushoutSection_iff ..).mp h using 1 <;>
      exact Scheme.Hom.app_eq_appLE _
  have : IsIso (pullback.snd p q).appTop := isIso_appTop_of_algClosed L _ _
  let := ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  algebraize [q.appTop.hom]
  apply isIso_of_isPushout_of_faithfullyFlat _ _ _ _ hpo
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance

end Langlands.AlgebraicGeometry.GlobalFunctionsFieldProof
