import Langlands.AbelianScheme.AmpleSectionIsogenyDegree
import Langlands.AlgebraicGeometry.LinearSystem.CompleteGeneratingSystem
import Langlands.AlgebraicGeometry.LinearSystem.CoordinateIdentity
import Langlands.AlgebraicGeometry.Modules.FlatSectionDescent
import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOneAmpleProof

/-! # Isogeny factorizations of complete ample linear systems -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard
  Langlands.AlgebraicGeometry.LinearSystem Langlands.AlgebraicGeometry.Modules.DerivedSections
  Langlands.SchemeModule

noncomputable section

namespace Langlands.AbelianScheme

/-- Factoring a complete ample linear system through a finite flat surjection
between abelian varieties forces the surjection to be an isomorphism. -/
abbrev CompleteLinearSystemIsogenyStatement : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    {A B : AbelianScheme (Spec (CommRingCat.of K))} {L : LineBundle A.X.left}
    (C : CompleteGeneratingSystem A.X.hom L), L.IsAmple →
    ∀ (q : A.X ⟶ B.X) [IsFinite q.left] [Flat q.left] [Surjective q.left]
      (b : B.X.left ⟶ ProjectiveSpace K C.n),
      b ≫ projectiveSpaceToSpec K C.n = B.X.hom → q.left ≫ b = C.map → IsIso q.left

/-- The descended coordinates span the original section space after pullback.
The ample section count forces the rank of the finite flat morphism to be one. -/
theorem isIso_of_completeLinearSystem_factors : CompleteLinearSystemIsogenyStatement.{u} := by
  intro K _ _ A B L C hL q _ _ _ b hb h
  have : IsProper (b ≫ projectiveSpaceToSpec K C.n) := hb ▸ inferInstanceAs (IsProper B.X.hom)
  have : IsProper b := IsProper.of_comp _ (projectiveSpaceToSpec K C.n)
  have : IsFinite (q.left ≫ b) := h ▸ C.isFinite_map_of_isAmple hL
  have : IsFinite b := by
    apply (IsFinite.iff_isProper_and_locallyQuasiFinite b).mpr
    refine ⟨inferInstance, LocallyQuasiFinite.of_finite_preimage_singleton b fun z ↦ ?_⟩
    have hpre : q.left '' ((q.left ≫ b) ⁻¹' {z}) = b ⁻¹' {z} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        obtain ⟨x, rfl⟩ := q.left.surjective y
        exact ⟨x, hy, rfl⟩
    rw [← hpre]
    exact ((q.left ≫ b).finite_preimage_singleton z).image q.left
  let M := projectiveCoordinateLineBundle K C.n
  have hM : M.IsAmple := by
    obtain ⟨M', hM', ha⟩ := projectiveSpaceTwistOneAmple K C.n
    exact ha.of_iso (eqToIso hM')
  let N := (LineBundle.pullback b).obj M
  have hN : N.IsAmple := hM.pullback_of_isAffineHom b
  let e : ((LineBundle.pullback q.left).obj N).obj ≅ L.obj :=
    (Scheme.Modules.pullbackComp q.left b).app M.obj ≪≫
      (Scheme.Modules.pullbackCongr h).app M.obj ≪≫
      linearSystemTwistIso A.X.hom C.basis C.generates
  let F := relativeGlobalSectionsPullback q N.obj ≫ (relativeGlobalSections A.X.hom).map e.hom
  have happ (s : (relativeGlobalSections B.X.hom).obj N.obj) :
      F s = e.hom.app ⊤ (pullbackSection q.left N.obj s) := by
    change e.hom.app ⊤ (relativeGlobalSectionsPullback q N.obj s) = _
    rw [relativeGlobalSectionsPullback_apply]
  let c (i : Fin (C.n + 1)) : (relativeGlobalSections B.X.hom).obj N.obj :=
    pullbackSection b (twistOne K C.n) (twistOneCoordinate K C.n i)
  have hF (i : Fin (C.n + 1)) : F (c i) = C.basis i := by
    rw [happ]
    change (linearSystemTwistIso A.X.hom C.basis C.generates).hom.app ⊤
      (((Scheme.Modules.pullbackComp q.left b).hom.app (twistOne K C.n) ≫
        (Scheme.Modules.pullbackCongr h).hom.app (twistOne K C.n)).app ⊤
        (pullbackSection q.left ((Scheme.Modules.pullback b).obj (twistOne K C.n))
          (pullbackSection b (twistOne K C.n) (twistOneCoordinate K C.n i)))) = _
    rw [RelativeProjectiveSpace.pullbackSection_comp_eq]
    exact linearSystemTwistIso_coordinate A.X.hom C.basis C.generates i
  have hsurj : Function.Surjective F := by
    intro s
    refine ⟨∑ i, C.basis.repr s i • c i, ?_⟩
    calc
      F (∑ i, C.basis.repr s i • c i) = ∑ i, C.basis.repr s i • C.basis i := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ (map_smul F.hom _ _).trans (congrArg (_ • ·) (hF i))
      _ = s := C.basis.sum_repr s
  have hinj : Function.Injective F := by
    intro s t heq
    rw [happ, happ] at heq
    apply Langlands.AlgebraicGeometry.Modules.pullbackSection_injective q.left N.obj
    exact (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective heq
  apply isIso_of_finrank_globalSections_pullback_eq q N hN
  exact (((relativeGlobalSections A.X.hom).mapIso e).toLinearEquiv.trans
    (LinearEquiv.ofBijective F.hom ⟨hinj, hsurj⟩).symm).finrank_eq

end Langlands.AbelianScheme
