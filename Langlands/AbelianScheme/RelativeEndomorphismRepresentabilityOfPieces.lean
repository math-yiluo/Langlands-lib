import Langlands.AbelianScheme.RelativeEndomorphismAffineHomScheme
import Langlands.AbelianScheme.RelativeEndomorphismAffineExtension
import Langlands.AbelianScheme.RelativeEndomorphismRepresentabilityStatement
import Langlands.AlgebraicGeometry.NoetherianValuativeCriterion
import Langlands.AlgebraicGeometry.ProjectiveSpace.Charts
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Relative endomorphism representability from affine Hom-scheme pieces -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AbelianScheme

universe u

section Finite

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A locally finite type, formally unramified morphism of schemes is locally quasi-finite. -/
lemma locallyQuasiFinite_of_formallyUnramified {X Y : Scheme.{u}} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h1 := HasRingHomProperty.appLE (P := @FormallyUnramified) f ‹_› U V e
  have h2 := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f ‹_› U V e
  algebraize [(f.appLE U V e).hom]
  exact RingHom.quasiFinite_algebraMap.mpr inferInstance

/-- A finite morphism to an affine scheme is H-projective. -/
theorem isHProjective_of_isFinite {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of R)) [IsFinite p] :
    Langlands.AlgebraicGeometry.IsHProjective p := by
  have : IsAffine X := isAffine_of_isAffineHom p
  let φ : CommRingCat.of R ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop
  have hp : p = X.toSpecΓ ≫ Spec.map φ := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  let : Algebra R Γ(X, ⊤) := φ.hom.toAlgebra
  have hfin : φ.hom.Finite := by
    have := p.finite_appTop
    exact RingHom.Finite.comp this (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.surjective)
  have : Module.Finite R Γ(X, ⊤) := hfin
  obtain ⟨s, hs⟩ := (Module.Finite.finiteType (R := R) Γ(X, ⊤)).out
  let n := s.card
  let e : Fin n ≃ s := s.equivFin.symm
  let b : Fin (n + 1) → Γ(X, ⊤) := Fin.cons 1 (fun k => (e k : Γ(X, ⊤)))
  obtain ⟨θ, hθ⟩ := _root_.AlgebraicGeometry.ProjSpace.exists_algHom_away_apply_ratio_eq R n 0 b rfl
  have hθs : Function.Surjective θ := by
    rw [← AlgHom.range_eq_top, eq_top_iff, ← hs, Algebra.adjoin_le_iff]
    intro x hx
    refine ⟨_root_.AlgebraicGeometry.ProjSpace.ratio R n 0 (Fin.succ (e.symm ⟨x, hx⟩)), ?_⟩
    change θ _ = x
    rw [hθ]
    simp [b]
  let θ' := CommRingCat.ofHom θ.toRingHom
  have hθφ : CommRingCat.ofHom (algebraMap R
      (HomogeneousLocalization.Away
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X 0))) ≫ θ' = φ := by
    ext r
    exact θ.commutes r
  let i : X ⟶ Langlands.AlgebraicGeometry.ProjectiveSpace R n :=
    X.toSpecΓ ≫ Spec.map θ' ≫
      (Langlands.AlgebraicGeometry.ProjectiveSpace.affineOpenCover R n).openCover.f
        (0 : Fin (n + 1))
  have hi : i ≫ Langlands.AlgebraicGeometry.projectiveSpaceToSpec R n = p := by
    simp only [i, Category.assoc]
    rw [Langlands.AlgebraicGeometry.ProjectiveSpace.affineOpenCover_comp_toSpec R n 0,
      ← Spec.map_comp]
    exact (congrArg (fun g => X.toSpecΓ ≫ Spec.map g) hθφ).trans hp.symm
  have : IsProper (Langlands.AlgebraicGeometry.projectiveSpaceToSpec R n) :=
    _root_.AlgebraicGeometry.ProjSpace.isProper_π R n
  have : IsClosedImmersion (Spec.map θ') :=
    IsClosedImmersion.spec_of_surjective θ' (fun y => hθs y)
  have : IsFinite i := by
    have : IsFinite (i ≫ Langlands.AlgebraicGeometry.projectiveSpaceToSpec R n) := by
      rw [hi]; infer_instance
    exact IsFinite.of_comp i (Langlands.AlgebraicGeometry.projectiveSpaceToSpec R n)
  have : Mono i := by
    simp only [i]
    infer_instance
  exact ⟨n, i, (IsClosedImmersion.iff_isFinite_and_mono i).mpr ⟨inferInstance, inferInstance⟩, hi⟩

end Finite

section Hypotheses

/-- For abelian schemes `A` and `B` over `S` and a discrete valuation ring `V` over `S` with
fraction field `K`, every homomorphism `A_K → B_K` is the restriction of a homomorphism
`A_V → B_V`. -/
def NeronHomExtension : Prop :=
  ∀ (S : Scheme.{u}) (A B : Langlands.AbelianScheme S) (V : Type u) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K]
    (t : Spec (CommRingCat.of V) ⟶ S),
    Function.Surjective
      (Langlands.GroupScheme.Cartier.restrict A.toCommGroupScheme B.toCommGroupScheme
        (Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ t))
          (V := Over.mk t) (Spec.map (CommRingCat.ofHom (algebraMap V K))) rfl))

end Hypotheses

section Lifts

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S) {E : Over S}
  (β : (Langlands.GroupScheme.Cartier.relativeHomFunctor A.toCommGroupScheme
      A.toCommGroupScheme ⋙ forget AddCommGrpCat.{u}) ≅ yoneda.obj E)

include β in
/-- If `E` represents the relative endomorphism functor of `A`, then valuative squares over the
structure morphism of `E` with a discrete valuation ring have lifts. -/
lemma hasLift_of_iso_yoneda (hN : NeronHomExtension.{u}) (sq : ValuativeCommSq E.hom)
    (hR : IsDiscreteValuationRing sq.R) : sq.commSq.HasLift := by
  let a : Spec (CommRingCat.of sq.K) ⟶ Spec (CommRingCat.of sq.R) :=
    Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))
  let TV : Over S := Over.mk sq.i₂
  let TK : Over S := Over.mk (a ≫ sq.i₂)
  let jK : TK ⟶ TV := Over.homMk a rfl
  let gK : TK ⟶ E := Over.homMk sq.i₁ sq.commSq.w
  obtain ⟨χ, hχ⟩ := hN S A A sq.R sq.K sq.i₂ (β.inv.app (op TK) gK)
  have h' : β.hom.app (op TK)
      (Langlands.GroupScheme.Cartier.restrict A.toCommGroupScheme A.toCommGroupScheme jK χ) =
        jK ≫ β.hom.app (op TV) χ := by
    have h := β.hom.naturality_apply jK.op χ
    simp only [Functor.comp_map] at h
    exact h
  have hl : jK ≫ β.hom.app (op TV) χ = gK :=
    h'.symm.trans ((congrArg (β.hom.app (op TK)) hχ).trans (β.inv_hom_id_app_apply (op TK) gK))
  exact ⟨⟨{ l := (β.hom.app (op TV) χ).left,
             fac_left := congrArg CommaMorphism.left hl,
             fac_right := Over.w (β.hom.app (op TV) χ) }⟩⟩

include β in
/-- Valuative squares with a discrete valuation ring over a closed open piece of a scheme
representing the relative endomorphism functor of `A` have lifts. -/
lemma hasLift_of_iso_yoneda_of_isClosed (hN : NeronHomExtension.{u}) (U : E.left.Opens)
    (hU : IsClosed (U : Set E.left)) (sq : ValuativeCommSq (U.ι ≫ E.hom))
    (hR : IsDiscreteValuationRing sq.R) : sq.commSq.HasLift := by
  let sq' : ValuativeCommSq E.hom :=
    { R := sq.R, K := sq.K, i₁ := sq.i₁ ≫ U.ι, i₂ := sq.i₂,
      commSq := ⟨by rw [Category.assoc]; exact sq.commSq.w⟩ }
  obtain ⟨⟨⟨l, hl1, hl2⟩⟩⟩ := hasLift_of_iso_yoneda A β hN sq' hR
  have hl1' : Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ l = sq.i₁ ≫ U.ι := hl1
  have hl2' : l ≫ E.hom = sq.i₂ := hl2
  have hrange : Set.range l ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    have hd : DenseRange (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) :=
      (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap sq.R sq.K)).mpr (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective sq.R sq.K)]
        exact bot_le)
    have hc : IsClosed (l ⁻¹' (U : Set E.left)) := hU.preimage l.continuous
    have hsub : Set.range (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) ⊆
        l ⁻¹' (U : Set E.left) := by
      rintro _ ⟨x, rfl⟩
      have hx := Set.mem_range_self (f := U.ι) (sq.i₁ x)
      rw [Scheme.Opens.range_ι] at hx
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hl1', Scheme.Hom.comp_apply]
      exact hx
    rintro _ ⟨y, rfl⟩
    exact hc.closure_subset_iff.mpr hsub (hd y)
  refine ⟨⟨{ l := IsOpenImmersion.lift U.ι l hrange, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← cancel_mono U.ι, Category.assoc, IsOpenImmersion.lift_fac, hl1']
  · rw [← Category.assoc, IsOpenImmersion.lift_fac, hl2']

end Lifts

/-- The affine-test Hom-scheme interface and the Néron extension property of homomorphisms of
abelian schemes together imply relative endomorphism representability by a disjoint union of
H-projective schemes. -/
theorem relativeEndomorphismRepresentability_of_affineHomSchemePieces
    (hP : AffineHomSchemePiecesStatement.{u}) (hN : NeronHomExtension.{u}) :
    RelativeEndomorphismRepresentabilityStatement.{u} := by
  intro R _ _ A hA
  obtain ⟨H, hsep, hlft, hfu, ⟨α⟩, I, U, hUc, hUqc, hdisj, hcov⟩ := hP R A hA
  obtain ⟨β⟩ := Langlands.GroupScheme.Cartier.nonempty_iso_yoneda_of_affine α
  have hLN : IsLocallyNoetherian H.left := LocallyOfFiniteType.isLocallyNoetherian H.hom
  refine ⟨H, hLN, ⟨Functor.isoWhiskerLeft _ β⟩, I, fun i => Over.mk ((U i).ι ≫ H.hom),
    fun i => ?_, ?_⟩
  · have : QuasiCompact ((U i).ι ≫ H.hom) := hUqc i
    have hUC : UniversallyClosed ((U i).ι ≫ H.hom) :=
      Langlands.AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_hasLift
        ((U i).ι ≫ H.hom)
        (fun sq hR => hasLift_of_iso_yoneda_of_isClosed A β hN (U i) (hUc i) sq hR)
    have : IsProper ((U i).ι ≫ H.hom) :=
      { toIsSeparated := inferInstance, toUniversallyClosed := hUC,
        toLocallyOfFiniteType := inferInstance }
    have := locallyQuasiFinite_of_formallyUnramified H.hom
    have : IsFinite ((U i).ι ≫ H.hom) := IsFinite.of_isProper_of_locallyQuasiFinite _
    exact isHProjective_of_isFinite ((U i).ι ≫ H.hom)
  · have hcol := nonempty_isColimit_cofanMk_of (fun i => (U i).ι)
      (by simpa only [Scheme.Opens.opensRange_ι] using hcov)
      (fun i j hij => by simpa only [Function.onFun, Scheme.Opens.opensRange_ι] using hdisj hij)
    have : IsIso (Sigma.desc fun i => (U i).ι) := by
      have h := (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp hcol
      simpa only [cofan_mk_inj, Cofan.mk_pt] using h
    refine ⟨Over.isoMk (asIso (Sigma.desc fun i => (U i).ι)).symm ?_⟩
    rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
    refine Sigma.hom_ext _ _ fun i => ?_
    simp

end Langlands.AbelianScheme
