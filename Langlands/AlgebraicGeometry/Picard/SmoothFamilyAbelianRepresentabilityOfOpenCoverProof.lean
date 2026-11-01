import Langlands.AlgebraicGeometry.Picard.SmoothFamilyAbelianRepresentabilityOfOpenCoverStatement
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyOpenCoverGluing
import Langlands.AbelianScheme.AbelianSchemeStructureOfOpenCoverProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiGluingProof
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof

/-! # Zariski-local existence of an abelian-scheme smooth-family representer -/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.SmoothFamilyOpenCover

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

/-- The trivial line bundle on an abelian variety over an algebraically closed
field is algebraically trivial via the constant family on the variety itself. -/
lemma isAlgebraicallyTrivialViaSmoothFamily_trivial {K : Type u} [Field K] [IsAlgClosed K]
    (B : AbelianScheme (Spec (CommRingCat.of K))) :
    IsAlgebraicallyTrivialViaSmoothFamily B (LineBundle.trivial B.X.left) :=
  ⟨B.X, inferInstance, inferInstance, inferInstance, inferInstance,
    smoothGeometricIntegrality K B.X.left B.X.hom inferInstance inferInstance,
    Over.homMk (unitSection B) (unitSection_comp B), Over.homMk (unitSection B) (unitSection_comp B),
    LineBundle.trivial _, ⟨LineBundle.pullbackTrivialIso _⟩, ⟨LineBundle.pullbackTrivialIso _⟩⟩

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The trivial rigidified family satisfies the smooth-family condition. -/
lemma isAlgebraicallyTrivialFamily_trivial (T : Over S) :
    IsAlgebraicallyTrivialFamilyViaSmoothFamily A
      (RigidifiedLineBundle.trivial
        ((relativeSection A.X.hom (unitSection A)
          (unitSection_comp A)).app T)) := by
  intro K _ _ s
  refine isAlgebraicallyTrivialViaSmoothFamily_of_iso _ ?_
    (isAlgebraicallyTrivialViaSmoothFamily_trivial _)
  exact ((LineBundle.pullback _).mapIso (LineBundle.pullbackTrivialIso _) ≪≫
    LineBundle.pullbackTrivialIso _).symm

/-- A universal family transports along an isomorphism of parameters. -/
lemma isUniversal_of_iso {P Q : Over S} (L : RigidifiedFamily A P) (e : P ≅ Q)
    (hL : IsUniversalSmoothFamilyOnQuasiSeparatedTests A L) :
    IsUniversalSmoothFamilyOnQuasiSeparatedTests A ((rp[A] e.inv).obj L) := by
  refine ⟨smoothFamilyPullback S A _ _ e.inv L hL.1, fun T _ q ↦ ?_⟩
  obtain ⟨h, hh, hu⟩ := hL.2 T q
  refine ⟨h ≫ e.hom, ?_, fun k hk ↦ ?_⟩
  · show cm[A] ((rp[A] e.inv).obj L) T (h ≫ e.hom) = q.val
    rw [cm_pullback, Category.assoc, e.hom_inv_id, Category.comp_id, hh]
  · have hk' : cm[A] L T (k ≫ e.inv) = q.val := by
      rw [← cm_pullback]
      exact hk
    rw [← hu _ hk', Category.assoc, e.inv_hom_id, Category.comp_id]

section Charts

variable {ι : Type u} {U : ι → Scheme.{u}} (f : ∀ i, U i ⟶ S) [∀ i, IsOpenImmersion (f i)]
  (B : ∀ i, AbelianScheme (U i))

/-- Local parameters given by abelian schemes over the members of an open cover. -/
abbrev chartParam (i : ι) : Over S := (Over.map (f i)).obj (B i).X

variable {f B} (M : ∀ i, RigidifiedFamily A (chartParam f B i))
  (hM : ∀ i, IsUniversalOn A (f i).opensRange (M i))
  (hMa : ∀ i, IsAlgebraicallyTrivialFamilyViaSmoothFamily A (M i))

/-- The local data of the families on abelian-scheme charts. -/
def chartData : LocalData A (fun i ↦ (f i).opensRange) where
  P := chartParam f B
  M := M
  quasiSeparated i := by
    change QuasiSeparated ((B i).X.hom ≫ f i)
    infer_instance
  universal := hM
  algTriv := hMa

variable (hW : TopologicalSpace.IsOpenCover (fun i ↦ (f i).opensRange))

/-- Over each basis open, the glued parameter is the restriction of an abelian scheme. -/
lemma exists_chart [QuasiSeparatedSpace S] (V : (basisCover _ hW).I₀) :
    ∃ B' : AbelianScheme ((basisCover _ hW).X V),
      Nonempty ((Over.pullback ((basisCover _ hW).f V)).obj
        ((chartData A M hM hMa).glued hW) ≅ B'.X) := by
  let i := idx V
  have hr : Set.range V.1.ι ⊆ Set.range (f i) := by
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
    exact le_idx V
  let g : V.1.toScheme ⟶ U i := IsOpenImmersion.lift (f i) V.1.ι hr
  have hg : g ≫ f i = V.1.ι := IsOpenImmersion.lift_fac _ _ _
  refine ⟨(AbelianScheme.baseChange g).obj (B i), ⟨?_⟩⟩
  have hpb := (((chartData A M hM hMa).gluingData hW).isPullback_natTrans_ι_toBase V).flip
  have h2 : IsPullback (pullback.fst (B i).X.hom g) (pullback.snd (B i).X.hom g)
      ((B i).X.hom ≫ f i) V.1.ι := by
    have h : IsPullback (pullback.fst (B i).X.hom g) (pullback.snd (B i).X.hom g)
        ((B i).X.hom ≫ f i) (g ≫ f i) :=
      IsPullback.of_isLimit (pullbackIsPullbackOfCompMono (B i).X.hom g (f i))
    rw [hg] at h
    exact h
  refine Over.isoMk (hpb.isoPullback.symm ≪≫ (h2.isoPullback).symm) ?_
  change ((hpb.isoPullback.symm ≪≫ (h2.isoPullback).symm).hom ≫ pullback.snd _ _) =
    pullback.snd _ _
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, IsPullback.isoPullback_inv_snd]
  exact hpb.isoPullback_inv_snd

end Charts

/-- The open-cover representability statement follows from Zariski gluing of
rigidified classes and from existence of abelian-scheme structures on schemes
locally isomorphic to abelian schemes. -/
theorem smoothFamilyAbelianRepresentabilityOfOpenCover_of
    (glue : RigidifiedClassesZariskiGluingStatement.{u})
    (abel : AbelianSchemeStructureOfOpenCoverStatement.{u}) :
    SmoothFamilyAbelianRepresentabilityOfOpenCoverStatement.{u} := by
  intro S _ A 𝒰 H
  choose B L hL using H
  let M := fun i ↦ (familyBaseChangeInverse (𝒰.f i) A (B i).X).obj (L i)
  have hM := fun i ↦ isUniversalOn_familyBaseChangeInverse A (𝒰.f i) (L i) (hL i)
  have hMa := fun i ↦ isAlgebraicallyTrivial_familyBaseChangeInverse A (𝒰.f i) (L i) (hL i).1
  let D := chartData A (f := 𝒰.f) (B := B) M hM hMa
  have hW := 𝒰.isOpenCover_opensRange
  obtain ⟨L₀, hL₀⟩ := D.exists_universal hW glue
  have : QuasiSeparatedSpace (Over.mk (𝟙 S)).left := ‹QuasiSeparatedSpace S›
  obtain ⟨s₀, -⟩ := (hL₀.2 (Over.mk (𝟙 S))
    (atClass A _ (isAlgebraicallyTrivialFamily_trivial A (Over.mk (𝟙 S))))).exists
  let s : 𝟙_ (Over S) ⟶ D.glued hW := Over.homMk s₀.left (Over.w s₀)
  obtain ⟨B', e, -⟩ := abel S (D.glued hW) s (basisCover _ hW) (exists_chart A M hM hMa hW)
  exact ⟨B', (rp[A] e.inv).obj L₀, isUniversal_of_iso A L₀ e hL₀⟩

/-- The open-cover representability statement follows from Zariski gluing of
rigidified classes, using the published abelian-structure theorem. -/
theorem smoothFamilyAbelianRepresentabilityOfOpenCover_of_gluing
    (glue : RigidifiedClassesZariskiGluingStatement.{u}) :
    SmoothFamilyAbelianRepresentabilityOfOpenCoverStatement.{u} :=
  smoothFamilyAbelianRepresentabilityOfOpenCover_of glue abelianSchemeStructureOfOpenCover

end Langlands.AbelianScheme.SmoothFamilyOpenCover

namespace Langlands.AbelianScheme

/-- Zariski-local existence of an abelian-scheme smooth-family representer. -/
theorem smoothFamilyAbelianRepresentabilityOfOpenCover :
    SmoothFamilyAbelianRepresentabilityOfOpenCoverStatement.{u} :=
  SmoothFamilyOpenCover.smoothFamilyAbelianRepresentabilityOfOpenCover_of_gluing
    rigidifiedClassesZariskiGluing

end Langlands.AbelianScheme
