import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusIsoLocus
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicDirectImageStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicEvaluation
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicDirectImageProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusBaseChangeStatement
import Langlands.AlgebraicGeometry.PullbackFiniteLocalBasisRankProof
import Langlands.AlgebraicGeometry.LocallyFreeRankIso
import Langlands.AlgebraicGeometry.Modules.LineBundleFlatDescentStr
import Langlands.AlgebraicGeometry.ProjectiveBundle.FrameChoiceTwist
import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationBaseChange

/-! # Proof: base change of torsion evaluations and of the projective frame locus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Picard

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate
open Langlands.Scheme.Modules Langlands.Scheme.Modules.LineBundleFlatDescent
open Langlands.AlgebraicGeometry.Modules.DerivedSections

set_option backward.isDefEq.respectTransparency false

section Coherence

variable {S T A A' : Scheme.{u}}

/-- The inverse square comparison in terms of the generalized composition comparisons. -/
theorem pullbackSquareIso_inv_app_eq (f : T ⟶ S) (π : A ⟶ S) (π' : A' ⟶ T) (q : A' ⟶ A)
    (w : q ≫ π = π' ≫ f) (V : S.Modules) :
    (pullbackSquareIso f π π' q w).inv.app V =
      (compIso π' f (π' ≫ f) rfl V).hom ≫ (compIso q π (π' ≫ f) w V).inv := by
  rw [Iso.eq_comp_inv, compIso_rfl, compIso_hom]
  simp [pullbackSquareIso, Langlands.SchemeModule.RigidifiedModule.compHom]

/-- Pulling back the inverse identity comparison and composing with the composition
comparison along `f ≫ 𝟙 = f` gives the identity. -/
theorem pullback_map_pullbackId_inv_comp_compIso (f : T ⟶ S) (h : f ≫ 𝟙 S = f)
    (V : S.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId S).inv.app V) ≫
      (compIso f (𝟙 S) f h V).hom = 𝟙 _ := by
  have h0 := Langlands.SchemeModule.RigidifiedModule.pullbackComp_inv_app_comp_pullbackId f V
  have h0' : (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId S).hom.app V) =
      (Scheme.Modules.pullbackComp f (𝟙 S)).hom.app V ≫ eqToHom (by simp) := by
    rw [← h0, Iso.hom_inv_id_app_assoc]
  rw [compIso_hom]
  simp only [Langlands.SchemeModule.RigidifiedModule.compHom, Scheme.Modules.pullbackCongr,
    eqToIso.hom]
  rw [← cancel_epi ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId S).hom.app V)),
    ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, h0']
  simp

/-- Coherence of the identifications `V ≅ σ^* π^* V` with an arbitrary base change. -/
theorem section_baseChange_coherence (π : A ⟶ S) (σ : S ⟶ A) (hσ : σ ≫ π = 𝟙 S)
    (f : T ⟶ S) (q : A' ⟶ A) (π' : A' ⟶ T) (w : q ≫ π = π' ≫ f) (σ' : T ⟶ A')
    (hσ' : σ' ≫ π' = 𝟙 T) (hq : σ' ≫ q = f ≫ σ) (V : S.Modules) :
    (Scheme.Modules.pullbackId T).inv.app ((Scheme.Modules.pullback f).obj V) ≫
        (compIso σ' π' (𝟙 T) hσ' ((Scheme.Modules.pullback f).obj V)).inv ≫
        (Scheme.Modules.pullback σ').map ((pullbackSquareIso f π π' q w).inv.app V) =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId S).inv.app V) ≫
        (Scheme.Modules.pullback f).map (compIso σ π (𝟙 S) hσ V).inv ≫
        (compIso f σ (σ' ≫ q) hq.symm ((Scheme.Modules.pullback π).obj V)).hom ≫
        (compIso σ' q (σ' ≫ q) rfl ((Scheme.Modules.pullback π).obj V)).inv := by
  have h1 : (σ' ≫ q) ≫ π = f := by rw [hq, Category.assoc, hσ, Category.comp_id]
  have hw' : σ' ≫ π' ≫ f = f := by rw [← Category.assoc, hσ', Category.id_comp]
  have hR := compIso_assoc f σ π (σ' ≫ q) (𝟙 S) f hq.symm hσ (Category.comp_id f) h1 V
  have hL1 := compIso_assoc σ' q π (σ' ≫ q) (π' ≫ f) f rfl w hw' h1 V
  have hL2 := compIso_assoc σ' π' f (𝟙 T) (π' ≫ f) f hσ' rfl hw' (Category.id_comp f) V
  have hid := compIso_id_left_congr (𝟙 T) f rfl (Category.id_comp f) V
  rw [← cancel_mono ((compIso σ' q (σ' ≫ q) rfl ((Scheme.Modules.pullback π).obj V)).hom ≫
    (compIso (σ' ≫ q) π f h1 V).hom)]
  have hLHS : ((Scheme.Modules.pullbackId T).inv.app ((Scheme.Modules.pullback f).obj V) ≫
        (compIso σ' π' (𝟙 T) hσ' ((Scheme.Modules.pullback f).obj V)).inv ≫
        (Scheme.Modules.pullback σ').map ((pullbackSquareIso f π π' q w).inv.app V)) ≫
      ((compIso σ' q (σ' ≫ q) rfl ((Scheme.Modules.pullback π).obj V)).hom ≫
        (compIso (σ' ≫ q) π f h1 V).hom) = 𝟙 _ := by
    rw [pullbackSquareIso_inv_app_eq, CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
    rw [hL1, Iso.map_inv_hom_id_assoc, ← hL2, Iso.inv_hom_id_assoc, hid]
    simp [Scheme.Modules.pullbackCongr]
  have hRHS : ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId S).inv.app V) ≫
        (Scheme.Modules.pullback f).map (compIso σ π (𝟙 S) hσ V).inv ≫
        (compIso f σ (σ' ≫ q) hq.symm ((Scheme.Modules.pullback π).obj V)).hom ≫
        (compIso σ' q (σ' ≫ q) rfl ((Scheme.Modules.pullback π).obj V)).inv) ≫
      ((compIso σ' q (σ' ≫ q) rfl ((Scheme.Modules.pullback π).obj V)).hom ≫
        (compIso (σ' ≫ q) π f h1 V).hom) = 𝟙 _ := by
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc, hR, Iso.map_inv_hom_id_assoc,
      pullback_map_pullbackId_inv_comp_compIso]
  rw [hLHS, hRHS]
  rfl

end Coherence

variable {P : Prerequisites.{u}} {S T : Scheme.{u}} {g d n : ℕ}

/-- The torsion sections of a pulled-back datum are the base changes of the
original torsion sections. -/
theorem Datum.torsionPoint_pullback_fst (a : Datum P S g d n) (f : T ⟶ S)
    (r : Fin (2 * g) → ZMod n) :
    (a.pullback f).torsionPoint r ≫ pullback.fst a.abelian.X.hom f =
      f ≫ a.torsionPoint r := by
  have h := congrArg (fun x => (Additive.toMul (toSection _ _ n x)).left)
    (enumerateTuple_pullback a.level.sections f r)
  simp only [toSection_levelRestrict] at h
  exact h

/-- The torsion evaluation, written with the generalized composition comparison. -/
theorem Datum.torsionEvaluation_eq (a : Datum P S g d n) (r : Fin (2 * g) → ZMod n) :
    a.torsionEvaluation r =
      (Scheme.Modules.pullbackId S).inv.app a.rigidificationModule ≫
        (compIso (a.torsionPoint r) a.abelian.X.hom (𝟙 S) (a.torsionPoint_hom r)
          a.rigidificationModule).inv ≫
        (Scheme.Modules.pullback (a.torsionPoint r)).map a.cubicEvaluationAdjoint := by
  have hc : (Scheme.Modules.pullbackCongr (a.torsionPoint_hom r).symm).hom.app
        a.rigidificationModule ≫
      (Scheme.Modules.pullbackComp (a.torsionPoint r) a.abelian.X.hom).inv.app
        a.rigidificationModule =
      (compIso (a.torsionPoint r) a.abelian.X.hom (𝟙 S) (a.torsionPoint_hom r)
        a.rigidificationModule).inv := by
    rw [← cancel_mono (compIso (a.torsionPoint r) a.abelian.X.hom (𝟙 S) (a.torsionPoint_hom r)
      a.rigidificationModule).hom, Iso.inv_hom_id, compIso_hom]
    simp [Langlands.SchemeModule.RigidifiedModule.compHom, Scheme.Modules.pullbackCongr]
  rw [Datum.torsionEvaluation, ← hc]
  simp only [Category.assoc]
  rfl

/-- The comparison of the targets of a torsion evaluation and of its base change. -/
def Datum.torsionEvaluationBaseChangeIso (a : Datum P S g d n) (f : T ⟶ S)
    (r : Fin (2 * g) → ZMod n) :
    (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pullback (a.torsionPoint r)).obj a.cubicBundle.obj) ≅
      (Scheme.Modules.pullback ((a.pullback f).torsionPoint r)).obj
        (a.pullback f).cubicBundle.obj :=
  compIso f (a.torsionPoint r) ((a.pullback f).torsionPoint r ≫ pullback.fst a.abelian.X.hom f)
      (a.torsionPoint_pullback_fst f r).symm a.cubicBundle.obj ≪≫
    (compIso ((a.pullback f).torsionPoint r) (pullback.fst a.abelian.X.hom f) _ rfl
      a.cubicBundle.obj).symm ≪≫
    (Scheme.Modules.pullback ((a.pullback f).torsionPoint r)).mapIso
      ((LineBundle.forget _).mapIso (a.cubicBundlePullbackIso f)).symm

/-- Torsion evaluation commutes with base change, through the canonical direct-image
comparison. -/
theorem Datum.rigidificationBaseChangeMap_comp_torsionEvaluation (a : Datum P S g d n)
    (f : T ⟶ S) (r : Fin (2 * g) → ZMod n) :
    a.rigidificationBaseChangeMap f ≫ (a.pullback f).torsionEvaluation r =
      (Scheme.Modules.pullback f).map (a.torsionEvaluation r) ≫
        (a.torsionEvaluationBaseChangeIso f r).hom := by
  have hq := a.torsionPoint_pullback_fst f r
  have hσ := a.torsionPoint_hom r
  have hσ' := (a.pullback f).torsionPoint_hom r
  have hn1 := (Scheme.Modules.pullbackId T).inv.naturality (a.rigidificationBaseChangeMap f)
  have hn2 : (Scheme.Modules.pullback (𝟙 T)).map (a.rigidificationBaseChangeMap f) ≫
      (compIso ((a.pullback f).torsionPoint r) (a.pullback f).abelian.X.hom (𝟙 T) hσ'
        (a.pullback f).rigidificationModule).inv =
      (compIso ((a.pullback f).torsionPoint r) (a.pullback f).abelian.X.hom (𝟙 T) hσ'
        ((Scheme.Modules.pullback f).obj a.rigidificationModule)).inv ≫
        (Scheme.Modules.pullback ((a.pullback f).torsionPoint r)).map
          ((Scheme.Modules.pullback (a.pullback f).abelian.X.hom).map
            (a.rigidificationBaseChangeMap f)) := by
    rw [Iso.comp_inv_eq, Category.assoc, compIso_naturality, Iso.inv_hom_id_assoc]
  have hce : (Scheme.Modules.pullback (a.pullback f).abelian.X.hom).map
        (a.rigidificationBaseChangeMap f) ≫ (a.pullback f).cubicEvaluationAdjoint =
      (pullbackSquareIso f a.abelian.X.hom (a.pullback f).abelian.X.hom
          (pullback.fst a.abelian.X.hom f) pullback.condition).inv.app a.rigidificationModule ≫
        (Scheme.Modules.pullback (pullback.fst a.abelian.X.hom f)).map a.cubicEvaluationAdjoint ≫
        ((LineBundle.forget _).mapIso (a.cubicBundlePullbackIso f)).inv := by
    rw [← Category.assoc, a.cubicEvaluationAdjoint_baseChange f]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hcoh := section_baseChange_coherence a.abelian.X.hom (a.torsionPoint r) hσ f
    (pullback.fst a.abelian.X.hom f) (a.pullback f).abelian.X.hom pullback.condition
    ((a.pullback f).torsionPoint r) hσ' hq a.rigidificationModule
  have hn3 := compIso_naturality f (a.torsionPoint r)
    ((a.pullback f).torsionPoint r ≫ pullback.fst a.abelian.X.hom f) hq.symm
    a.cubicEvaluationAdjoint
  have hn4 : (Scheme.Modules.pullback
        ((a.pullback f).torsionPoint r ≫ pullback.fst a.abelian.X.hom f)).map
        a.cubicEvaluationAdjoint ≫
      (compIso ((a.pullback f).torsionPoint r) (pullback.fst a.abelian.X.hom f) _ rfl
        a.cubicBundle.obj).inv =
      (compIso ((a.pullback f).torsionPoint r) (pullback.fst a.abelian.X.hom f) _ rfl
        ((Scheme.Modules.pullback a.abelian.X.hom).obj a.rigidificationModule)).inv ≫
        (Scheme.Modules.pullback ((a.pullback f).torsionPoint r)).map
          ((Scheme.Modules.pullback (pullback.fst a.abelian.X.hom f)).map
            a.cubicEvaluationAdjoint) := by
    rw [Iso.comp_inv_eq, Category.assoc, compIso_naturality, Iso.inv_hom_id_assoc]
  rw [Datum.torsionEvaluation_eq, Datum.torsionEvaluation_eq]
  simp only [Datum.torsionEvaluationBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, CategoryTheory.Functor.map_comp]
  erw [reassoc_of% hn1]
  have hce' := congrArg (Scheme.Modules.pullback ((a.pullback f).torsionPoint r)).map hce
  simp only [CategoryTheory.Functor.map_comp] at hce'
  rw [reassoc_of% hn2, hce', reassoc_of% hcoh, reassoc_of% hn3, reassoc_of% hn4]

/-- The comparison of the targets of a frame evaluation and of its base change. -/
def Datum.frameEvaluationBaseChangeIso {m : ℕ} (a : Datum P S g d n) (f : T ⟶ S)
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) (k : Fin (m + 2)) :
    (Scheme.Modules.pullback f).obj (∏ᶜ fun j : {j : Fin (m + 2) // j ≠ k} =>
        (Scheme.Modules.pullback (a.torsionPoint (ρ j))).obj a.cubicBundle.obj) ≅
      ∏ᶜ fun j : {j : Fin (m + 2) // j ≠ k} =>
        (Scheme.Modules.pullback ((a.pullback f).torsionPoint (ρ j))).obj
          (a.pullback f).cubicBundle.obj :=
  PreservesProduct.iso (Scheme.Modules.pullback f) _ ≪≫
    Pi.mapIso fun j => a.torsionEvaluationBaseChangeIso f (ρ j)

/-- Frame evaluation commutes with base change, through the canonical direct-image
comparison. -/
theorem Datum.rigidificationBaseChangeMap_comp_frameEvaluation {m : ℕ} (a : Datum P S g d n)
    (f : T ⟶ S) (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) (k : Fin (m + 2)) :
    a.rigidificationBaseChangeMap f ≫ (a.pullback f).frameEvaluation ρ k =
      (Scheme.Modules.pullback f).map (a.frameEvaluation ρ k) ≫
        (a.frameEvaluationBaseChangeIso f ρ k).hom := by
  apply Pi.hom_ext
  intro j
  simp only [Datum.frameEvaluation, Datum.frameEvaluationBaseChangeIso, Category.assoc,
    Iso.trans_hom, PreservesProduct.iso_hom]
  rw [Pi.lift_comp_π, Pi.mapIso_hom_π, piComparison_comp_π_assoc,
    ← CategoryTheory.Functor.map_comp_assoc, Pi.lift_comp_π]
  exact a.rigidificationBaseChangeMap_comp_torsionEvaluation f (ρ j)

/-- Over a locally noetherian base, a point of the new base lies in the frame locus of
the pulled-back datum exactly when its image lies in the original frame locus. -/
theorem Datum.mem_frameLocus_pullback_iff [IsLocallyNoetherian S] (hd : 0 < d) {m : ℕ}
    (a : Datum P S g d n) (f : T ⟶ S) (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) (t : T) :
    t ∈ (a.pullback f).frameLocus ρ ↔ f t ∈ a.frameLocus ρ := by
  obtain ⟨hrank, hbc⟩ := cubicDirectImage P S g d n hd a
  have : IsIso (a.rigidificationBaseChangeMap f) := hbc T f
  have hV := hasFiniteLocalBasis_of_isLocallyFreeOfRank hrank
  have hV' : Langlands.Scheme.Modules.HasFiniteLocalBasis (a.pullback f).rigidificationModule :=
    hasFiniteLocalBasis_of_isLocallyFreeOfRank
      (((pullbackFiniteLocalBasisRank T S f _).2 _ hrank).ofIso
        (asIso (a.rigidificationBaseChangeMap f)))
  rw [← SetLike.mem_coe, (a.pullback f).coe_frameLocus hV', ← SetLike.mem_coe,
    a.coe_frameLocus hV, Set.mem_iInter, Set.mem_iInter]
  refine forall_congr' fun k => ?_
  rw [← mem_isoLocus_iff_of_comm (asIso (a.rigidificationBaseChangeMap f))
    (a.frameEvaluationBaseChangeIso f ρ k) _ _
    (a.rigidificationBaseChangeMap_comp_frameEvaluation f ρ k) t]
  exact mem_isoLocus_pullback_iff_of_hasFiniteLocalBasis f hV
    (a.hasFiniteLocalBasis_frameTarget ρ k) _ t

/-- The projective frame locus is compatible with arbitrary base change over a
locally noetherian base. -/
theorem frameLocusBaseChange : FrameLocusBaseChangeStatement.{u} := by
  intro P S T _ g d n hd a f ρ
  ext t
  exact a.mem_frameLocus_pullback_iff hd f ρ t

end Langlands.AbelianScheme.PolarizedFiniteLevel
