import Langlands.AbelianScheme.PointedProjectiveAbelianLocusStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameHilbertIncidence
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingFaithful
import Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluingAbelian
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.TwistOne

/-! # Pointed abelian presentations of marked projective families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel.FrameHilbert

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable {S T : Scheme.{u}} {g n m : ℕ}
  {I : (RelativeProjectiveSpace S m).IdealSheafData}
  {σ : (Fin (2 * g) → ZMod n) → (S ⟶ ProjectiveSpace (ULift.{u} ℤ) m)}

/-- The abelian scheme structure and labelled sections of a marked closed projective family.
The zero label is the identity. The other labels are still arbitrary sections. -/
structure AbelianPresentation (I : (RelativeProjectiveSpace S m).IdealSheafData)
    (σ : (Fin (2 * g) → ZMod n) → (S ⟶ ProjectiveSpace (ULift.{u} ℤ) m)) where
  abelian : AbelianScheme S
  dimension : abelian.HasRelativeDimension g
  comparison : abelian.X.left ≅ I.subscheme
  overBase : comparison.hom ≫ projection I = abelian.X.hom
  marks : (Fin (2 * g) → ZMod n) → (S ⟶ abelian.X.left)
  marks_comp : ∀ r, marks r ≫ comparison.hom ≫ I.subschemeι =
    RelativeProjectiveSpace.lift m (𝟙 S) (σ r)
  mark_zero : marks 0 = η[abelian.X].left

namespace AbelianPresentation

variable (B : AbelianPresentation I σ)

/-- The chosen abelian scheme embeds as the actual family. -/
def embedding : B.abelian.X.left ⟶ RelativeProjectiveSpace S m :=
  B.comparison.hom ≫ I.subschemeι

instance : IsClosedImmersion B.embedding := inferInstanceAs (IsClosedImmersion (_ ≫ _))

@[reassoc (attr := simp)]
theorem embedding_toBase : B.embedding ≫ RelativeProjectiveSpace.toBase S m = B.abelian.X.hom :=
  (Category.assoc _ _ _).trans B.overBase

@[simp] theorem embedding_ker : B.embedding.ker = I := by
  rw [embedding, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

@[reassoc (attr := simp)]
theorem marks_embedding (r : Fin (2 * g) → ZMod n) :
    B.marks r ≫ B.embedding = RelativeProjectiveSpace.lift m (𝟙 S) (σ r) := B.marks_comp r

@[reassoc (attr := simp)]
theorem marks_overBase (r : Fin (2 * g) → ZMod n) : B.marks r ≫ B.abelian.X.hom = 𝟙 S := by
  rw [← B.embedding_toBase, B.marks_embedding_assoc, RelativeProjectiveSpace.lift_toBase]

/-- The labels as maps over the base. -/
def markedSection (r : Fin (2 * g) → ZMod n) : Over.mk (𝟙 S) ⟶ B.abelian.X :=
  Over.homMk (B.marks r) (B.marks_overBase r)

/-- A pointed abelian presentation of the Cartesian family, with its pulled-back marks. -/
def ofPointedPullback (t : T ⟶ S) (marks : (Fin (2 * g) → ZMod n) → (S ⟶ I.subscheme))
    (hm : ∀ r, marks r ≫ I.subschemeι = RelativeProjectiveSpace.lift m (𝟙 S) (σ r))
    (A : AbelianScheme T) (e : A.X.left ≅ pullback (projection I) t)
    (hg : A.HasRelativeDimension g) (hbase : e.hom ≫ pullback.snd (projection I) t = A.X.hom)
    (hunit : η[A.X].left ≫ e.hom ≫ pullback.fst (projection I) t = t ≫ marks 0) :
    AbelianPresentation (I.comap (RelativeProjectiveSpace.map m t)) (fun r => t ≫ σ r) := by
  let J := I.comap (RelativeProjectiveSpace.map m t)
  let c := isPullback_subschemeBaseChange I t
  have hsection (r : Fin (2 * g) → ZMod n) : marks r ≫ projection I = 𝟙 S := by
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ RelativeProjectiveSpace.toBase S m) (hm r))).trans
        (RelativeProjectiveSpace.lift_toBase _ _ _)
  let q (r : Fin (2 * g) → ZMod n) : T ⟶ pullback (projection I) t :=
    pullback.lift (t ≫ marks r) (𝟙 T) (by rw [Category.assoc, hsection, Category.comp_id,
      Category.id_comp])
  refine ⟨A, hg, e ≪≫ c.isoPullback.symm, ?_, fun r => q r ≫ e.inv, ?_, ?_⟩
  · change e.hom ≫ c.isoPullback.inv ≫ projection J = A.X.hom
    rw [c.isoPullback_inv_snd, hbase]
  · intro r
    apply RelativeProjectiveSpace.hom_ext
    · rw [RelativeProjectiveSpace.lift_toBase]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
      change q r ≫ e.inv ≫ e.hom ≫ c.isoPullback.inv ≫
        projection (I.comap (RelativeProjectiveSpace.map m t)) = 𝟙 T
      rw [Iso.inv_hom_id_assoc, c.isoPullback_inv_snd]
      exact pullback.lift_snd _ _ _
    · rw [RelativeProjectiveSpace.lift_toIntegral]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
      change (q r ≫ e.inv) ≫ (e.hom ≫ c.isoPullback.inv) ≫ J.subschemeι ≫
          RelativeProjectiveSpace.toIntegral T m = t ≫ σ r
      rw [show J.subschemeι ≫ RelativeProjectiveSpace.toIntegral T m =
          subschemeBaseChange I t ≫ I.subschemeι ≫ RelativeProjectiveSpace.toIntegral S m by
        simp [J]]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, c.isoPullback_inv_fst_assoc,
        q, pullback.lift_fst_assoc, reassoc_of% hm, RelativeProjectiveSpace.lift_toIntegral]
  · apply (cancel_mono e.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hunit.symm
    · rw [Category.assoc, hbase, pullback.lift_snd, ← unitSection_eq_one_left, unitSection_comp]

private def comparePullback (t : T ⟶ S) :
    Limits.pullback B.abelian.X.hom t ≅ Limits.pullback (projection I) t :=
  asIso (Limits.pullback.map B.abelian.X.hom t (projection I) t B.comparison.hom (𝟙 T)
    (𝟙 S) (by simpa only [Category.comp_id] using B.overBase.symm) (by simp))

@[reassoc]
private theorem comparePullback_hom_fst (t : T ⟶ S) :
    (B.comparePullback t).hom ≫ Limits.pullback.fst (projection I) t =
      Limits.pullback.fst B.abelian.X.hom t ≫ B.comparison.hom :=
  Limits.pullback.lift_fst _ _ _

private theorem comparePullback_hom_snd (t : T ⟶ S) :
    (B.comparePullback t).hom ≫ Limits.pullback.snd (projection I) t =
      Limits.pullback.snd B.abelian.X.hom t :=
  (Limits.pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- Base change of a chosen abelian scheme presentation, with the actual changed group law. -/
def pullback (t : T ⟶ S) :
    AbelianPresentation (I.comap (RelativeProjectiveSpace.map m t)) (fun r => t ≫ σ r) := by
  let A := B.abelian
  refine ofPointedPullback t (fun r => B.marks r ≫ B.comparison.hom) (fun r => ?_)
    ((baseChange t).obj A) (B.comparePullback t)
    (A.hasRelativeDimension_baseChange g B.dimension t) (B.comparePullback_hom_snd t) ?_
  · exact (Category.assoc _ _ _).trans (B.marks_comp r)
  · rw [← unitSection_eq_one_left, B.comparePullback_hom_fst, ← Category.assoc,
      unitSection_baseChange_fst, Category.assoc, unitSection_eq_one_left, B.mark_zero]

/-- Naturality of the chosen projective embedding. -/
@[reassoc]
theorem pullback_embedding_map (t : T ⟶ S) :
    (B.pullback t).embedding ≫ RelativeProjectiveSpace.map m t =
      Limits.pullback.fst B.abelian.X.hom t ≫ B.embedding := by
  unfold embedding pullback ofPointedPullback
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← subschemeBaseChange_subschemeι, IsPullback.isoPullback_inv_fst_assoc,
    B.comparePullback_hom_fst_assoc]

/-- Naturality of the sections of the chosen pointed presentation. -/
@[reassoc]
theorem pullback_marks_fst (t : T ⟶ S) (r : Fin (2 * g) → ZMod n) :
    (B.pullback t).marks r ≫ Limits.pullback.fst B.abelian.X.hom t = t ≫ B.marks r := by
  apply (cancel_mono B.comparison.hom).mp
  have h : (B.pullback t).marks r ≫ Limits.pullback.fst B.abelian.X.hom t ≫ B.comparison.hom =
      t ≫ B.marks r ≫ B.comparison.hom := by
    change (Limits.pullback.lift _ _ _ ≫ (B.comparePullback t).inv) ≫
      Limits.pullback.fst B.abelian.X.hom t ≫ B.comparison.hom = _
    rw [Category.assoc, ← B.comparePullback_hom_fst, Iso.inv_hom_id_assoc,
      Limits.pullback.lift_fst]
  simpa only [Category.assoc] using h

/-- The twist for the changed embedding is the pullback of the original twist. -/
def pullbackTwistIso (t : T ⟶ S) :
    (LineBundle.pullback (B.pullback t).embedding).obj (RelativeProjectiveSpace.twistOne T m) ≅
      (LineBundle.pullback (Limits.pullback.fst B.abelian.X.hom t ≫ B.embedding)).obj
        (RelativeProjectiveSpace.twistOne S m) :=
  (LineBundle.pullback (B.pullback t).embedding).mapIso
    (RelativeProjectiveSpace.twistOnePullbackIso m t).symm ≪≫
    (LineBundle.pullbackComp _ _).app _ ≪≫
    eqToIso (congrArg (fun f => (LineBundle.pullback f).obj (RelativeProjectiveSpace.twistOne S m))
      (B.pullback_embedding_map t))

/-- Every realization of a presented family agrees with its pointed abelian scheme
structure, as well as its embedding and labelled sections. -/
theorem exists_iso_of_realizes {P : Prerequisites.{u}} {d : ℕ}
    {a : Datum P S g d n} {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m}
    {ρ : Fin (m + 2) → Fin (2 * g) → ZMod n} (he : a.IsFrameEmbedding ρ ψ)
    (hr : a.Realizes ψ I σ) : ∃ e : B.abelian ≅ a.abelian,
      hom e.hom ≫ ψ = B.embedding ∧ ∀ r, B.marks r ≫ hom e.hom = a.torsionPoint r := by
  let := he.isClosedImmersion
  let c := hr.subschemeIso
  let e := B.comparison ≪≫ c.symm
  have hcompare : e.hom ≫ c.hom = B.comparison.hom := by simp [e]
  have hψ : e.hom ≫ ψ = B.embedding := by
    rw [← hr.subschemeIso_hom_subschemeι, ← Category.assoc, hcompare]
    rfl
  have hbase : e.hom ≫ a.abelian.X.hom = B.abelian.X.hom := by
    rw [← he.toBase, ← Category.assoc, hψ, B.embedding_toBase]
  have hmarks (r : Fin (2 * g) → ZMod n) : B.marks r ≫ e.hom = a.torsionPoint r := by
    apply (cancel_mono ψ).mp
    rw [Category.assoc, hψ, B.marks_embedding, ← hr.torsionPoint_subschemeIso he r,
      hr.subschemeIso_hom_subschemeι]
  let eO : B.abelian.X ≅ a.abelian.X := Over.isoMk e hbase
  have hunit : η[B.abelian.X] ≫ eO.hom = η[a.abelian.X] := by
    apply Over.OverMorphism.ext
    have h := hmarks 0
    rw [a.torsionPoint_zero] at h
    change B.marks 0 ≫ e.hom = unitSection a.abelian at h
    rw [B.mark_zero, unitSection_eq_one_left] at h
    exact h
  exact ⟨abelianIsoOfUnit eO hunit, hψ, hmarks⟩

end AbelianPresentation

/-- A realization on a test scheme supplies the required pointed abelian structure on
its Cartesian family when the original zero label is incident. -/
theorem hasPointedAbelianPullback_of_realizes {P : Prerequisites.{u}} {d : ℕ}
    (s : S ⟶ I.subscheme)
    (hs : s ≫ I.subschemeι = RelativeProjectiveSpace.lift m (𝟙 S) (σ 0))
    (t : T ⟶ S) {a : Datum P T g d n} {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace T m}
    {ρ : Fin (m + 2) → Fin (2 * g) → ZMod n} (he : a.IsFrameEmbedding ρ ψ)
    (hr : a.Realizes ψ (I.comap (RelativeProjectiveSpace.map m t)) (fun r => t ≫ σ r)) :
    HasPointedAbelianPullback (projection I) s g t := by
  let := he.isClosedImmersion
  let J := I.comap (RelativeProjectiveSpace.map m t)
  let q := isPullback_subschemeBaseChange I t
  let c := hr.subschemeIso
  let e := c ≪≫ q.isoPullback
  have hc : c.hom ≫ J.subschemeι = ψ := hr.subschemeIso_hom_subschemeι
  have hf : e.hom ≫ Limits.pullback.fst (projection I) t =
      c.hom ≫ subschemeBaseChange I t := by
    simp only [e, Iso.trans_hom, Category.assoc, q.isoPullback_hom_fst]
  refine ⟨a.abelian, e, a.dimension, ?_, ?_⟩
  · change (c.hom ≫ q.isoPullback.hom) ≫ Limits.pullback.snd (projection I) t = _
    rw [Category.assoc, q.isoPullback_hom_snd]
    change c.hom ≫ J.subschemeι ≫ RelativeProjectiveSpace.toBase T m = _
    rw [← Category.assoc, hc, he.toBase]
  · have hu : η[a.abelian.X].left = a.torsionPoint 0 := by
      rw [← unitSection_eq_one_left, a.torsionPoint_zero]
      rfl
    rw [hu]
    apply (cancel_mono I.subschemeι).mp
    calc
      _ = (a.torsionPoint 0 ≫ c.hom ≫ J.subschemeι) ≫
          RelativeProjectiveSpace.map m t := by
        simp only [Category.assoc, reassoc_of% hf, subschemeBaseChange_subschemeι, J]
      _ = RelativeProjectiveSpace.lift m (𝟙 T) (t ≫ σ 0) ≫
          RelativeProjectiveSpace.map m t := by
        exact congrArg (fun f => f ≫ RelativeProjectiveSpace.map m t)
          (hr.torsionPoint_subschemeIso he 0)
      _ = (t ≫ s) ≫ I.subschemeι := by
        rw [Category.assoc, hs]
        apply RelativeProjectiveSpace.hom_ext <;> simp

end Langlands.AbelianScheme.PolarizedFiniteLevel.FrameHilbert
