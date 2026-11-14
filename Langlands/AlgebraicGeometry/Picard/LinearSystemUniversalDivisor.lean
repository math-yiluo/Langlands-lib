import Langlands.AlgebraicGeometry.Picard.LinearSystemFibres
import Langlands.AlgebraicGeometry.Picard.PointIdealGluing
import Langlands.RingTheory.Grassmannian.LineQuotientCoordinates

/-! # The universal divisor of the linear system over a Grassmannian

Let `C` be a Čech representative of a line bundle `L` on `Y` over `Spec R` (with frames on the
cover), `Q` its module, and `D` a representing scheme of the Grassmannian of rank-one quotients
of `Q`. On the `B`-points of `D.Gr` landing in a chart, the zero locus of the section attached to
the chart coordinates of the corresponding quotient is natural; these glue to an ideal sheaf `W`
on `Y ×_R D.Gr`. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule

open scoped TensorProduct
open Scheme.TwoAffineOpenCover Langlands.RingTheory.Grassmannian.LineQuotientCoordinates
open Module.Grassmannian.ProjectiveEmbedding (Rep InChart)

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)} {L : LineBundle X}
  {𝒰 : X.OrderedAffineCover} (e : ∀ i, Γ(L.obj, 𝒰.U i))
  (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (𝒰.U i)) (C : CechRep π L.obj 𝒰)
  (D : Rep R C.Q 1)

namespace LinSys

variable {C}

/-- The rank-one quotient corresponding to a point of the Grassmannian. -/
def ptOf {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ D.Gr)
    (hk : k ≫ D.p = specMap R B) : Module.Grassmannian B (B ⊗[R] C.Q) 1 :=
  (D.pt B).symm ⟨k, hk⟩

lemma pt_ptOf {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ D.Gr)
    (hk : k ≫ D.p = specMap R B) : (D.pt B (ptOf D k hk)).1 = k := by
  rw [ptOf, Equiv.apply_symm_apply]

/-- Points landing in a chart. -/
def InSomeChart {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ D.Gr) : Prop :=
  ∃ x : C.Q, Set.range k.base ⊆ (D.V (fun _ => x) : Set D.Gr)

lemma inChart_ptOf {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ D.Gr)
    (hk : k ≫ D.p = specMap R B) (x : C.Q)
    (hx : Set.range k.base ⊆ (D.V (fun _ => x) : Set D.Gr)) :
    InChart (fun _ => x) (ptOf D k hk) := by
  have h := (D.hVchart (fun _ => x) B (ptOf D k hk)).1
  rw [pt_ptOf] at h
  exact h hx

/-- The chart coordinates of an admissible point. -/
def vOf {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ D.Gr)
    (hk : k ≫ D.p = specMap R B) (hP : InSomeChart D k) : C.Q →ₗ[R] B :=
  coord hP.choose (ptOf D k hk) (inChart_ptOf D k hk _ hP.choose_spec)

lemma span_range_vOf {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ D.Gr)
    (hk : k ≫ D.p = specMap R B) (hP : InSomeChart D k) :
    Ideal.span (Set.range (vOf D k hk hP)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  apply Ideal.subset_span
  exact ⟨hP.choose, coord_self _ _ _⟩

lemma ptOf_comp {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (φ : B →ₐ[R] B') (k : Spec (.of B) ⟶ D.Gr) (hk : k ≫ D.p = specMap R B)
    (hk' : (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ k) ≫ D.p = specMap R B') :
    ptOf D (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ k) hk' =
      Module.Grassmannian.map φ (ptOf D k hk) := by
  apply (D.pt B').injective
  apply Subtype.ext
  rw [D.hpt, pt_ptOf, ptOf, Equiv.apply_symm_apply]

lemma coord_congr {B : Type u} [CommRing B] [Algebra R B] (x : C.Q)
    {N N' : Module.Grassmannian B (B ⊗[R] C.Q) 1} (h : N = N') (hN : InChart (fun _ => x) N)
    (hN' : InChart (fun _ => x) N') : coord x N hN = coord x N' hN' := by
  subst h; rfl

lemma vOf_comp {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (φ : B →ₐ[R] B') (k : Spec (.of B) ⟶ D.Gr) (hk : k ≫ D.p = specMap R B)
    (hP : InSomeChart D k)
    (hk' : (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ k) ≫ D.p = specMap R B')
    (hP' : InSomeChart D (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ k)) :
    ∃ c : B', IsUnit c ∧
      vOf D (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ k) hk' hP' =
        c • (φ.toLinearMap ∘ₗ vOf D k hk hP) := by
  set x₁ := hP.choose
  set x₂ := hP'.choose
  have hr : Set.range (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ k).base ⊆
      (D.V (fun _ => x₁) : Set D.Gr) := by
    rintro _ ⟨y, rfl⟩
    exact hP.choose_spec ⟨_, rfl⟩
  have h₁ := inChart_ptOf D _ hk' x₁ hr
  have h₂ := inChart_ptOf D _ hk' x₂ hP'.choose_spec
  have hcomp := ptOf_comp D φ k hk hk'
  obtain ⟨hu, hch⟩ := coord_change x₂ x₁ _ h₂ h₁
  refine ⟨coord x₂ (ptOf D _ hk') h₂ x₁, hu, hch.trans ?_⟩
  congr 1
  have hN : InChart (fun _ => x₁) (ptOf D k hk) := inChart_ptOf D k hk x₁ hP.choose_spec
  rw [coord_congr x₁ hcomp h₁ (hcomp ▸ h₁), coord_map φ x₁ _ hN]
  rfl

variable (L) in
/-- The zero locus attached to an admissible point. -/
def FOf {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ D.Gr)
    (hk : k ≫ D.p = specMap R B) (hP : InSomeChart D k) :
    (pullback π (specMap R B)).IdealSheafData :=
  SectionZeroIdeal.zeroIdeal (pbLB (pullback.fst π (specMap R B)) L)
    (C.homEquivSections B (vOf D k hk hP))

include he in
lemma FOf_comp {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (φ : B →ₐ[R] B') (k : Spec (.of B) ⟶ D.Gr) (hk : k ≫ D.p = specMap R B)
    (hP : InSomeChart D k)
    (hk' : (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ k) ≫ D.p = specMap R B')
    (hP' : InSomeChart D (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ k)) :
    FOf L D (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ k) hk' hP' =
      (FOf L D k hk hP).comap (bcMap (π := π) B' φ) := by
  obtain ⟨c, hc, hv⟩ := vOf_comp D φ k hk hP hk' hP'
  rw [FOf, FOf, hv, zeroIdeal_homEquivSections_smul e he C c hc,
    zeroIdeal_comap_homEquivSections e he C (bcMap (π := π) B' φ) φ (bcMap_fst B' φ)
      (bcMap_snd B' φ)]

include he in
/-- **The point ideals of the linear system.** -/
def pointIdeals : PointIdeals π D.p where
  P k := InSomeChart D k
  F k hk hP := FOf L D k hk hP
  P_comp φ k hP := ⟨hP.choose, by
    rintro _ ⟨y, rfl⟩
    exact hP.choose_spec ⟨_, rfl⟩⟩
  F_comp φ k hk hP := FOf_comp e he D φ k hk hP _ _
  cover z := by
    obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp (D.hV.ge (Set.mem_univ z))
    have hxe : x = fun _ => x 0 := funext fun i => by rw [Subsingleton.elim i 0]
    obtain ⟨_, ⟨O, hO, rfl⟩, hzO, hOV⟩ :=
      D.Gr.isBasis_affineOpens.exists_subset_of_mem_open hx (D.V x).2
    refine ⟨⟨O, hO⟩, hzO, x 0, ?_⟩
    rintro _ ⟨w, rfl⟩
    have h := (range_affPt (⟨O, hO⟩ : D.Gr.affineOpens)).subset ⟨w, rfl⟩
    rw [← hxe]
    exact hOV h

include he in
/-- **The universal divisor.** -/
theorem exists_universalDivisor : ∃ W : (pullback π D.p).IdealSheafData,
    ∀ {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ D.Gr)
      (hk : k ≫ D.p = specMap R B) (hP : InSomeChart D k),
      W.comap (ptMap π D.p k hk) = FOf L D k hk hP := by
  obtain ⟨W, hW⟩ := (pointIdeals e he D).exists_glued
  exact ⟨W, fun k hk hP => (pointIdeals e he D).comap_ptMap hW k hk hP⟩

end LinSys

end Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule
