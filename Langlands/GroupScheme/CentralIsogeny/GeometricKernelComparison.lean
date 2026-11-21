import Langlands.GroupScheme.AffinePoints
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.GroupScheme.CentralIsogeny.CommonSemisimpleRefinement
import Langlands.GroupScheme.CentralIsogeny.Transport
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.KernelTriviality
import Langlands.AlgebraicGeometry.ReducedGeometricSingleton
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AbelianScheme.AlgClosedIsogenyPointLifting

/-! # Comparison of isogenies by their geometric kernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 850000

variable {F K : Type u} [Field F] [CharZero F] [Field K] [Algebra F K] [IsAlgClosed K]

local notation "S" => Spec (CommRingCat.of F)
local notation "A" => CommAlgCat.of F K
local notation "T" => Functor.obj (algSpec (CommRingCat.of F)) (op A)

/-- A characteristic-zero isogeny is invertible if its geometric kernel has a single point. -/
theorem IsIsogeny.isIso_of_subsingleton_geometricKernel
    {G H : GroupScheme S} {a : G ⟶ H} (ha : IsIsogeny a)
    (hK : Subsingleton (affinePoints (kernel a) A)) : IsIso a := by
  let C := kernel a
  let b := Spec.algebraMap F K
  let Y := pullback C.X.hom b
  let pr := pullback.snd C.X.hom b
  let i := pullback.fst C.X.hom b
  have hfinite : IsFinite C.X.hom := MorphismProperty.of_isPullback (kernel_isPullback_scheme a) ha.1
  have hs : Smooth C.X.hom := affineCartierSmooth F C inferInstance inferInstance
  let : Smooth pr := inferInstanceAs (Smooth (pullback.snd C.X.hom b))
  have : IsReduced Y := Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field K Y pr
  have hpoints (x y : Spec (CommRingCat.of K) ⟶ Y) (hx : x ≫ pr = 𝟙 _) (hy : y ≫ pr = 𝟙 _) :
      x = y := by
    let tx : affinePoints C A := Over.homMk (x ≫ i) (by
      change (x ≫ i) ≫ C.X.hom = b
      rw [Category.assoc, pullback.condition, ← Category.assoc, hx, Category.id_comp])
    let ty : affinePoints C A := Over.homMk (y ≫ i) (by
      change (y ≫ i) ≫ C.X.hom = b
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy, Category.id_comp])
    apply pullback.hom_ext
    · exact congrArg (fun z : affinePoints C A => z.left) (hK.elim tx ty)
    · exact hx.trans hy.symm
  let z : affinePoints C A := 1
  let zY : Spec (CommRingCat.of K) ⟶ Y := pullback.lift z.left (𝟙 _) (by
    rw [Category.id_comp]
    exact Over.w z)
  have : Nonempty Y := ⟨zY (IsLocalRing.closedPoint K)⟩
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace pr
  obtain ⟨c, _, hc⟩ := nonempty_inter_closedPoints
    (Z := Set.univ) (Set.nonempty_of_mem (Set.mem_univ (zY (IsLocalRing.closedPoint K))))
    isClosed_univ.isLocallyClosed
  have hclosed : closedPoints Y ⊆ {c} := by
    intro d hd
    have he := hpoints (pointOfClosedPoint pr d hd) (pointOfClosedPoint pr c hc)
      (pointOfClosedPoint_comp pr d hd) (pointOfClosedPoint_comp pr c hc)
    have hv := congrArg (fun f : Spec (CommRingCat.of K) ⟶ Y => f (IsLocalRing.closedPoint K)) he
    change d = c
    rwa [pointOfClosedPoint_apply, pointOfClosedPoint_apply] at hv
  have hall : (Set.univ : Set Y) ⊆ {c} := by
    rw [← closure_closedPoints]
    exact closure_minimal hclosed hc
  let : Subsingleton Y := ⟨fun x y => (hall (Set.mem_univ x)).trans (hall (Set.mem_univ y)).symm⟩
  let : IsIso C.X.hom := Langlands.AlgebraicGeometry.reducedGeometricSingleton_isIso F K C.X.left C.X.hom
  let : Mono a.hom.hom := mono_of_kernel_hom_isIso a
  let : Mono a.hom.hom.left := Over.mono_left_of_mono a.hom.hom
  let : IsFinite a.hom.hom.left := ha.1
  let : Flat a.hom.hom.left := ha.2.1
  let : Surjective a.hom.hom.left := ha.2.2
  let : IsIso a.hom.hom.left := Flat.isIso_of_surjective_of_mono _
  let : IsIso ((Over.forget S).map a.hom.hom) := inferInstanceAs (IsIso a.hom.hom.left)
  let : IsIso a.hom.hom := isIso_of_reflects_iso a.hom.hom (Over.forget S)
  let e : G ≅ H := Grp.mkIso' (asIso a.hom.hom)
  change IsIso e.hom
  infer_instance

/-- An isogeny factoring one homomorphism through another is an isomorphism if the
geometric kernels of the factored and target maps have the same positive finite cardinality. -/
theorem IsIsogeny.isIso_of_geometricKernel_card_eq
    {G H J : GroupScheme S} {a : G ⟶ H} (ha : IsIsogeny a)
    (p : G ⟶ J) (r : H ⟶ J) (hcomm : a ≫ r = p)
    (hcard : Nat.card (affinePoints (kernel p) A) = Nat.card (affinePoints (kernel r) A))
    (hpos : 0 < Nat.card (affinePoints (kernel r) A)) : IsIso a := by
  let Z₁ := affinePoints (kernel p) A
  let Z₂ := affinePoints (kernel r) A
  have hcomp : a.hom.hom ≫ r.hom.hom = p.hom.hom :=
    congrArg (fun f : G ⟶ J => f.hom.hom) hcomm
  have hp (z : Z₁) : (z ≫ (kernelι p).hom.hom ≫ a.hom.hom) ≫ r.hom.hom = 1 := by
    rw [Category.assoc, Category.assoc, hcomp, ← Category.assoc]
    exact (kernelPointsEquiv p T z).property
  let e : Z₁ → Z₂ := fun z => (kernelPointsEquiv r T).symm
    ⟨z ≫ (kernelι p).hom.hom ≫ a.hom.hom, hp z⟩
  have he (z : Z₁) : e z ≫ (kernelι r).hom.hom = z ≫ (kernelι p).hom.hom ≫ a.hom.hom :=
    congrArg Subtype.val ((kernelPointsEquiv r T).apply_symm_apply _)
  have hs : Function.Surjective e := by
    intro z
    let x := z ≫ (kernelι r).hom.hom
    let : IsFinite a.hom.hom.left := ha.1
    let : Surjective a.hom.hom.left := ha.2.2
    obtain ⟨y, hy⟩ := Langlands.exists_point_lift_of_locallyOfFiniteType_surjective a.hom.hom.left x.left
    let y₀ : G.affinePoints A := Over.homMk y (by
      rw [← Over.w a.hom.hom, ← Category.assoc, hy]
      exact Over.w x)
    have hy₀ : y₀ ≫ a.hom.hom = x := Over.OverMorphism.ext hy
    have hz : y₀ ≫ p.hom.hom = 1 := by
      rw [← hcomm, Grp.comp_hom_hom, ← Category.assoc, hy₀]
      exact (kernelPointsEquiv r T z).property
    let w := (kernelPointsEquiv p T).symm ⟨y₀, hz⟩
    have hw : w ≫ (kernelι p).hom.hom = y₀ :=
      congrArg Subtype.val ((kernelPointsEquiv p T).apply_symm_apply ⟨y₀, hz⟩)
    refine ⟨w, (cancel_mono (kernelι r).hom.hom).mp ?_⟩
    rw [he, ← Category.assoc, hw, hy₀]
  let : Finite Z₁ := Nat.finite_of_card_ne_zero (hcard.trans_ne hpos.ne')
  let : Finite Z₂ := Nat.finite_of_card_ne_zero hpos.ne'
  let : Fintype Z₁ := Fintype.ofFinite Z₁
  let : Fintype Z₂ := Fintype.ofFinite Z₂
  have hi : Function.Injective e := (Fintype.bijective_iff_surjective_and_card e).mpr
    ⟨hs, by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hcard⟩ |>.1
  apply ha.isIso_of_subsingleton_geometricKernel (K := K)
  constructor
  intro x y
  let w (v : affinePoints (kernel a) A) := v ≫ (kernelι a).hom.hom
  have hw (v : affinePoints (kernel a) A) : w v ≫ a.hom.hom = 1 :=
    (kernelPointsEquiv a T v).property
  have hwp (v : affinePoints (kernel a) A) : w v ≫ p.hom.hom = 1 := by
    rw [← hcomm, Grp.comp_hom_hom, ← Category.assoc, hw, MonObj.one_comp]
  let z (v : affinePoints (kernel a) A) := (kernelPointsEquiv p T).symm ⟨w v, hwp v⟩
  have hz (v : affinePoints (kernel a) A) : z v ≫ (kernelι p).hom.hom = w v :=
    congrArg Subtype.val ((kernelPointsEquiv p T).apply_symm_apply ⟨w v, hwp v⟩)
  have hxy : z x = z y := by
    apply hi
    apply (cancel_mono (kernelι r).hom.hom).mp
    rw [he, he, ← Category.assoc, ← Category.assoc, hz, hz, hw, hw]
  apply (cancel_mono (kernelι a).hom.hom).mp
  change w x = w y
  rw [← hz x, ← hz y, hxy]

/-- Over a characteristic-zero field, a simply connected central cover and a semisimple
central cover of the same group are isomorphic over the target if their geometric kernels
have the same positive finite cardinality. -/
theorem exists_iso_centralCover_of_geometricKernel_card_eq
    {G H J : GroupScheme S} (p : G ⟶ J) (r : H ⟶ J)
    (hG : IsSimplyConnected G) (hH : IsSemisimple H) (hJ : IsSemisimple J)
    (hp : IsCentralIsogeny p) (hr : IsCentralIsogeny r)
    (hcard : Nat.card (affinePoints (kernel p) A) = Nat.card (affinePoints (kernel r) A))
    (hpos : 0 < Nat.card (affinePoints (kernel r) A)) :
    ∃ e : G ≅ H, e.hom ≫ r = p := by
  obtain ⟨D, q, s, hD, hq, hs, hcomm⟩ :=
    centralIsogenyCommonSemisimpleRefinement F G H J p r hG.isSemisimple hH hJ hp hr
  let : IsIso q := hG.central_isogeny_isIso D q hD hq
  let d := asIso q
  let a := d.inv ≫ s
  have ha : IsIsogeny a := (hs.iso_comp d.symm).isIsogeny
  have hf : a ≫ r = p := by
    change (inv q ≫ s) ≫ r = p
    rw [Category.assoc, ← hcomm, IsIso.inv_hom_id_assoc]
  let : IsIso a := ha.isIso_of_geometricKernel_card_eq p r hf hcard hpos
  exact ⟨asIso a, hf⟩

/-- The geometric point-count criterion for comparing an isogeny factor with two covers. -/
def GeometricKernelCardComparisonStatement : Prop :=
  ∀ (F K : Type u) [Field F] [CharZero F] [Field K] [Algebra F K] [IsAlgClosed K]
    (G H J : GroupScheme (Spec (CommRingCat.of F)))
    (a : G ⟶ H) (p : G ⟶ J) (r : H ⟶ J),
    IsIsogeny a → a ≫ r = p →
    Nat.card (affinePoints (kernel p) (CommAlgCat.of F K)) =
      Nat.card (affinePoints (kernel r) (CommAlgCat.of F K)) →
    0 < Nat.card (affinePoints (kernel r) (CommAlgCat.of F K)) → IsIso a

end Langlands.GroupScheme
