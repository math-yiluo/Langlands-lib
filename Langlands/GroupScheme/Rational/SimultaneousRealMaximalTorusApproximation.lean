import Langlands.GroupScheme.Rational.SimplyConnectedRealPlacesSurjectivity
import Langlands.GroupScheme.Lie.OpenMaximalTorusLieCentralizer
import Langlands.GroupScheme.Lie.ElementCentralizerFieldBaseChange
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeReflection
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.Global.RealCompletionWeakApproximation
import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldWeilRestrictionTopology

/-! # Simultaneous approximation of maximal tori at the real places -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Limits
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- A maximal torus over a number field can be chosen in independently
prescribed real rational conjugacy classes. -/
theorem simultaneousRealMaximalTorusApproximation :
    SimultaneousRealMaximalTorusApproximationStatement.{u} := by
  classical
  intro F _ _ G hG T j hj
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  by_cases hreal : Nonempty (RealPlaceIndex F)
  swap
  · obtain ⟨T₀, i, hi⟩ := maximalTorusExistence F G
    exact ⟨T₀, i, hi, fun w => (hreal ⟨w⟩).elim⟩
  let d := Lie.dimension G
  let c : Lie.FiniteCoordinates G d := Lie.finiteCoordinates G
  let (w : RealPlaceIndex F) : NontriviallyNormedField w.1.Completion :=
    infiniteCompletionNontriviallyNormedField w.1
  let (w : RealPlaceIndex F) : CharZero w.1.Completion :=
    charZero_of_injective_ringHom (algebraMap F w.1.Completion).injective
  let (w : RealPlaceIndex F) : IsAffineHom ((baseChange (realPlaceBaseMap w)).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (realPlaceBaseMap w))
    infer_instance
  have hopen (w : RealPlaceIndex F) :=
    Lie.exists_open_identityComponent_elementCentralizer_conjugate (K := w.1.Completion)
      (c.baseChange F w.1.Completion) (j w)
      (connectedReductiveFieldExtensionStatement F w.1.Completion G hG) (hj w)
  choose U hU hUn hcentral using hopen
  obtain ⟨v, hv⟩ := (Langlands.Global.realCompletionVectorWeakApproximation F d).exists_mem_open
    (isOpen_set_pi Set.finite_univ fun w _ => hU w) (Set.univ_pi_nonempty_iff.mpr hUn)
  let X : lieKernel G F := ((c.equiv (.of (CommRingCat.of F) F)).symm v).toMul
  obtain ⟨C, i, hrep, hi⟩ := Lie.elementCentralizer_isClosedRepresentable G X
  let : IsAffineHom C.X.hom := hi.isAffineHom
  let : LocallyOfFiniteType C.X.hom := by
    have : IsClosedImmersion i.hom.hom.left := hi
    rw [← Over.w i.hom.hom]
    infer_instance
  let : Smooth C.X.hom := affineCartierSmooth F C inferInstance inferInstance
  let C₀ := identityComponent C
  let i₀ : C₀ ⟶ G := identityComponentι C ≫ i
  have hi₀ : IsClosedSubgroup i₀ := (IdentityComponent.isClosedSubgroup_identityComponentι C).comp hi
  have hloc (w : RealPlaceIndex F) :
      let b := realPlaceBaseMap w
      ∃ (a : (baseChange b).obj C₀ ≅ (T w).toGrp)
        (g : Over.mk (𝟙 _) ⟶ ((baseChange b).obj G).X),
        (baseChange b).map i₀ ≫ (((baseChange b).obj G).innerIso g).hom = a.hom ≫ j w := by
    let K := w.1.Completion
    let b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F) := algebraBaseMap F K
    let B := GroupScheme.baseChange b
    let H := B.obj G
    let Cw := B.obj C
    let : IsAffineHom Cw.X.hom := inferInstanceAs (IsAffineHom (pullback.snd C.X.hom b))
    let : Smooth Cw.X.hom := inferInstanceAs (Smooth (pullback.snd C.X.hom b))
    let vK : Fin d → K := fun a => algebraMap F K (v a)
    let cH := c.baseChange F K
    let Xw := Lie.kernelFieldExtension (K := K) G X
    have hXw : cH.equiv (.of (CommRingCat.of K) K) (Additive.ofMul Xw) = vK := by
      change (c.baseChange F K).equiv (.of (CommRingCat.of K) K)
        (Additive.ofMul (Lie.kernelFieldExtension (K := K) G X)) = vK
      rw [Lie.FiniteCoordinates.baseChange_equiv_apply, Lie.kernelBaseChangeLinearEquiv_ofMul,
        Lie.kernelFieldExtension, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply]
      have hc := c.naturality (CommAlgCat.ofHom (Algebra.ofId F K)) (Additive.ofMul X)
      change c.equiv (.of (CommRingCat.of F) K)
        (lieKernelMapLinear G (Algebra.ofId F K) (Additive.ofMul X)) = _ at hc
      change c.equiv (.of (CommRingCat.of F) K)
        (lieKernelMapLinear G (Algebra.ofId F K) (Additive.ofMul X)) = vK
      rw [hc]
      simp only [X, ofMul_toMul, LinearEquiv.apply_symm_apply]
      rfl
    have hX : ((cH.equiv (.of (CommRingCat.of K) K)).symm vK).toMul = Xw := by
      rw [← hXw, LinearEquiv.symm_apply_apply, toMul_ofMul]
    have hrepw : (Lie.elementCentralizer H
        ((cH.equiv (.of (CommRingCat.of K) K)).symm vK).toMul).IsRepresentedBy (B.map i) := by
      rw [hX]
      change (Lie.elementCentralizer ((GroupScheme.baseChange (algebraBaseMap F K)).obj G)
        (Lie.kernelFieldExtension (K := K) G X)).IsRepresentedBy (B.map i)
      rw [Lie.elementCentralizer_fieldBaseChange (E := K) X]
      exact hrep.baseChange b
    have hvK : vK ∈ U w := hv w (Set.mem_univ _)
    obtain ⟨g, a, ha⟩ := hcentral w vK hvK Cw (B.map i) (hi.baseChange b) hrepw
    let e : B.obj C₀ ≅ identityComponent Cw := IdentityComponent.baseChangeIso C (algebraMap F K)
    have he : e.hom ≫ identityComponentι Cw ≫ B.map i = B.map i₀ := by
      change (IdentityComponent.baseChangeIso C (algebraMap F K)).hom ≫
        identityComponentι Cw ≫ B.map i = B.map (identityComponentι C ≫ i)
      rw [IdentityComponent.baseChangeIso_hom_identityComponentι_assoc, Functor.map_comp]
    have ha' : (identityComponentι Cw ≫ B.map i) ≫ (H.innerIso g).inv = a.inv ≫ j w := by
      calc
        _ = a.inv ≫ ((a.hom ≫ identityComponentι Cw ≫ B.map i) ≫ (H.innerIso g).inv) := by
          rw [← Category.assoc a.inv, Iso.inv_hom_id_assoc]
        _ = a.inv ≫ j w := by rw [ha, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    refine ⟨e ≪≫ a.symm, g⁻¹, ?_⟩
    change B.map i₀ ≫ (H.innerIso g⁻¹).hom = (e.hom ≫ a.inv) ≫ j w
    rw [H.innerIso_inv_hom, ← he, Category.assoc, ha', Category.assoc]
  let w₀ := Classical.choice hreal
  obtain ⟨e₀, g₀, he₀⟩ := hloc w₀
  have hT₀ : IsTorus C₀ := IsTorus.of_baseChange (K := w₀.1.Completion)
    (IsTorus.of_iso e₀ (hj w₀).1)
  let T₀ : CommGroupScheme (Spec (CommRingCat.of F)) := { C₀ with comm := hT₀.isCommMonObj }
  have hmax : IsMaximalTorus (T := T₀) i₀ := by
    apply IsMaximalTorus.of_baseChange (K := w₀.1.Completion) hi₀
    apply (IsMaximalTorus.comp_iso_iff (k := w₀.1.Completion) _
      (((baseChange (realPlaceBaseMap w₀)).obj G).innerIso g₀)).mp
    change IsMaximalTorus (k := w₀.1.Completion)
      (T := (CommGroupScheme.baseChange (realPlaceBaseMap w₀)).obj T₀)
      ((baseChange (realPlaceBaseMap w₀)).map i₀ ≫
        (((baseChange (realPlaceBaseMap w₀)).obj G).innerIso g₀).hom)
    rw [he₀]
    exact IsMaximalTorus.iso_comp (k := w₀.1.Completion)
      (T' := (CommGroupScheme.baseChange (realPlaceBaseMap w₀)).obj T₀) e₀ (hj w₀)
  exact ⟨T₀, i₀, hmax, hloc⟩

end Langlands.GroupScheme
