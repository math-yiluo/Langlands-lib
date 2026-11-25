/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeAffineCanonicalComparisons
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologySeparated
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyGluing
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives
-- Stacks 02KH, qcqs paragraph: the Mayer–Vietoris alternative.
-- Generalized to every compact open, without compactness of the ambient scheme.
-- Quantifying over open immersions makes the induction invariant under open-chart models.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem flatCohomologyBaseChange_bijective_of_compact_open
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]
    {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of R)) (U : X.Opens) (hU : IsCompact (U : Set X)) :
    ∀ (Y : Scheme.{u}) (j : Y ⟶ X) (_ : IsOpenImmersion j), j.opensRange = U →
      ∀ (N : Y.Modules) (_ : N.IsQuasicoherent) (n : ℕ),
        Function.Bijective (Scheme.Modules.H.baseChange (S := B) (j ≫ f) N n) := by
  classical
  let P (U : X.Opens) : Prop :=
    ∀ (Y : Scheme.{u}) (j : Y ⟶ X) (_ : IsOpenImmersion j), j.opensRange = U →
      ∀ (N : Y.Modules) (_ : N.IsQuasicoherent) (n : ℕ),
        Function.Bijective (Scheme.Modules.H.baseChange (S := B) (j ≫ f) N n)
  change P U
  apply compact_open_induction_on (P := P) U hU
  · intro Y j hj hjrange N hN n
    have : IsEmpty Y := ⟨fun y ↦ by
      have hy : j y ∈ j.opensRange := ⟨y, rfl⟩
      rw [hjrange] at hy
      exact hy⟩
    exact Scheme.Modules.H.baseChange_bijective_of_isSeparated _ N n
  · intro U hU V ih Y j hj hjrange N hN n
    let A : Y.Opens := j ⁻¹ᵁ U
    let C : Y.Opens := j ⁻¹ᵁ V.1
    have hAimage : j ''ᵁ A = U := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, hjrange,
        inf_eq_right.mpr le_sup_left]
    have hC : IsAffineOpen C :=
      V.2.preimage_of_isOpenImmersion j (hjrange.symm ▸ le_sup_right)
    have hAc : IsCompact (A : Set Y) :=
      j.isOpenEmbedding.isEmbedding.isCompact_iff.mpr (by
        change IsCompact (j ''ᵁ A : Set X)
        rw [hAimage]
        exact hU)
    have : CompactSpace A.toScheme := isCompact_iff_compactSpace.mp hAc
    have : QuasiSeparatedSpace Y := j.isOpenEmbedding.quasiSeparatedSpace
    have hIc : IsCompact ((A ⊓ C : Y.Opens) : Set Y) :=
      hAc.inter_of_isOpen hC.isCompact A.isOpen C.isOpen
    have : CompactSpace (A ⊓ C).toScheme := isCompact_iff_compactSpace.mp hIc
    have : IsAffine C.toScheme := hC
    have : (A ⊓ C).toScheme.IsSeparated := ⟨by
      rw [← Limits.terminal.comp_from (Y.homOfLE (inf_le_right : A ⊓ C ≤ C))]
      infer_instance⟩
    apply Scheme.Modules.H.baseChange_bijective_of_openCover _ N A C ?_ ?_ ?_ ?_ n
    · change j ⁻¹ᵁ U ⊔ j ⁻¹ᵁ V.1 = ⊤
      rw [← j.preimage_sup, ← hjrange, j.preimage_opensRange]
    · intro r
      apply ih A.toScheme (A.ι ≫ j) inferInstance ?_ _ inferInstance r
      rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, hAimage]
    · intro r
      exact Scheme.Modules.H.baseChange_bijective_of_isSeparated _ _ r
    · intro r
      exact Scheme.Modules.H.baseChange_bijective_of_isSeparated _ _ r

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Target affine dictionary for a source comparison with a normalized linear lift.
Source: Stacks Project, Tags 02KH (both parts), 01XJ, 01E4 and 03FD.
(blueprint: new-flat-base-change-affine-target)

Proof: Write A = Gamma(V), B = Gamma(W), H = HOver(h,N,p), T = B tensor_A H,
and C = HOver(h_B,N_B,p). First use the canonical module/abelian comparison on
section complexes, denoted e0, rather than the supplied arbitrary additive eH.
As in the source construction, affine Leray and the tensor-pullback section
formula give a B-linear equivalence a0 from T to Gamma(g^*P,W), normalized by e0.
The affine chart square identifies U_B with f' inverse W and N_B with g'^*F
restricted there. Higher images of the latter are quasi-coherent by the qcqs
higher-image theorem; affine vanishing makes its cocycle-normalized Leray edge
invertible. Composing the chart and module/abelian comparisons with this edge
gives a canonical B-linear equivalence b0 from C to Gamma(Q,W).

On the common section complexes, an augmented resolution comparison computing
moduleCohomologyFMap(D.psi) and the exact inverse-image Ext comparison compute
the same map of cohomology classes. The augmentation and components equations
in D remove changes of resolutions, and D.unit_square identifies the coefficient
map with the pullback unit. Thus b0(baseChangeLinear(y)) is the displayed target
class evaluated on e0 inverse y, after restriction to W. This compatibility is
proved on complexes, without assuming the parent dictionary or beta isomorphism.

Let c : T equiv_B C be the canonical H.baseChange equivalence. It is invertible
by flat cohomology base change: B is A-flat by g.flat_appLE, U is qcqs by f and
V affine, and N is quasi-coherent. More explicitly, the separated case uses a
finite affine Cech cover and exact tensor; compact-open induction and the
Mayer-Vietoris gluing theorem extend it to qcqs U. No resolution beta is used.
Regard the supplied bijective linear a as an equivalence and put
b = b0 composed with c composed with a0 inverse composed with a composed with
c inverse. All factors are B-linear equivalences. Source normalization at s = 1
gives a(1 tensor xi) = a0(1 tensor e0(eH inverse xi)). Since
baseChangeLinear(xi) = c(1 tensor xi), cancellation gives
b(baseChangeLinear(xi)) = b0(baseChangeLinear(e0(eH inverse xi))). Apply the
canonical compatibility above and cancel e0 inverse with e0; this is the
required formula. Empty opens, zero coefficients and degree zero obey the same
identities. The normalized lift assumption is essential: an arbitrary additive
eH need not induce a B-linear change of coordinates. -/
theorem Scheme.Modules.exists_flatBaseChange_affine_target
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] [Flat (pullback.snd g f)]
    (F : X.Modules) [F.IsQuasicoherent]
    (I : InjectiveResolution F)
    (J : InjectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F))
    (p : ℕ) (V : S.Opens) (W : S'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (eVW : W ≤ g ⁻¹ᵁ V)
    (D : Scheme.Modules.FlatBaseChangeOpenChoices f g F I J V) :
    letI : Algebra Γ(S, V) Γ(S', W) := (g.appLE V W eVW).hom.toAlgebra
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    let N := (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F
    let P := ((Scheme.Modules.pushforward f).rightDerived p).obj F
    let Q := ((Scheme.Modules.pushforward (pullback.fst g f)).rightDerived p).obj
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F)
    ∀ (eH : ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) ≃+
          Scheme.Modules.HOver h N p)
      (a : TensorProduct Γ(S, V) Γ(S', W) (Scheme.Modules.HOver h N p) →ₗ[Γ(S', W)]
        Γ((Scheme.Modules.tensorPullback g).obj P, W)),
      Function.Bijective a →
      (∀ (s : Γ(S', W)) (xi : Scheme.Modules.HOver h N p),
        a (s ⊗ₜ[Γ(S, V)] xi) = s •
          ((Scheme.Modules.tensorPullback g).obj P).presheaf.map (homOfLE eVW).op
            (Scheme.Modules.Hom.app
              ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app P)
              V (D.sourceClass p (eH.symm xi)))) →
      ∃ b : Scheme.Modules.HOver (Scheme.Modules.baseChangeSnd (S := Γ(S', W)) h)
          (Scheme.Modules.baseChangedModule (S := Γ(S', W)) h N) p →ₗ[Γ(S', W)]
          Γ(Q, W),
        Function.Bijective b ∧
        (∀ xi : Scheme.Modules.HOver h N p,
          b (Scheme.Modules.H.baseChangeLinear (S := Γ(S', W)) h N p xi) =
            Q.presheaf.map (homOfLE eVW).op
              (D.targetClass p
                (Scheme.Modules.moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
                  ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p (eH.symm xi)))) := by
  classical
  let : Algebra Γ(S, V) Γ(S', W) := (g.appLE V W eVW).hom.toAlgebra
  intro h N P Q
  have : Module.Flat Γ(S, V) Γ(S', W) := g.flat_appLE hV hW eVW
  have : CompactSpace (f ⁻¹ᵁ V).toScheme :=
    isCompact_iff_compactSpace.mp (f.isCompact_preimage hV.isCompact)
  have : IsAffine V.toScheme := hV
  have : QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme :=
    quasiSeparatedSpace_of_quasiSeparated (f ∣_ V)
  have hb := flatCohomologyBaseChange_bijective_of_compact_open
    (B := Γ(S', W)) h ⊤ isCompact_univ (f ⁻¹ᵁ V).toScheme (𝟙 _) inferInstance
    (Scheme.Hom.opensRange_of_isIso _) N inferInstance p
  rw [Category.id_comp] at hb
  let c := LinearEquiv.ofBijective (Scheme.Modules.H.baseChange (S := Γ(S', W)) h N p) hb
  choose e0 a0 b0 ha0 hb0 using
    Scheme.Modules.exists_flatBaseChange_affine_canonical_comparisons
      f g F I J p V W hV hW eVW D
  intro eH a ha ha_tmul
  let ae := LinearEquiv.ofBijective a ha
  let b := c.symm.trans (ae.trans (a0.symm.trans (c.trans b0)))
  refine ⟨b.toLinearMap, b.bijective, ?_⟩
  intro xi
  have hc (y : Scheme.Modules.HOver h N p) :
      c (1 ⊗ₜ[Γ(S, V)] y) =
        Scheme.Modules.H.baseChangeLinear (S := Γ(S', W)) h N p y := by
    change (1 : Γ(S', W)) •
      Scheme.Modules.H.baseChangeLinear (S := Γ(S', W)) h N p y = _
    exact one_smul _ _
  have ht : a (1 ⊗ₜ[Γ(S, V)] xi) =
      a0 (1 ⊗ₜ[Γ(S, V)] e0 (eH.symm xi)) := by
    refine (ha_tmul 1 xi).trans ?_
    simpa only [e0.symm_apply_apply] using (ha0 1 (e0 (eH.symm xi))).symm
  have ht' : a0.symm (a (1 ⊗ₜ[Γ(S, V)] xi)) =
      1 ⊗ₜ[Γ(S, V)] e0 (eH.symm xi) :=
    (congrArg a0.symm ht).trans (a0.symm_apply_apply _)
  change b (Scheme.Modules.H.baseChangeLinear (S := Γ(S', W)) h N p xi) = _
  calc
    b (Scheme.Modules.H.baseChangeLinear (S := Γ(S', W)) h N p xi) =
        b (c (1 ⊗ₜ[Γ(S, V)] xi)) := congrArg b (hc xi).symm
    _ = b0 (c (a0.symm (a (1 ⊗ₜ[Γ(S, V)] xi)))) :=
      congrArg (fun z ↦ b0 (c (a0.symm (a z)))) (c.symm_apply_apply _)
    _ = b0 (c (1 ⊗ₜ[Γ(S, V)] e0 (eH.symm xi))) := congrArg (fun z ↦ b0 (c z)) ht'
    _ = b0 (Scheme.Modules.H.baseChangeLinear (S := Γ(S', W)) h N p
        (e0 (eH.symm xi))) := congrArg b0 (hc _)
    _ = _ := by simpa only [e0.symm_apply_apply] using hb0 (e0 (eH.symm xi))
end AlgebraicGeometry
