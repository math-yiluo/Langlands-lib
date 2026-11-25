/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

import all WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.FormalCompletionExact
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelFactorization
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Reduction of a finite formal graph onto the closed fibre

Source: Stacks Project, Tags 0889(1), 087W and 00MB.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem completion_preserves_limits {X : Scheme.{u}} [IsNoetherian X]
    (J : X.IdealSheafData) : PreservesFiniteLimits (completion X J) := by
  classical
  let zC : HasZeroMorphisms (CoherentModules X) := inferInstance
  let zD : HasZeroMorphisms (CoherentFormalModule X J) := inferInstance
  obtain ⟨hC, hD, hAdd, hExact⟩ := formalCompletion_exact X J
  let _ : Abelian (CoherentModules X) := hC.some
  let _ : Abelian (CoherentFormalModule X J) := hD.some
  let _ : Subsingleton (Preadditive (CoherentModules X)) :=
    @CategoryTheory.subsingleton_preadditive_of_hasBinaryBiproducts _ _
      (@Preadditive.preadditiveHasZeroMorphisms _ _ hC.some.toPreadditive)
      (@Abelian.hasBinaryBiproducts _ _ hC.some)
  let _ : Subsingleton (Preadditive (CoherentFormalModule X J)) :=
    @CategoryTheory.subsingleton_preadditive_of_hasBinaryBiproducts _ _
      (@Preadditive.preadditiveHasZeroMorphisms _ _ hD.some.toPreadditive)
      (@Abelian.hasBinaryBiproducts _ _ hD.some)
  let hAdd' : @Functor.Additive _ _ _ _ hC.some.toPreadditive hD.some.toPreadditive
      (completion X J) := by
    convert hAdd using 1
  let _ := hAdd'
  have hPres : PreservesFiniteLimits (completion X J) ∧
      PreservesFiniteColimits (completion X J) := by
    apply ((Functor.exact_tfae (completion X J)).out 1 4).mp
    let P (z₁ : HasZeroMorphisms (CoherentModules X))
        (z₂ : HasZeroMorphisms (CoherentFormalModule X J)) : Prop :=
      ∀ hz : @Functor.PreservesZeroMorphisms _ _ _ _ z₁ z₂ (completion X J),
        ∀ S : @ShortComplex (CoherentModules X) _ z₁,
          @ShortComplex.ShortExact _ _ z₁ S →
            @ShortComplex.ShortExact _ _ z₂
              (@ShortComplex.map _ _ _ _ z₁ z₂ S (completion X J) hz)
    have hP : P zC zD := fun _ ↦ hExact
    have hP' : P
        (@Preadditive.preadditiveHasZeroMorphisms _ _ hC.some.toPreadditive)
        (@Preadditive.preadditiveHasZeroMorphisms _ _ hD.some.toPreadditive) :=
      (congrArg₂ P (Subsingleton.elim _ _) (Subsingleton.elim _ _)) ▸ hP
    exact hP' inferInstance
  exact hPres.1

private theorem coherent_pullback {X : Scheme.{u}} [IsNoetherian X]
    {H F G : CoherentModules X} (a : F ⟶ H) (b : G ⟶ H) :
    RingedSpace.IsCoherent X.toRingedSpace (pullback a.hom b.hom) := by
  have h := RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace
  have hsum := (h.2.1 _
    (ShortComplex.Splitting.ofHasBinaryBiproduct F.obj G.obj).shortExact).2.1
      F.property G.property
  have hker := (h.1 _ _ (biprod.desc a.hom (-b.hom)) hsum H.property).1
  exact h.2.2.2.2 _ _
    ((kernelIsKernel (biprod.desc a.hom (-b.hom))).conePointUniqueUpToIso
      (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct a.hom b.hom)) hker

private theorem completed_pullback_lift {X : Scheme.{u}} [IsNoetherian X]
    (J : X.IdealSheafData) {H F G : CoherentModules X} (a : F ⟶ H) (b : G ⟶ H)
    (T : CoherentFormalModule X J) (f : T ⟶ (completion X J).obj F)
    (g : T ⟶ (completion X J).obj G)
    (hfg : f ≫ (completion X J).map a = g ≫ (completion X J).map b) :
    let P : CoherentModules X := ⟨pullback a.hom b.hom, coherent_pullback a b⟩
    ∃ v : T ⟶ (completion X J).obj P,
      v ≫ (completion X J).map (ObjectProperty.homMk (pullback.fst a.hom b.hom)) = f ∧
      v ≫ (completion X J).map (ObjectProperty.homMk (pullback.snd a.hom b.hom)) = g := by
  have := completion_preserves_limits J
  let P : CoherentModules X := ⟨pullback a.hom b.hom, coherent_pullback a b⟩
  let p : P ⟶ F := ObjectProperty.homMk (pullback.fst a.hom b.hom)
  let q : P ⟶ G := ObjectProperty.homMk (pullback.snd a.hom b.hom)
  have hpq : p ≫ a = q ≫ b := by
    apply ObjectProperty.hom_ext
    exact pullback.condition
  let c := PullbackCone.mk p q hpq
  have hc : IsLimit c := by
    apply PullbackCone.IsLimit.mk _
      (fun s ↦ ObjectProperty.homMk
        (pullback.lift s.fst.hom s.snd.hom (congrArg (fun v ↦ v.hom) s.condition)))
    · intro s
      apply ObjectProperty.hom_ext
      exact pullback.lift_fst _ _ _
    · intro s
      apply ObjectProperty.hom_ext
      exact pullback.lift_snd _ _ _
    · intro s m hm₁ hm₂
      apply ObjectProperty.hom_ext
      apply pullback.hom_ext
      · exact (congrArg (fun v ↦ v.hom) hm₁).trans (pullback.lift_fst s.fst.hom s.snd.hom
          (congrArg (fun v ↦ v.hom) s.condition)).symm
      · exact (congrArg (fun v ↦ v.hom) hm₂).trans (pullback.lift_snd s.fst.hom s.snd.hom
          (congrArg (fun v ↦ v.hom) s.condition)).symm
  obtain ⟨v, hv⟩ := PullbackCone.IsLimit.lift'
    (isLimitPullbackConeMapOfIsLimit (completion X J) hpq hc) f g hfg
  exact ⟨v, hv⟩

private theorem completed_kernel_lift {X : Scheme.{u}} [IsNoetherian X]
    (J : X.IdealSheafData) {P Q : CoherentModules X} (d : P ⟶ Q)
    (T : CoherentFormalModule X J) (g : T ⟶ (completion X J).obj P)
    (hg : g ≫ (completion X J).map d = 0) :
    let K : CoherentModules X := ⟨kernel d.hom,
      ((RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).1
        P.obj Q.obj d.hom P.property Q.property).1⟩
    ∃ v : T ⟶ (completion X J).obj K,
      v ≫ (completion X J).map (ObjectProperty.homMk (kernel.ι d.hom)) = g := by
  have := completion_preserves_limits J
  let K : CoherentModules X := ⟨kernel d.hom,
    ((RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).1
      P.obj Q.obj d.hom P.property Q.property).1⟩
  let i : K ⟶ P := ObjectProperty.homMk (kernel.ι d.hom)
  have hi : i ≫ d = 0 := by
    apply ObjectProperty.hom_ext
    exact kernel.condition _
  let c := KernelFork.ofι i hi
  have hc : IsLimit c := by
    apply Fork.IsLimit.mk'
    intro s
    let k : s.pt ⟶ K := ObjectProperty.homMk
      (kernel.lift d.hom s.ι.hom (congrArg (fun v ↦ v.hom) s.condition))
    refine ⟨k, ?_, ?_⟩
    · apply ObjectProperty.hom_ext
      exact kernel.lift_ι _ _ _
    · intro l hl
      apply ObjectProperty.hom_ext
      apply (cancel_mono (kernel.ι d.hom)).mp
      exact (congrArg (fun v ↦ v.hom) hl).trans (kernel.lift_ι d.hom s.ι.hom
        (congrArg (fun v ↦ v.hom) s.condition)).symm
  have hzero : (completion X J).PreservesZeroMorphisms := by
    obtain ⟨_, _, hAdd, _⟩ := formalCompletion_exact X J
    let _ := hAdd
    infer_instance
  obtain ⟨v, hv⟩ := KernelFork.IsLimit.lift'
    (KernelFork.mapIsLimit c hc (completion X J)) g hg
  exact ⟨v, hv⟩

set_option backward.isDefEq.respectTransparency false in
private theorem formal_zero_of_level {X : Scheme.{u}} [IsNoetherian X]
    (J : X.IdealSheafData) (T U : CoherentFormalModule X J) (n : ℕ)
    (hU : ∀ m : ℕ, IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower J.toModulesι (n + 1)).2 (U.obj.obj (op m))))
    (f : T ⟶ U) (hf : f.hom.app (op n) = 0) : f = 0 := by
  have hs := (formalModule_annihilated_power_iff J U n).mp hU
  have hhigh (m : ℕ) (hm : n ≤ m) : f.hom.app (op m) = 0 := by
    have := hs m hm
    apply (cancel_mono (U.obj.map (homOfLE hm).op)).mp
    simpa only [hf, comp_zero, zero_comp] using (f.hom.naturality (homOfLE hm).op).symm
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext a
  obtain ⟨m⟩ := a
  change f.hom.app (op m) = 0
  by_cases hm : n ≤ m
  · exact hhigh m hm
  · have hmn : m ≤ n := by omega
    have := formalTransition_epi T hmn
    apply (cancel_epi (T.obj.map (homOfLE hmn).op)).mp
    simpa only [hf, comp_zero, zero_comp] using f.hom.naturality (homOfLE hmn).op

set_option backward.isDefEq.respectTransparency false in
/-- The first projection of the finite comparison graph is surjective modulo J.
No torsion condition on the comparison arrow is required for this closed-fibre assertion.

Source: Stacks Project, Tag 0889(1), affine comparison argument, using the affine
formal-module dictionary of Tag 087W and exact finite completion of Tag 00MB.
Proof: Restrict to an affine open Spec(A). Coherent modules, their pullback and the
kernel of the displayed discrepancy correspond to finite A-modules. The compatible
family θ induces a map between their I-adic completions. Exactness of completion
identifies the completion of this kernel with the kernel of the completed discrepancy
on the completed pullback. Compatibility with a and a' makes (id, θ) a map into this
completed pullback. Its level n+1 component makes its discrepancy zero. Thus it lifts
into the completed kernel, and its first projection is the identity on completed F.
Reducing modulo I makes the completed first projection surjective. For a finite module,
its completion modulo I is canonically the original module modulo I, compatibly with
maps. Hence E -> F/IF is surjective on affine sections. These affine opens cover X,
so the displayed sheaf morphism is epi. For J=0 the graph is the usual graph; for J=1
the target quotient is zero. Zero modules and an empty scheme also satisfy the assertion.
(blueprint: lem-weil-pbc-formal-graph-first-quotient-epi). -/
theorem formalGraph_first_quotient_epi
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (θ : (completion X J).obj F ⟶ (completion X J).obj F')
    (hθ : θ ≫ (completion X J).map a' = (completion X J).map a)
    (n : ℕ) :
    let t : formalModuleQuotient J (n + 1) F.obj ⟶
        formalModuleQuotient J (n + 1) F'.obj := θ.hom.app (op n)
    let d : pullback a.hom a'.hom ⟶ formalModuleQuotient J (n + 1) F'.obj :=
      pullback.snd a.hom a'.hom ≫ formalModuleQuotientπ J (n + 1) F'.obj -
        pullback.fst a.hom a'.hom ≫ formalModuleQuotientπ J (n + 1) F.obj ≫ t
    Epi (kernel.ι d ≫ pullback.fst a.hom a'.hom ≫ formalModuleQuotientπ J 1 F.obj) := by
  classical
  dsimp only
  let P : CoherentModules X := ⟨pullback a.hom a'.hom, coherent_pullback a a'⟩
  let p : P ⟶ F := ObjectProperty.homMk (pullback.fst a.hom a'.hom)
  let q : P ⟶ F' := ObjectProperty.homMk (pullback.snd a.hom a'.hom)
  let t : formalModuleQuotient J (n + 1) F.obj ⟶
      formalModuleQuotient J (n + 1) F'.obj := θ.hom.app (op n)
  let Q : CoherentModules X := ⟨formalModuleQuotient J (n + 1) F'.obj,
    ((completion X J).obj F').property.1 n⟩
  let d : P ⟶ Q := ObjectProperty.homMk
    (q.hom ≫ formalModuleQuotientπ J (n + 1) F'.obj -
      p.hom ≫ formalModuleQuotientπ J (n + 1) F.obj ≫ t)
  obtain ⟨g, hgp, hgq⟩ := completed_pullback_lift J a a'
    ((completion X J).obj F) (𝟙 _) θ (by simpa using hθ.symm)
  have hQ : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower J.toModulesι (n + 1)).2 Q.obj) :=
    ((completion X J).obj F').property.2.1 n
  have hd : formalModuleQuotientMap J d.hom (Nat.le_refl (n + 1)) =
      (formalModuleQuotientMap J q.hom (Nat.le_refl (n + 1)) -
        formalModuleQuotientMap J p.hom (Nat.le_refl (n + 1)) ≫ t) ≫
          formalModuleQuotientπ J (n + 1) Q.obj := by
    have : Epi (formalModuleQuotientπ J (n + 1) P.obj) :=
      inferInstanceAs (Epi (cokernel.π _))
    apply (cancel_epi (formalModuleQuotientπ J (n + 1) P.obj)).mp
    simp [formalModuleQuotientMap, formalModuleQuotientπ, d,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc]
  have hgzero : g ≫ (completion X J).map d = 0 := by
    apply formal_zero_of_level J _ _ n
    · intro m
      change IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower J.toModulesι (n + 1)).2
        (formalModuleQuotient J (m + 1) Q.obj))
      have : Epi (formalModuleQuotientπ J (m + 1) Q.obj) :=
        inferInstanceAs (Epi (cokernel.π _))
      have := idealModuleProduct_mono
        (Scheme.idealSheafPower J.toModulesι (n + 1)).2
        (formalModuleQuotient J (m + 1) Q.obj)
      apply IsZero.of_mono_eq_zero (Scheme.idealModuleProductι
        (Scheme.idealSheafPower J.toModulesι (n + 1)).2 _)
      have hz := (idealModuleProduct_quotient_comp_zero_iff
        (Scheme.idealSheafPower J.toModulesι (n + 1)).2
        (formalModuleQuotientπ J (m + 1) Q.obj) (𝟙 _)).mpr (hQ.eq_zero_of_src _)
      simpa using hz
    · change g.hom.app (op n) ≫
        formalModuleQuotientMap J d.hom (Nat.le_refl (n + 1)) = 0
      rw [hd, ← Category.assoc, Preadditive.comp_sub]
      have hp := congrArg (fun z ↦ z.hom.app (op n)) hgp
      have hq := congrArg (fun z ↦ z.hom.app (op n)) hgq
      change g.hom.app (op n) ≫ formalModuleQuotientMap J p.hom
        (Nat.le_refl (n + 1)) = 𝟙 _ at hp
      change g.hom.app (op n) ≫ formalModuleQuotientMap J q.hom
        (Nat.le_refl (n + 1)) = t at hq
      rw [← Category.assoc _ _ t, hp, Category.id_comp, hq, sub_self, zero_comp]
  obtain ⟨v, hv⟩ := completed_kernel_lift J d ((completion X J).obj F) g hgzero
  have he : v ≫ (completion X J).map (ObjectProperty.homMk (kernel.ι d.hom)) ≫
      (completion X J).map p = 𝟙 _ := by rw [← Category.assoc, hv]; exact hgp
  have he₀ := congrArg (fun z ↦ z.hom.app (op 0)) he
  change v.hom.app (op 0) ≫
    formalModuleQuotientMap J (kernel.ι d.hom) (Nat.le_refl 1) ≫
      formalModuleQuotientMap J p.hom (Nat.le_refl 1) = 𝟙 _ at he₀
  have hred : Epi (formalModuleQuotientMap J (kernel.ι d.hom ≫ p.hom)
      (Nat.le_refl 1)) := by
    rw [formalModuleQuotientMap_comp J _ _ (Nat.le_refl 1) (Nat.le_refl 1)]
    exact epi_of_epi_fac he₀
  have hfac : formalModuleQuotientπ J 1 (kernel d.hom) ≫
      formalModuleQuotientMap J (kernel.ι d.hom ≫ p.hom) (Nat.le_refl 1) =
      kernel.ι d.hom ≫ p.hom ≫ formalModuleQuotientπ J 1 F.obj := by
    simp [formalModuleQuotientπ, formalModuleQuotientMap]
  change Epi (kernel.ι d.hom ≫ p.hom ≫ formalModuleQuotientπ J 1 F.obj)
  rw [← hfac]
  have : Epi (formalModuleQuotientπ J 1 (kernel d.hom)) :=
    inferInstanceAs (Epi (cokernel.π _))
  infer_instance

end AlgebraicGeometry
