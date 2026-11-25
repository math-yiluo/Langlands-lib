/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects
import all WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernel
import all WeilConjectures.AlgebraicGeometry.FormalSystemsPullback
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

/-! # Open restriction preserves formal kernels

Source: Stacks Project, Lemma 087X, claims (a)--(d) and final sentence.
(blueprint: lem-weil-pbc-coherent-formal-modules-restriction-kernels).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The proved power-quotient comparison of Stacks 0887, transported from tensor
pullback to ordinary open restriction using their adjunctions. -/
private noncomputable def restrictionQuotientIso {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (U : X.Opens) (M : X.Modules)
    (hM : M.IsQuasicoherent) (n : ℕ) :
    formalModuleQuotient (I.comap U.ι) (n + 1)
        ((Scheme.Modules.restrictFunctor U.ι).obj M) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj (formalModuleQuotient I (n + 1) M) := by
  let t := (Scheme.Modules.nonempty_tensorPullbackAdjunction U.ι).some.leftAdjointUniq
    (Scheme.Modules.restrictAdjunction U.ι)
  exact (((formalCompletionFunctor (I.comap U.ι)).mapIso (t.app M)).app (Opposite.op n)).symm ≪≫
    powerQuotientIso U.ι I M hM (n + 1) ≪≫ t.app (formalModuleQuotient I (n + 1) M)

/-- The transported quotient comparison respects its projection; this is the
projection identity in the proof of Stacks 0887. -/
private theorem restrictionQuotientIso_π {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (U : X.Opens) (M : X.Modules)
    (hM : M.IsQuasicoherent) (n : ℕ) :
    formalModuleQuotientπ (I.comap U.ι) (n + 1)
        ((Scheme.Modules.restrictFunctor U.ι).obj M) ≫
      (restrictionQuotientIso I U M hM n).hom =
        (Scheme.Modules.restrictFunctor U.ι).map (formalModuleQuotientπ I (n + 1) M) := by
  let T := Scheme.Modules.tensorPullback U.ι
  let R := Scheme.Modules.restrictFunctor U.ι
  let t : T ≅ R :=
    (Scheme.Modules.nonempty_tensorPullbackAdjunction U.ι).some.leftAdjointUniq
      (Scheme.Modules.restrictAdjunction U.ι)
  change formalModuleQuotientπ (I.comap U.ι) (n + 1) (R.obj M) ≫
    formalModuleQuotientMap (I.comap U.ι) (t.app M).inv (Nat.le_refl (n + 1)) ≫
      (powerQuotientIso U.ι I M hM (n + 1)).hom ≫
        (t.app (formalModuleQuotient I (n + 1) M)).hom = _
  rw [← Category.assoc, quotientMap_π, Category.assoc,
    ← Category.assoc _ (powerQuotientIso U.ι I M hM (n + 1)).hom,
    powerQuotientIso_π]
  change (t.app M).inv ≫ T.map (formalModuleQuotientπ I (n + 1) M) ≫
    t.hom.app (formalModuleQuotient I (n + 1) M) = _
  rw [t.hom.naturality]
  change (t.app M).inv ≫ (t.app M).hom ≫ R.map _ = _
  rw [Iso.inv_hom_id_assoc]

/-- Restrict an image presentation using the preserved sheaf kernel and the
restricted epi-mono factorization (Stacks 087X, restriction of construction (a)). -/
private theorem restrictionImage {X : Scheme.{u}} (U : X.Opens)
    {A B C : X.Modules} (a : A ⟶ B) (b : A ⟶ C)
    {S : X.Modules} (j : S ⟶ C)
    (hS : ∃ e : S ≅ Abelian.image (kernel.ι a ≫ b),
      e.hom ≫ Abelian.image.ι (kernel.ι a ≫ b) = j) :
    ∃ e : (Scheme.Modules.restrictFunctor U.ι).obj S ≅
        Abelian.image (kernel.ι ((Scheme.Modules.restrictFunctor U.ι).map a) ≫
          (Scheme.Modules.restrictFunctor U.ι).map b),
      e.hom ≫ Abelian.image.ι (kernel.ι ((Scheme.Modules.restrictFunctor U.ι).map a) ≫
        (Scheme.Modules.restrictFunctor U.ι).map b) =
          (Scheme.Modules.restrictFunctor U.ι).map j := by
  let R := Scheme.Modules.restrictFunctor U.ι
  obtain ⟨e, he⟩ := hS
  let f := kernel.ι a ≫ b
  let f' := kernel.ι (R.map a) ≫ R.map b
  let k := PreservesKernel.iso R a
  let q := k.inv ≫ R.map (Abelian.factorThruImage f ≫ e.inv)
  have : Epi q := by dsimp [q]; infer_instance
  have : Mono j := by rw [← he]; infer_instance
  have : Mono (R.map j) := inferInstance
  have hq₀ : (Abelian.factorThruImage f ≫ e.inv) ≫ j = f := by
    rw [← he, Category.assoc, Iso.inv_hom_id_assoc, Abelian.image.fac]
  have hq : q ≫ R.map j = f' := by
    dsimp only [q, f']
    rw [Category.assoc, ← R.map_comp, hq₀]
    dsimp only [f]
    rw [R.map_comp, ← Category.assoc, PreservesKernel.iso_inv_ι]
  have : StrongEpi q := strongEpi_of_epi q
  let d := image.isoStrongEpiMono q (R.map j) hq ≪≫
    (Abelian.imageIsoImage f').symm
  refine ⟨d, ?_⟩
  dsimp only [d, Iso.trans_hom, Iso.symm_hom]
  change (image.isoStrongEpiMono q (R.map j) hq).hom ≫
    (Abelian.imageIsoImage f').inv ≫ Abelian.image.ι f' = R.map j
  have hi : (Abelian.imageIsoImage f').inv ≫ Abelian.image.ι f' = image.ι f' := by
    simpa only [Iso.inv_hom_id_assoc] using
      congrArg ((Abelian.imageIsoImage f').inv ≫ ·)
        (Abelian.imageIsoImage_hom_comp_image_ι f').symm
  rw [hi]
  exact image.isoStrongEpiMono_hom_comp_ι q (R.map j) hq

/-- Restriction preserves kernels in the formal category, without assuming abelianness.
Source: Stacks Project, Lemma 087X, claims (a)--(d) and final sentence.
(blueprint: lem-weil-pbc-coherent-formal-modules-restriction-kernels).

Proof: Obtain the shifted-image quotient presentation and the uniform vanishing
bound from coherentFormalModule_kernel_construction. Naturality of alpha, the image
factorization, and the quotient projections show that its inclusion kills alpha.
The proved transition-zero monicity helper and coherentFormalModule_kernel_factorization
make this a limiting fork on X. Ordinary module restriction preserves kernels and
maps the epi-mono presentation of each shifted image to its image presentation on U.
The proved powerQuotientIso and its projection identity from FormalSystemsPullback
(Stacks 0887) identify the restricted quotient levels, after transporting the tensor
pullback comparison along the unique left-adjoint isomorphism with restriction.
Map the two presentation equations to obtain the transition and inclusion equations
on U. The sheaf-kernel comparison transports the original transition-zero bound;
the same monicity helper proves that the restricted formal inclusion is monic.
Apply the factorization theorem on U with the restricted presentation. Together with
monicity this makes the mapped fork limiting. Mathlib's preservation-of-one-limit-cone
criterion then gives preservation of every kernel fork. Only module sheaves use an
abelian structure; no abelian structure on coherent formal modules is assumed. -/
theorem coherentFormalModules_restriction_preservesKernel {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData) (U : X.Opens)
    [IsNoetherian U.toScheme] {F G : CoherentFormalModule X I} (α : F ⟶ G) :
    PreservesLimit (parallelPair α 0) (coherentFormalModulesRestriction I U) := by
  classical
  obtain ⟨c, _, S, j, hS, K, ι, e, htrans, hcomp, hzero⟩ :=
    coherentFormalModule_kernel_construction I F G α
  have hjzero (m : ℕ) : j.app (Opposite.op m) ≫ α.hom.app (Opposite.op m) = 0 := by
    obtain ⟨a, ha⟩ := hS m
    let f := kernel.ι (α.hom.app (Opposite.op (m + c))) ≫
      F.obj.map (homOfLE (Nat.le_add_right m c)).op
    have hf : f ≫ α.hom.app (Opposite.op m) = 0 := by
      dsimp only [f]
      rw [Category.assoc, α.hom.naturality, ← Category.assoc, kernel.condition, zero_comp]
    have himage : Abelian.image.ι f ≫ α.hom.app (Opposite.op m) = 0 := by
      apply (cancel_epi (Abelian.factorThruImage f)).mp
      simpa only [← Category.assoc, Abelian.image.fac, comp_zero] using hf
    rw [← ha, Category.assoc]
    exact (congrArg (a.hom ≫ ·) himage).trans comp_zero
  have hιzero : ι ≫ α = 0 := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext a
    obtain ⟨n⟩ := a
    change ι.hom.app (Opposite.op n) ≫ α.hom.app (Opposite.op n) = 0
    have : Epi (formalModuleQuotientπ I (n + 1) (S.obj (Opposite.op (n + c)))) := by
      dsimp only [formalModuleQuotientπ]
      infer_instance
    apply (cancel_epi (e n).hom).mp
    apply (cancel_epi (formalModuleQuotientπ I (n + 1) (S.obj (Opposite.op (n + c))))).mp
    simp only [comp_zero]
    rw [← Category.assoc _ _ (α.hom.app (Opposite.op n)),
      ← Category.assoc _ _ (α.hom.app (Opposite.op n)), hcomp n, Category.assoc,
      α.hom.naturality, ← Category.assoc, hjzero, zero_comp]
  have : Mono ι := formalMono_of_kernel_transition_zero ι c hzero
  let C := KernelFork.ofι ι hιzero
  have hC : IsLimit C := KernelFork.IsLimit.ofι' ι hιzero (fun γ hγ ↦ Classical.choice (by
    obtain ⟨δ, hδ⟩ := coherentFormalModule_kernel_factorization
      I F G α c S j hS K ι e htrans hcomp _ γ hγ
    exact ⟨⟨δ, hδ⟩⟩))
  let R := coherentFormalModulesRestriction I U
  let r := Scheme.Modules.restrictFunctor U.ι
  let S' := S ⋙ r
  let j' := Functor.whiskerRight j r
  have hS' : ∀ m : ℕ, ∃ a : S'.obj (Opposite.op m) ≅
      Abelian.image (kernel.ι ((R.map α).hom.app (Opposite.op (m + c))) ≫
        (R.obj F).obj.map (homOfLE (Nat.le_add_right m c)).op),
      a.hom ≫ Abelian.image.ι (kernel.ι ((R.map α).hom.app (Opposite.op (m + c))) ≫
        (R.obj F).obj.map (homOfLE (Nat.le_add_right m c)).op) = j'.app (Opposite.op m) := by
    intro m
    exact restrictionImage U (α.hom.app (Opposite.op (m + c)))
      (F.obj.map (homOfLE (Nat.le_add_right m c)).op) (j.app (Opposite.op m)) (hS m)
  have hqcF (n : ℕ) : (F.obj.obj (Opposite.op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
      (F.property.1 n)).1
  have hqcG (n : ℕ) : (G.obj.obj (Opposite.op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
      (G.property.1 n)).1
  have hqcS (n : ℕ) : (S.obj (Opposite.op n)).IsQuasicoherent := by
    have := hqcF (n + c)
    have := hqcF n
    have := hqcG (n + c)
    have := Scheme.Modules.isQuasicoherent_kernel (α.hom.app (Opposite.op (n + c)))
    let f := kernel.ι (α.hom.app (Opposite.op (n + c))) ≫
      F.obj.map (homOfLE (Nat.le_add_right n c)).op
    have := Scheme.Modules.isQuasicoherent_cokernel f
    have := Scheme.Modules.isQuasicoherent_kernel (cokernel.π f)
    obtain ⟨a, _⟩ := hS n
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso a.symm
      (inferInstanceAs (Abelian.image f).IsQuasicoherent)
  let e' (n : ℕ) : formalModuleQuotient (I.comap U.ι) (n + 1)
      (S'.obj (Opposite.op (n + c))) ≅ (R.obj K).obj.obj (Opposite.op n) :=
    restrictionQuotientIso I U _ (hqcS (n + c)) n ≪≫ r.mapIso (e n)
  have htrans' (n : ℕ) :
      formalModuleQuotientπ (I.comap U.ι) (n + 2) (S'.obj (Opposite.op (n + 1 + c))) ≫
          (e' (n + 1)).hom ≫ (R.obj K).obj.map (homOfLE (Nat.le_succ n)).op =
        S'.map (homOfLE (Nat.add_le_add_right (Nat.le_succ n) c)).op ≫
          formalModuleQuotientπ (I.comap U.ι) (n + 1) (S'.obj (Opposite.op (n + c))) ≫
            (e' n).hom := by
    change formalModuleQuotientπ (I.comap U.ι) (n + 2) (r.obj _) ≫
        (restrictionQuotientIso I U _ (hqcS (n + 1 + c)) (n + 1)).hom ≫
          r.map (e (n + 1)).hom ≫ r.map _ =
      r.map _ ≫ formalModuleQuotientπ (I.comap U.ι) (n + 1) (r.obj _) ≫
        (restrictionQuotientIso I U _ (hqcS (n + c)) n).hom ≫ r.map (e n).hom
    rw [← Category.assoc, restrictionQuotientIso_π]
    rw [← Category.assoc
      (formalModuleQuotientπ (I.comap U.ι) (n + 1) (r.obj (S.obj (Opposite.op (n + c)))))
      (restrictionQuotientIso I U _ (hqcS (n + c)) n).hom (r.map (e n).hom),
      restrictionQuotientIso_π I U _ (hqcS (n + c)) n]
    change r.map _ ≫ r.map (e (n + 1)).hom ≫
        r.map (K.obj.map (homOfLE (Nat.le_succ n)).op) =
      (r.map _ ≫ r.map _) ≫ r.map (e n).hom
    simpa only [Functor.map_comp, Category.assoc] using congrArg r.map (htrans n)
  have hcomp' (n : ℕ) :
      formalModuleQuotientπ (I.comap U.ι) (n + 1) (S'.obj (Opposite.op (n + c))) ≫
          (e' n).hom ≫ (R.map ι).hom.app (Opposite.op n) =
        j'.app (Opposite.op (n + c)) ≫ (R.obj F).obj.map
          (homOfLE (Nat.le_add_right n c)).op := by
    change formalModuleQuotientπ (I.comap U.ι) (n + 1) (r.obj _) ≫
        (restrictionQuotientIso I U _ (hqcS (n + c)) n).hom ≫
          r.map (e n).hom ≫ r.map _ = r.map _ ≫ r.map _
    rw [← Category.assoc, restrictionQuotientIso_π]
    change r.map _ ≫ r.map (e n).hom ≫ r.map (ι.hom.app (Opposite.op n)) =
      r.map _ ≫ r.map (F.obj.map (homOfLE (Nat.le_add_right n c)).op)
    simpa only [Functor.map_comp] using congrArg r.map (hcomp n)
  have hzero' (n : ℕ) : kernel.ι ((R.map ι).hom.app (Opposite.op (n + c))) ≫
      (R.obj K).obj.map (homOfLE (Nat.le_add_right n c)).op = 0 := by
    change kernel.ι (r.map (ι.hom.app (Opposite.op (n + c)))) ≫ r.map _ = 0
    rw [← PreservesKernel.iso_inv_ι r (ι.hom.app (Opposite.op (n + c))), Category.assoc,
      ← r.map_comp]
    change (PreservesKernel.iso r (ι.hom.app (Opposite.op (n + c)))).inv ≫
      r.map (kernel.ι (ι.hom.app (Opposite.op (n + c))) ≫
        K.obj.map (homOfLE (Nat.le_add_right n c)).op) = 0
    rw [hzero n, r.map_zero, comp_zero]
  have : Mono (R.map ι) := formalMono_of_kernel_transition_zero (R.map ι) c hzero'
  apply preservesLimit_of_preserves_limit_cone hC
  refine (KernelFork.isLimitMapConeEquiv C R).symm ?_
  exact KernelFork.IsLimit.ofι' (R.map ι) (C.map_condition R) (fun γ hγ ↦ Classical.choice (by
    obtain ⟨δ, hδ⟩ := coherentFormalModule_kernel_factorization
      (I.comap U.ι) (R.obj F) (R.obj G) (R.map α) c S' j' hS'
      (R.obj K) (R.map ι) e' htrans' hcomp' _ γ hγ
    exact ⟨⟨δ, hδ⟩⟩))

end AlgebraicGeometry
