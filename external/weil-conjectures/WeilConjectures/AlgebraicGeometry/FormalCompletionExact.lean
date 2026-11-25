/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAbelian
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import WeilConjectures.AlgebraicGeometry.FormalCompletionAffineKernel
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesLocalExactness
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum

/-! # Exactness of coherent formal completion

Source: Stacks Project, Cohomology of Schemes, Lemma 0881 and equation 0880
(blueprint: lem-weil-pbc-formal-completion-exact).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem hasHomology_of_abelian_witness {C : Type*} [Category C]
    [Limits.HasZeroMorphisms C] (h : Nonempty (Abelian C)) (S : ShortComplex C) :
    S.HasHomology :=
  open CategoryTheory.Limits Opposite in open scoped ZeroObject in by
  let z : HasZeroMorphisms C := inferInstance
  let hh := @categoryWithHomology_of_abelian C _ h.some
  have hh' : @CategoryWithHomology C _ z := by
    convert hh using 1
    exact Subsingleton.elim _ _
  exact hh'.hasHomology S

private theorem hasKernels_of_abelian_witness {C : Type*} [Category C]
    [Limits.HasZeroMorphisms C] (h : Nonempty (Abelian C)) : Limits.HasKernels C :=
  open CategoryTheory.Limits Opposite in open scoped ZeroObject in by
  let z : HasZeroMorphisms C := inferInstance
  have : Abelian C := h.some
  let k := (inferInstance : HasKernels C)
  have k' : @HasKernels C _ z := by
    convert k using 1
  exact k'

private theorem completion_additive (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) : (completion X I).Additive :=
  open CategoryTheory.Limits Opposite in open scoped ZeroObject in by
  constructor
  intro F G f g
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  change formalModuleQuotientMap I (f.hom + g.hom) (Nat.le_refl (n.unop + 1)) =
    formalModuleQuotientMap I f.hom (Nat.le_refl (n.unop + 1)) +
      formalModuleQuotientMap I g.hom (Nat.le_refl (n.unop + 1))
  apply (cancel_epi (cokernel.π
    (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι _).2 _))).mp
  simp [formalModuleQuotientMap, formalModuleQuotientπ, Preadditive.comp_add,
    Preadditive.add_comp]

private theorem coherent_closedUnderKernels (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderKernels (C := X.Modules)
      (RingedSpace.IsCoherent X.toRingedSpace) :=
  open CategoryTheory.Limits Opposite in open scoped ZeroObject in by
  constructor
  rintro _ ⟨f, k, hk, hF, hG⟩
  have h := (RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).1 _ _ f hF hG
  exact (RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).2.2.2.2 _ _
    ((kernelIsKernel f).conePointUniqueUpToIso hk) h.1

private theorem coherent_closedUnderCokernels (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderCokernels (C := X.Modules)
      (RingedSpace.IsCoherent X.toRingedSpace) :=
  open CategoryTheory.Limits Opposite in open scoped ZeroObject in by
  constructor
  rintro _ ⟨f, k, hk, hF, hG⟩
  have h := (RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).1 _ _ f hF hG
  exact (RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).2.2.2.2 _ _
    ((cokernelIsCokernel f).coconePointUniqueUpToIso hk) h.2

private theorem coherent_abelian (X : Scheme.{u}) [IsNoetherian X] :
    Nonempty (Abelian (CoherentModules X)) :=
  open CategoryTheory.Limits Opposite in open scoped ZeroObject in by
  let P : ObjectProperty X.Modules := RingedSpace.IsCoherent X.toRingedSpace
  have h := RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace
  have : P.IsClosedUnderIsomorphisms := ⟨fun e hF ↦ h.2.2.2.2 _ _ e hF⟩
  have : P.ContainsZero := ⟨_, isZero_zero _, h.2.2.2.1⟩
  have : P.IsClosedUnderKernels := coherent_closedUnderKernels X
  have : P.IsClosedUnderCokernels := coherent_closedUnderCokernels X
  have : P.IsClosedUnderBinaryProducts := by
    constructor
    rintro B ⟨p⟩
    let F := p.diag.obj ⟨WalkingPair.left⟩
    let G := p.diag.obj ⟨WalkingPair.right⟩
    have hF : P F := p.prop_diag_obj ⟨WalkingPair.left⟩
    have hG : P G := p.prop_diag_obj ⟨WalkingPair.right⟩
    have hsum : P (F ⊞ G) :=
      (h.2.1 _ (ShortComplex.Splitting.ofHasBinaryBiproduct F G).shortExact).2.1 hF hG
    let q := p.toLimitPresentation.changeDiag (diagramIsoPair p.diag).symm
    exact P.prop_of_iso ((BinaryBiproduct.isLimit F G).conePointUniqueUpToIso q.isLimit) hsum
  have : P.IsClosedUnderFiniteProducts := ObjectProperty.IsClosedUnderFiniteProducts.mk'
  exact ⟨inferInstance⟩

private theorem completion_epi (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) {F G : CoherentModules X} (f : F ⟶ G) [Epi f] :
    Epi ((completion X I).map f) :=
  open CategoryTheory.Limits Opposite in open scoped ZeroObject in by
  let P : ObjectProperty X.Modules := RingedSpace.IsCoherent X.toRingedSpace
  have h := RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace
  have : P.IsClosedUnderIsomorphisms := ⟨fun e hF ↦ h.2.2.2.2 _ _ e hF⟩
  have : P.ContainsZero := ⟨_, isZero_zero _, h.2.2.2.1⟩
  have : P.IsClosedUnderCokernels := coherent_closedUnderCokernels X
  have := P.preservesEpimorphisms_ι_of_isNormalMonoCategory
  have : Epi f.hom := P.ι.map_epi f
  apply (IsCoherentFormalModule I).ι.epi_of_epi_map
  change Epi (formalCompletionMap I f.hom)
  have : ∀ n, Epi ((formalCompletionMap I f.hom).app n) := by
    intro n
    change Epi (formalModuleQuotientMap I f.hom (Nat.le_refl (n.unop + 1)))
    have : Epi (formalModuleQuotientπ I (n.unop + 1) F.obj ≫
        formalModuleQuotientMap I f.hom (Nat.le_refl (n.unop + 1))) := by
      change Epi (cokernel.π _ ≫ cokernel.desc _ _ _)
      rw [cokernel.π_desc]
      change Epi (f.hom ≫ cokernel.π _)
      infer_instance
    exact epi_of_epi (formalModuleQuotientπ I (n.unop + 1) F.obj) _
  exact NatTrans.epi_of_epi_app _

/-- The coherent-module and coherent-formal-module categories are abelian, and the
canonical completion functor is additive and carries every short exact sequence to a
short exact sequence. The additivity witness supplies zero preservation when mapping
short complexes; it is not a hypothesis. Positive level n is indexed by op (n - 1).

Source: Stacks Project, Cohomology of Schemes, Lemma 0881, equation 0880; Homology,
Lemma 010N (4) (blueprint: lem-weil-pbc-formal-completion-exact).

Proof:
1. Coherent modules are closed under kernels, cokernels and finite sums on a locally
Noetherian scheme (lem-weil-pbc-coherent-kernel-cokernel-locnoeth), and under isomorphism
(lem-weil-pbc-coherent-modules-kernel-cokernel-sum). Apply
lem-weil-pbc-abelian-full-subcategory-exact. The formal category is abelian by
lem-weil-pbc-coherent-formal-modules-abelian. Reduction of maps modulo ideal powers is
additive: precompose with the quotient epimorphism and use uniqueness of the induced map.
2. Choose a finite affine cover by Noetherian rings. Restriction commutes with ideal
products and their quotient cokernels (lem-weil-pbc-ideal-times-quasi-coherent-affine-sections).
Thus restriction commutes with completion. By
lem-weil-pbc-coherent-formal-modules-local-exactness it suffices to check short exactness
on each affine open.
3. On an affine open U, sections of the original sequence are short exact: kernels are
sectionwise, and quasi-coherent cokernels have surjective affine sections
(lem-weil-pbc-quasi-coherent-module-cokernel-image). Coherent modules have finite affine
sections by pqf-lem-coherent-ft-locnoeth and lem-weil-pbc-quasi-coherent-finite-type-affine.
4. The affine equivalence of lem-weil-pbc-coherent-formal-modules-affine identifies the
completed sequence with the adic completions of these finite modules. Affine sections of
F/I^n F are M/I^n M, including the induced maps, by
lem-weil-pbc-ideal-times-quasi-coherent-affine-sections and
lem-weil-pbc-affine-tilde-gamma-adjunction.
5. Apply lem-weil-pbc-completion-exact-finite-modules (Algebra, Lemma 00MB (2)). The
completion ring is Noetherian (lem-weil-pbc-adic-completion-noetherian); therefore the
sequence is short exact in its abelian category of finite modules
(lem-weil-pbc-finite-modules-noetherian-abelian).
6. The additive quasi-inverse of the affine equivalence carries this sequence back to a
short exact formal sequence (lem-weil-pbc-equivalence-injective-resolutions). Naturality
of the equivalence identifies it with the restricted completed sequence. Apply the local
criterion from step 2. Together with step 1 this proves exactness.
-/
theorem formalCompletion_exact (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) :
    Nonempty (Abelian (AlgebraicGeometry.CoherentModules X)) ∧
      Nonempty (Abelian (AlgebraicGeometry.CoherentFormalModule X I)) ∧
      ∃ h : (AlgebraicGeometry.completion X I).Additive,
        ∀ S : ShortComplex (AlgebraicGeometry.CoherentModules X), S.ShortExact →
          (@ShortComplex.map _ _ _ _ _ _ S (AlgebraicGeometry.completion X I)
            (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
              (AlgebraicGeometry.completion X I) h)).ShortExact :=
  open CategoryTheory.Limits Opposite in open scoped ZeroObject in by
  classical
  refine ⟨coherent_abelian X, (coherentFormalModule_abelian X I).1, ?_⟩
  have h : (completion X I).Additive := completion_additive X I
  refine ⟨h, ?_⟩
  intro S hS
  let T := @ShortComplex.map _ _ _ _ _ _ S (completion X I)
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ (completion X I) h)
  have : Epi T.g := by
    have := hS.epi_g
    exact completion_epi X I S.g
  obtain ⟨hN, ρ, hz, hρ, hlocal⟩ := coherentFormalModules_local_exactness X I
  apply ((hlocal X.affineOpens (fun U ↦ U.1) (iSup_affineOpens_eq_top X) T).2).mpr
  intro U
  let V := @ShortComplex.map _ _ _ _ _ _ T (ρ U.1) (hz U.1)
  have : V.HasHomology := hasHomology_of_abelian_witness
    (@coherentFormalModule_abelian U.1.toScheme (hN U.1) (I.comap U.1.ι)).1 V
  have hk : IsLimit (KernelFork.ofι V.f V.zero) :=
    (@formalCompletion_affine_kernel X _ I h U.1 (hN U.1) U.2
      (ρ U.1) (hz U.1) (hρ U.1).2.1 S hS).some
  have hm : Mono V.f := Fork.IsLimit.mono hk
  have he : Epi V.g := by
    have : HasKernels (CoherentFormalModule X I) :=
      hasKernels_of_abelian_witness (coherentFormalModule_abelian X I).1
    let K := ShortComplex.mk (kernel.ι T.g) T.g (kernel.condition T.g)
    have : K.HasHomology :=
      hasHomology_of_abelian_witness (coherentFormalModule_abelian X I).1 K
    have hK : K.ShortExact := ⟨K.exact_of_f_is_kernel (kernelIsKernel T.g)⟩
    exact ((hρ U.1).2.2 K hK).epi_g
  exact ShortComplex.ShortExact.mk' (V.exact_of_f_is_kernel hk) hm he

end AlgebraicGeometry
