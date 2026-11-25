/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import WeilConjectures.CategoryTheory.FiniteTypeConstantLocalLinear
import WeilConjectures.CategoryTheory.FiniteTypeExtensionLocalPresentation
import WeilConjectures.CategoryTheory.FiniteTypeRestrictionExact
import WeilConjectures.CategoryTheory.FiniteTypeRestrictionMapExact
import WeilConjectures.CategoryTheory.LocalModuleIso

/-!
# Finite type locally constant module sheaves form a weak Serre subcategory

Source: Stacks Project, Modules on Sites, Tag 093U (3)
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

set_option linter.style.haveILetI false

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {B : Type u} [CommRing B]

private theorem restrictMap_preservesFiniteLimits (R : Sheaf J RingCat.{u})
    {X Y : C} (f : X ⟶ Y) : PreservesFiniteLimits (overMap.{u} R f) :=
  (overMap_exact R f).1

private theorem restrictMap_preservesFiniteColimits (R : Sheaf J RingCat.{u})
    {X Y : C} (f : X ⟶ Y) : PreservesFiniteColimits (overMap.{u} R f) :=
  (overMap_exact R f).2

attribute [local instance] restrictMap_preservesFiniteLimits restrictMap_preservesFiniteColimits

private def trivializationSieve
    (F : CategoryTheory.ringedSiteModules.{u}
      ((constantSheaf J RingCat.{u}).obj (RingCat.of B))) (U : C) : Sieve U where
  arrows V _ := ∃ M : ModuleCat.{u} B, Module.Finite B M ∧
    Nonempty (F.over V ≅ ((strictPerfectConstantSheaf J B).obj M).over V)
  downward_closed := by
    intro V W f hf g
    obtain ⟨M, hM, ⟨e⟩⟩ := hf
    exact ⟨M, hM, ⟨restrictIso F ((strictPerfectConstantSheaf J B).obj M) g.op e⟩⟩

private theorem locallyConstant_iff_trivializationSieve
    (F : CategoryTheory.ringedSiteModules.{u}
      ((constantSheaf J RingCat.{u}).obj (RingCat.of B))) :
    IsFiniteTypeLocallyConstant J B F ↔ ∀ U, trivializationSieve F U ∈ J U := by
  constructor
  · intro h U
    obtain ⟨S, hS, h⟩ := h U
    exact J.superset_covering (fun V f hf ↦ h V f hf) hS
  · intro h U
    exact ⟨trivializationSieve F U, h U, fun V f hf ↦ hf⟩

private theorem finite_kernel {M N : ModuleCat.{u} B} [IsNoetherianRing B]
    [Module.Finite B M] (f : M ⟶ N) : Module.Finite B (kernel f : ModuleCat.{u} B) := by
  exact Module.Finite.of_injective (kernel.ι f).hom
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

private theorem finite_cokernel {M N : ModuleCat.{u} B}
    [Module.Finite B N] (f : M ⟶ N) : Module.Finite B (cokernel f : ModuleCat.{u} B) := by
  exact Module.Finite.of_surjective (cokernel.π f).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- Kernel and cokernel closure, proved by refining simultaneous trivializations.
Source: Stacks Project, Modules on Sites, Tag 093U (3).
(auxiliary; not a blueprint node).

Proof: Intersect trivializing covers for the source and target. Transport the morphism
through these trivializations. Local linearity supplies a further covering where it is
induced by a coefficient-module map. Exactness of restriction and of the constant-module
functor identifies its kernel and cokernel with constants. The algebraic kernel is finite
by Noetherianity, and the algebraic cokernel is a quotient of a finite module. Transitivity
of covering sieves gives the asserted local trivializations on the original site. -/
private theorem finiteTypeLocallyConstant_kernel_cokernel [IsNoetherianRing B]
    (F G : CategoryTheory.ringedSiteModules.{u}
      ((constantSheaf J RingCat.{u}).obj (RingCat.of B))) (f : F ⟶ G)
    (hF : IsFiniteTypeLocallyConstant J B F) (hG : IsFiniteTypeLocallyConstant J B G) :
    IsFiniteTypeLocallyConstant J B (kernel f) ∧
      IsFiniteTypeLocallyConstant J B (cokernel f) := by
  letI : PreservesFiniteLimits (strictPerfectConstantSheaf J B) :=
    (strictPerfectConstantSheaf_exact J B).1
  letI : PreservesFiniteColimits (strictPerfectConstantSheaf J B) :=
    (strictPerfectConstantSheaf_exact J B).2
  have hlocal (U : C) (M N : ModuleCat.{u} B) (hM : Module.Finite B M)
      (hN : Module.Finite B N)
      (eF : F.over U ≅ ((strictPerfectConstantSheaf J B).obj M).over U)
      (eG : G.over U ≅ ((strictPerfectConstantSheaf J B).obj N).over U) :
      ∃ S ∈ J U, ∀ (V : C) (a : V ⟶ U), S a →
        trivializationSieve (kernel f) U a ∧ trivializationSieve (cokernel f) U a := by
    let := hM
    let := hN
    let φ := eF.inv ≫ f.over U ≫ eG.hom
    obtain ⟨S, hS, h⟩ := exists_cover_constant_linearMap J B M N U φ
    refine ⟨S, hS, ?_⟩
    intro V a ha
    letI : PreservesFiniteLimits (overFunctor.{u}
        ((constantSheaf J RingCat.{u}).obj (RingCat.of B)) V) :=
      (overFunctor_exact ((constantSheaf J RingCat.{u}).obj (RingCat.of B)) V).1
    letI : PreservesFiniteColimits (overFunctor.{u}
        ((constantSheaf J RingCat.{u}).obj (RingCat.of B)) V) :=
      (overFunctor_exact ((constantSheaf J RingCat.{u}).obj (RingCat.of B)) V).2
    obtain ⟨g, hg⟩ := h V a ha
    let eFV := restrictIso F ((strictPerfectConstantSheaf J B).obj M) a.op eF
    let eGV := restrictIso G ((strictPerfectConstantSheaf J B).obj N) a.op eG
    have hv : f.over V ≫ eGV.hom = eFV.hom ≫
        ((strictPerfectConstantSheaf J B).map g).over V := by
      rw [← hg]
      ext W x
      change eG.hom.val.app ((Over.map a).op.obj W) (f.val.app (Opposite.op W.unop.left) x) =
        eG.hom.val.app ((Over.map a).op.obj W) (f.val.app (Opposite.op W.unop.left)
          (eF.inv.val.app ((Over.map a).op.obj W)
            (eF.hom.val.app ((Over.map a).op.obj W) x)))
      have he := ConcreteCategory.congr_hom
        (congrArg (fun k ↦ k.val.app ((Over.map a).op.obj W)) eF.hom_inv_id) x
      change eF.inv.val.app ((Over.map a).op.obj W)
        (eF.hom.val.app ((Over.map a).op.obj W) x) = x at he
      exact (congrArg (fun y ↦ eG.hom.val.app ((Over.map a).op.obj W)
        (f.val.app (Opposite.op W.unop.left) y)) he).symm
    let ek := PreservesKernel.iso (overFunctor _ V) f ≪≫
      kernel.mapIso (f.over V) (((strictPerfectConstantSheaf J B).map g).over V)
        eFV eGV hv ≪≫
      (PreservesKernel.iso (overFunctor _ V) ((strictPerfectConstantSheaf J B).map g)).symm ≪≫
      (overFunctor _ V).mapIso (PreservesKernel.iso (strictPerfectConstantSheaf J B) g).symm
    let ec := PreservesCokernel.iso (overFunctor _ V) f ≪≫
      cokernel.mapIso (f.over V) (((strictPerfectConstantSheaf J B).map g).over V)
        eFV eGV hv ≪≫
      (PreservesCokernel.iso (overFunctor _ V) ((strictPerfectConstantSheaf J B).map g)).symm ≪≫
      (overFunctor _ V).mapIso (PreservesCokernel.iso (strictPerfectConstantSheaf J B) g).symm
    exact ⟨⟨kernel g, finite_kernel g, ⟨ek⟩⟩, ⟨cokernel g, finite_cokernel g, ⟨ec⟩⟩⟩
  constructor
  all_goals
    apply (locallyConstant_iff_trivializationSieve _).2
    intro U
    obtain ⟨S, hS, hFS⟩ := hF U
    obtain ⟨T, hT, hGT⟩ := hG U
    apply J.transitive (J.intersection_covering hS hT)
    intro V a ha
    obtain ⟨M, hM, ⟨eF⟩⟩ := hFS V a ha.1
    obtain ⟨N, hN, ⟨eG⟩⟩ := hGT V a ha.2
    obtain ⟨R, hR, h⟩ := hlocal V M N hM hN eF eG
    apply J.superset_covering _ hR
    intro W b hb
    first | exact (h W b hb).1 | exact (h W b hb).2

private theorem finiteTypeLocallyConstant_extension [IsNoetherianRing B]
    (S : ShortComplex (CategoryTheory.ringedSiteModules.{u}
      ((constantSheaf J RingCat.{u}).obj (RingCat.of B))))
    (hS : S.ShortExact) (h₁ : IsFiniteTypeLocallyConstant J B S.X₁)
    (h₃ : IsFiniteTypeLocallyConstant J B S.X₃) :
    IsFiniteTypeLocallyConstant J B S.X₂ := by
  letI : PreservesFiniteLimits (strictPerfectConstantSheaf J B) :=
    (strictPerfectConstantSheaf_exact J B).1
  letI : PreservesFiniteColimits (strictPerfectConstantSheaf J B) :=
    (strictPerfectConstantSheaf_exact J B).2
  let F := strictPerfectConstantSheaf J B
  let R := (constantSheaf J RingCat.{u}).obj (RingCat.of B)
  apply (locallyConstant_iff_trivializationSieve _).2
  intro U
  obtain ⟨A, hA, h₁A⟩ := h₁ U
  obtain ⟨T, hT, h₃T⟩ := h₃ U
  apply J.transitive (J.intersection_covering hA hT)
  intro V a ha
  obtain ⟨M, hM, ⟨eM⟩⟩ := h₁A V a ha.1
  obtain ⟨N, hN, ⟨eN⟩⟩ := h₃T V a ha.2
  obtain ⟨A', hA', h⟩ := exists_cover_constant_presentation S hS V M N hM hN eM eN
  apply J.transitive hA'
  intro W b hb
  obtain ⟨K, Q, hK, hQ, φ, ⟨ec⟩⟩ := h W b hb
  let := hK
  let := hQ
  obtain ⟨A'', hA'', h'⟩ := exists_cover_constant_linearMap J B K Q W φ
  apply J.superset_covering _ hA''
  intro Z c hc
  letI : PreservesFiniteLimits (overFunctor.{u} R Z) := (overFunctor_exact R Z).1
  letI : PreservesFiniteColimits (overFunctor.{u} R Z) := (overFunctor_exact R Z).2
  obtain ⟨g, hg⟩ := h' Z c hc
  let eK := (overFunctorMap R c).app (F.obj K)
  let eQ := (overFunctorMap R c).app (F.obj Q)
  have : (overMap R c).Additive := ⟨fun {_ _} f g ↦ by ext V x; rfl⟩
  change eK.inv ≫ (overMap R c).map φ ≫ eQ.hom = (F.map g).over Z at hg
  have hv : (overMap R c).map φ ≫ eQ.hom = eK.hom ≫ (F.map g).over Z := by
    apply (cancel_epi eK.inv).1
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hg
  let e := (overFunctorMap R c).app S.X₂ |>.symm
  let e' := e ≪≫ (overMap R c).mapIso ec ≪≫
    PreservesCokernel.iso (overMap R c) φ ≪≫
    cokernel.mapIso _ ((F.map g).over Z) eK eQ hv ≪≫
    (PreservesCokernel.iso (overFunctor R Z) (F.map g)).symm ≪≫
    (overFunctor R Z).mapIso (PreservesCokernel.iso F g).symm
  exact ⟨cokernel g, finite_cokernel g, ⟨e'⟩⟩

/-- Finite type locally constant module sheaves are closed under kernels, cokernels and
extensions. Source: Stacks Project, Modules on Sites, Tag 093U (3)
(auxiliary; not a blueprint node).

Proof plan:
1. On each object pass to its slice and successively trivialize both sheaves. Compose covers
and use relocalization. Restriction is exact: kernels are sectionwise and epimorphisms are
locally surjective, also on slices. The faithful exact forgetful functor transfers this to
module sheaves. Constants restrict canonically to constants.
2. A morphism between constant finite modules is locally induced by a linear map. Constant
module section exactness identifies its kernel and cokernel with constants of the algebraic
kernel and cokernel. Noetherianity makes the kernel finite; quotient generators give finite
cokernel. Empty-cover members have zero restriction.
3. For an extension trivialize the outer terms to constants M and N. Choose a finite free
surjection B^t onto N. Its kernel K is finite by Noetherianity. Constant section exactness
provides the corresponding constant short exact sequence, including t = 0.
4. Local surjectivity lifts the finitely many generators of N after successive refinements.
Their linear combination defines a map from the constant free module to the middle sheaf;
the constant sheafification universal property extends it and verifies its composite.
5. The kernel property gives g from the constant K to the constant M. The maps
k ↦ (-g(k), k) and (m, v) ↦ i(m) + lift(v) present the middle sheaf as the cokernel of the
first map: the second is locally surjective and its kernel is the image of the first.
6. Refine until g comes from a linear h. Additivity identifies the constant direct sum;
constant section exactness identifies the cokernel with the constant algebraic quotient
(M ⊕ B^t)/{(-h(k), k)}. Images of finite generators generate this quotient. Empty-cover
members are zero; composition of all covers proves extension closure without using points.
The proof uses the localized-ringed-site construction, local surjectivity, exact forgetful
functor, constant restriction, local constant morphisms, constant section exactness and
Noetherian finite-submodule lemmas recorded in the node. -/
theorem finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (B : Type u) [CommRing B] [IsNoetherianRing B] :
    (∀ (F G : CategoryTheory.ringedSiteModules.{u}
        ((constantSheaf J RingCat.{u}).obj (RingCat.of B))) (f : F ⟶ G),
      IsFiniteTypeLocallyConstant J B F → IsFiniteTypeLocallyConstant J B G →
        IsFiniteTypeLocallyConstant J B (kernel f) ∧
        IsFiniteTypeLocallyConstant J B (cokernel f)) ∧
    (∀ S : ShortComplex (CategoryTheory.ringedSiteModules.{u}
        ((constantSheaf J RingCat.{u}).obj (RingCat.of B))),
      S.ShortExact → IsFiniteTypeLocallyConstant J B S.X₁ →
        IsFiniteTypeLocallyConstant J B S.X₃ → IsFiniteTypeLocallyConstant J B S.X₂) := by
  exact ⟨fun F G f hF hG ↦ finiteTypeLocallyConstant_kernel_cokernel F G f hF hG,
    fun S hS h₁ h₃ ↦ finiteTypeLocallyConstant_extension S hS h₁ h₃⟩

end SheafOfModules
