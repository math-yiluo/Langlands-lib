/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtaleUnitsSheaf
public import WeilConjectures.CategoryTheory.TorsionSheafConstantModule
import Mathlib.Algebra.Category.Grp.EpiMono

/-! # Roots of unity on the small pro-etale site

Source: Stacks Project, Section 59.28, Tag 03PK; Definition 59.23.1, Tag 03P4
(auxiliary; not a blueprint node).

The power map, kernel, constant-ring module and transition maps use the original
sectionwise global-sections rings. No invertibility hypothesis on the exponent is imposed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The `N`-th power morphism on `G_m`, written additively as `N • 𝟙`.
Source: Stacks Project, Tag 03PK (auxiliary; not a blueprint node). -/
def proEtaleUnitsPower (S : Scheme.{u}) (N : ℕ) :
    proEtaleUnitsSheaf S ⟶ proEtaleUnitsSheaf S :=
  N • 𝟙 (proEtaleUnitsSheaf S)

/-- The sheaf of `N`-th roots of unity, the kernel of the power map on `O_Sˣ`.
Source: Stacks Project, Tags 03PK and 03P4 (auxiliary; not a blueprint node). -/
noncomputable def proEtaleRootsOfUnitySheaf (S : Scheme.{u}) (N : ℕ) :
    Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1} :=
  kernel (proEtaleUnitsPower S N)

/-- The canonical inclusion of roots of unity into units.
Source: Stacks Project, Tags 03PK and 03P4 (auxiliary; not a blueprint node). -/
noncomputable def proEtaleRootsOfUnityInclusion (S : Scheme.{u}) (N : ℕ) :
    proEtaleRootsOfUnitySheaf S N ⟶ proEtaleUnitsSheaf S :=
  kernel.ι (proEtaleUnitsPower S N)

/-- The canonical sectionwise identification of the kernel with the roots-of-unity group
is uniquely determined by its compatibility with the inclusion into units.
Source: Stacks Project, Tags 03PK and 03P4 (auxiliary; not a blueprint node).
Proof: the inclusion of abelian sheaves into presheaves creates kernels and evaluation
preserves them. Thus its sectionwise kernel is the subgroup of units whose `N`-th power
is one, precisely Mathlib's `rootsOfUnity`. The inclusion determines the identification
uniquely because it is injective. Universe lifting and additive notation change no elements. -/
theorem existsUnique_proEtaleRootsOfUnitySections (S : Scheme.{u}) (N : ℕ) (U : S.ProEtᵒᵖ) :
    ∃! e : (proEtaleRootsOfUnitySheaf S N).obj.obj U ≃+
        Additive (rootsOfUnity N ((proEtaleStructureSheaf S).obj.obj U)),
      ∀ x, ULift.up (Additive.ofMul (Additive.toMul (e x)).val) =
        (proEtaleRootsOfUnityInclusion S N).hom.app U x := by
  let E := sheafToPresheaf (ProEt.topology S) AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ _).obj U
  let φ := E.map (proEtaleUnitsPower S N)
  let e := PreservesKernel.iso E (proEtaleUnitsPower S N) ≪≫
    AddCommGrpCat.kernelIsoKer φ
  let g : φ.hom.ker ≃+
      Additive (rootsOfUnity N ((proEtaleStructureSheaf S).obj.obj U)) :=
    { toFun := fun y ↦ Additive.ofMul ⟨y.1.down.toMul, by
        apply (mem_rootsOfUnity N _).2
        have hy : N • y.1 = 0 := y.2
        exact congrArg (fun z ↦ z.down.toMul) hy⟩
      invFun := fun y ↦ ⟨ULift.up (Additive.ofMul y.toMul.val), by
        change N • (ULift.up (Additive.ofMul y.toMul.val)) = 0
        apply ULift.ext
        apply Additive.toMul.injective
        exact (mem_rootsOfUnity N _).1 y.toMul.property⟩
      left_inv := fun y ↦ by rfl
      right_inv := fun y ↦ by rfl
      map_add' := fun y z ↦ by rfl }
  let e' := e.addCommGroupIsoToAddEquiv.trans g
  have he (x : (proEtaleRootsOfUnitySheaf S N).obj.obj U) :
      ULift.up (Additive.ofMul (Additive.toMul (e' x)).val) =
        (proEtaleRootsOfUnityInclusion S N).hom.app U x := by
    change ((e.hom ≫ AddCommGrpCat.ofHom φ.hom.ker.subtype) x) = _
    rw [Iso.trans_hom, Category.assoc, AddCommGrpCat.kernelIsoKer_hom_comp_subtype,
      PreservesKernel.iso_hom, kernelComparison_comp_ι]
    rfl
  refine ⟨e', he, ?_⟩
  intro e'' he''
  apply AddEquiv.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg (fun y ↦ y.down.toMul) ((he'' x).trans (he x).symm)

/-- Sections of the roots-of-unity sheaf, identified by the canonical kernel inclusion.
Source: Stacks Project, Tags 03PK and 03P4 (auxiliary; not a blueprint node).
The selected equivalence is uniquely characterized, rather than an arbitrary isomorphism. -/
noncomputable def proEtaleRootsOfUnitySections (S : Scheme.{u}) (N : ℕ) (U : S.ProEtᵒᵖ) :
    (proEtaleRootsOfUnitySheaf S N).obj.obj U ≃+
      Additive (rootsOfUnity N ((proEtaleStructureSheaf S).obj.obj U)) :=
  (existsUnique_proEtaleRootsOfUnitySections S N U).exists.choose

/-- Every group of sections is killed by `N`.
Source: Stacks Project, Tag 03PK (auxiliary; not a blueprint node).
Proof: use the sectionwise kernel description: a section is a unit `x` with `x^N = 1`.
In additive notation this equality is `N • x = 0`. Injectivity of the kernel inclusion
then proves the same equality in the roots-of-unity sheaf. -/
theorem proEtaleRootsOfUnity_nsmul (S : Scheme.{u}) (N : ℕ)
    (U : S.ProEtᵒᵖ) (x : (proEtaleRootsOfUnitySheaf S N).obj.obj U) : N • x = 0 := by
  have hmono : Mono (proEtaleRootsOfUnityInclusion S N) := by
    dsimp [proEtaleRootsOfUnityInclusion]
    infer_instance
  have : Mono (proEtaleRootsOfUnityInclusion S N).hom :=
    (sheafToPresheaf _ _).map_mono _
  have hx := congrArg (fun f ↦ f.hom.app U x) (kernel.condition (proEtaleUnitsPower S N))
  apply (AddCommGrpCat.mono_iff_injective
    ((proEtaleRootsOfUnityInclusion S N).hom.app U)).mp inferInstance
  change N • ((proEtaleRootsOfUnityInclusion S N).hom.app U x) = 0 at hx
  simpa only [map_nsmul, map_zero] using hx

/-- The constant coefficient ring in the ambient universe of pro-etale abelian sheaves.
Source: Stacks Project, Tags 03PK and 03CY (auxiliary; not a blueprint node). -/
noncomputable abbrev proEtaleRootsOfUnityCoefficientRing (S : Scheme.{u}) (N : ℕ) :
    Sheaf (ProEt.topology S) RingCat.{u + 1} :=
  constantZModRingSheaf (ProEt.topology S) N

/-- The canonical module sheaf over the constant ring sheaf `Z/N` for positive `N`.
Source: Stacks Project, Tags 03PK and 03CY (auxiliary; not a blueprint node). -/
noncomputable def proEtaleRootsOfUnityModule (S : Scheme.{u}) (N : ℕ) (hN : 0 < N) :
    ringedSiteModules.{u + 1} (proEtaleRootsOfUnityCoefficientRing S N) :=
  torsionSheafModule.{u + 1} (ProEt.topology S) N hN (proEtaleRootsOfUnitySheaf S N)
    (proEtaleRootsOfUnity_nsmul S N)

/-- Taking the `(N'/N)`-th power of an `N'`-th root lands in the kernel of `[N]`.
Source: Stacks Project, Tag 03PK (auxiliary; not a blueprint node).
Proof: from `N ∣ N'` and positive `N`, obtain `(N'/N)*N = N'`. Compose the two
power maps and use the kernel equation for `[N']`; sectionwise this is
`(x^(N'/N))^N = x^N' = 1`. -/
theorem proEtaleRootsOfUnityTransition_condition (S : Scheme.{u}) (N N' : ℕ)
    (hN : 0 < N) (hN' : 0 < N') (h : N ∣ N') :
    (proEtaleRootsOfUnityInclusion S N' ≫
      ((N' / N) • 𝟙 (proEtaleUnitsSheaf S))) ≫ proEtaleUnitsPower S N = 0 := by
  have _ := hN
  have _ := hN'
  simp only [proEtaleUnitsPower, Preadditive.comp_nsmul, Category.comp_id, smul_smul,
    Nat.mul_comm N (N' / N),
    Nat.div_mul_cancel h]
  exact kernel.condition (proEtaleUnitsPower S N')

/-- The transition morphism, induced by `x ↦ x^(N'/N)` on units via the kernel property.
Source: Stacks Project, Tag 03PK (auxiliary; not a blueprint node). -/
noncomputable def proEtaleRootsOfUnityTransition (S : Scheme.{u}) (N N' : ℕ)
    (hN : 0 < N) (hN' : 0 < N') (h : N ∣ N') :
    proEtaleRootsOfUnitySheaf S N' ⟶ proEtaleRootsOfUnitySheaf S N :=
  kernel.lift (proEtaleUnitsPower S N)
    (proEtaleRootsOfUnityInclusion S N' ≫ ((N' / N) • 𝟙 (proEtaleUnitsSheaf S)))
    (proEtaleRootsOfUnityTransition_condition S N N' hN hN' h)

end AlgebraicGeometry.Scheme
