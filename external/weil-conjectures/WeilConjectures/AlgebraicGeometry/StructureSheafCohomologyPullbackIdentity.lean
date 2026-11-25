/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-! Identity law for pullback on structure-sheaf cohomology.
(blueprint: lem-sc-structure-sheaf-cohomology-pullback-identity)
-/

@[expose] public section

universe u

open CategoryTheory

private theorem ext_map_to_identity {C : Type*} [Category C] [Abelian C]
    [HasExt.{u} C] [EnoughInjectives C] (L : C ⥤ C) [L.Additive]
    [Limits.PreservesFiniteLimits L] [Limits.PreservesFiniteColimits L] (α : L ⟶ 𝟭 C)
    {A B : C} {n : ℕ} (x : Abelian.Ext A B n) :
    (x.mapExactFunctor L).comp (Abelian.Ext.mk₀ (α.app B)) (add_zero n) =
      (Abelian.Ext.mk₀ (α.app A)).comp x (zero_add n) := by
  induction n generalizing B with
  | zero =>
    obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective A B).2 x
    rw [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀,
      Abelian.Ext.mk₀_comp_mk₀]
    exact congrArg Abelian.Ext.mk₀ (α.naturality f)
  | succ n ih =>
    let S := ShortComplex.mk (Injective.ι B) (Limits.cokernel.π (Injective.ι B))
      (Limits.cokernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    obtain ⟨y, rfl⟩ := Abelian.Ext.covariant_sequence_exact₁ A hS x
      (Abelian.Ext.eq_zero_of_injective _) rfl
    let φ : S.map L ⟶ S :=
      { τ₁ := α.app S.X₁
        τ₂ := α.app S.X₂
        τ₃ := α.app S.X₃
        comm₁₂ := (α.naturality S.f).symm
        comm₂₃ := (α.naturality S.g).symm }
    calc
      _ = ((y.mapExactFunctor L).comp (Abelian.Ext.mk₀ (α.app S.X₃))
          (add_zero n)).comp hS.extClass rfl :=
        Adjunction.mapExactFunctor_comp_extClass_comp_mk₀ hS hS φ y
      _ = ((Abelian.Ext.mk₀ (α.app A)).comp y (zero_add n)).comp hS.extClass rfl :=
        congrArg (fun z : Abelian.Ext (L.obj A) S.X₃ n => z.comp hS.extClass rfl) (ih y)
      _ = _ := (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (α.app A)) y hS.extClass
        (zero_add n) rfl (zero_add (n + 1)))

namespace AlgebraicGeometry.Scheme

/-- The canonical pullback along an identity scheme morphism is the identity.
Source: Stacks Project, Cohomology of Sheaves, Section 01F7, equation-functorial
and Remark 01FB.

Proof: Write L for inverse image along the identity and let alpha : L ≅ Id
be the unique left-adjoint comparison with identity direct image, compatible with the
adjunction unit. The adjoint of the identity structure map is alpha at the additive
structure sheaf O. Write c : Z ≅ L(Z) for the constant-integer-sheaf comparison used
in the definition. Its construction by uniqueness of left adjoints gives
c.hom ≫ alpha.hom.app Z = id. Naturality of alpha on Ext identifies L(x) followed
by alpha at O with alpha at Z followed by x. Prove this by induction on the degree:
in degree zero use naturality on ordinary morphisms; in successor degree embed O
into an injective, express x as a connecting class, and use naturality of extension
classes for the map of short exact sequences induced by alpha. Unfolding H.mapFunctor
and H.map, pullback sends x to the Yoneda
composite c.hom ; L(x) ; alpha at O. Substitution and cancellation give x.
Thus the additive homomorphism is the identity in every degree. In degree zero this
is the usual identity map on global sections; the argument also applies to the empty
scheme, where all the cohomology groups are zero.
(blueprint: lem-sc-structure-sheaf-cohomology-pullback-identity) -/
theorem structureSheafCohomologyPullback_identity (X : Scheme.{u}) (n : ℕ) :
    structureSheafCohomologyPullback (𝟙 X) n =
      AddMonoidHom.id (Sheaf.H (structureSheafAb X) n) := by
  let G := 𝟭 (TopologicalSpace.Opens X)
  let J := Opens.grothendieckTopology X
  let adj := G.sheafAdjunctionContinuous AddCommGrpCat.{u} J J
  let α := adj.leftAdjointUniq Adjunction.id
  have hstructure :
      (adj.homEquiv (structureSheafAb X) (structureSheafAb X)).symm
        (⟨Functor.whiskerRight (𝟙 X : X ⟶ X).c
          (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u})⟩) =
        α.hom.app (structureSheafAb X) := by
    change (adj.homEquiv (structureSheafAb X) (structureSheafAb X)).symm
      (𝟙 (structureSheafAb X)) = α.hom.app (structureSheafAb X)
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    exact (Adjunction.homEquiv_leftAdjointUniq_hom_app adj Adjunction.id _).symm
  let A := AddCommGrpCat.of (ULift.{u} ℤ)
  let Z := (constantSheaf J AddCommGrpCat.{u}).obj A
  let cAdj := constantSheafAdj J AddCommGrpCat.{u} Limits.isTerminalTop
  let e := G.constantSheafsheafPullbackIso AddCommGrpCat.{u} J J
    Limits.isTerminalTop Limits.isTerminalTop
  have hc : e.hom.app A = α.hom.app Z := by
    dsimp only [e, Functor.constantSheafsheafPullbackIso, Iso.app_hom]
    apply (((cAdj.comp adj).ofNatIsoRight
      (G.sheafPushforwardContinuousCompSheafSectionsObjIso AddCommGrpCat.{u} J J
        (Opposite.op (⊤ : TopologicalSpace.Opens X)))).homEquiv A Z).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    change cAdj.unit.app A = (cAdj.homEquiv A Z) ((adj.homEquiv Z Z) (α.hom.app Z))
    have hα : (adj.homEquiv Z Z) (α.hom.app Z) = 𝟙 Z :=
      Adjunction.homEquiv_leftAdjointUniq_hom_app adj Adjunction.id Z
    exact (cAdj.homEquiv_id A).symm.trans (congrArg (cAdj.homEquiv A Z) hα.symm)
  let L := G.sheafPullback AddCommGrpCat.{u} J J
  have : Limits.PreservesFiniteLimits L := Limits.preservesFiniteLimits_of_natIso α.symm
  have : Limits.PreservesColimits L := adj.leftAdjoint_preservesColimits
  have : Limits.PreservesBinaryBiproducts L :=
    Limits.preservesBinaryBiproducts_of_preservesBinaryProducts L
  have : L.Additive := Functor.additive_of_preservesBinaryBiproducts L
  ext x
  unfold structureSheafCohomologyPullback
  simp only [AddMonoidHom.comp_apply, Sheaf.H.mapFunctor_apply, Sheaf.H.map_apply]
  change ((Abelian.Ext.mk₀ (e.inv.app A)).comp
    (x.mapExactFunctor (G.sheafPullback AddCommGrpCat.{u} J J)) (zero_add n)).comp
    (Abelian.Ext.mk₀ ((adj.homEquiv (structureSheafAb X) (structureSheafAb X)).symm
      (⟨Functor.whiskerRight (𝟙 X : X ⟶ X).c
        (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u})⟩)))
      (add_zero n) = x
  rw [hstructure]
  rw [Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ (e.inv.app A)) (x.mapExactFunctor L)
    (Abelian.Ext.mk₀ (α.hom.app (structureSheafAb X))) (zero_add n) (add_zero n) (by omega)]
  rw [ext_map_to_identity L α.hom x, ← hc, Abelian.Ext.mk₀_comp_mk₀_assoc]
  simp

end AlgebraicGeometry.Scheme
