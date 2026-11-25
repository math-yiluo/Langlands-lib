/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.Curve.AdditiveCohomologyTensorKernel
import WeilConjectures.AlgebraicGeometry.Curve.AdditiveCohomologyTensorSurjective

/-! # Canonical linear base change of additive first cohomology -/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.IsCurve

/-- Pullback of additive cohomology intertwines structural scalar actions.
Source: Stacks Project, Tags 03P2 and 02KH, naturality of the comparison.

Proof: Choose the scalar sheaf maps supplied by hscalar and hscalar'. Apply the
upper-star/lower-star adjunction to the two composites with q. On an etale object,
their adjoint sections coincide: hq identifies q with structural pullback, which
preserves products, and the cartesian square identifies the pulled-back scalar c
with the structural image of algebraMap k k' c. Section coordinates are injective,
so the two adjoint maps, and hence the two composites, agree. Naturality of the
canonical Ext pullback and functoriality of H.map now give the scalar identity.
No cohomological base-change isomorphism or finite-dimensionality is used. -/
private theorem additive_cohomology_pullback_smul
    {k k' : Type u}
    [Field k] [Field k'] [Algebra k k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve f]
    {C' : Scheme.{u}} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G' : Sheaf C'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (a' : ∀ U : C'.Etaleᵒᵖ, G'.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (q : (Etale.upperStar AddCommGrpCat.{u + 1} ι').obj G ⟶ G')
    (hq : (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
        a' (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ ι').obj U.unop))
          (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} ι').homEquiv
            G G' q).hom.app U x) =
          (Limits.pullback.fst U.unop.hom ι').appTop (a U x)))
    [Module k (Sheaf.H G 1)] [Module k' (Sheaf.H G' 1)]
    (hscalar : ∀ c : k, ∃ μ : G ⟶ G,
        (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
          let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
          a U (μ.hom.app U x) = a U x * ρ c) ∧
        ∀ x : Sheaf.H G 1,
          Sheaf.H.map μ 1 x = c • x)
    (hscalar' : ∀ c : k', ∃ μ : G' ⟶ G',
        (∀ (U : C'.Etaleᵒᵖ) (x : G'.obj.obj U),
          let ρ : k' →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f'.appTop.hom.comp (Scheme.ΓSpecIso (.of k')).inv.hom)
          a' U (μ.hom.app U x) = a' U x * ρ c) ∧
        ∀ x : Sheaf.H G' 1,
          Sheaf.H.map μ 1 x = c • x) :
    ∀ (c : k) (x : Sheaf.H G 1),
      Sheaf.H.map q 1 (Etale.cohomologyMap ι' G 1 (c • x)) =
        algebraMap k k' c • Sheaf.H.map q 1 (Etale.cohomologyMap ι' G 1 x) := by
  intro c x
  obtain ⟨μ, hμ, hμH⟩ := hscalar c
  obtain ⟨ν, hν, hνH⟩ := hscalar' (algebraMap k k' c)
  have hcomm : (Etale.upperStar AddCommGrpCat.{u + 1} ι').map μ ≫ q = q ≫ ν := by
    let adj := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} ι'
    apply (adj.homEquiv G G').injective
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    apply Sheaf.hom_ext
    ext U y
    let V := (MorphismProperty.Over.pullback @Etale ⊤ ι').obj U.unop
    apply (a' (Opposite.op V)).injective
    change a' (Opposite.op V) ((adj.homEquiv G G' q).hom.app U (μ.hom.app U y)) =
      a' (Opposite.op V) (ν.hom.app (Opposite.op V)
        ((adj.homEquiv G G' q).hom.app U y))
    rw [hq, hμ, hν, hq]
    rw [map_mul]
    congr 1
    have hw : (Limits.pullback.fst U.unop.hom ι') ≫ U.unop.hom ≫ f =
        V.hom ≫ f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) := by
      dsimp [V]
      rw [← Category.assoc, Limits.pullback.condition, Category.assoc, h.w]
      rfl
    have hs := congrArg Scheme.Hom.appTop hw
    simp only [Scheme.Hom.comp_appTop] at hs
    have hn := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap k k'))
    change CommRingCat.ofHom (algebraMap k k') ≫ (Scheme.ΓSpecIso (.of k')).inv =
      (Scheme.ΓSpecIso (.of k)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))).appTop at hn
    have he : (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ U.unop.hom.appTop ≫
        (Limits.pullback.fst U.unop.hom ι').appTop =
      CommRingCat.ofHom (algebraMap k k') ≫ (Scheme.ΓSpecIso (.of k')).inv ≫
        f'.appTop ≫ V.hom.appTop := by
      simpa only [Category.assoc] using
        (congrArg (fun t ↦ (Scheme.ΓSpecIso (.of k)).inv ≫ t) hs).trans
          (by rw [← Category.assoc, ← Category.assoc, ← hn]; simp only [Category.assoc])
    exact ConcreteCategory.congr_hom he c
  rw [← hμH x, Etale.cohomologyMap_map]
  rw [← Sheaf.H.map_comp_apply, hcomm, Sheaf.H.map_comp_apply, hνH]

/-- The canonical pullback of additive structure-sheaf cohomology is extension
of scalars. The given actions are required to be induced by structural scalar
multiplication on sections; no finite-dimensionality is assumed or asserted.
Source: Stacks Project, Tags 02KH and 03P2; Tag 0A3P, first sentence of proof.
(blueprint: lem-pbc-additive-cohomology-linear-base-change)

Proof: Identify G and G' with the lifted additive structure sheaves through the
natural section coordinates a and a'. The scalar section formulas uniquely determine
all scalar endomorphisms. The natural etale/Zariski comparison, together with the
Ext/derived and coefficient-universe comparisons, therefore intertwines the given
scalar actions with the usual actions on coherent cohomology. Choose a finite affine
cover of C. It exists since IsCurve supplies quasi-compactness; separatedness over the
affine field spectrum makes all intersections affine. Pull it back to C'. On every
intersection, affine sections after base change are the tensor product of the old
sections by k'. The adjoint formula hq identifies the induced cochain map with
s mapping to 1 tensor s. Naturality of the Cech/cohomology comparisons identifies this
map with H(q) composed with the canonical etale cohomology pullback. Tensoring over a
field is exact, so cohomology of the tensor complex is tensor cohomology. This gives
the k'-linear equivalence e and its normalization on every original class. The
displayed pullback square is handled by its unique isomorphism to the chosen
categorical pullback. In degree-one-zero cases (empty schemes, affine curves, and
zero-dimensional proper curves), the same complexes give the zero equivalence. No
Frobenius, torsion, connectedness, smoothness, or algebraic closedness is used. -/
theorem exists_additive_cohomology_linear_base_change
    {k k' : Type u}
    [Field k] [Field k'] [Algebra k k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve f]
    {C' : Scheme.{u}} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G' : Sheaf C'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (a' : ∀ U : C'.Etaleᵒᵖ, G'.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (ha' : ∀ (U V : C'.Etaleᵒᵖ) (g : U ⟶ V) (x : G'.obj.obj U),
      a' V (G'.obj.map g x) = g.unop.left.appTop (a' U x))
    (q : (Etale.upperStar AddCommGrpCat.{u + 1} ι').obj G ⟶ G')
    (hq : (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
        a' (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ ι').obj U.unop))
          (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} ι').homEquiv
            G G' q).hom.app U x) =
          (Limits.pullback.fst U.unop.hom ι').appTop (a U x)))
    [Module k (Sheaf.H G 1)] [Module k' (Sheaf.H G' 1)]
    (hscalar : ∀ c : k, ∃ μ : G ⟶ G,
        (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
          let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
          a U (μ.hom.app U x) = a U x * ρ c) ∧
        ∀ x : Sheaf.H G 1,
          Sheaf.H.map μ 1 x = c • x)
    (hscalar' : ∀ c : k', ∃ μ : G' ⟶ G',
        (∀ (U : C'.Etaleᵒᵖ) (x : G'.obj.obj U),
          let ρ : k' →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f'.appTop.hom.comp (Scheme.ΓSpecIso (.of k')).inv.hom)
          a' U (μ.hom.app U x) = a' U x * ρ c) ∧
        ∀ x : Sheaf.H G' 1,
          Sheaf.H.map μ 1 x = c • x) :
    ∃ e : Sheaf.H G' 1 ≃ₗ[k'] (k' ⊗[k] Sheaf.H G 1),
      ∀ x, e (Sheaf.H.map q 1 (Etale.cohomologyMap ι' G 1 x)) = 1 ⊗ₜ[k] x := by
  classical
  let : Module k (Sheaf.H G' 1) := Module.compHom _ (algebraMap k k')
  let : IsScalarTower k k' (Sheaf.H G' 1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let l : Sheaf.H G 1 →ₗ[k] Sheaf.H G' 1 :=
    { toFun := fun x ↦ Sheaf.H.map q 1 (Etale.cohomologyMap ι' G 1 x)
      map_add' := fun x y ↦ by simp only [map_add]
      map_smul' := additive_cohomology_pullback_smul
        f h G G' a a' q hq hscalar hscalar' }
  let B : k' →ₗ[k'] Sheaf.H G 1 →ₗ[k] Sheaf.H G' 1 :=
    { toFun := fun b ↦ b • l
      map_add' := fun b c ↦ add_smul b c l
      map_smul' := fun b c ↦ mul_smul b c l }
  let β : (k' ⊗[k] Sheaf.H G 1) →ₗ[k'] Sheaf.H G' 1 :=
    TensorProduct.AlgebraTensorModule.lift B
  have hβ (b : k') (x : Sheaf.H G 1) :
      β (b ⊗ₜ[k] x) = b • Sheaf.H.map q 1 (Etale.cohomologyMap ι' G 1 x) := by
    rfl
  have hker := additive_cohomology_tensor_kernel
    f h G G' a a' ha ha' q hq hscalar hscalar' β hβ
  have hinj : Function.Injective β := by
    intro z w heq
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, heq, sub_self]
  have hsurj := additive_cohomology_tensor_surjective
    f h G G' a a' ha ha' q hq hscalar hscalar' β hβ
  have hbij : Function.Bijective β := ⟨hinj, hsurj⟩
  let e := LinearEquiv.ofBijective β hbij
  refine ⟨e.symm, ?_⟩
  intro x
  apply e.injective
  rw [e.apply_symm_apply]
  change Sheaf.H.map q 1 (Etale.cohomologyMap ι' G 1 x) = β (1 ⊗ₜ[k] x)
  rw [hβ, one_smul]

end AlgebraicGeometry.IsCurve
