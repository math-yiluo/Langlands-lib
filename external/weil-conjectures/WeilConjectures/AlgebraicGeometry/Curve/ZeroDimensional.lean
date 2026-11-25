/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimensionComplex

/-!
# Étale cohomology of zero-dimensional schemes over an algebraically closed field

Let `k` be an algebraically closed field and `X` a scheme of finite type over `k` of dimension
at most zero. Then `X` is a finite set of closed points `x` with residue fields `k`, and for
every abelian étale sheaf `F` on `X`,
`H⁰(X, F) ≅ ∏ₓ F_x̄` and `Hᵠ(X, F) = 0` for `q > 0`.

## Main statements

- `AlgebraicGeometry.Scheme.bijective_toPresheafFiber_etalePoint`: on `Spec κ` for a separably
  closed field `κ`, the stalk of an étale presheaf at the tautological geometric point is its
  group of global sections.
- `AlgebraicGeometry.nonempty_addEquiv_sheafH_zero_pi_sheafFiber`: `H⁰(X, F) ≅ ∏ₓ F_x̄` for
  `X` zero-dimensional of finite type over an algebraically closed field.
- `AlgebraicGeometry.subsingleton_sheafH_of_topologicalKrullDim_le_zero`: `Hᵠ(X, F) = 0` for
  `q > 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Etale

namespace Scheme

variable (κ : Type u) [Field κ] [IsSepClosed κ]

/-- The tautological element of the fibre of the terminal object `Spec κ` of the small étale
site of `Spec κ`, at the geometric point `𝟙 : Spec κ ⟶ Spec κ`. -/
noncomputable def etalePointFiberObj :
    (pointSmallEtale (𝟙 (Spec (.of κ)))).fiber.obj (etalePoint κ) :=
  Over.homMk (𝟙 _)

/-- For the geometric point `𝟙 : Spec κ ⟶ Spec κ`, an element `v` of the fibre of an étale
`Spec κ`-scheme `V` is a section of `V`, so it is the image of the tautological element under
a morphism `Spec κ ⟶ V` of the étale site. -/
lemma exists_hom_etalePoint_fiber_map {V : (Spec (.of κ)).Etale}
    (v : (pointSmallEtale (𝟙 (Spec (.of κ)))).fiber.obj V) :
    ∃ σ : etalePoint κ ⟶ V,
      (pointSmallEtale (𝟙 (Spec (.of κ)))).fiber.map σ (etalePointFiberObj κ) = v := by
  refine ⟨MorphismProperty.Over.homMk v.left (Over.w v), ?_⟩
  refine Over.OverMorphism.ext ?_
  exact Category.id_comp v.left

/-- **Stalks on a geometric point.** Let `κ` be a separably closed field. The stalk of an
abelian presheaf `P` on the small étale site of `Spec κ` at the geometric point
`𝟙 : Spec κ ⟶ Spec κ` is its group of global sections: the canonical map `P(Spec κ) ⟶ P_κ` is
bijective, since every element of the fibre of an étale `Spec κ`-scheme is a section. -/
lemma bijective_toPresheafFiber_etalePoint
    (P : (Spec (.of κ)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Function.Bijective ((pointSmallEtale (𝟙 (Spec (.of κ)))).toPresheafFiber (etalePoint κ)
      (etalePointFiberObj κ) P) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : LocallySmall.{u} (Spec (.of κ)).Etale := locallySmall_self _
  constructor
  · intro a b h
    obtain ⟨Y, f, y, -, hab⟩ := ((pointSmallEtale _).toPresheafFiber_eq_iff' _ _ a b).1 h
    obtain ⟨σ, -⟩ := exists_hom_etalePoint_fiber_map κ y
    have hσ : σ ≫ f = 𝟙 _ := isTerminalEtalePoint.hom_ext _ _
    have := congr(P.map σ.op $hab)
    simpa [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, hσ] using this
  · intro p
    obtain ⟨Y, y, z, rfl⟩ := (pointSmallEtale _).toPresheafFiber_jointly_surjective p
    obtain ⟨σ, hσ⟩ := exists_hom_etalePoint_fiber_map κ y
    exact ⟨P.map σ.op z, by rw [GrothendieckTopology.Point.toPresheafFiber_w_apply, hσ]⟩

end Scheme

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The points of a scheme `X` of dimension at most zero, locally of finite type and
quasi-compact over a field, form a finite set of closed points. -/
lemma Scheme.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] [QuasiCompact g]
    (hX : topologicalKrullDim X ≤ 0) : Finite X ∧ ∀ x : X, IsClosed ({x} : Set X) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian X := {}
  have hdim : topologicalKrullDim (Set.univ : Set X) ≤ 0 := by
    rwa [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph]
  obtain ⟨hfin, hcl⟩ :=
    IsClosed.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero isClosed_univ hdim
  exact ⟨Set.finite_univ_iff.mp hfin, fun x ↦ hcl x (Set.mem_univ x)⟩

/-- Blueprint `lemma-sheaves-finite-support-finite-morphisms--1`, positive degrees: **étale
cohomology in dimension zero.** Let `k` be algebraically closed and `X` a scheme of finite type over
`k` of dimension at most zero. Then `Hᵠ(X, F) = 0` for every abelian étale sheaf `F` and `q > 0`:
`X` is a finite set of closed points with algebraically closed residue fields, so `F` is the
direct sum of the pushforwards of its restrictions to these points, which are acyclic.
(blueprint: `lemma-sheaves-finite-support-finite-morphisms--1`) -/
theorem subsingleton_sheafH_of_topologicalKrullDim_le_zero {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] [QuasiCompact g]
    (hX : topologicalKrullDim X ≤ 0) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) : Subsingleton (Sheaf.H F (n + 1)) := by
  obtain ⟨hfin, hcl⟩ := Scheme.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero g hX
  have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x ↦ x.2⟩
  refine Etale.subsingleton_H_of_isZero_upperStar ⊥ (Set.toFinite _) (fun x _ ↦ hcl x)
    (fun x _ ↦ ?_) F (Scheme.Etale.isZero_sheaf_of_isEmpty _) n
  have := Scheme.isAlgClosed_residueField_of_isClosed g x (hcl x)
  infer_instance

/-- Blueprint `lemma-sheaves-finite-support-finite-morphisms--1`, degree zero: **étale cohomology in
dimension zero.** Let `k` be algebraically closed and `X` a scheme of finite type over `k` of
dimension at most zero, and `F` an abelian étale sheaf on `X`. Then
`H⁰(X, F) ≅ ∏ₓ F_x̄`, the (finite) product of the geometric stalks of `F` at the points of `X`.

The points of `X` are finitely many closed points with algebraically closed residue fields
(`AlgebraicGeometry.Scheme.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero`); the
unit maps assemble to an isomorphism `F ≅ ⨁ₓ iₓ_* iₓ^* F` along `iₓ : Spec κ(x) ⟶ X`, and
`H⁰(X, iₓ_* iₓ^* F) = H⁰(Spec κ(x), iₓ^* F)` is the stalk of `iₓ^* F` at the tautological
geometric point (`AlgebraicGeometry.Scheme.bijective_toPresheafFiber_etalePoint`), which is
the stalk of `F` at `x̄`. The vanishing in positive degrees is
`AlgebraicGeometry.subsingleton_sheafH_of_topologicalKrullDim_le_zero`.
(blueprint: `lemma-sheaves-finite-support-finite-morphisms--1`) -/
theorem nonempty_addEquiv_sheafH_zero_pi_sheafFiber {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] [QuasiCompact g]
    (hX : topologicalKrullDim X ≤ 0) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Nonempty (Sheaf.H F 0 ≃+
      ∀ x : X, ((Scheme.pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) := by
  obtain ⟨hfin, hcl⟩ := Scheme.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero g hX
  have := Fintype.ofFinite X
  have : HasFiniteBiproducts (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have hκ (x : X) : IsAlgClosed (X.residueField x) :=
    Scheme.isAlgClosed_residueField_of_isClosed g x (hcl x)
  have hsep (x : X) : IsSepClosed (X.residueField x) := by have := hκ x; infer_instance
  have hsep' (x : X) : IsSepClosed (IsLocalRing.ResidueField (X.presheaf.stalk x)) := hsep x
  have (x : X) : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.1 (hcl x)
  let i (x : X) := X.fromSpecResidueField x
  let adj (x : X) := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (i x)
  let G' (x : X) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    (i x)_*[AddCommGrpCat.{u + 1}].obj ((i x)^*[AddCommGrpCat.{u + 1}].obj F)
  let φ : F ⟶ ⨁ G' := biproduct.lift fun x ↦ (adj x).unit.app F
  -- `φ` is an isomorphism, as it is one after pulling back to every point
  have hφ : IsIso φ := by
    refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective AddCommGrpCat.{u + 1} i
      (fun y ↦ ⟨y, IsLocalRing.closedPoint _, X.fromSpecResidueField_apply _ _⟩) φ fun x ↦ ?_
    let P := (i x)^*[AddCommGrpCat.{u + 1}]
    have hz (y : X) (hxy : y ≠ x) : IsZero (P.obj (G' y)) := by
      -- `iₓ` factors through the open complement `V` of `y`, over which `G' y` vanishes
      let V : X.Opens := ⟨{y}ᶜ, (hcl y).isOpen_compl⟩
      have hV : Set.range (i x) ⊆ Set.range V.ι := by
        rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι, Set.singleton_subset_iff]
        exact fun h ↦ hxy h.symm
      have h0 := Etale.isZero_upperStar_lowerStar_of_disjoint_range _ V.ι (i y)
        (by rw [Scheme.Opens.range_ι, Scheme.range_fromSpecResidueField]; simp [V])
        ((i y)^*[AddCommGrpCat.{u + 1}].obj F)
      exact (Functor.map_isZero (IsOpenImmersion.lift V.ι _ hV)^*[AddCommGrpCat.{u + 1}]
        h0).of_iso ((Etale.upperStarComp AddCommGrpCat.{u + 1} (IsOpenImmersion.lift V.ι _ hV)
          V.ι _ (IsOpenImmersion.lift_fac _ _ _).symm).app _)
    have hπ : IsIso (P.map (biproduct.π G' x)) := by
      refine ⟨P.map (biproduct.ι G' x), ?_, ?_⟩
      · rw [← P.map_comp, ← P.map_id, ← IsBilimit.total (biproduct.isBilimit G'), P.map_sum,
          Finset.sum_eq_single x (fun y _ hxy ↦ ?_) (by simp)]
        rw [P.map_comp, (hz y hxy).eq_zero_of_tgt (P.map (biproduct.π G' y)), zero_comp]
      · rw [← P.map_comp, biproduct.ι_π_self, P.map_id]
    have hunit : IsIso (P.map ((adj x).unit.app F)) := by
      have : IsIso (P.map ((adj x).unit.app F) ≫ (adj x).counit.app (P.obj F)) := by
        rw [(adj x).left_triangle_components F]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right _ ((adj x).counit.app (P.obj F))
    have : IsIso (P.map φ ≫ P.map (biproduct.π G' x)) := by
      rw [← P.map_comp, biproduct.lift_π]
      exact hunit
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hπ this
  -- `H⁰(X, F) ≅ ∏ₓ H⁰(X, G' x)`
  let e₁ : Sheaf.H F 0 ≃+ Sheaf.H (⨁ G') 0 :=
    { toFun := Sheaf.H.map φ 0
      invFun := Sheaf.H.map (inv φ) 0
      left_inv := fun a ↦ by
        rw [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id, Sheaf.H.map_id_apply]
      right_inv := fun a ↦ by
        rw [← Sheaf.H.map_comp_apply, IsIso.inv_hom_id, Sheaf.H.map_id_apply]
      map_add' := map_add _ }
  let e₂ : Sheaf.H (⨁ G') 0 ≃+ ∀ x, Sheaf.H (G' x) 0 :=
    Abelian.Ext.addEquivBiproduct _ (biproduct.isBilimit G') 0
  -- `H⁰(X, G' x) ≅ H⁰(Spec κ(x), iₓ^* F)`
  let e₃ (x : X) : Sheaf.H (G' x) 0 ≃+ Sheaf.H ((i x)^*[AddCommGrpCat.{u + 1}].obj F) 0 :=
    AddEquiv.ofBijective ((Sheaf.H.map ((adj x).counit.app _) 0).comp
      (Etale.cohomologyMap (i x) _ 0)) (Etale.bijective_edgeMap_of_isFinite (i x) _ 0)
  -- `H⁰(Spec κ(x), iₓ^* F)` is the stalk of `iₓ^* F` at the tautological point
  let e₄ (x : X) : Sheaf.H ((i x)^*[AddCommGrpCat.{u + 1}].obj F) 0 ≃+
      ((Scheme.pointSmallEtale (𝟙 (Spec (.of (X.residueField x))))).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj
        ((i x)^*[AddCommGrpCat.{u + 1}].obj F) :=
    (Sheaf.H.equiv₀ _ Scheme.isTerminalEtalePoint).trans
      (AddEquiv.ofBijective _ (Scheme.bijective_toPresheafFiber_etalePoint (X.residueField x)
        ((i x)^*[AddCommGrpCat.{u + 1}].obj F).obj))
  -- the stalk of `iₓ^* F` at the tautological point is the stalk of `F` at `x̄`
  let r (x : X) : X.residueField x ≃+* AlgebraicClosure (X.residueField x) :=
    RingEquiv.ofBijective (algebraMap _ _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let eΩ (x : X) : Spec (.of (AlgebraicClosure (X.residueField x))) ≅ Spec (X.residueField x) :=
    Scheme.Spec.mapIso (r x).toCommRingCatIso.op
  let e₅ (x : X) : ((Scheme.pointSmallEtale (𝟙 (Spec (.of (X.residueField x))))).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj
        ((i x)^*[AddCommGrpCat.{u + 1}].obj F) ≅
      (Scheme.pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj F :=
    (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} (i x) (𝟙 _)).app F ≪≫
      (GrothendieckTopology.Point.sheafFiberIso
        (Scheme.pointSmallEtaleCongr (Iso.refl _) (i x))).app F ≪≫
      ((GrothendieckTopology.Point.sheafFiberIso
        (Scheme.pointSmallEtaleCongr (eΩ x) (i x))).app F).symm
  exact ⟨e₁.trans (e₂.trans (AddEquiv.piCongrRight fun x ↦
    (e₃ x).trans ((e₄ x).trans (e₅ x).addCommGroupIsoToAddEquiv)))⟩

end AlgebraicGeometry
