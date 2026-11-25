/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Sites.Point.DiscreteModule
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.Mathlib.FieldTheory.KrullTopology
public import WeilConjectures.PointCount

/-!
# Étale sheaves on the spectrum of a field and discrete Galois modules

Let `K` be a field and `Ω` a separable closure of `K`, with absolute Galois group
`G = Gal(Ω/K)` carrying the Krull topology. The geometric point `Spec Ω ⟶ Spec K` is a point of
the small étale site of `Spec K`, and `G` acts on its fibre functor
`X ↦ Hom_K(Spec Ω, X)` by precomposition with `Spec σ`.

We show that this is a Galois point in the sense of
`CategoryTheory.GrothendieckTopology.Point.IsGaloisPoint`: hence the geometric fibre functor is
an equivalence between abelian étale sheaves on `Spec K` and discrete `G`-modules, and
`Hⁿ(Spec K_ét, F) ≃ Hⁿ(G, F_Ω)`.

## Main definitions and statements

- `AlgebraicGeometry.Scheme.galoisPoint`: the geometric point of `Spec K` given by `Ω`.
- `AlgebraicGeometry.Scheme.galoisPointAct`: the action of `Gal(Ω/K)` on its fibre functor.
- `AlgebraicGeometry.Scheme.isGaloisPoint_galoisPoint`: this is a Galois point.
- `AlgebraicGeometry.Scheme.etaleSheafEquivDiscreteModule`: the equivalence of categories
  between abelian étale sheaves on `Spec K` and discrete `Gal(Ω/K)`-modules.
- `AlgebraicGeometry.Scheme.sheafHAddEquivGaloisH`: `Hⁿ(Spec K_ét, F) ≃ Hⁿ(Gal(Ω/K), F_Ω)`.

## Implementation details

The proof goes through the étale `K`-schemes `Spec E` for finite subextensions `E` of `Ω/K`
with their canonical geometric point `x_E` (`AlgebraicGeometry.Scheme.galoisPointFiberSpec`):

* the fibre at `Spec E` is a single `G`-orbit, as every `K`-embedding `E → Ω` extends to an
  automorphism of `Ω`, and the stabiliser of `x_E` is the open subgroup `Gal(Ω/E)`;
* every element of the fibre of an étale `K`-scheme `X` comes from some `(Spec E, x_E)`, as the
  residue fields of `X` are finite over `K`.

We use `ℤ`-coefficients: an étale sheaf of modules over a finite ring `A` is in particular an
abelian étale sheaf, and the statements needed about such sheaves concern their underlying
abelian groups.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (K : Type u) [Field K] (Ω : Type u) [Field Ω] [Algebra K Ω]

/-- The geometric point `Spec Ω ⟶ Spec K` given by a field extension `Ω` of `K`. -/
noncomputable def specAlgebraMap : Spec (.of Ω) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K Ω))

variable {K Ω} in
/-- The automorphism `Spec σ` of the geometric point `Spec Ω ⟶ Spec K`, for `σ ∈ Gal(Ω/K)`. -/
noncomputable def galoisOverHom (σ : Gal(Ω/K)) :
    Over.mk (specAlgebraMap K Ω) ⟶ Over.mk (specAlgebraMap K Ω) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) (by
    dsimp only [specAlgebraMap, Over.mk_hom]
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact σ.commutes x)

@[simp]
lemma galoisOverHom_left (σ : Gal(Ω/K)) :
    (galoisOverHom σ).left = Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) :=
  rfl

lemma galoisOverHom_one : galoisOverHom (1 : Gal(Ω/K)) = 𝟙 _ := by
  ext : 1
  exact Spec.map_id _

lemma galoisOverHom_mul (σ τ : Gal(Ω/K)) :
    galoisOverHom (σ * τ) = galoisOverHom σ ≫ galoisOverHom τ := by
  ext : 1
  simp only [galoisOverHom_left, Over.comp_left, ← Spec.map_comp]
  rfl

variable [IsSepClosed Ω]

/-- The geometric point of the small étale site of `Spec K` given by a separably closed
extension `Ω` of `K`, with fibre functor `X ↦ Hom_K(Spec Ω, X)` valued in `Type (u + 1)`. -/
noncomputable def galoisPoint : (Spec (.of K)).smallEtaleTopology.Point.{u + 1} :=
  (pointSmallEtale (specAlgebraMap K Ω)).ulift.{u + 1}

lemma galoisPoint_fiber_obj (X : (Spec (.of K)).Etale) :
    (galoisPoint K Ω).fiber.obj X =
      ULift.{u + 1} (Over.mk (specAlgebraMap K Ω) ⟶ (Etale.forget _).obj X) :=
  rfl


@[simp]
lemma galoisPoint_fiber_map_down {X Y : (Spec (.of K)).Etale} (f : X ⟶ Y)
    (x : (galoisPoint K Ω).fiber.obj X) :
    ((galoisPoint K Ω).fiber.map f x).down = x.down ≫ (Etale.forget _).map f :=
  rfl

/-- The action of `σ ∈ Gal(Ω/K)` on the fibre functor of `galoisPoint K Ω`, by precomposition
with `Spec σ`. -/
noncomputable def galoisPointActHom (σ : Gal(Ω/K)) :
    (galoisPoint K Ω).fiber ⟶ (galoisPoint K Ω).fiber where
  app X := TypeCat.ofHom fun x ↦ ULift.up (galoisOverHom σ ≫ x.down)
  naturality X Y f := by
    ext x
    exact ULift.ext (Category.assoc _ _ _).symm

@[simp]
lemma galoisPointActHom_app_down (σ : Gal(Ω/K)) {X : (Spec (.of K)).Etale}
    (x : (galoisPoint K Ω).fiber.obj X) :
    ((galoisPointActHom K Ω σ).app X x).down = galoisOverHom σ ≫ x.down :=
  rfl

/-- The action of `Gal(Ω/K)` on the fibre functor of `galoisPoint K Ω`. -/
noncomputable def galoisPointAct : Gal(Ω/K) →* End (galoisPoint K Ω).fiber where
  toFun σ := .of (galoisPointActHom K Ω σ)
  map_one' := by
    apply End.ext
    refine NatTrans.ext (funext fun X ↦ ?_)
    ext x
    refine ULift.ext ?_
    change galoisOverHom 1 ≫ x.down = x.down
    rw [galoisOverHom_one, Category.id_comp]
  map_mul' σ τ := by
    apply End.ext
    refine NatTrans.ext (funext fun X ↦ ?_)
    ext x
    refine ULift.ext ?_
    change galoisOverHom (σ * τ) ≫ x.down = galoisOverHom σ ≫ galoisOverHom τ ≫ x.down
    rw [galoisOverHom_mul, Category.assoc]

@[simp]
lemma galoisPointAct_app_down (σ : Gal(Ω/K)) {X : (Spec (.of K)).Etale}
    (x : (galoisPoint K Ω).fiber.obj X) :
    ((galoisPointAct K Ω σ).asHom.app X x).down = galoisOverHom σ ≫ x.down :=
  rfl

/-- The fibre functor of `galoisPoint K Ω` reflects isomorphisms of abelian étale sheaves. -/
lemma isIso_of_isIso_galoisPoint_sheafFiber_map
    {F F' : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}} (f : F ⟶ F')
    (hf : IsIso ((galoisPoint K Ω).sheafFiber.map f)) : IsIso f := by
  have h := isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ
    (Spec (.of K)) (ι := PUnit.{u + 1}) (Ω := fun _ ↦ Ω) (fun _ ↦ specAlgebraMap K Ω) (by
      refine Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨PUnit.unit, default, ?_⟩
      exact Subsingleton.elim _ _)
  refine ((h.jointlyReflectIsomorphisms AddCommGrpCat.{u + 1}).isIso_iff f).2 ?_
  rintro ⟨-, ⟨⟨⟩⟩⟩
  exact hf

variable [Algebra.IsSeparable K Ω]

section finite

variable (E : IntermediateField K Ω) [FiniteDimensional K E]

instance etale_specAlgebraMap_intermediateField : Etale (specAlgebraMap K E) :=
  have : Algebra.Etale K E := .of_finite_of_isSeparable
  HasRingHomProperty.Spec_iff.2 (RingHom.etale_algebraMap.2 this)

/-- The étale `K`-scheme `Spec E` for a finite subextension `E` of `Ω / K`. -/
noncomputable abbrev galoisEtaleSpec : (Spec (.of K)).Etale :=
  Etale.mk (specAlgebraMap K E)

/-- The canonical geometric point `x_E : Spec Ω ⟶ Spec E` of `Spec E`, as an element of the
fibre of `galoisPoint K Ω`. -/
noncomputable def galoisPointFiberSpec : (galoisPoint K Ω).fiber.obj (galoisEtaleSpec K Ω E) :=
  ULift.up (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap E Ω))) (by
    dsimp only [specAlgebraMap, Over.mk_hom, Etale.forget_mk]
    rw [← Spec.map_comp]
    rfl))

@[simp]
lemma galoisPointFiberSpec_down_left :
    (galoisPointFiberSpec K Ω E).down.left = Spec.map (CommRingCat.ofHom (algebraMap E Ω)) :=
  rfl

variable {K Ω E} in
/-- The stabiliser of `x_E` is the fixing subgroup `Gal(Ω/E)` of `E`. -/
lemma galoisPointAct_galoisPointFiberSpec_eq_iff (σ : Gal(Ω/K)) :
    (galoisPointAct K Ω σ).asHom.app _ (galoisPointFiberSpec K Ω E) = galoisPointFiberSpec K Ω E ↔
      σ ∈ E.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have h' : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap E Ω)) =
        Spec.map (CommRingCat.ofHom (algebraMap E Ω)) := congrArg (fun y ↦ y.down.left) h
    rw [← Spec.map_comp, Spec.map_inj] at h'
    exact congr($(h').hom ⟨x, hx⟩)
  · intro h
    refine ULift.ext (Over.OverMorphism.ext ?_)
    change Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap E Ω)) =
        Spec.map (CommRingCat.ofHom (algebraMap E Ω))
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact h x.1 x.2

variable {K Ω E} in
/-- The fibre of `galoisPoint K Ω` at `Spec E` is the orbit of `x_E`: every `K`-embedding
`E → Ω` extends to an automorphism of `Ω`. -/
lemma exists_galoisPointAct_galoisPointFiberSpec_eq
    (y : (galoisPoint K Ω).fiber.obj (galoisEtaleSpec K Ω E)) :
    ∃ σ : Gal(Ω/K), (galoisPointAct K Ω σ).asHom.app _ (galoisPointFiberSpec K Ω E) = y := by
  have : IsSepClosure K Ω := ⟨‹_›, ‹_›⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ, Spec.map ψ = y.down.left := ⟨_, Spec.map_preimage y.down.left⟩
  have hw : CommRingCat.ofHom (algebraMap K E) ≫ ψ = CommRingCat.ofHom (algebraMap K Ω) := by
    rw [← Spec.map_inj, Spec.map_comp, hψ]
    exact Over.w y.down
  let φ : E →ₐ[K] Ω :=
    { ψ.hom with commutes' r := congr($(hw).hom r) }
  let τ := φ.liftNormal Ω
  let σ : Gal(Ω/K) := AlgEquiv.ofBijective τ (Algebra.IsAlgebraic.algHom_bijective τ)
  refine ⟨σ, ULift.ext (Over.OverMorphism.ext ?_)⟩
  change Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap E Ω)) = y.down.left
  rw [← Spec.map_comp, ← hψ]
  congr 1
  ext x
  exact (φ.liftNormal_commutes Ω x).trans rfl

variable {K} in
/-- The residue fields of an étale `K`-scheme are finite over `K`. -/
lemma finite_residueFieldAlgebraMap_of_etale {Y : Scheme.{u}} (f : Y ⟶ Spec (.of K)) [Etale f]
    (p : Y) : (f.residueFieldAlgebraMap p).Finite := by
  have hq : IsClosed {f.base p} := by
    rw [show ({f.base p} : Set (Spec (.of K))) = Set.univ from
      Set.eq_univ_of_forall fun y ↦ Subsingleton.elim _ _]
    exact isClosed_univ
  have h₁ : (Hom.residueFieldAlgebraMap (𝟙 (Spec (.of K))) (f.base p)).Finite :=
    Hom.finite_residueField_of_isClosed (𝟙 (Spec (.of K))) _ hq
  have h₂ := f.finite_residueFieldMap p
  have h := Hom.residueFieldAlgebraMap_comp f (𝟙 (Spec (.of K))) p
  rw [Category.comp_id] at h
  rw [h]
  exact h₂.comp h₁

variable {K Ω} in
/-- Every element of the fibre of `galoisPoint K Ω` at an étale `K`-scheme `X` is the image of
`x_E` under a morphism `Spec E ⟶ X`, for some finite subextension `E` of `Ω / K`: namely the
image of the residue field at the corresponding point of `X`. -/
lemma exists_galoisPoint_fiber_map_eq (X : (Spec (.of K)).Etale)
    (x : (galoisPoint K Ω).fiber.obj X) :
    ∃ (E : IntermediateField K Ω) (_ : FiniteDimensional K E) (g : galoisEtaleSpec K Ω E ⟶ X),
      (galoisPoint K Ω).fiber.map g (galoisPointFiberSpec K Ω E) = x := by
  obtain ⟨⟨p, φ⟩, hφ⟩ := (SpecToEquivOfField Ω X.left).symm.surjective x.down.left
  change Spec.map φ ≫ X.left.fromSpecResidueField p = x.down.left at hφ
  have ha : Spec.map (CommRingCat.ofHom (X.hom.residueFieldAlgebraMap p)) =
      X.left.fromSpecResidueField p ≫ X.hom :=
    X.hom.specMap_residueFieldAlgebraMap p
  have hw : CommRingCat.ofHom (X.hom.residueFieldAlgebraMap p) ≫ φ =
      CommRingCat.ofHom (algebraMap K Ω) := by
    rw [← Spec.map_inj, Spec.map_comp, ha, ← Category.assoc, hφ]
    exact Over.w x.down
  let : Algebra K (X.left.residueField p) := (X.hom.residueFieldAlgebraMap p).toAlgebra
  have : Module.Finite K (X.left.residueField p) := finite_residueFieldAlgebraMap_of_etale X.hom p
  let φ' : X.left.residueField p →ₐ[K] Ω := { φ.hom with commutes' r := congr($(hw).hom r) }
  let ψ : X.left.residueField p →ₐ[K] φ'.fieldRange :=
    φ'.codRestrict φ'.fieldRange.toSubalgebra fun c ↦ ⟨c, rfl⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, c, rfl⟩
    exact ⟨c, rfl⟩
  have : FiniteDimensional K φ'.fieldRange := Module.Finite.of_surjective ψ.toLinearMap hψ
  refine ⟨φ'.fieldRange, this, MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.left.fromSpecResidueField p) ?_ trivial, ?_⟩
  · change _ ≫ X.hom = specAlgebraMap K φ'.fieldRange
    rw [Category.assoc, ← ha, ← Spec.map_comp]
    congr 1
    ext r
    exact congrArg Subtype.val (ψ.commutes r)
  · refine ULift.ext (Over.OverMorphism.ext ?_)
    change Spec.map (CommRingCat.ofHom (algebraMap φ'.fieldRange Ω)) ≫
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.left.fromSpecResidueField p = x.down.left
    rw [← hφ, ← Category.assoc, ← Spec.map_comp]
    congr 2

end finite

section galois

open GrothendieckTopology.Point

variable {K Ω} in
/-- `Gal(Ω/E)` fixes the image of `x_E` under a morphism `g : Spec E ⟶ X`. -/
lemma galoisPointAct_fiber_map_galoisPointFiberSpec {E : IntermediateField K Ω}
    [FiniteDimensional K E] {X : (Spec (.of K)).Etale} (g : galoisEtaleSpec K Ω E ⟶ X)
    {σ : Gal(Ω/K)} (hσ : σ ∈ E.fixingSubgroup) :
    (galoisPointAct K Ω σ).asHom.app X
        ((galoisPoint K Ω).fiber.map g (galoisPointFiberSpec K Ω E)) =
      (galoisPoint K Ω).fiber.map g (galoisPointFiberSpec K Ω E) := by
  rw [NatTrans.naturality_apply, (galoisPointAct_galoisPointFiberSpec_eq_iff σ).2 hσ]

/-- The fibres of abelian étale sheaves at `galoisPoint K Ω` are discrete `Gal(Ω/K)`-modules. -/
lemma isDiscreteModule_galoisPoint
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Action.IsDiscreteModule.{u + 1}
      (((galoisPoint K Ω).sheafFiberAction (galoisPointAct K Ω)).obj F) := by
  intro v
  obtain ⟨X, x, t, rfl⟩ := (galoisPoint K Ω).toPresheafFiber_jointly_surjective v
  obtain ⟨E, _, g, rfl⟩ := exists_galoisPoint_fiber_map_eq X x
  refine Subgroup.isOpen_mono (fun σ hσ ↦ ?_) E.fixingSubgroup_isOpen
  rw [Action.mem_stabilizer]
  change ((galoisPoint K Ω).presheafFiberAct (galoisPointAct K Ω) F.obj σ).hom _ = _
  rw [toPresheafFiber_presheafFiberAct_apply, galoisPointAct_fiber_map_galoisPointFiberSpec g hσ]

/-- The counit `(Φ.equivariantSheaf M)_Φ ⟶ M` at `galoisPoint K Ω` is an isomorphism for
every discrete `Gal(Ω/K)`-module `M`. -/
lemma isIso_galoisPoint_fromEquivariantSheaf (M : DiscreteModule.{u + 1} Gal(Ω/K)) :
    IsIso ((galoisPoint K Ω).fromEquivariantSheaf (galoisPointAct K Ω) M.obj) := by
  suffices IsIso ((galoisPoint K Ω).fromEquivariantSheaf (galoisPointAct K Ω) M.obj).hom from
    inferInstance
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    obtain ⟨X, x, f, rfl⟩ := (galoisPoint K Ω).toPresheafFiber_jointly_surjective v
    obtain ⟨E, _, g, rfl⟩ := exists_galoisPoint_fiber_map_eq X x
    rw [← toPresheafFiber_w_apply] at hv ⊢
    set f' := ((galoisPoint K Ω).equivariantSheaf (galoisPointAct K Ω) M.obj).obj.map g.op f
    have h₀ : f'.1 (galoisPointFiberSpec K Ω E) = 0 := by
      rw [← hv]
      exact (toPresheafFiber_fromEquivariantSheaf_hom_apply _ _ _ _ _ _).symm
    have hf' : f' = 0 := by
      refine Subtype.ext (funext fun y ↦ ?_)
      obtain ⟨σ, rfl⟩ := exists_galoisPointAct_galoisPointFiberSpec_eq y
      rw [f'.2 σ, h₀, map_zero]
      rfl
    rw [hf', map_zero]
  · intro m
    have hU : (M.obj.stabilizer m : Set Gal(Ω/K)) ∈ nhds 1 :=
      (M.isOpen_stabilizer m).mem_nhds (one_mem _)
    obtain ⟨E, _, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 hU
    choose τ hτ using fun y ↦ exists_galoisPointAct_galoisPointFiberSpec_eq (E := E) y
    have key (σ : Gal(Ω/K)) (y : (galoisPoint K Ω).fiber.obj (galoisEtaleSpec K Ω E))
        (hσ : (galoisPointAct K Ω σ).asHom.app _ (galoisPointFiberSpec K Ω E) = y) :
        (M.obj.ρ σ).asHom.hom m = (M.obj.ρ (τ y)).asHom.hom m := by
      have h : (τ y)⁻¹ * σ ∈ E.fixingSubgroup := by
        set t := τ y
        have ht : (galoisPointAct K Ω t).asHom.app _ (galoisPointFiberSpec K Ω E) = y := hτ y
        rw [← galoisPointAct_galoisPointFiberSpec_eq_iff, act_mul_app, hσ, ← ht,
          ← act_mul_app, inv_mul_cancel, act_one_app]
      have h' := Action.mem_stabilizer.1 (hEU h)
      rw [Action.ρ_mul_apply] at h'
      conv_rhs => rw [← h']
      rw [← Action.ρ_mul_apply, ← Action.ρ_mul_apply, mul_inv_cancel, one_mul]
    let f : ((galoisPoint K Ω).equivariantPresheaf (galoisPointAct K Ω) M.obj).obj
        (op (galoisEtaleSpec K Ω E)) :=
      ⟨fun y ↦ (M.obj.ρ (τ y)).asHom.hom m, fun σ y ↦ by
        dsimp only
        rw [← key (σ * τ y) _ (by rw [act_mul_app, hτ y]), Action.ρ_mul_apply]⟩
    refine ⟨(galoisPoint K Ω).toPresheafFiber _ (galoisPointFiberSpec K Ω E)
      ((galoisPoint K Ω).equivariantPresheaf (galoisPointAct K Ω) M.obj) f, ?_⟩
    rw [toPresheafFiber_fromEquivariantSheaf_hom_apply]
    change (M.obj.ρ (τ _)).asHom.hom m = m
    rw [← key 1 _ (act_one_app _ _ _ _), Action.ρ_one_apply]

/-- **The geometric point of the spectrum of a field is a Galois point.** -/
theorem isGaloisPoint_galoisPoint :
    (galoisPoint K Ω).IsGaloisPoint.{u + 1} (galoisPointAct K Ω) where
  isDiscreteModule := isDiscreteModule_galoisPoint K Ω
  isIso_fromEquivariantSheaf := isIso_galoisPoint_fromEquivariantSheaf K Ω
  isIso_of_isIso_sheafFiber_map := isIso_of_isIso_galoisPoint_sheafFiber_map K Ω

end galois

section main

/-- **Étale sheaves on a field and discrete Galois modules.** Let `K` be a field with separable
closure `Ω` and absolute Galois group `G = Gal(Ω/K)`. The geometric fibre functor at
`Spec Ω ⟶ Spec K`, with the action of `G` by transport of structure, is an equivalence between
abelian étale sheaves on `Spec K` and discrete `G`-modules. -/
noncomputable def etaleSheafEquivDiscreteModule :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} ≌
      DiscreteModule.{u + 1} Gal(Ω/K) :=
  (isGaloisPoint_galoisPoint K Ω).equivalence

lemma etaleSheafEquivDiscreteModule_functor_obj_obj
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((etaleSheafEquivDiscreteModule K Ω).functor.obj F).obj =
      ((galoisPoint K Ω).sheafFiberAction (galoisPointAct K Ω)).obj F :=
  rfl


/-- **Étale cohomology of a field is Galois cohomology**:
`Hⁿ(Spec K_ét, F) ≃ Hⁿ(Gal(Ω/K), F_Ω)` for every abelian étale sheaf `F` on `Spec K`. -/
noncomputable def sheafHAddEquivGaloisH
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    (Sheaf.H F n : Type (u + 1)) ≃+
      DiscreteModule.H Gal(Ω/K) ((etaleSheafEquivDiscreteModule K Ω).functor.obj F) n :=
  (isGaloisPoint_galoisPoint K Ω).sheafHAddEquiv F n

/-- Global sections of an abelian étale sheaf on `Spec K` are the Galois invariants of its
geometric fibre. -/
noncomputable def sheafHZeroAddEquivInvariants
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Sheaf.H F 0 : Type (u + 1)) ≃+
      (DiscreteModule.invariants.{u + 1} Gal(Ω/K)).obj
        ((etaleSheafEquivDiscreteModule K Ω).functor.obj F) :=
  (isGaloisPoint_galoisPoint K Ω).sheafHZeroAddEquiv F

/-- The étale cohomology of the constant sheaf with value `A` on `Spec K` is the Galois
cohomology of the trivial module `A`. -/
noncomputable def sheafHConstantSheafAddEquivGaloisH (A : AddCommGrpCat.{u + 1}) (n : ℕ) :
    (Sheaf.H ((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) n :
      Type (u + 1)) ≃+
      DiscreteModule.H Gal(Ω/K) (DiscreteModule.trivial.{u + 1} Gal(Ω/K) A) n :=
  (isGaloisPoint_galoisPoint K Ω).sheafHConstantSheafAddEquiv A n

end main

end AlgebraicGeometry.Scheme
