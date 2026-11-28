import Langlands.Correspondence.Laumon.FieldMonodromy

/-!
# The Galois group of a field as the fundamental group of its spectrum

Let `K` be a field, `Ω` a separable closure of `K` and `Ω̄ = AlgebraicClosure Ω`. The group
`Gal(Ω/K)` acts on the finite étale fibre functor at `fieldGeometricPoint K Ω : Spec Ω̄ → Spec K`
through `fieldGaloisToAut K Ω`. This module proves that `Gal(Ω/K)`, with its Krull topology and
this action, is a fundamental group of the fibre functor in the sense of Mathlib's
`CategoryTheory.PreGaloisCategory.IsFundamentalGroup`, so that `fieldGaloisToAut K Ω` is a
homeomorphism onto the automorphism group of the fibre functor (Stacks Project, Lemma 58.6.3,
Tag 0BNE).

The fibres are computed through the geometric points with values in `Ω`: composition with
`Spec Ω̄ → Spec Ω` (`fieldFiberLift`) is a bijection from the `K`-morphisms `Spec Ω → P` to the
`K`-morphisms `Spec Ω̄ → P`, for every finite étale `K`-scheme `P`, because the residue fields of
`P` are separable over `K`. It carries the action of `σ` by precomposition with `Spec σ` to the
action of `fieldGaloisToAut K Ω σ`. On the side of `Ω`, weil-conjectures's study of the Galois
point of `Spec K` (`AlgebraicGeometry.Scheme.exists_galoisPoint_fiber_map_eq` and the lemmas
on the points `x_E : Spec Ω → Spec E` of the finite subextensions `E` of `Ω / K`) gives the three
conditions of a fundamental group: stabilizers are open, the action on a connected object is
transitive and only the identity acts trivially.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry PreGaloisCategory

namespace Langlands.Henniart.Laumon

/-- For field extensions `K → Ω → M`, the composite `Spec M → Spec Ω → Spec K` is
`Spec M → Spec K`. -/
lemma specAlgebraMap_comp_specAlgebraMap (K Ω M : Type u) [Field K] [Field Ω] [Field M]
    [Algebra K Ω] [Algebra Ω M] [Algebra K M] [IsScalarTower K Ω M] :
    Scheme.specAlgebraMap Ω M ≫ Scheme.specAlgebraMap K Ω = Scheme.specAlgebraMap K M := by
  rw [Scheme.specAlgebraMap, Scheme.specAlgebraMap, Scheme.specAlgebraMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]

/-- The geometric point `fieldGeometricPoint K Ω` is `Spec Ω̄ → Spec K`. -/
lemma fieldGeometricPoint_eq_specAlgebraMap :
    fieldGeometricPoint K Ω = Scheme.specAlgebraMap K (AlgebraicClosure Ω) :=
  Category.comp_id _

/-- The geometric point `fieldGeometricPoint K Ω` is `Spec Ω̄ → Spec Ω → Spec K`. -/
lemma specAlgebraMap_comp_specAlgebraMap_eq_fieldGeometricPoint :
    Scheme.specAlgebraMap Ω (AlgebraicClosure Ω) ≫ Scheme.specAlgebraMap K Ω =
      fieldGeometricPoint K Ω :=
  (specAlgebraMap_comp_specAlgebraMap K Ω (AlgebraicClosure Ω)).trans
    (fieldGeometricPoint_eq_specAlgebraMap K Ω).symm

variable [IsSepClosure K Ω]

/-- The extension `fieldGaloisLift K Ω σ` of `σ` to `Ω̄` restricts to `σ` on `Ω`. -/
lemma fieldGaloisLift_algebraMap (σ : Gal(Ω/K)) (a : Ω) :
    fieldGaloisLift K Ω σ (algebraMap Ω (AlgebraicClosure Ω) a) =
      algebraMap Ω (AlgebraicClosure Ω) (σ a) := by
  have h : algebraicClosureRestriction K Ω (fieldGaloisLift K Ω σ) = σ :=
    (MulEquiv.ofBijective _ (algebraicClosureRestriction_bijective K Ω)).apply_symm_apply σ
  conv_rhs => rw [← h]
  exact (AlgEquiv.restrictNormal_commutes (fieldGaloisLift K Ω σ) Ω a).symm

/-- `fieldGaloisToAut K Ω σ` acts on a point `t : Spec Ω̄ → P` by precomposition with the
spectrum of the extension of `σ` to `Ω̄`. -/
lemma fieldGaloisToAut_hom_app_left (σ : Gal(Ω/K)) (P : (Spec (.of K)).FiniteEtale)
    (t : (Scheme.FiniteEtale.fiber (fieldGeometricPoint K Ω)).obj P) :
    ((fieldGaloisToAut K Ω σ).asIso.hom.app P t).left =
      Spec.map (CommRingCat.ofHom (fieldGaloisLift K Ω σ : AlgebraicClosure Ω →+*
        AlgebraicClosure Ω)) ≫ t.left :=
  rfl

/-- The action of `Gal(Ω/K)` on the fibres of the finite étale fibre functor at
`fieldGeometricPoint K Ω`, through `fieldGaloisToAut K Ω`. -/
instance fieldGaloisFiberMulAction (P : (Spec (.of K)).FiniteEtale) :
    MulAction Gal(Ω/K) ((Scheme.FiniteEtale.fiber (fieldGeometricPoint K Ω)).obj P) :=
  MulAction.compHom _ (fieldGaloisToAut K Ω)

lemma fieldGalois_smul_def (σ : Gal(Ω/K)) {P : (Spec (.of K)).FiniteEtale}
    (t : (Scheme.FiniteEtale.fiber (fieldGeometricPoint K Ω)).obj P) :
    σ • t = (fieldGaloisToAut K Ω σ).asIso.hom.app P t :=
  rfl

section Points

variable [IsSepClosed Ω]

omit [IsSepClosure K Ω] in
/-- A `K`-point `Spec Ω → P` of a finite étale `K`-scheme gives the `K`-point
`Spec Ω̄ → Spec Ω → P` of the fibre at `fieldGeometricPoint K Ω`. -/
def fieldFiberLift {P : (Spec (.of K)).FiniteEtale}
    (y : (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ω)).fiber.obj P.obj) :
    (Scheme.FiniteEtale.fiber (fieldGeometricPoint K Ω)).obj P :=
  Over.homMk (Scheme.specAlgebraMap Ω (AlgebraicClosure Ω) ≫ y.left) (by
    rw [Category.assoc]
    exact (congrArg (Scheme.specAlgebraMap Ω (AlgebraicClosure Ω) ≫ ·) (Over.w y)).trans
      (specAlgebraMap_comp_specAlgebraMap_eq_fieldGeometricPoint K Ω))

omit [IsSepClosure K Ω] in
@[simp]
lemma fieldFiberLift_left {P : (Spec (.of K)).FiniteEtale}
    (y : (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ω)).fiber.obj P.obj) :
    (fieldFiberLift K Ω y).left = Scheme.specAlgebraMap Ω (AlgebraicClosure Ω) ≫ y.left :=
  rfl

omit [IsSepClosure K Ω] in
/-- `fieldFiberLift` is injective, since `Spec Ω̄ → Spec Ω` is an epimorphism of schemes. -/
lemma fieldFiberLift_injective (P : (Spec (.of K)).FiniteEtale) :
    Function.Injective (fieldFiberLift K Ω (P := P)) := by
  intro y₁ y₂ h
  apply Over.OverMorphism.ext
  exact Scheme.specMap_comp_injective (algebraMap Ω (AlgebraicClosure Ω)) P.obj.left
    (congrArg CommaMorphism.left h)

/-- `fieldFiberLift` is surjective: every `K`-morphism `Spec Ω̄ → P` factors through
`Spec Ω̄ → Spec Ω`, since the residue fields of `P` are separable over `K`. -/
lemma fieldFiberLift_surjective (P : (Spec (.of K)).FiniteEtale) :
    Function.Surjective (fieldFiberLift K Ω (P := P)) := by
  intro t
  have : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have ht : t.left ≫ P.obj.hom = Scheme.specAlgebraMap K (AlgebraicClosure Ω) :=
    (Scheme.FiniteEtale.fiber_left_comp _ t).trans (fieldGeometricPoint_eq_specAlgebraMap K Ω)
  obtain ⟨z, hz⟩ := Scheme.exists_specAlgebraMap_comp_eq (Ks := Ω) P.obj t.left ht
  have hz' : z ≫ P.obj.hom = Scheme.specAlgebraMap K Ω := by
    refine Scheme.specMap_comp_injective (algebraMap Ω (AlgebraicClosure Ω)) _ ?_
    refine ((Category.assoc _ _ _).symm.trans ?_).trans
      (specAlgebraMap_comp_specAlgebraMap K Ω (AlgebraicClosure Ω)).symm
    exact (congrArg (· ≫ P.obj.hom) hz).trans ht
  exact ⟨Over.homMk z hz', Scheme.FiniteEtale.fiber_ext _ hz⟩

/-- `fieldFiberLift` carries precomposition with `Spec σ` to the action of
`fieldGaloisToAut K Ω σ`. -/
lemma fieldGaloisToAut_fieldFiberLift (σ : Gal(Ω/K)) {P : (Spec (.of K)).FiniteEtale}
    (y : (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ω)).fiber.obj P.obj) :
    (fieldGaloisToAut K Ω σ).asIso.hom.app P (fieldFiberLift K Ω y) =
      fieldFiberLift K Ω (Scheme.galoisOverHom σ ≫ y) := by
  apply Scheme.FiniteEtale.fiber_ext
  change Spec.map (CommRingCat.ofHom (fieldGaloisLift K Ω σ : AlgebraicClosure Ω →+*
      AlgebraicClosure Ω)) ≫ Scheme.specAlgebraMap Ω (AlgebraicClosure Ω) ≫ y.left =
    Scheme.specAlgebraMap Ω (AlgebraicClosure Ω) ≫ Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
      y.left
  have h : Spec.map (CommRingCat.ofHom (fieldGaloisLift K Ω σ : AlgebraicClosure Ω →+*
      AlgebraicClosure Ω)) ≫ Scheme.specAlgebraMap Ω (AlgebraicClosure Ω) =
      Scheme.specAlgebraMap Ω (AlgebraicClosure Ω) ≫
        Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) := by
    rw [Scheme.specAlgebraMap, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact fieldGaloisLift_algebraMap K Ω σ a
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ y.left) h)).trans
    (Category.assoc _ _ _)

omit [IsSepClosure K Ω] in
/-- `fieldFiberLift` is natural in the finite étale `K`-scheme. -/
lemma fiber_map_fieldFiberLift {P Q : (Spec (.of K)).FiniteEtale} (f : P ⟶ Q)
    (y : (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ω)).fiber.obj P.obj) :
    (Scheme.FiniteEtale.fiber (fieldGeometricPoint K Ω)).map f (fieldFiberLift K Ω y) =
      fieldFiberLift K Ω
        ((Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ω)).fiber.map f.hom y) := by
  apply Scheme.FiniteEtale.fiber_ext
  exact Category.assoc _ _ _

/-- The stabilizer of a `K`-point `Spec Ω → X` of an étale `K`-scheme contains the fixing
subgroup of a finite subextension of `Ω / K`: the point factors through the canonical point
`Spec Ω → Spec E` of a finite subextension `E`. -/
lemma exists_fixingSubgroup_le_stabilizer {X : (Spec (.of K)).Etale}
    (y : (Scheme.pointSmallEtale (Scheme.specAlgebraMap K Ω)).fiber.obj X) :
    ∃ (E : IntermediateField K Ω), FiniteDimensional K E ∧
      ∀ σ ∈ E.fixingSubgroup, Scheme.galoisOverHom σ ≫ y = y := by
  have : Algebra.IsSeparable K Ω := IsSepClosure.separable
  obtain ⟨E, hE, g, hg⟩ := Scheme.exists_galoisPoint_fiber_map_eq X (ULift.up y)
  refine ⟨E, hE, fun σ hσ => ?_⟩
  have h1 := Scheme.galoisPointAct_fiber_map_galoisPointFiberSpec g hσ
  rw [hg] at h1
  exact congrArg ULift.down h1

/-- The finite étale `K`-scheme `Spec E` of a finite subextension `E` of `Ω / K`. -/
def finiteEtaleSpecOfIntermediateField [Algebra.IsSeparable K Ω] (E : IntermediateField K Ω)
    [FiniteDimensional K E] : (Spec (.of K)).FiniteEtale :=
  ⟨Scheme.galoisEtaleSpec K Ω E, by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K E)))
    exact (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)⟩

end Points

/-- **`Gal(Ω/K)` is a fundamental group of the finite étale fibre functor of `Spec K`.** Its
action through `fieldGaloisToAut K Ω` on the fibres at `fieldGeometricPoint K Ω` is natural and
continuous, transitive on the fibres of connected (in particular Galois) objects, and only the
identity acts trivially on all fibres. -/
instance fieldGalois_isFundamentalGroup :
    IsFundamentalGroup (Scheme.FiniteEtale.fiber (fieldGeometricPoint K Ω)) Gal(Ω/K) := by
  have := IsSepClosure.sep_closed K (K := Ω)
  have : Algebra.IsSeparable K Ω := IsSepClosure.separable
  set F := Scheme.FiniteEtale.fiber (fieldGeometricPoint K Ω)
  exact
  { naturality := fun σ X Y f x => (mulAction_naturality F (fieldGaloisToAut K Ω σ) f x).symm
    transitive_of_isGalois := fun X _ => by
      obtain ⟨t₀⟩ := nonempty_fiber_of_isConnected F X
      obtain ⟨y₀, rfl⟩ := fieldFiberLift_surjective K Ω X t₀
      obtain ⟨E, hE, g, hg⟩ := Scheme.exists_galoisPoint_fiber_map_eq X.obj (ULift.up y₀)
      let PE := finiteEtaleSpecOfIntermediateField K Ω E
      let g' : PE ⟶ X := ObjectProperty.homMk g
      let xE := (Scheme.galoisPointFiberSpec K Ω E).down
      have : Nonempty (F.obj PE) := ⟨fieldFiberLift K Ω (P := PE) xE⟩
      have hsurj := surjective_of_nonempty_fiber_of_isConnected F g'
      have key : ∀ t : F.obj X, ∃ σ : Gal(Ω/K), σ • fieldFiberLift K Ω y₀ = t := by
        intro t
        obtain ⟨u, rfl⟩ := hsurj t
        obtain ⟨v, rfl⟩ := fieldFiberLift_surjective K Ω PE u
        obtain ⟨σ, hσ⟩ := Scheme.exists_galoisPointAct_galoisPointFiberSpec_eq (E := E)
          (ULift.up v)
        refine ⟨σ, ?_⟩
        have hv : Scheme.galoisOverHom σ ≫ xE = v := congrArg ULift.down hσ
        have hy₀ : xE ≫ (Scheme.Etale.forget _).map g = y₀ := congrArg ULift.down hg
        change (fieldGaloisToAut K Ω σ).asIso.hom.app X (fieldFiberLift K Ω y₀) =
          F.map g' (fieldFiberLift K Ω v)
        rw [fieldGaloisToAut_fieldFiberLift, fiber_map_fieldFiberLift, ← hv, ← hy₀]
        congr 1
      refine ⟨fun t₁ t₂ => ?_⟩
      obtain ⟨σ₁, rfl⟩ := key t₁
      obtain ⟨σ₂, rfl⟩ := key t₂
      exact ⟨σ₂ * σ₁⁻¹, by rw [mul_smul, inv_smul_smul]⟩
    continuous_smul := fun X => by
      have := obj_discreteTopology F X
      refine (continuousSMul_iff_stabilizer_isOpen).2 fun t => ?_
      obtain ⟨y, rfl⟩ := fieldFiberLift_surjective K Ω X t
      obtain ⟨E, hE, hσ⟩ := exists_fixingSubgroup_le_stabilizer K Ω y
      refine Subgroup.isOpen_mono (fun σ hσE => ?_) E.fixingSubgroup_isOpen
      rw [MulAction.mem_stabilizer_iff]
      change (fieldGaloisToAut K Ω σ).asIso.hom.app X (fieldFiberLift K Ω y) = _
      rw [fieldGaloisToAut_fieldFiberLift, hσ σ hσE]
    non_trivial' := fun σ h => by
      ext a
      rw [AlgEquiv.one_apply]
      let E := IntermediateField.adjoin K {a}
      have : FiniteDimensional K E :=
        IntermediateField.adjoin.finiteDimensional (Algebra.IsSeparable.isIntegral K a)
      let PE := finiteEtaleSpecOfIntermediateField K Ω E
      let xE := (Scheme.galoisPointFiberSpec K Ω E).down
      have h1 := h PE (fieldFiberLift K Ω (P := PE) xE)
      change (fieldGaloisToAut K Ω σ).asIso.hom.app PE _ = _ at h1
      have h2 := fieldFiberLift_injective K Ω PE
        ((fieldGaloisToAut_fieldFiberLift K Ω σ (P := PE) xE).symm.trans h1)
      have h3 : (Scheme.galoisPointAct K Ω σ).asHom.app _ (Scheme.galoisPointFiberSpec K Ω E) =
          Scheme.galoisPointFiberSpec K Ω E := ULift.ext h2
      have h4 := (Scheme.galoisPointAct_galoisPointFiberSpec_eq_iff σ).1 h3
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 h4 a
        (IntermediateField.mem_adjoin_simple_self K a) }

/-- `fieldGaloisToAut K Ω` is Mathlib's `CategoryTheory.PreGaloisCategory.toAut` for the action
`fieldGaloisFiberMulAction`. -/
lemma toAut_eq_fieldGaloisToAut :
    toAut (Scheme.FiniteEtale.fiber (fieldGeometricPoint K Ω)) Gal(Ω/K) =
      fieldGaloisToAut K Ω := by
  ext σ P t
  rfl

/-- **The Galois group of a field is the fundamental group of its spectrum.** The action
`fieldGaloisToAut K Ω` is a homeomorphism from `Gal(Ω/K)` with its Krull topology onto the
automorphism group of the finite étale fibre functor at `fieldGeometricPoint K Ω` (Stacks
Project, Lemma 58.6.3). -/
theorem fieldGaloisToAut_isHomeomorph : IsHomeomorph (fieldGaloisToAut K Ω) := by
  rw [← toAut_eq_fieldGaloisToAut]
  exact toAut_isHomeomorph _ _

/-- `fieldGaloisToAut K Ω` as an isomorphism of topological groups. -/
def fieldGaloisContinuousMulEquiv :
    Gal(Ω/K) ≃ₜ* Aut (Scheme.FiniteEtale.fiber (fieldGeometricPoint K Ω)) where
  toMulEquiv := MulEquiv.ofBijective (fieldGaloisToAut K Ω)
    (fieldGaloisToAut_isHomeomorph K Ω).bijective
  continuous_toFun := (fieldGaloisToAut_isHomeomorph K Ω).continuous
  continuous_invFun := (fieldGaloisToAut_isHomeomorph K Ω).homeomorph.symm.continuous

@[simp]
lemma fieldGaloisContinuousMulEquiv_apply (σ : Gal(Ω/K)) :
    fieldGaloisContinuousMulEquiv K Ω σ = fieldGaloisToAut K Ω σ :=
  rfl

end Langlands.Henniart.Laumon
