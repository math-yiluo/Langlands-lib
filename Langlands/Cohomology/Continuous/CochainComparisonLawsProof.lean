import Langlands.Cohomology.Continuous.CochainComparisonLawsStatement

universe u
open CategoryTheory
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Evaluation detects equality even without a discreteness assumption. -/
theorem nestedEval_injective (A : TopRep.{u} k G) (n : ℕ) :
    Function.Injective (nestedEval A n) := by
  induction n with
  | zero =>
    intro a b h
    exact congrFun h Fin.elim0
  | succ n ih =>
    intro a b h
    apply ContinuousMap.ext
    intro g
    apply ih
    funext x
    exact congrFun h (Fin.cons g x)

/-- A function of finitely many discrete variables can be nested continuously. -/
def nestedLift [DiscreteTopology G] (A : TopRep.{u} k G) :
    (n : ℕ) → ((Fin n → G) → A) → TopRep.resolutionX A n
  | 0, f => f Fin.elim0
  | n + 1, f => ⟨fun g => nestedLift A n (fun x => f (Fin.cons g x)), continuous_of_discreteTopology⟩

@[simp]
theorem nestedEval_lift [DiscreteTopology G] (A : TopRep.{u} k G) (n : ℕ)
    (f : (Fin n → G) → A) : nestedEval A n (nestedLift A n f) = f := by
  induction n with
  | zero =>
    funext x
    exact congrArg f (Subsingleton.elim _ _)
  | succ n ih =>
    funext x
    change nestedEval A n (nestedLift A n _) (Fin.tail x) = f x
    rw [ih]
    simp

theorem homogeneousTermMap_bijective [DiscreteTopology G] (A : TopRep.{u} k G) (n : ℕ) :
    Function.Bijective (homogeneousTermMap A n) := by
  have hEval : Function.Bijective
      (fun f : (TopRep.homogeneousCochains A).X n =>
        (⟨nestedEval A (n + 1) f.1, nestedEval_invariant A (n + 1) f⟩ :
          covariantFunctions A (n + 1))) := by
    constructor
    · intro a b h
      apply Subtype.ext
      exact nestedEval_injective A (n + 1) (congrArg Subtype.val h)
    · intro f
      have hi : nestedLift A (n + 1) f.1 ∈ (TopRep.resolutionX A (n + 1)).ρ.invariants := by
        intro g
        apply nestedEval_injective A (n + 1)
        funext x
        rw [nestedEval_action, nestedEval_lift]
        simpa only [mul_inv_cancel_left] using
          (f.property g (fun i => g⁻¹ * x i)).symm
      exact ⟨⟨nestedLift A (n + 1) f.1, hi⟩, Subtype.ext (nestedEval_lift A (n + 1) f.1)⟩
  exact (covariantHomEquiv A (n + 1)).bijective.comp hEval

theorem homogeneousComparison_isIso [DiscreteTopology G] (A : TopRep.{u} k G) :
    IsIso (homogeneousComparison A) := by
  have (n : ℕ) : IsIso ((homogeneousComparison A).f n) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    exact homogeneousTermMap_bijective A n
  exact HomologicalComplex.Hom.isIso_of_components _

theorem continuousToOrdinaryCochains_isIso [DiscreteTopology G] (A : TopRep.{u} k G) :
    IsIso (continuousToOrdinaryCochains A) := by
  let := homogeneousComparison_isIso A
  unfold continuousToOrdinaryCochains
  infer_instance

theorem continuousToOrdinary_isIso [DiscreteTopology G] (A : TopRep.{u} k G) (q : ℕ) :
    IsIso (continuousToOrdinary A q) := by
  let := continuousToOrdinaryCochains_isIso A
  unfold continuousToOrdinary
  infer_instance

omit [TopologicalSpace k] [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The bar-to-standard map on free generators is given by partial products. -/
theorem diagonalSuccIsoFree_inv_single (n : ℕ) (x : Fin n → G) (g : G) (r : k) :
    (Rep.diagonalSuccIsoFree k G n).inv.hom (Finsupp.single x (.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd x) r := by
  simp only [Rep.diagonalSuccIsoFree, Rep.diagonalSuccIsoTensorTrivial, Iso.trans_inv,
    Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  have step : (Rep.Hom.hom (Rep.leftRegularTensorTrivialIsoFree k G (Fin n → G)).inv)
      (Finsupp.single x (.single g r)) = .single g 1 ⊗ₜ[k] .single x r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single x g r
  rw [step]
  simp only [Rep.mkIso_inv, Representation.linearizeOfMulActionIso, Representation.Equiv.mk_symm,
    LinearEquiv.refl_symm, ConcreteCategory.hom_ofHom, Action.tensorObj_V,
    Functor.mapIso_inv, Rep.tensor_V, Rep.tensor_ρ, Iso.symm_inv, Functor.Monoidal.μIso_hom,
    Rep.μ_hom, CategoryTheory.MonoidalCategory.tensorIso_inv, Representation.linearizeTrivialIso,
    Rep.hom_tensorHom, Representation.IntertwiningMap.tensor_apply,
    Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.mk_apply,
    LinearEquiv.refl_apply]
  have h₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G n).inv (g, x) ((1 : k) * r)
  have h₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin n → G)) g x 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G n).inv) z) h₂).trans h₁).trans (by
      simp only [one_mul]
      exact congrArg (fun y => MonoidAlgebra.single y r)
        (Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g x))

/-- The chosen comparison evaluates at the tuple of partial products. -/
theorem continuousToOrdinaryCochains_apply (A : TopRep.{u} k G) (n : ℕ)
    (f : (TopRep.homogeneousCochains A).X n) (x : Fin n → G) :
    (continuousToOrdinaryCochains A).f n f x =
      nestedEval A (n + 1) f.1 (Fin.partialProd x) := by
  change (homogeneousTermMap A n f).hom
    ((Rep.diagonalSuccIsoFree k G n).inv.hom (Finsupp.single x (.single 1 1))) = _
  rw [diagonalSuccIsoFree_inv_single]
  simp only [one_smul]
  exact (homogeneousTermMap_single A n f (Fin.partialProd x) 1).trans (one_smul k _)

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Evaluation of the recursive change-of-group map is coordinatewise precomposition. -/
theorem nestedEval_resolutionMap (A : TopRep.{u} k G) (B : TopRep.{u} k H)
    (φ : H →ₜ* G) (f : TopRep.res φ A ⟶ B) (n : ℕ)
    (a : TopRep.resolutionX A n) (x : Fin n → H) :
    nestedEval B n ((ContinuousCohomology.resolutionMap φ f n).hom a) x =
      f.hom (nestedEval A n a (φ ∘ x)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change nestedEval B n ((ContinuousCohomology.resolutionMap φ f n).hom (a (φ (x 0))))
      (Fin.tail x) = _
    rw [ih]
    rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Partial products commute with a group homomorphism. -/
theorem map_partialProd (φ : H →ₜ* G) (n : ℕ) (x : Fin n → H) :
    φ ∘ Fin.partialProd x = Fin.partialProd (φ ∘ x) := by
  funext i
  induction i using Fin.induction with
  | zero => simp
  | succ i ih => simp only [Function.comp_apply, Fin.partialProd_succ, map_mul] at *; rw [ih]

/-- The square with Mathlib's actual cochain maps commutes. -/
theorem continuousToOrdinaryCochains_naturality
    (A : TopRep.{u} k G) (B : TopRep.{u} k H)
    (φ : H →ₜ* G) (f : TopRep.res φ A ⟶ B) :
    (((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (ContinuousCohomology.cochainsMap φ f) ≫
        continuousToOrdinaryCochains B) =
      continuousToOrdinaryCochains A ≫
        groupCohomology.cochainsMap (φ : H →* G) (Rep.ofHom f.hom.toIntertwiningMap) := by
  ext n a x
  change (continuousToOrdinaryCochains B).f n
    ((ContinuousCohomology.cochainsMap φ f).f n a) x =
      f.hom ((continuousToOrdinaryCochains A).f n a (φ ∘ x))
  rw [continuousToOrdinaryCochains_apply, continuousToOrdinaryCochains_apply]
  change nestedEval B (n + 1) ((ContinuousCohomology.resolutionMap φ f (n + 1)).hom a.1)
    (Fin.partialProd x) = _
  rw [nestedEval_resolutionMap, map_partialProd]

/-- Passing to homology preserves the canonical naturality square. -/
theorem continuousToOrdinary_naturality
    (A : TopRep.{u} k G) (B : TopRep.{u} k H)
    (φ : H →ₜ* G) (f : TopRep.res φ A ⟶ B) (q : ℕ) :
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
        (ContinuousCohomology.map φ f q) ≫ continuousToOrdinary B q =
      continuousToOrdinary A q ≫
        groupCohomology.map (φ : H →* G) (Rep.ofHom f.hom.toIntertwiningMap) q := by
  have h := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (TopModuleCat.{u} k) (ComplexShape.up ℕ) q).map
      (ContinuousCohomology.cochainsMap φ f))
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))
  have h' : (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
      (ContinuousCohomology.map φ f q) ≫
        (((TopRep.homogeneousCochains B).sc q).mapHomologyIso
          (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).inv =
      (((TopRep.homogeneousCochains A).sc q).mapHomologyIso
        (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).inv ≫
      HomologicalComplex.homologyMap
        (((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (ContinuousCohomology.cochainsMap φ f)) q := h
  have hc := congrArg (fun c => HomologicalComplex.homologyMap c q)
    (continuousToOrdinaryCochains_naturality A B φ f)
  simp only [HomologicalComplex.homologyMap_comp] at hc
  calc
    _ = (((TopRep.homogeneousCochains A).sc q).mapHomologyIso
        (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).inv ≫
        (HomologicalComplex.homologyMap
          (((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map (ContinuousCohomology.cochainsMap φ f)) q ≫
          HomologicalComplex.homologyMap (continuousToOrdinaryCochains B) q) := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ HomologicalComplex.homologyMap
          (continuousToOrdinaryCochains B) q) h').trans (Category.assoc _ _ _))
    _ = _ := by
      rw [hc]
      exact (Category.assoc _ _ _).symm

/-- Discrete invertibility and naturality for the published canonical maps. -/
theorem cochainComparisonLaws : CochainComparisonLaws.{u} := by
  constructor
  · intro k G _ _ _ _ _ _ A
    have := continuousToOrdinaryCochains_isIso A
    exact ⟨this, fun n => inferInstance, continuousToOrdinary_isIso A⟩
  · intro k G H _ _ _ _ _ _ _ _ A B φ f
    exact ⟨continuousToOrdinaryCochains_naturality A B φ f,
      continuousToOrdinary_naturality A B φ f⟩

example : CochainComparisonLaws.{u} := @cochainComparisonLaws.{u}

end Langlands.Continuous
