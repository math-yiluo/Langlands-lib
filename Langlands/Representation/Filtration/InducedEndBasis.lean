import Langlands.Representation.Filtration.HomVanishingBasis
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # A basis of the endomorphisms of an induced object, through an adjunction

Let `Res ⊣ Ind` be an adjunction between preadditive categories `C` and `D` with `Ind : C ⥤ D`
additive, and let `T : C ⥤ Rep R G` be additive, full and faithful. For `X : C`, the adjunction
identifies `End(Ind X)` with the maps `T (Res (Ind X)) ⟶ T X`, and precomposition with
`Ind.map a` corresponds to precomposition with `(Ind ⋙ Res ⋙ T).map a`. So a basis of the maps
`(Ind ⋙ Res ⋙ T).obj X ⟶ T.obj X` over `(End X)ᵐᵒᵖ`, such as `homVanishingBasis`, transports to
a basis of `End(Ind X)` over `(End X)ᵐᵒᵖ` acting by precomposition with `Ind.map`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.RepFunctorFiltration

universe uR uG uV uC vC uD vD

section Precomp

variable {C : Type uC} [Category.{vC} C] [Preadditive C] {D : Type uD} [Category.{vD} D]
  [Preadditive D] (Φ : C ⥤ D) [Φ.Additive]

/-- The left `(End X)ᵐᵒᵖ`-module structure on `Φ X ⟶ Z` given by precomposition with `Φ.map`:
`op a • f = Φ.map a ≫ f`. -/
@[instance_reducible]
def endPrecompModule (X : C) (Z : D) : Module (End X)ᵐᵒᵖ (Φ.obj X ⟶ Z) where
  smul a f := Φ.map a.unop ≫ f
  one_smul f := by
    change Φ.map (𝟙 X) ≫ f = f
    rw [Φ.map_id, Category.id_comp]
  mul_smul a b f := by
    change Φ.map (b.unop * a.unop) ≫ f = Φ.map a.unop ≫ Φ.map b.unop ≫ f
    rw [End.mul_def, Φ.map_comp, Category.assoc]
  smul_zero _ := comp_zero
  smul_add _ _ _ := Preadditive.comp_add _ _ _ _ _ _
  add_smul a b f := by
    change Φ.map (a.unop + b.unop) ≫ f = Φ.map a.unop ≫ f + Φ.map b.unop ≫ f
    rw [Φ.map_add, Preadditive.add_comp]
  zero_smul f := by
    change Φ.map (0 : X ⟶ X) ≫ f = 0
    rw [Φ.map_zero, zero_comp]

theorem endPrecompModule_smul (X : C) (Z : D) (a : (End X)ᵐᵒᵖ) (f : Φ.obj X ⟶ Z) :
    letI := endPrecompModule Φ X Z
    a • f = Φ.map a.unop ≫ f :=
  rfl

end Precomp

variable {R : Type uR} {G : Type uG} [CommRing R] [Monoid G]
  {C : Type uC} [Category.{vC} C] [Preadditive C] {D : Type uD} [Category.{vD} D]
  [Preadditive D] {Ind : C ⥤ D} {Res : D ⥤ C} (adj : Res ⊣ Ind) [Ind.Additive] [Res.Additive]
  (T : C ⥤ Rep.{uV} R G) [T.Additive] [T.Full] [T.Faithful]

/-- The adjunction transport `x ↦ T.map (adj.homEquiv _ _).symm x` from `End(Ind X)` to the
maps `(Ind ⋙ Res ⋙ T).obj X ⟶ T.obj X`, as an additive equivalence. -/
def inducedEndEquiv (X : C) :
    (Ind.obj X ⟶ Ind.obj X) ≃+ ((Ind ⋙ Res ⋙ T).obj X ⟶ T.obj X) :=
  (adj.homAddEquiv (Ind.obj X) X).symm.trans
    { (Functor.FullyFaithful.ofFullyFaithful T).homEquiv with
      map_add' := fun _ _ => T.map_add }

omit [Ind.Additive] in
theorem inducedEndEquiv_apply (X : C) (x : Ind.obj X ⟶ Ind.obj X) :
    inducedEndEquiv adj T X x = T.map ((adj.homEquiv (Ind.obj X) X).symm x) :=
  rfl

omit [Ind.Additive] in
/-- Precomposition with `Ind.map a` corresponds to precomposition with
`(Ind ⋙ Res ⋙ T).map a`. -/
theorem inducedEndEquiv_map_comp (X : C) (a : X ⟶ X) (x : Ind.obj X ⟶ Ind.obj X) :
    inducedEndEquiv adj T X (Ind.map a ≫ x) =
      (Ind ⋙ Res ⋙ T).map a ≫ inducedEndEquiv adj T X x := by
  rw [inducedEndEquiv_apply, inducedEndEquiv_apply, Adjunction.homEquiv_naturality_left_symm,
    T.map_comp]
  rfl

/-- `inducedEndEquiv` as an `(End X)ᵐᵒᵖ`-linear equivalence for the two precomposition
actions. -/
def inducedEndLinearEquiv (X : C) :
    letI := endPrecompModule Ind X (Ind.obj X)
    letI := precompModule (Ind ⋙ Res ⋙ T) X (T.obj X)
    (Ind.obj X ⟶ Ind.obj X) ≃ₗ[(End X)ᵐᵒᵖ] ((Ind ⋙ Res ⋙ T).obj X ⟶ T.obj X) :=
  letI := endPrecompModule Ind X (Ind.obj X)
  letI := precompModule (Ind ⋙ Res ⋙ T) X (T.obj X)
  { inducedEndEquiv adj T X with
    map_smul' := fun a x => inducedEndEquiv_map_comp adj T X a.unop x }

variable {n : ℕ} (s : RepFunctorFiltration (Ind ⋙ Res ⋙ T) n) (X : C)
  (hsec : ∀ k : Fin n, ∃ σ : (s.graded k).obj X ⟶ (s.step k.succ).representation X,
    σ ≫ s.gradedProjection X k = 𝟙 _)
  (θ : ∀ j : Fin n, (s.graded j).obj X ⟶ T.obj X) (S : Finset (Fin n))
  (hθ : ∀ j ∈ S, Function.Bijective (fun a : X ⟶ X => (s.graded j).map a ≫ θ j))
  (hzero : ∀ j ∉ S, ∀ g : (s.graded j).obj X ⟶ T.obj X, g = 0)

/-- **The basis of `End(Ind X)`.** Under the hypotheses of `homVanishingBasis` for the filtered
functor `Ind ⋙ Res ⋙ T` and the target `T.obj X`, `End(Ind X)` is free over `(End X)ᵐᵒᵖ`
acting by precomposition with `Ind.map`, with a basis indexed by `S`. -/
def inducedEndBasis :
    letI := endPrecompModule Ind X (Ind.obj X)
    Module.Basis S (End X)ᵐᵒᵖ (Ind.obj X ⟶ Ind.obj X) :=
  letI := endPrecompModule Ind X (Ind.obj X)
  letI := precompModule (Ind ⋙ Res ⋙ T) X (T.obj X)
  (s.homVanishingBasis X (T.obj X) hsec θ S hθ hzero).map
    (inducedEndLinearEquiv adj T X).symm

/-- The basis vectors correspond under the adjunction to the vectors of `homVanishingBasis`. -/
theorem inducedEndEquiv_inducedEndBasis (j : S) :
    inducedEndEquiv adj T X (inducedEndBasis adj T s X hsec θ S hθ hzero j) =
      s.homVanishingBasis X (T.obj X) hsec θ S hθ hzero j := by
  let _ := endPrecompModule Ind X (Ind.obj X)
  let _ := precompModule (Ind ⋙ Res ⋙ T) X (T.obj X)
  exact (inducedEndLinearEquiv adj T X).apply_symm_apply _

/-- Every endomorphism `x` of `Ind X` is uniquely `∑_{j ∈ S} Ind.map (a j) ≫ b j`, where
`b j` is the basis vector `inducedEndBasis … j`. -/
theorem existsUnique_inducedEnd_expansion (x : Ind.obj X ⟶ Ind.obj X) :
    ∃! a : S → (X ⟶ X),
      x = ∑ j : S, Ind.map (a j) ≫ inducedEndBasis adj T s X hsec θ S hθ hzero j := by
  let _ := endPrecompModule Ind X (Ind.obj X)
  let b := inducedEndBasis adj T s X hsec θ S hθ hzero
  have hsum : ∀ c : S → (End X)ᵐᵒᵖ, b.equivFun.symm c = ∑ j : S, Ind.map (c j).unop ≫ b j :=
    fun c => b.equivFun_symm_apply c
  refine ⟨fun j => (b.equivFun x j).unop, ?_, fun a ha => ?_⟩
  · change x = ∑ j : S, Ind.map (MulOpposite.op (b.equivFun x j).unop).unop ≫ b j
    simp only [MulOpposite.op_unop]
    rw [← hsum, LinearEquiv.symm_apply_apply]
  · funext j
    have h : b.equivFun.symm (fun j => MulOpposite.op (a j)) = x := by
      rw [hsum]
      exact ha.symm
    rw [← h, LinearEquiv.apply_symm_apply]
    rfl

end Langlands.RepFunctorFiltration
