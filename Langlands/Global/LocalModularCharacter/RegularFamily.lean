import Langlands.GroupScheme.AffinePointFiniteCoordinates
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Regular families of points of an affine group scheme

Let `G` be an affine group scheme over a field `F` and `K` an `F`-algebra. A family
`f : T → G(K)` is regular for an `F`-subalgebra `𝒮` of `T → K` if every regular function of `G`,
evaluated along the family, lies in `𝒮`. Such a family is a point of `G(𝒮)`, so products and
inverses of regular families are regular. The main example of `𝒮` is the algebra of functions
strictly differentiable at a point. -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Global.LocalModularCharacter

section StrictDiff

variable (F : Type*) [CommSemiring F] (K : Type*) [NontriviallyNormedField K] [Algebra F K]
  {T : Type*} [NormedAddCommGroup T] [NormedSpace K T]

/-- The `F`-algebra of functions `T → K` that are strictly differentiable at `t₀`. -/
def strictDiffSubalgebra (t₀ : T) : Subalgebra F (T → K) where
  carrier := {h | ∃ L : T →L[K] K, HasStrictFDerivAt h L t₀}
  mul_mem' := fun ⟨_, hL⟩ ⟨_, hM⟩ => ⟨_, hL.mul hM⟩
  add_mem' := fun ⟨_, hL⟩ ⟨_, hM⟩ => ⟨_, hL.add hM⟩
  algebraMap_mem' r := ⟨0, hasStrictFDerivAt_const (algebraMap F K r) t₀⟩

variable {F K}

theorem mem_strictDiffSubalgebra {t₀ : T} {h : T → K} :
    h ∈ strictDiffSubalgebra F K t₀ ↔ ∃ L : T →L[K] K, HasStrictFDerivAt h L t₀ :=
  Iff.rfl

theorem const_mem_strictDiffSubalgebra (t₀ : T) (k : K) :
    (fun _ : T => k) ∈ strictDiffSubalgebra F K t₀ :=
  ⟨0, hasStrictFDerivAt_const k t₀⟩

end StrictDiff

variable {F : Type u} [Field F] (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
variable {K : Type u} [CommRing K] [Algebra F K] {T : Type u} (𝒮 : Subalgebra F (T → K))

/-- Evaluation of a family of functions at a parameter, as an algebra map. -/
def familyEval (t : T) : 𝒮 →ₐ[F] K :=
  (Pi.evalAlgHom F (fun _ : T => K) t).comp 𝒮.val

@[simp] theorem familyEval_apply (t : T) (h : 𝒮) : familyEval 𝒮 t h = (h : T → K) t := rfl

/-- The values of a regular function along a family of points. -/
def familyValue (f : T → Lie.AffinePoints G K) (a : Γ(G.X.left, ⊤)) : T → K :=
  fun t => G.affinePointEvaluation (CommAlgCat.of F K) (f t) a

/-- A family of points is regular for `𝒮` when all its regular-function values lie in `𝒮`. -/
def IsRegularFamily (f : T → Lie.AffinePoints G K) : Prop :=
  ∀ a : Γ(G.X.left, ⊤), familyValue G f a ∈ 𝒮

/-- The coordinate algebra map of a family of points. -/
def familyAlgHom (f : T → Lie.AffinePoints G K) : AffineCoordinateRing F G.X →ₐ[F] (T → K) :=
  AlgHom.pi fun t =>
    (affineSchemePointEquiv F G.X (CommAlgCat.of F K) (f t)).toAlgHom

theorem familyAlgHom_apply (f : T → Lie.AffinePoints G K) (a : Γ(G.X.left, ⊤)) :
    familyAlgHom G f a = familyValue G f a := by
  funext t
  exact G.affineSchemePointEquiv_evaluation (CommAlgCat.of F K) (f t) a

/-- A regular family as a point with coefficients in `𝒮`. -/
def liftFamily (f : T → Lie.AffinePoints G K) (hf : IsRegularFamily G 𝒮 f) :
    Lie.AffinePoints G 𝒮 :=
  (affineSchemePointEquiv F G.X (CommAlgCat.of F 𝒮)).symm
    (AlgPoint.ofAlgHom ((familyAlgHom G f).codRestrict 𝒮 fun a =>
      (familyAlgHom_apply G f a).symm ▸ hf a))

theorem affinePointEvaluation_liftFamily (f : T → Lie.AffinePoints G K)
    (hf : IsRegularFamily G 𝒮 f) (a : Γ(G.X.left, ⊤)) :
    G.affinePointEvaluation (CommAlgCat.of F 𝒮) (liftFamily G 𝒮 f hf) a = ⟨_, hf a⟩ := by
  refine (G.affineSchemePointEquiv_evaluation (CommAlgCat.of F 𝒮) (liftFamily G 𝒮 f hf) a).symm.trans
    ?_
  rw [liftFamily, Equiv.apply_symm_apply]
  exact Subtype.ext (familyAlgHom_apply G f a)

omit [IsAffine G.X.left] in
/-- The value of a point with coefficients in `𝒮`, as a function, is computed parameterwise. -/
theorem affinePointEvaluation_family_apply (P : Lie.AffinePoints G 𝒮)
    (a : Γ(G.X.left, ⊤)) (t : T) :
    (G.affinePointEvaluation (CommAlgCat.of F 𝒮) P a : T → K) t =
      G.affinePointEvaluation (CommAlgCat.of F K) (Lie.affineMap G (familyEval 𝒮 t) P) a := by
  change _ = G.affinePointEvaluation (CommAlgCat.of F K)
    (G.affinePointMap (CommAlgCat.ofHom (familyEval 𝒮 t)) P) a
  rw [affinePointEvaluation_map]
  rfl

theorem affineMap_familyEval_liftFamily (f : T → Lie.AffinePoints G K)
    (hf : IsRegularFamily G 𝒮 f) (t : T) :
    Lie.affineMap G (familyEval 𝒮 t) (liftFamily G 𝒮 f hf) = f t := by
  apply G.affinePointEvaluation_injective (CommAlgCat.of F K)
  funext a
  show G.affinePointEvaluation (CommAlgCat.of F K)
    (Lie.affineMap G (familyEval 𝒮 t) (liftFamily G 𝒮 f hf)) a = familyValue G f a t
  rw [← affinePointEvaluation_family_apply, affinePointEvaluation_liftFamily]

omit [IsAffine G.X.left] in
/-- A family that is the parameterwise specialization of a point of `G(𝒮)` is regular. -/
theorem isRegularFamily_of_specialization (P : Lie.AffinePoints G 𝒮)
    (f : T → Lie.AffinePoints G K) (hP : ∀ t, Lie.affineMap G (familyEval 𝒮 t) P = f t) :
    IsRegularFamily G 𝒮 f := by
  intro a
  have h : familyValue G f a = (G.affinePointEvaluation (CommAlgCat.of F 𝒮) P a : T → K) := by
    funext t
    rw [affinePointEvaluation_family_apply, hP]
    rfl
  rw [h]
  exact SetLike.coe_mem _

/-- A point of `G(𝒮)` specializing to the family `f` is the lift of `f`. -/
theorem liftFamily_eq (f : T → Lie.AffinePoints G K) (hf : IsRegularFamily G 𝒮 f)
    (P : Lie.AffinePoints G 𝒮) (hP : ∀ t, Lie.affineMap G (familyEval 𝒮 t) P = f t) :
    liftFamily G 𝒮 f hf = P := by
  apply G.affinePointEvaluation_injective (CommAlgCat.of F 𝒮)
  funext a
  change G.affinePointEvaluation (CommAlgCat.of F 𝒮) (liftFamily G 𝒮 f hf) a =
    G.affinePointEvaluation (CommAlgCat.of F 𝒮) P a
  rw [affinePointEvaluation_liftFamily]
  apply Subtype.ext
  funext t
  change familyValue G f a t = _
  rw [affinePointEvaluation_family_apply, hP]
  rfl

omit [IsAffine G.X.left] in
/-- Evaluation of regular functions commutes with change of coefficients. -/
theorem affinePointEvaluation_affineMap {A B : Type u} [CommRing A] [Algebra F A] [CommRing B]
    [Algebra F B] (f : A →ₐ[F] B) (x : Lie.AffinePoints G A) (a : Γ(G.X.left, ⊤)) :
    G.affinePointEvaluation (CommAlgCat.of F B) (Lie.affineMap G f x) a =
      f (G.affinePointEvaluation (CommAlgCat.of F A) x a) := by
  change G.affinePointEvaluation (CommAlgCat.of F B)
    (G.affinePointMap (CommAlgCat.ofHom f) x) a = _
  rw [affinePointEvaluation_map]
  rfl

variable {G 𝒮}

theorem IsRegularFamily.mul {f g : T → Lie.AffinePoints G K} (hf : IsRegularFamily G 𝒮 f)
    (hg : IsRegularFamily G 𝒮 g) : IsRegularFamily G 𝒮 (fun t => f t * g t) :=
  isRegularFamily_of_specialization G 𝒮 (liftFamily G 𝒮 f hf * liftFamily G 𝒮 g hg) _
    fun t => by
      rw [map_mul, affineMap_familyEval_liftFamily, affineMap_familyEval_liftFamily]

theorem IsRegularFamily.inv {f : T → Lie.AffinePoints G K} (hf : IsRegularFamily G 𝒮 f) :
    IsRegularFamily G 𝒮 (fun t => (f t)⁻¹) :=
  isRegularFamily_of_specialization G 𝒮 (liftFamily G 𝒮 f hf)⁻¹ _
    fun t => by rw [map_inv, affineMap_familyEval_liftFamily]

omit [IsAffine G.X.left] in
theorem isRegularFamily_const (hconst : ∀ k : K, (fun _ : T => k) ∈ 𝒮)
    (g : Lie.AffinePoints G K) : IsRegularFamily G 𝒮 (fun _ => g) :=
  fun _ => hconst _

omit [IsAffine G.X.left] in
theorem IsRegularFamily.comp {T' : Type u} {f : T → Lie.AffinePoints G K}
    (hf : IsRegularFamily G 𝒮 f) (𝒮' : Subalgebra F (T' → K)) (σ : T' → T)
    (hσ : ∀ h ∈ 𝒮, h ∘ σ ∈ 𝒮') : IsRegularFamily G 𝒮' (f ∘ σ) :=
  fun a => hσ _ (hf a)

/-- The lift of a product of regular families is the product of the lifts. -/
theorem liftFamily_mul {f g : T → Lie.AffinePoints G K} (hf : IsRegularFamily G 𝒮 f)
    (hg : IsRegularFamily G 𝒮 g) :
    liftFamily G 𝒮 (fun t => f t * g t) (hf.mul hg) = liftFamily G 𝒮 f hf * liftFamily G 𝒮 g hg :=
  liftFamily_eq G 𝒮 _ _ _ fun t => by
    rw [map_mul, affineMap_familyEval_liftFamily, affineMap_familyEval_liftFamily]

end Langlands.Global.LocalModularCharacter
