import Langlands.Algebra.LocalAlgebraApproximationExistenceStatement
import Langlands.Algebra.LocalCompatibleMapApproximationExistenceStatement
import Langlands.Algebra.LocalModuleApproximation

/-! # Simultaneous local approximation of a module map from Stacks 00QV -/

open scoped Matrix

universe uI uA uB uE uF uE' uF' uR uS uM uN uM' uN'

namespace Langlands.Algebra

section matrices

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

namespace LocalAlgebraSystem

variable (D : LocalAlgebraSystem.{uI, uA, uB} ι R S) {ν : Type uE} {κ : Type uF}

/-- Pushing a component matrix along a transition does not change its image in `S`. -/
theorem matrix_map_algMap_map_algι {i j : ι} (h : i ≤ j) (X : Matrix ν κ (D.alg i)) :
    (X.map (D.algMap i j h)).map (D.algι j) = X.map (D.algι i) := by
  ext r c
  exact D.algι_compat i j h (X r c)

/-- Above any index, a finite matrix over `S` comes from a component when the algebra
colimit map is onto. -/
theorem exists_matrix_map_algι (hD : Function.Surjective D.algebraColimitMap) [Finite ν]
    [Finite κ] (Y : Matrix ν κ S) (i₀ : ι) :
    ∃ j, ∃ _ : i₀ ≤ j, ∃ X : Matrix ν κ (D.alg j), X.map (D.algι j) = Y := by
  obtain ⟨i, x, hx⟩ := D.exists_algι_eq_fun hD (fun p : ν × κ ↦ Y p.1 p.2)
  obtain ⟨j, hij, hj⟩ := exists_ge_ge i i₀
  refine ⟨j, hj, Matrix.of fun r c ↦ D.algMap i j hij (x (r, c)), ?_⟩
  ext r c
  exact (D.algι_compat i j hij (x (r, c))).trans (hx (r, c))

/-- Two finite component matrices with the same image in `S` agree after some transition
when the algebra colimit map is injective. -/
theorem exists_matrix_map_algMap_eq (hD : Function.Injective D.algebraColimitMap) [Finite ν]
    [Finite κ] {i : ι} (X Y : Matrix ν κ (D.alg i)) (h : X.map (D.algι i) = Y.map (D.algι i)) :
    ∃ j, ∃ hij : i ≤ j, X.map (D.algMap i j hij) = Y.map (D.algMap i j hij) := by
  obtain ⟨j, hij, hj⟩ := D.exists_algMap_eq_zero_fun hD (fun p : ν × κ ↦ X p.1 p.2 - Y p.1 p.2)
    (fun p ↦ by rw [map_sub, sub_eq_zero]; exact congrFun₂ h p.1 p.2)
  refine ⟨j, hij, ?_⟩
  ext r c
  have := hj (r, c)
  rw [map_sub, sub_eq_zero] at this
  exact this

/-- A matrix over one component, pushed to every index of the tail above that component. -/
def tailMatrix (i₀ : ι) (X : Matrix ν κ (D.alg i₀)) (j : {j : ι // i₀ ≤ j}) :
    Matrix ν κ ((D.tail i₀).alg j) :=
  X.map (D.algMap i₀ j.1 j.2)

/-- The pushed matrices are compatible with the transitions of the tail. -/
theorem tailMatrix_map (i₀ : ι) (X : Matrix ν κ (D.alg i₀)) (j k : {j : ι // i₀ ≤ j})
    (h : j ≤ k) : (D.tailMatrix i₀ X j).map ((D.tail i₀).algMap j k h) = D.tailMatrix i₀ X k := by
  ext r c
  exact DirectedSystem.map_map' D.algMap j.2 h (X r c)

/-- The pushed matrices have the same image in `S` as the original component matrix. -/
theorem tailMatrix_map_algι (i₀ : ι) (X : Matrix ν κ (D.alg i₀)) (j : {j : ι // i₀ ≤ j}) :
    (D.tailMatrix i₀ X j).map ((D.tail i₀).algι j) = X.map (D.algι i₀) :=
  D.matrix_map_algMap_map_algι j.2 X

/-- Pushing matrices to the tail is multiplicative. -/
theorem tailMatrix_mul {μ : Type*} [Fintype κ] (i₀ : ι) (X : Matrix ν κ (D.alg i₀))
    (Y : Matrix κ μ (D.alg i₀)) (j : {j : ι // i₀ ≤ j}) :
    D.tailMatrix i₀ (X * Y) j = D.tailMatrix i₀ X j * D.tailMatrix i₀ Y j :=
  Matrix.map_mul

end LocalAlgebraSystem

end matrices

section maps

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

namespace LocalModuleSystem.CompatibleMap

variable {D : LocalAlgebraSystem.{uI, uA, uB} ι R S}
  {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N]

section cokernel

variable {E : LocalModuleSystem.{uI, uA, uB, uE} D M}
  {F : LocalModuleSystem.{uI, uA, uB, uF} D N} {f : M →ₗ[S] N}
  (φ : CompatibleMap E F f)

/-- The cokernel system has a bijective additive colimit map when that of the source is onto
and that of the target is bijective. -/
theorem cokernelSystem_moduleColimitMap_bijective
    (hE : Function.Surjective E.moduleColimitMap) (hF : Function.Bijective F.moduleColimitMap) :
    Function.Bijective φ.cokernelSystem.moduleColimitMap := by
  refine φ.cokernelSystem.moduleColimitMap_bijective_of (fun q ↦ ?_) (fun i q hq ↦ ?_)
  · obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨i, x, rfl⟩ := F.exists_ιM_eq hF.2 n
    exact ⟨i, Submodule.Quotient.mk x, rfl⟩
  · induction q using Submodule.Quotient.induction_on with
    | _ n =>
      rw [cokernelSystem_ιM_mk, Submodule.Quotient.mk_eq_zero] at hq
      obtain ⟨m, hm⟩ := hq
      obtain ⟨k, y, rfl⟩ := E.exists_ιM_eq hE m
      obtain ⟨l, hil, hkl⟩ := exists_ge_ge i k
      have hz : F.ιM l (F.map i l hil n - φ.component l (E.map k l hkl y)) = 0 := by
        rw [map_sub, F.ιM_compat, φ.ιM_comm, E.ιM_compat, hm, sub_self]
      obtain ⟨l', hll', hl'⟩ := F.exists_map_eq_zero hF.1 _ hz
      refine ⟨l', hil.trans hll', ?_⟩
      rw [map_sub, sub_eq_zero, DirectedSystem.map_map' F.map, ← φ.map_comm] at hl'
      rw [cokernelSystem_map_mk]
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨_, hl'.symm⟩

/-- The cokernel of a compatible map of approximation systems is an approximation system. -/
theorem cokernelSystem_isApproximation_of_isApproximation (hφ : φ.IsApproximation) :
    φ.cokernelSystem.IsApproximation :=
  φ.cokernelSystem_isApproximation hφ
    (φ.cokernelSystem_moduleColimitMap_bijective hφ.1.1.2.2 hφ.2.1.2)

end cokernel

section transport

variable {M' : Type uM'} {N' : Type uN'} [AddCommGroup M'] [AddCommGroup N'] [Module S M']
  [Module S N'] {E : LocalModuleSystem.{uI, uA, uB, uE} D M}
  {F : LocalModuleSystem.{uI, uA, uB, uF} D N} {g : M →ₗ[S] N}
  (φ : CompatibleMap E F g) (eM : M ≃ₗ[S] M') (eN : N ≃ₗ[S] N') (f : M' →ₗ[S] N')

/-- The same component maps, viewed between the systems whose cocones are composed with
linear equivalences of the targets, over a target map matching `g` under these
equivalences. -/
def mapLinearEquiv (hf : ∀ x, f (eM x) = eN (g x)) :
    CompatibleMap (E.mapLinearEquiv eM) (F.mapLinearEquiv eN) f where
  component := φ.component
  map_comm := φ.map_comm
  ιM_comm i m := (congrArg eN (φ.ιM_comm i m)).trans (hf _).symm

/-- Transport along linear equivalences of targets preserves approximation. -/
theorem mapLinearEquiv_isApproximation (hf : ∀ x, f (eM x) = eN (g x)) (hφ : φ.IsApproximation) :
    (φ.mapLinearEquiv eM eN f hf).IsApproximation :=
  ⟨E.mapLinearEquiv_isApproximation eM hφ.1, F.mapLinearEquiv_isApproximation eN hφ.2⟩

end transport

section induced

variable {M₂ : Type uM'} {N₂ : Type uN'} [AddCommGroup M₂] [AddCommGroup N₂] [Module S M₂]
  [Module S N₂] {E₁ : LocalModuleSystem.{uI, uA, uB, uE} D M}
  {F₁ : LocalModuleSystem.{uI, uA, uB, uF} D N}
  {E₂ : LocalModuleSystem.{uI, uA, uB, uE'} D M₂}
  {F₂ : LocalModuleSystem.{uI, uA, uB, uF'} D N₂}
  {f₁ : M →ₗ[S] N} {f₂ : M₂ →ₗ[S] N₂} {g : N →ₗ[S] N₂}
  (φ₁ : CompatibleMap E₁ F₁ f₁) (φ₂ : CompatibleMap E₂ F₂ f₂) (γ : CompatibleMap F₁ F₂ g)
  (hγ : ∀ i, LinearMap.range (φ₁.component i) ≤
    (LinearMap.range (φ₂.component i)).comap (γ.component i))
  (hg : LinearMap.range f₁ ≤ (LinearMap.range f₂).comap g)

/-- A compatible map between the targets of two compatible maps, carrying component images
into component images, induces a compatible map of the actual cokernel systems over the
induced map of target cokernels. -/
def cokernelSystemMap :
    CompatibleMap φ₁.cokernelSystem φ₂.cokernelSystem
      ((LinearMap.range f₁).mapQ (LinearMap.range f₂) g hg) where
  component i :=
    (LinearMap.range (φ₁.component i)).mapQ (LinearMap.range (φ₂.component i))
      (γ.component i) (hγ i)
  map_comm i j h x := by
    induction x using Submodule.Quotient.induction_on with
    | _ n =>
      change Submodule.Quotient.mk (γ.component j (F₁.map i j h n)) =
        Submodule.Quotient.mk (F₂.map i j h (γ.component i n))
      rw [γ.map_comm]
  ιM_comm i x := by
    induction x using Submodule.Quotient.induction_on with
    | _ n =>
      change Submodule.Quotient.mk (F₂.ιM i (γ.component i n)) =
        Submodule.Quotient.mk (g (F₁.ιM i n))
      rw [γ.ιM_comm]

/-- The induced cokernel map sends a quotient representative along `γ`. -/
@[simp] theorem cokernelSystemMap_component_mk (i : ι) (n : F₁.obj i) :
    (cokernelSystemMap φ₁ φ₂ γ hγ hg).component i (Submodule.Quotient.mk n) =
      Submodule.Quotient.mk (γ.component i n) := rfl

end induced

end LocalModuleSystem.CompatibleMap

end maps

/-- A linear map between cokernels of two matrices lifts to a matrix `C` between the free
modules together with a matrix `B` between the relation modules satisfying `A' * B = C * A`. -/
theorem exists_matrix_lift {S : Type uS} [CommRing S] {n m n' m' : ℕ}
    (A : Matrix (Fin n) (Fin m) S) (A' : Matrix (Fin n') (Fin m') S)
    (g : ((Fin n → S) ⧸ LinearMap.range A.mulVecLin) →ₗ[S]
      ((Fin n' → S) ⧸ LinearMap.range A'.mulVecLin)) :
    ∃ (B : Matrix (Fin m') (Fin m) S) (C : Matrix (Fin n') (Fin n) S),
      A' * B = C * A ∧ ∀ v, g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (C *ᵥ v) := by
  obtain ⟨c, hc⟩ := Module.projective_lifting_property (LinearMap.range A'.mulVecLin).mkQ
    (g ∘ₗ (LinearMap.range A.mulVecLin).mkQ) (Submodule.mkQ_surjective _)
  have hrange : ∀ v, (c ∘ₗ A.mulVecLin) v ∈ LinearMap.range A'.mulVecLin := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero]
    have hv := LinearMap.congr_fun hc (A *ᵥ v)
    have hAv : Submodule.Quotient.mk (p := LinearMap.range A.mulVecLin) (A *ᵥ v) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self A.mulVecLin v)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
      hAv, map_zero] at hv
    exact hv
  obtain ⟨b, hb⟩ := Module.projective_lifting_property A'.mulVecLin.rangeRestrict
    ((c ∘ₗ A.mulVecLin).codRestrict _ hrange) A'.mulVecLin.surjective_rangeRestrict
  have hb' : ∀ v, A' *ᵥ b v = c (A *ᵥ v) := fun v ↦
    congrArg Subtype.val (LinearMap.congr_fun hb v)
  refine ⟨LinearMap.toMatrix' b, LinearMap.toMatrix' c, ?_, fun v ↦ ?_⟩
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun v ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact hb' v
  · rw [LinearMap.toMatrix'_mulVec]
    exact (LinearMap.congr_fun hc v).symm

open LocalAlgebraSystem LocalModuleSystem in
/-- The first paragraph of the proof of Stacks 046Y from Stacks 00QV: a ring approximation
system for `R → ULift S` yields one ring system with approximation systems of both modules and
compatible component maps inducing the given map. -/
theorem localCompatibleMapApproximationExistence_of_localAlgebraApproximationExistence
    (h : LocalAlgebraApproximationExistenceStatement.{uR, max uS uM uN}) :
    LocalCompatibleMapApproximationExistenceStatement.{uR, uS, uM, uN} := by
  intro R S M N _ _ _ _ _ _ _ _ _ _ hS hM hN f
  have : IsLocalRing (ULift.{max uM uN} S) :=
    IsLocalRing.of_surjective' (ULift.ringEquiv (R := S)).symm.toRingHom
      (ULift.ringEquiv (R := S)).symm.surjective
  have : IsLocalHom (algebraMap R (ULift.{max uM uN} S)) := by
    refine ⟨fun r hr ↦ IsUnit.of_map (algebraMap R S) r ?_⟩
    have := hr.map (ULift.algEquiv : ULift.{max uM uN} S ≃ₐ[R] S)
    rwa [AlgEquiv.commutes] at this
  have hS' : EssFinitePresentation R (ULift.{max uM uN} S) := by
    obtain ⟨n, I, hI, P, ⟨e⟩⟩ := hS
    exact ⟨n, I, hI, P, ⟨e.trans ULift.algEquiv.symm⟩⟩
  obtain ⟨ι, _, _, _, D₀, hD₀⟩ := h R (ULift.{max uM uN} S) hS'
  let D₁ := D₀.mapAlgEquiv (ULift.algEquiv : ULift.{max uM uN} S ≃ₐ[R] S)
  have hD₁ : D₁.IsApproximation := D₀.mapAlgEquiv_isApproximation _ hD₀
  have := hM
  have := hN
  -- Presentations of `M` and `N`, and a matrix lift of `f`.
  obtain ⟨n, m, A, ⟨eA⟩⟩ := exists_matrix_presentation S M
  obtain ⟨n', m', A', ⟨eA'⟩⟩ := exists_matrix_presentation S N
  obtain ⟨B, C, hBC, hC⟩ := exists_matrix_lift A A' (eA'.symm.toLinearMap ∘ₗ f ∘ₗ eA.toLinearMap)
  -- Descend the four matrices to one component.
  obtain ⟨i₁, -, a₁, ha₁⟩ := D₁.exists_matrix_map_algι hD₁.1.2.2 A (Classical.arbitrary ι)
  obtain ⟨i₂, h₁₂, a'₂, ha'₂⟩ := D₁.exists_matrix_map_algι hD₁.1.2.2 A' i₁
  obtain ⟨i₃, h₂₃, b₃, hb₃⟩ := D₁.exists_matrix_map_algι hD₁.1.2.2 B i₂
  obtain ⟨i₄, h₃₄, c₄, hc₄⟩ := D₁.exists_matrix_map_algι hD₁.1.2.2 C i₃
  let a₄ := a₁.map (D₁.algMap i₁ i₄ ((h₁₂.trans h₂₃).trans h₃₄))
  let a'₄ := a'₂.map (D₁.algMap i₂ i₄ (h₂₃.trans h₃₄))
  let b₄ := b₃.map (D₁.algMap i₃ i₄ h₃₄)
  have ha₄ : a₄.map (D₁.algι i₄) = A := (D₁.matrix_map_algMap_map_algι _ a₁).trans ha₁
  have ha'₄ : a'₄.map (D₁.algι i₄) = A' := (D₁.matrix_map_algMap_map_algι _ a'₂).trans ha'₂
  have hb₄ : b₄.map (D₁.algι i₄) = B := (D₁.matrix_map_algMap_map_algι _ b₃).trans hb₃
  -- Make the relation `A' * B = C * A` hold on a component.
  obtain ⟨i₅, h₄₅, hrel⟩ := D₁.exists_matrix_map_algMap_eq hD₁.1.2.1 (a'₄ * b₄) (c₄ * a₄)
    (by rw [Matrix.map_mul, Matrix.map_mul, ha₄, ha'₄, hb₄, hc₄, hBC])
  let a := a₄.map (D₁.algMap i₄ i₅ h₄₅)
  let a' := a'₄.map (D₁.algMap i₄ i₅ h₄₅)
  let b := b₄.map (D₁.algMap i₄ i₅ h₄₅)
  let c := c₄.map (D₁.algMap i₄ i₅ h₄₅)
  have ha : a.map (D₁.algι i₅) = A := (D₁.matrix_map_algMap_map_algι _ a₄).trans ha₄
  have ha' : a'.map (D₁.algι i₅) = A' := (D₁.matrix_map_algMap_map_algι _ a'₄).trans ha'₄
  have hc : c.map (D₁.algι i₅) = C := (D₁.matrix_map_algMap_map_algι _ c₄).trans hc₄
  have habc : a' * b = c * a := by
    simpa only [Matrix.map_mul] using hrel
  -- Restrict to the tail above that component.
  let D := D₁.tail i₅
  have hD : D.IsApproximation := D₁.tail_isApproximation hD₁ i₅
  let φA := D.matrixMap (D₁.tailMatrix i₅ a) (D₁.tailMatrix_map i₅ a) A
    (fun j ↦ (D₁.tailMatrix_map_algι i₅ a j).trans ha)
  let φA' := D.matrixMap (D₁.tailMatrix i₅ a') (D₁.tailMatrix_map i₅ a') A'
    (fun j ↦ (D₁.tailMatrix_map_algι i₅ a' j).trans ha')
  let γ := D.matrixMap (D₁.tailMatrix i₅ c) (D₁.tailMatrix_map i₅ c) C
    (fun j ↦ (D₁.tailMatrix_map_algι i₅ c j).trans hc)
  have hγ : ∀ j, LinearMap.range (φA.component j) ≤
      (LinearMap.range (φA'.component j)).comap (γ.component j) := by
    intro j
    have key : ∀ w : Fin m → (D₁.tail i₅).alg j,
        D₁.tailMatrix i₅ a' j *ᵥ (D₁.tailMatrix i₅ b j *ᵥ w) =
          D₁.tailMatrix i₅ c j *ᵥ (D₁.tailMatrix i₅ a j *ᵥ w) := by
      intro w
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← D₁.tailMatrix_mul,
        ← D₁.tailMatrix_mul, habc]
    rintro _ ⟨v, rfl⟩
    exact ⟨D₁.tailMatrix i₅ b j *ᵥ v, key v⟩
  have hg : LinearMap.range A.mulVecLin ≤
      (LinearMap.range A'.mulVecLin).comap C.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    refine ⟨B *ᵥ v, ?_⟩
    change A' *ᵥ (B *ᵥ v) = C *ᵥ (A *ᵥ v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBC]
  let ψ := LocalModuleSystem.CompatibleMap.cokernelSystemMap φA φA' γ hγ hg
  have hψ : ψ.IsApproximation :=
    ⟨φA.cokernelSystem_isApproximation_of_isApproximation
        ⟨D.freeSystem_isApproximation hD, D.freeSystem_isApproximation hD⟩,
      φA'.cokernelSystem_isApproximation_of_isApproximation
        ⟨D.freeSystem_isApproximation hD, D.freeSystem_isApproximation hD⟩⟩
  have hf : ∀ x, f (eA x) =
      eA' ((LinearMap.range A.mulVecLin).mapQ (LinearMap.range A'.mulVecLin) C.mulVecLin hg x) := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ v =>
      rw [Submodule.mapQ_apply, Matrix.mulVecLin_apply, ← hC v]
      simp
  exact ⟨{j : ι // i₅ ≤ j}, inferInstance, inferInstance, inferInstance, D, _, _,
    ψ.mapLinearEquiv eA eA' f hf, ψ.mapLinearEquiv_isApproximation eA eA' f hf hψ⟩

end Langlands.Algebra
