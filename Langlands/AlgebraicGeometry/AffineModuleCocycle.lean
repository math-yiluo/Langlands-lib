import Langlands.AlgebraicGeometry.AffineAdditiveCocycle

/-! # Natural cocycles with arbitrary module coefficients -/

noncomputable section

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.AffineModuleCocycle

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable (N : Type v) [AddCommGroup N] [Module A N]

/-- Extension of coefficients along an algebra map. -/
def map {C D : Type u} [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
    (f : C →ₐ[A] D) : C ⊗[A] N →ₗ[A] D ⊗[A] N :=
  TensorProduct.map f.toLinearMap LinearMap.id

@[simp]
theorem map_tmul {C D : Type u} [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
    (f : C →ₐ[A] D) (c : C) (n : N) :
    map A N f (c ⊗ₜ[A] n) = f c ⊗ₜ[A] n := rfl

/-- Natural additive cocycles on pairs of algebra points of an affine cover. -/
structure Cocycle where
  toFun : ∀ (C : Type u) [CommRing C] [Algebra A C],
    (B →ₐ[A] C) → (B →ₐ[A] C) → C ⊗[A] N
  naturality : ∀ {C D : Type u} [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
    (f : C →ₐ[A] D) (a b : B →ₐ[A] C),
    toFun D (f.comp a) (f.comp b) = map A N f (toFun C a b)
  cocycle : ∀ (C : Type u) [CommRing C] [Algebra A C] (a b c : B →ₐ[A] C),
    toFun C a c = toFun C a b + toFun C b c

open AffineAdditiveCocycle Algebra.TensorProduct

/-- The associativity comparison on degree-two values with coefficients. -/
def assocThree :
    (B ⊗[A] (B ⊗[A] B)) ⊗[A] N ≃ₗ[A] B ⊗[A] (B ⊗[A] (B ⊗[A] N)) :=
  (TensorProduct.assoc A B (B ⊗[A] B) N).trans
    (TensorProduct.congr (LinearEquiv.refl A B) (TensorProduct.assoc A B B N))

theorem d1_assoc (x : (B ⊗[A] B) ⊗[A] N) :
    AmitsurDegreeOne.d1 A B N (TensorProduct.assoc A B B N x) =
      assocThree A B N
        (map A N (face23 A B) x - map A N (face13 A B) x +
          map A N (face12 A B) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
      simp only [map_add, map_sub] at hx hy ⊢
      rw [hx, hy]
      abel
  | tmul z n =>
      induction z using TensorProduct.inductionOn with
      | add x y hx hy =>
          simp only [TensorProduct.add_tmul, map_add, map_sub] at hx hy ⊢
          rw [hx, hy]
          abel
      | tmul b c =>
          simp [assocThree, map, face12, face13, face23, AmitsurDegreeOne.d1_tmul]

theorem d0_assoc (y : B ⊗[A] N) :
    TensorProduct.assoc A B B N
        (map A N (includeLeft : B →ₐ[A] B ⊗[A] B) y -
          map A N (includeRight : B →ₐ[A] B ⊗[A] B) y) =
      -AmitsurDegreeOne.d0 A B N y := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy =>
      simp only [map_add]
      rw [add_sub_add_comm, map_add, hx, hy, neg_add]
  | tmul b n =>
      simp [map, AmitsurDegreeOne.d0_tmul, neg_sub]

namespace Cocycle

variable (α : Cocycle A B N)

/-- A natural cocycle with arbitrary coefficients on a faithfully flat affine
cover is the coboundary of one coefficient tensor on that cover. -/
theorem exists_coboundary [Module.FaithfullyFlat A B] :
    ∃ β : B ⊗[A] N, ∀ (C : Type u) [CommRing C] [Algebra A C]
      (a b : B →ₐ[A] C), α.toFun C a b = map A N a β - map A N b β := by
  let D₂ := B ⊗[A] B
  let D₃ := B ⊗[A] (B ⊗[A] B)
  let x : D₂ ⊗[A] N := α.toFun D₂ includeLeft includeRight
  let i₁ : B →ₐ[A] D₃ := includeLeft
  let i₂ : B →ₐ[A] D₃ := includeRight.comp includeLeft
  let i₃ : B →ₐ[A] D₃ := includeRight.comp includeRight
  have hface (f : D₂ →ₐ[A] D₃) (g₁ g₂ : B →ₐ[A] D₃)
      (h₁ : f.comp includeLeft = g₁) (h₂ : f.comp includeRight = g₂) :
      map A N f x = α.toFun D₃ g₁ g₂ := by
    rw [← α.naturality, h₁, h₂]
  have h12 := hface (face12 A B) i₁ i₂ (by ext b; rfl) (by ext b; rfl)
  have h13 := hface (face13 A B) i₁ i₃ (by ext b; rfl) (by ext b; rfl)
  have h23 := hface (face23 A B) i₂ i₃ (by ext b; rfl) (by ext b; rfl)
  have hx : AmitsurDegreeOne.d1 A B N (TensorProduct.assoc A B B N x) = 0 := by
    rw [d1_assoc, h12, h13, h23, α.cocycle D₃ i₁ i₂ i₃]
    have hzero : α.toFun D₃ i₂ i₃ -
        (α.toFun D₃ i₁ i₂ + α.toFun D₃ i₂ i₃) + α.toFun D₃ i₁ i₂ = 0 := by abel
    rw [hzero, map_zero]
  obtain ⟨y, hy⟩ := AmitsurDegreeOne.exists_primitive A B N _ hx
  have hβ : map A N (includeLeft : B →ₐ[A] D₂) (-y) -
      map A N (includeRight : B →ₐ[A] D₂) (-y) = x := by
    apply (TensorProduct.assoc A B B N).injective
    rw [d0_assoc, map_neg, hy, neg_neg]
  refine ⟨-y, fun C _ _ a b => ?_⟩
  let f : D₂ →ₐ[A] C := productMap a b
  have h₁ : f.comp includeLeft = a := by ext c; exact productMap_left_apply a b c
  have h₂ : f.comp includeRight = b := by ext c; exact productMap_right_apply a b c
  rw [← h₁, ← h₂, α.naturality]
  change map A N f x = _
  rw [← hβ, map_sub]
  congr 1 <;>
    induction -y using TensorProduct.inductionOn with
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul c n => rfl

end Cocycle

end Langlands.AlgebraicGeometry.AffineModuleCocycle
