import Langlands.AlgebraicGeometry.RingEtaleGroupoidLevel

/-! # Stable subalgebras of algebras with a multiplicative coaction

For a ring étale groupoid `t₀ : B₀ →+* C₀` acting on a `B₀`-algebra `D` by a multiplicative
coaction, a subalgebra `S ⊆ D` is stable when the coaction of each of its elements comes from
`C₀ ⊗[B₀] S`. Stable subalgebras inherit multiplicative coactions, and over a Noetherian `B₀`
every finite subset of `D` lies in a finitely generated stable subalgebra (the exhaustion step
of the proof of Stacks Project Lemma 70.15.1, using Lemma 39.15.4, Tag 07TU, in ring form).
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry

variable {B₀ C₀ D : Type u} [CommRing B₀] [CommRing C₀] [CommRing D] [Algebra B₀ C₀]
  [Algebra B₀ D] {t₀ : B₀ →+* C₀}

namespace RingEtaleGroupoid

theorem lTensor_eq_map {D' : Type u} [CommRing D'] [Algebra B₀ D'] (ψ : D →ₐ[B₀] D')
    (z : C₀ ⊗[B₀] D) :
    LinearMap.lTensor C₀ ψ.toLinearMap z = Algebra.TensorProduct.map (AlgHom.id B₀ C₀) ψ z := by
  induction z with
  | tmul c d => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end RingEtaleGroupoid

namespace GroupoidCoaction

/-- A subalgebra `S` is stable under a coaction if the coaction of every element of `S` lies in
the image of `C₀ ⊗[B₀] S`. -/
def IsStableSubalgebra (θ : GroupoidCoaction t₀ D) (S : Subalgebra B₀ D) : Prop :=
  ∀ x : S, θ.coaction x ∈ LinearMap.range (AlgebraTensorModule.lTensor C₀ C₀ S.val.toLinearMap)

variable (θ : GroupoidCoaction t₀ D) (S : Subalgebra B₀ D)

/-- The semilinear restriction of a coaction to a stable subalgebra. -/
noncomputable def subalgebraSemilinearMap [Module.Flat B₀ C₀] (hS : θ.IsStableSubalgebra S) :
    S →ₛₗ[t₀] C₀ ⊗[B₀] S :=
  (LinearEquiv.ofInjective (AlgebraTensorModule.lTensor C₀ C₀ S.val.toLinearMap)
    (Module.Flat.lTensor_preserves_injective_linearMap S.val.toLinearMap
      Subtype.val_injective)).symm.toLinearMap.comp
    ((θ.semilinearMap.comp S.val.toLinearMap).codRestrict
      (LinearMap.range (AlgebraTensorModule.lTensor C₀ C₀ S.val.toLinearMap)) hS)

theorem subalgebraSemilinearMap_val [Module.Flat B₀ C₀] (hS : θ.IsStableSubalgebra S)
    (x : S) :
    LinearMap.lTensor C₀ S.val.toLinearMap (subalgebraSemilinearMap θ S hS x) =
      θ.coaction x := by
  exact LinearEquiv.ofInjective_symm_apply
    (AlgebraTensorModule.lTensor C₀ C₀ S.val.toLinearMap)
    (h := Module.Flat.lTensor_preserves_injective_linearMap S.val.toLinearMap
      Subtype.val_injective) _

end GroupoidCoaction

namespace RingEtaleGroupoid

open GroupoidCoaction

theorem lTensor_val_injective (hE₀ : RingEtaleGroupoid t₀) (S : Subalgebra B₀ D) :
    Function.Injective (LinearMap.lTensor C₀ S.val.toLinearMap) := by
  have := hE₀.flat
  exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

/-- The coaction restricted to a stable subalgebra. -/
noncomputable def subalgebraCoaction (hE₀ : RingEtaleGroupoid t₀) (θ : GroupoidCoaction t₀ D)
    (S : Subalgebra B₀ D) (hS : θ.IsStableSubalgebra S) : GroupoidCoaction t₀ S :=
  letI := hE₀.flat
  hE₀.coactionOfInjective θ S.val.toLinearMap Subtype.val_injective
    (subalgebraSemilinearMap θ S hS).toAddMonoidHom
    (fun b m => (subalgebraSemilinearMap θ S hS).map_smulₛₗ b m)
    (fun m => (subalgebraSemilinearMap_val θ S hS m).symm)

theorem subalgebraCoaction_val (hE₀ : RingEtaleGroupoid t₀) (θ : GroupoidCoaction t₀ D)
    (S : Subalgebra B₀ D) (hS : θ.IsStableSubalgebra S) (x : S) :
    Algebra.TensorProduct.map (AlgHom.id B₀ C₀) S.val
        ((hE₀.subalgebraCoaction θ S hS).coaction x) = θ.coaction x := by
  rw [← lTensor_eq_map]
  let := hE₀.flat
  exact subalgebraSemilinearMap_val θ S hS x

theorem subalgebraCoaction_isMultiplicative (hE₀ : RingEtaleGroupoid t₀)
    (θ : GroupoidCoaction t₀ D) (hθ : θ.IsMultiplicative) (S : Subalgebra B₀ D)
    (hS : θ.IsStableSubalgebra S) : (hE₀.subalgebraCoaction θ S hS).IsMultiplicative := by
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id B₀ C₀) S.val : C₀ ⊗[B₀] S → C₀ ⊗[B₀] D) := by
    intro x y hxy
    apply hE₀.lTensor_val_injective S
    rw [lTensor_eq_map, lTensor_eq_map, hxy]
  constructor
  · apply hinj
    rw [subalgebraCoaction_val, map_one, OneMemClass.coe_one]
    exact hθ.map_one
  · intro x y
    apply hinj
    rw [map_mul (Algebra.TensorProduct.map (AlgHom.id B₀ C₀) S.val), subalgebraCoaction_val,
      subalgebraCoaction_val, subalgebraCoaction_val, MulMemClass.coe_mul]
    exact hθ.map_mul x y

end RingEtaleGroupoid

namespace GroupoidCoaction

theorem mem_range_lTensor_of_le {N : Submodule B₀ D} {S : Subalgebra B₀ D}
    (hNS : N ≤ Subalgebra.toSubmodule S) {z : C₀ ⊗[B₀] D}
    (hz : z ∈ LinearMap.range (AlgebraTensorModule.lTensor C₀ C₀ N.subtype)) :
    z ∈ LinearMap.range (AlgebraTensorModule.lTensor C₀ C₀ S.val.toLinearMap) := by
  obtain ⟨w, rfl⟩ := hz
  let ι : N →ₗ[B₀] S :=
    { toFun := fun n => ⟨n.1, hNS n.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨AlgebraTensorModule.lTensor C₀ C₀ ι w, ?_⟩
  change LinearMap.lTensor C₀ S.val.toLinearMap (LinearMap.lTensor C₀ ι w) =
    LinearMap.lTensor C₀ N.subtype w
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
  rfl

/-- The subalgebra generated by a set whose coactions lie in the image of the generated
subalgebra is stable: elements with this property form a subalgebra, because the coaction is
multiplicative. -/
theorem isStableSubalgebra_adjoin (θ : GroupoidCoaction t₀ D) (hθ : θ.IsMultiplicative)
    (X : Set D)
    (hX : ∀ x ∈ X, θ.coaction x ∈
      LinearMap.range (AlgebraTensorModule.lTensor C₀ C₀ (Algebra.adjoin B₀ X).val.toLinearMap)) :
    θ.IsStableSubalgebra (Algebra.adjoin B₀ X) := by
  let S := Algebra.adjoin B₀ X
  let M : C₀ ⊗[B₀] S →ₐ[B₀] C₀ ⊗[B₀] D := Algebra.TensorProduct.map (AlgHom.id B₀ C₀) S.val
  have hrange : ∀ z : C₀ ⊗[B₀] D,
      z ∈ LinearMap.range (AlgebraTensorModule.lTensor C₀ C₀ S.val.toLinearMap) ↔
        z ∈ M.range := by
    intro z
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w, (RingEtaleGroupoid.lTensor_eq_map S.val w).symm⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w, RingEtaleGroupoid.lTensor_eq_map S.val w⟩
  let P : Subalgebra B₀ D :=
    { (M.range.toSubring.comap (θ.toRingHom hθ)) with
      algebraMap_mem' := fun b => by
        change θ.coaction (algebraMap B₀ D b) ∈ M.range
        rw [θ.coaction_algebraMap hθ]
        exact ⟨t₀ b ⊗ₜ 1, by simp [M]⟩ }
  have hXP : Algebra.adjoin B₀ X ≤ P := by
    rw [Algebra.adjoin_le_iff]
    intro x hx
    exact (hrange _).mp (hX x hx)
  intro x
  exact (hrange _).mpr (hXP x.2)

end GroupoidCoaction

namespace RingEtaleGroupoid

open GroupoidCoaction

/-- Over a Noetherian base, every finite subset lies in a finitely generated stable
subalgebra. -/
theorem exists_fg_stableSubalgebra [IsNoetherianRing B₀] (hE₀ : RingEtaleGroupoid t₀)
    (θ : GroupoidCoaction t₀ D) (hθ : θ.IsMultiplicative) (s : Finset D) :
    ∃ S : Subalgebra B₀ D, S.FG ∧ (s : Set D) ⊆ S ∧ θ.IsStableSubalgebra S := by
  classical
  choose H hHfin hxH hHst using fun x : D => hE₀.exists_finite_stableSubmodule θ x
  choose G hG using fun x : D => (Module.Finite.iff_fg (N := H x)).mp (hHfin x)
  let T : Finset D := s.biUnion G
  have hHle : ∀ x ∈ s, H x ≤ Subalgebra.toSubmodule (Algebra.adjoin B₀ (T : Set D)) := by
    intro x hx
    rw [← hG x]
    refine (Algebra.span_le_adjoin B₀ _).trans ?_
    apply Algebra.adjoin_mono
    intro y hy
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨x, hx, hy⟩)
  refine ⟨Algebra.adjoin B₀ (T : Set D), ⟨T, rfl⟩, fun x hx => hHle x hx (hxH x), ?_⟩
  apply isStableSubalgebra_adjoin θ hθ
  intro y hy
  obtain ⟨x, hx, hyx⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hy)
  have hyH : y ∈ H x := by
    rw [← hG x]
    exact Submodule.subset_span hyx
  exact mem_range_lTensor_of_le (hHle x hx) (hHst x ⟨y, hyH⟩)

end RingEtaleGroupoid

end Langlands.AlgebraicGeometry
