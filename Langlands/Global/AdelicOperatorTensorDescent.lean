import Langlands.Global.AdelicOperatorTensor
import Langlands.Automorphic.OperatorSubquotientLocalComponentStatement

/-! # Simultaneous descent for the prescribed adelic tensor factors -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Classical TensorProduct

universe u

namespace Langlands.Global.AdelicOperatorTensor

open NumberField Langlands.Archimedean Langlands.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem liftedGKDense {K L V : Type} [Group K] [TopologicalSpace K]
    [LieRing L] [LieAlgebra ℂ L] [AddCommGroup V] [Module ℂ V]
    {κ : Representation ℂ K V} {δ : L →ₗ⁅ℂ⁆ Module.End ℂ V} (h : GKModuleDensity.Hyp κ δ)
    (s : Finset (ULift.{u} V)) (T : Module.End ℂ (ULift.{u} V)) :
    ∃ A ∈ Algebra.adjoin ℂ (Set.range fun g : ULift.{u} (K ⊕ L) =>
      ULift.moduleEquiv.symm.conjAlgEquiv ℂ (GKModuleDensity.gens κ δ g.down)),
      ∀ x ∈ s, A x = T x := by
  let E : ULift.{u} V ≃ₗ[ℂ] V := ULift.moduleEquiv
  let φ := E.symm.conjAlgEquiv ℂ
  let gen := GKModuleDensity.gens κ δ
  have hgen : (Set.range fun g : ULift.{u} (K ⊕ L) => φ (gen g.down)) =
      φ.toAlgHom '' Set.range gen := by
    ext A
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨gen g.down, ⟨g.down, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨ULift.up g, rfl⟩
  obtain ⟨b, hb⟩ := GKModuleDensity.exists_freeAlgebra_eq h (s.image E) (φ.symm T)
  let B := FreeAlgebra.lift ℂ gen b
  have hB : B ∈ Algebra.adjoin ℂ (Set.range gen) := by
    rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift]
    exact ⟨b, rfl⟩
  refine ⟨φ B, ?_, ?_⟩
  · change φ B ∈ Algebra.adjoin ℂ (Set.range fun g : ULift.{u} (K ⊕ L) => φ (gen g.down))
    rw [hgen, ← AlgHom.map_adjoin]
    exact ⟨B, hB, rfl⟩
  · intro x hx
    have hx' := hb (E x) (Finset.mem_image_of_mem E hx)
    have hT : φ (φ.symm T) = T := φ.apply_symm_apply T
    rw [← hT]
    change E.symm (B (E x)) = E.symm ((φ.symm T) (E x))
    exact congrArg E.symm hx'

variable {F : Type u} [Field F] [NumberField F] {n r : ℕ}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "RK(" t ")" => Matrix.unitaryGroup (Fin t) ℝ
local notation "CK(" t ")" => Matrix.unitaryGroup (Fin t) ℂ
local notation "RL(" t ")" => ℂ ⊗[ℝ] Matrix (Fin t) (Fin t) ℝ
local notation "CL(" t ")" => ℂ ⊗[ℝ] Matrix (Fin t) (Fin t) ℂ

omit [NumberField F] in
private theorem nontrivial_slotSpace {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    (hf : Nontrivial Vf) (hr : ∀ v, Nontrivial (Vr v))
    (hc : ∀ v, Nontrivial (Vc v)) (i : Slot F) : Nontrivial (SlotSpace F Vf Vr Vc i) := by
  rcases i with _ | v | v
  · exact hf
  · let := hr v
    exact inferInstanceAs (Nontrivial (ULift (Vr v)))
  · let := hc v
    exact inferInstanceAs (Nontrivial (ULift (Vc v)))

/-- The free action on the prescribed tensor is irreducible if the finite
translations are dense and each archimedean factor satisfies admissible
`(𝔤, K)` density. -/
theorem isIrreducible_of_density {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    {fin : Representation ℂ (FiniteAdelicGL F n) Vf}
    {κr : ∀ v : RP, Representation ℂ RK(n) (Vr v)}
    {δr : ∀ v : RP, RL(n) →ₗ⁅ℂ⁆ Module.End ℂ (Vr v)}
    {κc : ∀ v : CP, Representation ℂ CK(n) (Vc v)}
    {δc : ∀ v : CP, CL(n) →ₗ⁅ℂ⁆ Module.End ℂ (Vc v)}
    {ρ : Representation ℂ (FreeOperatorAlgebra F n) (Space F Vf Vr Vc)}
    (hslot : HasActions F n fin κr δr κc δc ρ) (hne : Nontrivial Vf)
    (hfin : ∀ (s : Finset Vf) (T : Module.End ℂ Vf),
      ∃ A ∈ Algebra.adjoin ℂ (Set.range fin), ∀ x ∈ s, A x = T x)
    (hr : ∀ v, GKModuleDensity.Hyp (κr v) (δr v))
    (hc : ∀ v, GKModuleDensity.Hyp (κc v) (δc v)) : ρ.IsIrreducible := by
  let := Fintype.ofFinite (Slot F)
  refine tensor_isIrreducible_of_slot_density ρ (generatorAction F n fin κr δr κc δc)
    (liftGenerator F n) hslot
    (nontrivial_slotSpace hne (fun v => (hr v).irreducible.1) (fun v => (hc v).irreducible.1)) ?_
  rintro (_ | v | v) s T
  · exact hfin s T
  · exact liftedGKDense (hr v) s T
  · exact liftedGKDense (hc v) s T

private theorem exists_gkEmbedding_of_lift {K L V : Type} {W : Type u}
    [Group K] [LieRing L] [LieAlgebra ℂ L]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {κ : Representation ℂ K V} {δ : L →ₗ⁅ℂ⁆ Module.End ℂ V}
    {κ' : Representation ℂ K W} {δ' : L →ₗ⁅ℂ⁆ Module.End ℂ W}
    (j : ULift.{u} V →ₗ[ℂ] W) (hj : Function.Injective j)
    (h : ∀ (g : K ⊕ L) x,
      j ((ULift.moduleEquiv.symm.conjAlgEquiv ℂ (GKModuleDensity.gens κ δ g)) x) =
        GKModuleDensity.gens κ' δ' g (j x)) :
    ∃ j' : V →ₗ[ℂ] W, Function.Injective j' ∧ j' ∈ gkHoms κ δ κ' δ' := by
  let E : ULift.{u} V ≃ₗ[ℂ] V := ULift.moduleEquiv
  refine ⟨j ∘ₗ E.symm.toLinearMap, hj.comp E.symm.injective, ?_⟩
  refine ⟨fun k x => ?_, fun X x => ?_⟩
  · exact h (.inl k) (E.symm x)
  · exact h (.inr X) (E.symm x)

/-- The grouped finite factor and all infinite factors embed in the same quotient
for their actual finite, compact and complexified Lie operators. -/
def HasPlaceEmbeddings {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    (Q : IrreducibleOperatorSubquotient F r)
    (fin : Representation ℂ (FiniteAdelicGL F (r + 1)) Vf)
    (κr : ∀ v : RP, Representation ℂ RK(r + 1) (Vr v))
    (δr : ∀ v : RP, RL(r + 1) →ₗ⁅ℂ⁆ Module.End ℂ (Vr v))
    (κc : ∀ v : CP, Representation ℂ CK(r + 1) (Vc v))
    (δc : ∀ v : CP, CL(r + 1) →ₗ⁅ℂ⁆ Module.End ℂ (Vc v)) : Prop :=
  (∃ j : fin.IntertwiningMap Q.subquotient.finiteRepresentation, Function.Injective j.toLinearMap) ∧
  (∀ v : RP, ∃ j : Vr v →ₗ[ℂ] Q.Space, Function.Injective j ∧
    j ∈ gkHoms (κr v) (δr v) (Q.subquotient.realPlaceCompactRepresentation v)
      (Q.subquotient.realPlaceLieAction v)) ∧
  (∀ v : CP, ∃ j : Vc v →ₗ[ℂ] Q.Space, Function.Injective j ∧
    j ∈ gkHoms (κc v) (δc v) (Q.subquotient.complexPlaceCompactRepresentation v)
      (Q.subquotient.complexPlaceLieAction v))

set_option maxHeartbeats 3600000 in
private theorem placeEmbeddings_of_slots {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    {fin : Representation ℂ (FiniteAdelicGL F (r + 1)) Vf}
    {κr : ∀ v : RP, Representation ℂ RK(r + 1) (Vr v)}
    {δr : ∀ v : RP, RL(r + 1) →ₗ⁅ℂ⁆ Module.End ℂ (Vr v)}
    {κc : ∀ v : CP, Representation ℂ CK(r + 1) (Vc v)}
    {δc : ∀ v : CP, CL(r + 1) →ₗ⁅ℂ⁆ Module.End ℂ (Vc v)}
    (Q : IrreducibleOperatorSubquotient F r)
    (hQ : ∀ i : Slot F, ∃ j : SlotSpace F Vf Vr Vc i →ₗ[ℂ] Q.Space, Function.Injective j ∧
      ∀ (g : Generator F (r + 1) i) x, j (generatorAction F (r + 1) fin κr δr κc δc i g x) =
        Q.subquotient.freeRepresentation (liftGenerator F (r + 1) i g) (j x)) :
    HasPlaceEmbeddings Q fin κr δr κc δc := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨j, hj, hmap⟩ := hQ (.inl ())
    refine ⟨⟨j, ?_⟩, hj⟩
    intro d
    apply LinearMap.ext
    intro x
    have hd := hmap d x
    change j (fin d x) =
      Q.subquotient.freeRepresentation (FreeAlgebra.ι ℂ (Sum.inl (Sum.inl d))) (j x) at hd
    exact hd.trans (LinearMap.congr_fun (Q.subquotient.freeRepresentation_finite d) (j x))
  · intro v
    obtain ⟨j, hj, hmap⟩ := hQ (.inr (.inl v))
    have hgen (g : RK(r + 1) ⊕ RL(r + 1)) :
        Q.subquotient.freeRepresentation (liftGenerator F (r + 1) (.inr (.inl v)) ⟨g⟩) =
          GKModuleDensity.gens (Q.subquotient.realPlaceCompactRepresentation v)
            (Q.subquotient.realPlaceLieAction v) g := by
      rcases g with k | X
      · exact Q.subquotient.freeRepresentation_realPlaceCompact v k
      · exact Q.subquotient.freeRepresentation_realPlaceLie v X
    exact exists_gkEmbedding_of_lift (κ := κr v) (δ := δr v) j hj fun g x =>
      (hmap ⟨g⟩ x).trans (LinearMap.congr_fun (hgen g) (j x))
  · intro v
    obtain ⟨j, hj, hmap⟩ := hQ (.inr (.inr v))
    have hgen (g : CK(r + 1) ⊕ CL(r + 1)) :
        Q.subquotient.freeRepresentation (liftGenerator F (r + 1) (.inr (.inr v)) ⟨g⟩) =
          GKModuleDensity.gens (Q.subquotient.complexPlaceCompactRepresentation v)
            (Q.subquotient.complexPlaceLieAction v) g := by
      rcases g with k | X
      · exact Q.subquotient.freeRepresentation_complexPlaceCompact v k
      · exact Q.subquotient.freeRepresentation_complexPlaceLie v X
    exact exists_gkEmbedding_of_lift (κ := κc v) (δ := δc v) j hj fun g x =>
      (hmap ⟨g⟩ x).trans (LinearMap.congr_fun (hgen g) (j x))

local instance : AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F (r + 1)) := Submodule.addCommGroup _

set_option maxHeartbeats 1000000 in
/-- Descend an irreducible tensor quotient of a stable space of genuine automorphic forms. -/
theorem exists_with_placeEmbeddings {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    {fin : Representation ℂ (FiniteAdelicGL F (r + 1)) Vf}
    {κr : ∀ v : RP, Representation ℂ RK(r + 1) (Vr v)}
    {δr : ∀ v : RP, RL(r + 1) →ₗ⁅ℂ⁆ Module.End ℂ (Vr v)}
    {κc : ∀ v : CP, Representation ℂ CK(r + 1) (Vc v)}
    {δc : ∀ v : CP, CL(r + 1) →ₗ⁅ℂ⁆ Module.End ℂ (Vc v)}
    {ρ : Representation ℂ (FreeOperatorAlgebra F (r + 1)) (Space F Vf Vr Vc)}
    (hslot : HasActions F (r + 1) fin κr δr κc δc ρ) (hne : Nontrivial Vf)
    (hr : ∀ v, Nontrivial (Vr v)) (hc : ∀ v, Nontrivial (Vc v)) (hirr : ρ.IsIrreducible)
    (S : Subrepresentation
      ((stableAutomorphicAction F (r + 1)).comp (freeOperatorProjection F (r + 1)).toMonoidHom))
    (f : S.toRepresentation.IntertwiningMap ρ) (hf : Function.Surjective f) :
    ∃ Q : IrreducibleOperatorSubquotient F r, HasPlaceEmbeddings Q fin κr δr κc δc := by
  obtain ⟨Q, hQ⟩ := exists_irreducibleOperatorSubquotient_with_slotEmbeddings
    (F := F) (r := r) ρ (generatorAction F (r + 1) fin κr δr κc δc) (liftGenerator F (r + 1))
    hslot (nontrivial_slotSpace hne hr hc) hirr S f hf
  exact ⟨Q, placeEmbeddings_of_slots Q hQ⟩

end Langlands.Global.AdelicOperatorTensor
